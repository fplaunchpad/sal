// THE SYNC HUB (design-note step 4): a headless replica that lives with the
// relay and speaks the SAME gossip protocol as any peer, so a room's doc
// survives everyone disconnecting: push, leave, and someone else catches up
// later from the hub. Transport-agnostic: the node relay (src/relay.mjs)
// and the Cloudflare Durable Object (deploy/cloudflare/src/worker.mjs) both
// drive one HubPeer per room, feeding it the room's messages and giving it
// send/broadcast functions.
//
// INVISIBILITY: the hub never sends `join`, never authors an op, and never
// broadcasts presence, so clients never roster it -- it cannot block the
// certified GC's stability cut and never competes for the auto-GC
// leadership. It shows up only as `from: '#hub'` on protocol messages, and
// its merge commits are authorless like everyone else's.
//
// PERSISTENCE: every head change re-persists the whole record set through a
// RefStore (content-addressed, idempotent puts), debounced; on wake the hub
// rebuilds from the store, so a hibernated Durable Object or a restarted
// relay comes back with the doc.

import { Node } from './node.js';
import { NetworkNode } from './transport.js';
import { RefStore } from './idbstore.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';
import { compactiblePeritext } from '../../runtime/src/compact-peritext.js';

export const HUB_NAME = '#hub';

export const DATATYPES = Object.freeze({
  embedRGA: compactibleEmbedRGA,
  peritext: compactiblePeritext,
});

/** The Transport shape NetworkNode consumes, backed by caller-supplied
 *  send functions; incoming room traffic is fed via emit(). */
class HubTransport {
  constructor({ broadcast, sendTo }) {
    this.handlers = new Map();
    this.broadcastFn = broadcast;
    this.sendToFn = sendTo;
  }
  on(type, handler) {
    if (!this.handlers.has(type)) this.handlers.set(type, []);
    this.handlers.get(type).push(handler);
  }
  emit(msg) { const hs = this.handlers.get(msg.t); if (hs) for (const h of hs) h(msg); }
  send(obj) { this.broadcastFn({ ...obj, from: HUB_NAME }); }
  sendTo(name, obj) { this.sendToFn(name, { ...obj, from: HUB_NAME }); }
  close() {}
}

export class HubPeer {
  /** kv: the async KV the RefStore wraps (MemoryKV, openIdbKV, or the DO
   *  storage adapter); null disables persistence. */
  constructor({ room, datatypeLabel = 'embedRGA', kv = null, broadcast, sendTo }) {
    this.room = room;
    this.datatypeLabel = DATATYPES[datatypeLabel] ? datatypeLabel : 'embedRGA';
    this.store = kv ? new RefStore(kv) : null;
    this.tp = new HubTransport({ broadcast, sendTo });
    this.node = null;
    this.net = null;
    this.#persisting = null;
  }
  #persisting;

  /** Restore from the store (if any) and start speaking the protocol. The
   *  STORED datatype label wins over the constructor hint: a hibernated
   *  Durable Object can wake on a non-join message with no hint at all. */
  async init() {
    let node = null;
    if (this.store) {
      try {
        const meta = await this.store.getMeta(this.room);
        if (meta?.datatype && DATATYPES[meta.datatype]) this.datatypeLabel = meta.datatype;
      } catch {}
      try { node = await this.store.loadNode(this.room, DATATYPES[this.datatypeLabel], { name: HUB_NAME }); }
      catch (e) { console.warn(`[hub ${this.room}] store load failed: ${e.message}`); }
    }
    const datatype = DATATYPES[this.datatypeLabel];
    this.node = node ?? new Node(datatype, HUB_NAME);
    this.net = new NetworkNode(this.node, this.tp, {
      passive: false, // announce on join + pull-on-have: the availability behavior
      onChange: () => this.#persistSoon(),
    });
    return this;
  }

  /** Feed one already-`from`-tagged room message to the hub. */
  onMessage(msg) { this.tp.emit(msg); }
  /** A peer joined the room: the hub announces, the newcomer catches up. */
  onPeerJoin(name) { this.tp.emit({ t: 'join', name }); }
  onPeerLeave(name) { this.tp.emit({ t: 'leave', name }); }

  #persistSoon() {
    if (!this.store || this.#persisting) return;
    this.#persisting = (async () => {
      await new Promise((r) => setTimeout(r, 300)); // coalesce bursts
      this.#persisting = null;
      try {
        // certified history pruning: below a settled compact epoch nothing can
        // be needed again (gate inside pruneToEpochBase); fresh peers
        // bootstrap from the epoch base, so wake + storage stay O(document)
        if (typeof this.node.pruneToEpochBase === 'function') this.node.pruneToEpochBase();
        await this.store.persistNode(this.room, this.node,
          { datatypeLabel: this.datatypeLabel, pruneStored: true });
      } catch (e) { console.warn(`[hub ${this.room}] persist failed: ${e.message}`); }
    })();
  }

  /** Await any in-flight persist (tests + orderly shutdown). */
  async flushPersist() { while (this.#persisting) await this.#persisting; }
}
