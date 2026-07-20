// TRANSPORT (task #95, stage 2 client). A Transport carries the sync gossip
// (have / req / delta / roster / join / leave) over a channel; WsTransport is
// the WebSocket-relay binding (browser + Node both use the global WebSocket).
// The interface is deliberately small -- send / sendTo / on / ready / close --
// so a WebRTC-datachannel mesh could implement the same shape and drop in
// under NetworkNode unchanged.
//
// NetworkNode binds a src/node.js Node to a Transport and speaks the gossip:
//   have  advertise my ancestry gids + head            (push, on local change)
//   req   "send me what I lack" (have-summary + head)   (pull, awaited)
//   delta the missing commits + head                    (reply or push)
// A pull is an awaited request/reply (rid-correlated), giving the headless
// integration test a DETERMINISTIC, criss-cross-free linear fold over the real
// socket. Opportunistic push handlers keep a live editor converging best-effort
// (a genuine concurrent-merge criss-cross is caught and left for the next fold;
// virtual-LCA resolution is task #90, out of scope).

import { CrissCrossError } from '../../runtime/src/lca.js';

const WS = globalThis.WebSocket; // Node >=22 and every browser expose this

export class WsTransport {
  constructor(url, room, name) {
    this.url = url; this.room = room; this.name = name;
    this.handlers = new Map();
    this.ws = new WS(url);
    this.ready = new Promise((resolve, reject) => {
      this.ws.addEventListener('open', () => this.#raw({ t: 'join', room, name }));
      this.ws.addEventListener('error', (e) => reject(e.error ?? new Error('ws error')));
      this._resolveReady = resolve;
    });
    this.ws.addEventListener('message', (ev) => {
      let msg; try { msg = JSON.parse(typeof ev.data === 'string' ? ev.data : ev.data.toString()); } catch { return; }
      if (msg.t === 'roster') { this.roster = msg.names; this._resolveReady(msg.names); }
      const hs = this.handlers.get(msg.t);
      if (hs) for (const h of hs) h(msg);
    });
  }
  #raw(obj) { this.ws.send(JSON.stringify(obj)); }
  /** Broadcast to the room. */
  send(obj) { this.#raw(obj); }
  /** Address a single peer by name. */
  sendTo(name, obj) { this.#raw({ ...obj, to: name }); }
  on(type, handler) {
    if (!this.handlers.has(type)) this.handlers.set(type, []);
    this.handlers.get(type).push(handler);
  }
  close() { try { this.ws.close(); } catch {} }
}

export class NetworkNode {
  // passive: pure PULL only -- no auto-announce, no unsolicited-push merges. The
  // headless test runs passive so convergence is driven ONLY by converge()'s
  // deterministic fold (no concurrent-merge criss-cross). The live UI runs
  // active (opportunistic announce) for a responsive editor.
  constructor(node, transport, { onChange, passive = false } = {}) {
    this.node = node;
    this.tp = transport;
    this.onChange = onChange ?? (() => {});
    this.passive = passive;
    this.rid = 0;
    this.pending = new Map(); // rid -> resolve
    this.#wire();
    // the 'roster' reply arrives with tp.ready, BEFORE this NetworkNode's
    // handler is attached, so seed the roster the transport already captured
    if (transport.roster) for (const nm of transport.roster) node.register(nm);
  }

  #wire() {
    const t = this.tp, n = this.node;
    t.on('roster', (m) => { for (const nm of m.names) n.register(nm); });
    t.on('join', (m) => { n.register(m.name); if (!this.passive) this.announce(); });
    t.on('req', (m) => {
      const c = n.delta(new Set(m.have));
      t.sendTo(m.from, { t: 'delta', rid: m.rid, c, head: n.headGid });
    });
    t.on('have', (m) => {
      const c = n.delta(new Set(m.gids));
      if (c.length) t.sendTo(m.from, { t: 'delta', c, head: n.headGid });
    });
    t.on('delta', (m) => {
      if (m.rid !== undefined && this.pending.has(m.rid)) {
        this.#absorb(m); const r = this.pending.get(m.rid); this.pending.delete(m.rid); r(m);
      } else {
        this.#absorb(m); if (!this.passive) this.announce(); // push: catch up, re-advertise
      }
    });
  }

  #absorb(m) {
    const before = this.node.headGid;
    try {
      if (m.c && m.c.length) this.node.ingest(m.c);
      if (m.head) this.node.mergeWithGid(m.head);
    } catch (e) {
      // a genuine criss-cross (task #90) or a cross-epoch merge (a peer GC'd
      // alone; the demo linearizes epochs at a barrier) is DEFERRED, not fatal
      if (!(e instanceof CrissCrossError) && !/cross-epoch/.test(e.message)) throw e;
    }
    if (this.node.headGid !== before) this.onChange(this.node);
  }

  /** Advertise my current ancestry + head to the room (push). */
  announce() {
    this.tp.send({ t: 'have', gids: [...this.node.ancestryGids()], head: this.node.headGid });
  }

  /** Pull everything `fromName` has that I lack; awaited (rid-correlated). */
  pull(fromName, timeoutMs = 4000) {
    const rid = ++this.rid;
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => { this.pending.delete(rid); reject(new Error(`pull ${fromName} timed out`)); }, timeoutMs);
      this.pending.set(rid, (m) => { clearTimeout(timer); resolve(m); });
      this.tp.sendTo(fromName, { t: 'req', rid, have: [...this.node.ancestryGids()], head: this.node.headGid });
    });
  }
}

/** DETERMINISTIC convergence over the transport: a criss-cross-free LINEAR
 *  FOLD. The hub pulls each peer in turn (sequential merges -> unique LCA),
 *  then every peer pulls the hub's final head (fast-forward). After it returns,
 *  all nodes hold equal reads. `nns` is an array of NetworkNode; nns[0] hubs. */
export async function converge(nns) {
  const hub = nns[0];
  for (let k = 1; k < nns.length; k++) await hub.pull(nns[k].node.name);
  for (let k = 1; k < nns.length; k++) await nns[k].pull(hub.node.name);
  // one more hub round in case a peer authored between the two passes
  for (let k = 1; k < nns.length; k++) await hub.pull(nns[k].node.name);
  for (let k = 1; k < nns.length; k++) await nns[k].pull(hub.node.name);
}

/** THE BARRIER that lets every node reach the SAME compaction epoch (the
 *  demo's linearized-compaction discipline; concurrent divergent compaction is
 *  the deferred protocol half). After convergence every node holds the same
 *  DAG but a DIFFERENT certified cut (each excludes itself from the frontier
 *  meet). One no-op CHECKPOINT round fixes that: once every node has published
 *  a commit that absorbed the whole converged history, each node's frontier
 *  meet equals the full pre-checkpoint history -- identical across nodes -- so
 *  every node's compactStable computes the IDENTICAL re-coding (same SHA), and
 *  the final converge dedups them. Returns the per-node compaction results.
 *  cpId must be an id never used as an insert (a `del` of it is a no-op). */
export async function barrierCompact(nns, cpId, opts) {
  await converge(nns);
  for (const nn of nns) nn.node.commit({ type: 'del', id: cpId }); // no-op checkpoint
  await converge(nns);
  const results = nns.map((nn) => nn.node.compactStable(opts));
  await converge(nns); // reconcile the (identical) compaction commits
  return results;
}
