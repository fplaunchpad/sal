// TRANSPORT (task #95, stage 2 client). A Transport carries the sync gossip
// (have / req / delta / ack / roster / join / leave) over a channel; WsTransport is
// the WebSocket-relay binding (browser + Node both use the global WebSocket).
// The interface is deliberately small -- send / sendTo / on / ready / close --
// so a WebRTC-datachannel mesh could implement the same shape and drop in
// under NetworkNode unchanged.
//
// NetworkNode binds a src/node.js Node to a Transport and speaks the gossip:
//   have  advertise my ancestry gids + head            (push, on local change)
//   req   "send me what I lack" (have-summary + head)   (pull, awaited)
//   delta the missing commits + head                    (reply or push)
//   ack   "I merged through this verified head/epoch"   (soft GC evidence)
// A pull is an awaited request/reply (rid-correlated), giving the headless
// integration test a DETERMINISTIC, criss-cross-free linear fold over the real
// socket. Opportunistic push handlers keep a live editor converging best-effort
// (a genuine concurrent-merge criss-cross is caught and left for the next fold;
// virtual-LCA resolution is task #90, out of scope).

import { CrissCrossError } from '../../runtime/src/lca.js';

const WS = globalThis.WebSocket; // Node >=22 and every browser expose this

export class WsTransport {
  constructor(url, room, name, { dt } = {}) {
    this.url = url; this.room = room; this.name = name;
    this.dt = dt; // datatype label for the room's HUB (peritext | embedRGA)
    this.handlers = new Map();
    this.closed = false;        // close() was called by us
    this.everConnected = false; // a roster was received at least once
    this.attempt = 0;           // reconnect backoff counter
    this.ready = new Promise((resolve, reject) => { this._resolveReady = resolve; this._rejectReady = reject; });
    this.#connect();
  }

  // Connect (or RECONNECT: browsers close sockets of long-backgrounded tabs;
  // without this the page becomes a zombie that says "connected" and silently
  // drops every send). After a successful re-join the transport emits a
  // synthetic local 'up' event; a drop emits 'down'. If the relay was never
  // reachable at all, ready rejects and no reconnect loop starts.
  #connect() {
    // room/name ride the URL too: the node relay ignores them, but the
    // Cloudflare deployment routes the upgrade to a per-room Durable Object
    // BEFORE any message can arrive (deploy/cloudflare/src/worker.mjs)
    const sep = this.url.includes('?') ? '&' : '?';
    const ws = this.ws = new WS(
      `${this.url}${sep}room=${encodeURIComponent(this.room)}&name=${encodeURIComponent(this.name)}`);
    ws.addEventListener('open', () => { ws.send(JSON.stringify({ t: 'join', room: this.room, name: this.name, dt: this.dt })); });
    ws.addEventListener('error', () => {}); // 'close' always follows; the retry lives there
    ws.addEventListener('message', (ev) => {
      let msg; try { msg = JSON.parse(typeof ev.data === 'string' ? ev.data : ev.data.toString()); } catch { return; }
      const rejoin = msg.t === 'roster' && this.everConnected;
      if (msg.t === 'roster') {
        this.roster = msg.names; this.attempt = 0;
        if (!this.everConnected) { this.everConnected = true; this._resolveReady(msg.names); }
      }
      this.#emit(msg);
      if (rejoin) this.#emit({ t: 'up', names: msg.names });
    });
    ws.addEventListener('close', () => {
      if (this.closed) return;
      // retry BOTH a mid-session drop and a failed FIRST connection (a
      // transient handshake failure must not brick the page: keep trying and
      // the session heals itself when the relay is reachable again). 'down'
      // is only emitted after a successful join, so early retries are silent.
      if (this.everConnected) this.#emit({ t: 'down' });
      const delay = Math.min(250 * 2 ** this.attempt++, 5000);
      setTimeout(() => { if (!this.closed) this.#connect(); }, delay);
    });
  }

  #emit(msg) { const hs = this.handlers.get(msg.t); if (hs) for (const h of hs) h(msg); }
  #raw(obj) { if (this.ws.readyState === 1) this.ws.send(JSON.stringify(obj)); } // drop while down; gossip self-heals on 'up'
  /** Broadcast to the room. */
  send(obj) { this.#raw(obj); }
  /** Address a single peer by name. */
  sendTo(name, obj) { this.#raw({ ...obj, to: name }); }
  on(type, handler) {
    if (!this.handlers.has(type)) this.handlers.set(type, []);
    this.handlers.get(type).push(handler);
  }
  close() { this.closed = true; try { this.ws.close(); } catch {} }
}

export class NetworkNode {
  // passive: pure PULL only -- no auto-announce, no unsolicited-push merges. The
  // headless test runs passive so convergence is driven ONLY by converge()'s
  // deterministic fold (no concurrent-merge criss-cross). The live UI runs
  // active (opportunistic announce) for a responsive editor.
  constructor(node, transport, { onChange, passive = false, manual = false } = {}) {
    this.node = node;
    this.tp = transport;
    this.onChange = onChange ?? (() => {});
    this.passive = passive;
    // manual: GIT-STYLE explicit merge. Deltas are still FETCHED eagerly
    // (ingest: content-addressed, head untouched -- `git fetch`), but
    // mergeWithGid (`git merge`) waits for mergeStaged(). Because merge3 is
    // total, merging never conflicts; manual is a consent policy, not a
    // safety one. An explicit pull() always merges (it IS an explicit sync).
    this.manual = manual;
    this.staged = new Set(); // fetched-not-merged peer heads
    this.rid = 0;
    this.pending = new Map(); // rid -> resolve
    this.#wire();
    // the 'roster' reply arrives with tp.ready, BEFORE this NetworkNode's
    // handler is attached, so seed the roster the transport already captured
    if (transport.roster) for (const nm of transport.roster) node.register(nm);
    // and ANNOUNCE: over node's ws, several frames from one TCP read fire as
    // back-to-back synchronous message events, so a have sent right after the
    // roster (a hub greeting a joiner) can arrive before these handlers
    // existed. Advertising now makes any lost greeting self-healing: the
    // other side's have-handler sends back what we lack.
    if (!this.passive && transport.roster) this.announce();
  }

  #wire() {
    const t = this.tp, n = this.node;
    t.on('roster', (m) => { for (const nm of m.names) n.register(nm); });
    t.on('join', (m) => { n.register(m.name); if (!this.passive) this.announce(); });
    // a departed peer that never AUTHORED anything is dropped from the roster
    // (else a drive-by lurker blocks the certified GC's stability cut forever)
    t.on('leave', (m) => { if (typeof n.unregister === 'function') n.unregister(m.name); });
    // reconnected after a drop: announce to catch up BOTH ways (peers send
    // back what I lack; my advertised head triggers their pull-on-have)
    t.on('up', () => { if (!this.passive) this.announce(); });
    t.on('req', (m) => {
      const c = n.delta(new Set(m.have));
      t.sendTo(m.from, { t: 'delta', rid: m.rid, c, head: n.headGid });
    });
    t.on('have', (m) => {
      const c = n.delta(new Set(m.gids));
      if (c.length) t.sendTo(m.from, { t: 'delta', c, head: n.headGid });
      // The announcer advertised a head OUTSIDE my ancestry: they hold commits
      // I lack, so pull (a have only tops up the ANNOUNCER; without this, a
      // lone typist's edits never reach an idle peer). Active mode only --
      // passive stays pure-pull so converge()'s fold remains deterministic.
      if (!this.passive && m.head && !n.ancestryGids().has(m.head))
        t.sendTo(m.from, { t: 'req', have: [...n.ancestryGids()], head: n.headGid });
    });
    t.on('delta', (m) => {
      if (m.rid !== undefined && this.pending.has(m.rid)) {
        this.#absorb(m, { forceMerge: true }); // an awaited pull is an EXPLICIT sync
        const r = this.pending.get(m.rid); this.pending.delete(m.rid); r(m);
      } else {
        // push: catch up, then re-advertise ONLY IF the merge actually advanced
        // our head. Re-advertising after a no-op or a DEFERRED merge (a
        // criss-cross / cross-epoch that was swallowed below, head unchanged)
        // makes the peer pull + push again, and we absorb + defer + re-announce
        // again: a tight ping-pong that pegs the CPU and never terminates
        // because nothing changes. Gate the re-advertise on real progress.
        if (this.#absorb(m) && !this.passive) this.announce();
      }
    });
    // The relay authenticates `from` as the joined transport identity. The
    // runtime also requires a locally held head with the same recomputed epoch.
    t.on('ack', (m) => {
      if (typeof n.acknowledgeFetch === 'function' && m.head && m.epoch !== undefined)
        n.acknowledgeFetch(m.from, m.head, m.epoch);
    });
  }

  /** Absorb a delta; return true iff it ADVANCED our head (real progress). */
  #absorb(m, { forceMerge = false } = {}) {
    const before = this.node.headGid;
    try {
      if (m.c && m.c.length) this.node.ingest(m.c); // fetch: always, cheap, content-addressed
      if (m.head) {
        if (this.manual && !forceMerge) {
          if (!this.node.ancestryGids().has(m.head)) this.staged.add(m.head);
        } else this.node.mergeWithGid(m.head);
      }
    } catch (e) {
      // a genuine criss-cross (task #90) or a cross-epoch merge that cannot be
      // resolved is DEFERRED, not fatal
      if (!(e instanceof CrissCrossError) && !/cross-epoch/.test(e.message)) throw e;
    }
    const changed = this.node.headGid !== before;
    // Return a receipt even when the fetch added no commits. In manual mode it
    // names the still-current head, so a staged epoch cannot unlock pruning.
    if (m.from && m.head)
      this.tp.sendTo(m.from, { t: 'ack', head: this.node.headGid, epoch: this.node.epochKey });
    if (changed) this.onChange(this.node);
    return changed;
  }

  /** Switch merge policy. Leaving manual mode merges everything staged. */
  setManual(on) {
    this.manual = !!on;
    if (!this.manual) this.mergeStaged();
  }

  /** The explicit `git merge`: fold every staged head into mine (three-way
   *  merges over commits ALREADY fetched -- works offline). Returns the count
   *  still staged (a deferred criss-cross stays for the next round). */
  mergeStaged() {
    const before = this.node.headGid;
    for (const g of [...this.staged]) {
      try { this.node.mergeWithGid(g); this.staged.delete(g); }
      catch (e) { if (!(e instanceof CrissCrossError) && !/cross-epoch/.test(e.message)) throw e; }
    }
    for (const g of [...this.staged]) if (this.node.ancestryGids().has(g)) this.staged.delete(g);
    if (this.node.headGid !== before) { this.onChange(this.node); if (!this.passive) this.announce(); }
    return this.staged.size;
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
