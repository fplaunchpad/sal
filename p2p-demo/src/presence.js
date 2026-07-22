// Presence (task #107): ephemeral, OFF-DAG peer awareness. Live cursors and
// selections + identity, carried alongside the document over the SAME transport
// as the sync gossip, but NEVER committed or persisted. Presence is not a CRDT
// op: it has no place in the merge, the history, or the durable store; a peer
// that goes away simply stops being heard. This module is the pure registry
// (no DOM, no network, no clock of its own: the caller passes `now`), so it is
// testable headlessly; the browser feeds it presence messages and renders its
// list().

/** A stable per-peer color from the name (deterministic hue), so a peer looks
 *  the same in every tab without any coordination. */
export function peerColor(name) {
  let h = 0;
  for (let i = 0; i < name.length; i++) h = (h * 31 + name.charCodeAt(i)) >>> 0;
  return `hsl(${h % 360} 70% 45%)`;
}

/** [lo, hi) reading-position span a presence covers; lo===hi is a bare cursor. */
export function presenceSpan(p) {
  return [Math.min(p.anchor, p.focus), Math.max(p.anchor, p.focus)];
}

export class Presence {
  constructor(ttlMs = 8000) { this.ttl = ttlMs; this.peers = new Map(); }

  /** Record a peer's cursor/selection at time `now`. A selection is [anchor,
   *  focus] in reading positions (anchor===focus is a bare cursor). Overwrites
   *  the peer's prior presence: only the latest matters (ephemeral). */
  update(name, { anchor, focus }, now) {
    this.peers.set(name, { name, anchor, focus, color: peerColor(name), seen: now });
    return this;
  }

  /** Explicit departure (a `leave` from the relay). */
  remove(name) { this.peers.delete(name); return this; }

  /** Drop peers unheard-from for longer than ttl (a tab closed without a leave).
   *  Deterministic: the caller supplies `now`. */
  prune(now) {
    for (const [n, p] of this.peers) if (now - p.seen > this.ttl) this.peers.delete(n);
    return this;
  }

  /** Live peers, name-sorted (a stable render order across tabs). */
  list() {
    return [...this.peers.values()].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
  }
}
