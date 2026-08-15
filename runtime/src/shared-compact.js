// Adapter from the prefix-sharing representation to the certified absolute-
// coordinate compactor and back. This keeps the existing settled-cut guards
// authoritative while changing only the physical representation.

import { PMap } from './pmap.js';
import { eliasDeltaCode } from './datatypes/embedRGA.js';
import { decodeChain, compactEliasDelta, remapState } from './compact.js';
import { sharedEmbedRGA, encodeSharedRuns, decodeSharedRuns } from './datatypes/sharedEmbedRGA.js';

const enc = eliasDeltaCode.enc;

const directNode = (parent, delta, source) => Object.freeze({
  parent, delta, id: source.id, birthId: source.birthId,
  birthParentId: source.birthParentId,
});

function coordOf(path) {
  const ds = [];
  while (path) { ds.push(path.delta); path = path.parent; }
  ds.reverse(); return ds.map(enc).join('');
}

export function sharedToAbsolute(state) {
  const t = PMap.empty().begin();
  for (const [id, rec] of state) t.set(id,
    Object.freeze({ coord: coordOf(rec.path), el: rec.el }));
  return t.freeze();
}

export function absoluteToShared(state, birthSource = null) {
  const root = { kids: new Map(), live: null };
  for (const [id, rec] of state) {
    let n = root;
    for (const delta of decodeChain(rec.coord)) {
      let child = n.kids.get(delta);
      if (!child) n.kids.set(delta, child = { delta, kids: new Map(), live: null });
      n = child;
    }
    const source = birthSource?.get(id)?.path;
    n.live = { id, el: rec.el, birthParentId: source?.birthParentId ?? 0 };
  }
  let synthetic = -1;
  const records = PMap.empty().begin(), stack = [];
  for (const n of root.kids.values()) stack.push({ n, parent: null });
  while (stack.length) {
    const { n, parent } = stack.pop();
    const id = n.live?.id ?? synthetic--;
    const path = Object.freeze({ parent, delta: n.delta, id,
      birthId: n.live?.id ?? null, birthParentId: n.live?.birthParentId ?? null });
    if (n.live) records.set(n.live.id, Object.freeze({ path, el: n.live.el }));
    for (const child of n.kids.values()) stack.push({ n: child, parent: path });
  }
  return records.freeze();
}

export function compactSharedEliasDelta(state, cut, opts = {}) {
  const result = compactEliasDelta(sharedToAbsolute(state), cut, opts);
  return { ...result, state: absoluteToShared(result.state, state) };
}

const decodeAt = (coord, i) => {
  let k = i, c = 0; while (coord[k++] === '1') c++;
  let L = 1; for (let q = 0; q < c; q++) L = 2 * L + Number(coord[k++]);
  let v = 1; for (let q = 0; q < L - 1; q++) v = 2 * v + Number(coord[k++]);
  return [v, k];
};

/** Direct guarded compaction over shared path nodes. */
export function compactSharedDirect(state, cut, opts = {}) {
  const settled = cut?.settledIds ?? new Set(), fuse = opts.fuseSpines === true;
  const unguarded = opts.unguardedRenumber === true; // negative control only
  const root = { path: null, parent: null, delta: null, children: new Map(),
    record: null, seedSettled: false, inflightChild: false, inflightHere: false,
    evidence: false, stable: true, out: null, newCoord: '' };
  const wraps = new Map();
  const ensure = (path) => {
    if (!path) return root;
    let w = wraps.get(path);
    if (w) return w;
    const parent = ensure(path.parent);
    w = { path, parent, delta: path.delta, children: new Map(), record: null,
      seedSettled: false, inflightChild: false, inflightHere: false,
      evidence: false, stable: false, out: null, newCoord: '' };
    wraps.set(path, w); parent.children.set(path.delta, w); return w;
  };
  for (const [id, rec] of state) ensure(rec.path).record = { id, rec };
  const childOf = (parent, delta) => {
    let w = parent.children.get(delta);
    if (w) return w;
    const pid = parent.path?.id ?? 0, source = Object.freeze({
      parent: parent.path, delta, id: pid + delta,
      birthId: pid + delta, birthParentId: parent.path?.birthId ?? 0,
    });
    w = { path: source, parent, delta, children: new Map(), record: null,
      seedSettled: false, inflightChild: false, inflightHere: false,
      evidence: false, stable: false, out: null, newCoord: '' };
    wraps.set(source, w); parent.children.set(delta, w); return w;
  };
  // Declared in-flight coordinates seed only their settled prefix. The first
  // unsettled child freezes its parent's sibling group.
  for (const coord of (cut?.inflight ?? [])) {
    let n = root, i = 0;
    while (i < coord.length) {
      const [d, j] = decodeAt(coord, i), candidate = (n.path?.id ?? 0) + d;
      if (!settled.has(candidate)) { n.inflightChild = true; break; }
      n = childOf(n, d); n.seedSettled = true; i = j;
    }
    if (i >= coord.length && n !== root) n.inflightHere = true;
  }
  // Frozen anchors are expressed in the current order frame, so addressing is
  // by path deltas rather than telescoped birth ids.
  for (const coord of (cut?.frozenAnchorCoords ?? [])) {
    let n = root, i = 0;
    while (i < coord.length) {
      const [d, j] = decodeAt(coord, i); n = childOf(n, d);
      n.seedSettled = true; i = j;
    }
    n.inflightChild = true;
  }
  const post = [], st = [root];
  while (st.length) { const n = st.pop(); post.push(n); for (const c of n.children.values()) st.push(c); }
  for (let i = post.length - 1; i >= 0; i--) {
    const n = post[i];
    n.evidence = n.seedSettled || (n.record !== null && settled.has(n.record.id))
      || [...n.children.values()].some((c) => c.evidence);
  }
  const stats = { nodesBefore: wraps.size, nodesAfter: 0, groupsRenumbered: 0,
    symbolsBefore: wraps.size, symbolsAfter: 0,
    groupsSkippedInflight: 0, groupsSkippedUnstable: 0,
    spinesFused: 0, levelsRemoved: 0, spinesSkippedInflight: 0 };
  const records = PMap.empty().begin();
  const work = [{ logical: root, outParent: null }];
  while (work.length) {
    const { logical, outParent } = work.pop();
    const kids = [...logical.children.values()].sort((a, b) => a.delta - b.delta);
    for (const c of kids) c.stable = logical.stable && c.evidence;
    const allStable = kids.length > 0 && kids.every((c) => c.stable);
    const renumber = allStable && (!logical.inflightChild || unguarded);
    if (renumber) stats.groupsRenumbered++;
    else if (allStable && logical.inflightChild) stats.groupsSkippedInflight++;
    else if (kids.length) stats.groupsSkippedUnstable++;
    for (let i = kids.length - 1; i >= 0; i--) {
      const head = kids[i], nd = renumber ? i + 1 : head.delta;
      const out = directNode(outParent, nd, head.path); stats.nodesAfter++;
      head.out = out; head.newCoord = (logical.newCoord ?? '') + enc(nd);
      let tail = head;
      if (fuse && tail.record === null && tail.stable && tail.children.size === 1
          && !tail.inflightChild && !tail.inflightHere) {
        const members = [tail];
        for (;;) {
          const next = tail.children.values().next().value;
          next.stable = tail.stable && next.evidence;
          if (next.record !== null || !next.stable || next.children.size !== 1
              || next.inflightChild || next.inflightHere) {
            if (next.inflightChild || next.inflightHere) stats.spinesSkippedInflight++;
            break;
          }
          members.push(next); tail = next;
        }
        if (members.length > 1) {
          for (const m of members) { m.out = out; m.newCoord = head.newCoord; }
          stats.spinesFused++; stats.levelsRemoved += members.length - 1;
        }
      }
      if (head.record) records.set(head.record.id,
        Object.freeze({ path: out, el: head.record.rec.el }));
      // A fused tail is dead by construction. Its children continue below the
      // single retained output level; an unfused head continues normally.
      work.push({ logical: tail, outParent: out });
    }
  }
  // Live records below a processed logical node are installed when that node
  // becomes a child head. Root can never carry a record.
  const translate = (coord) => {
    let n = root, i = 0;
    while (i < coord.length) {
      const [d, j] = decodeAt(coord, i);
      const child = n.children.get(d); if (!child) break;
      n = child; i = j;
    }
    return n.newCoord + coord.slice(i);
  };
  stats.symbolsAfter = stats.nodesAfter;
  return { state: records.freeze(), translate, stats };
}

export function remapSharedState(state, translate) {
  return absoluteToShared(remapState(sharedToAbsolute(state), translate), state);
}

export const compactibleSharedEmbedRGA = {
  ...sharedEmbedRGA,
  compact: compactSharedDirect,
  remapState: remapSharedState,
  coordState: sharedToAbsolute,
  encodeState: (state) => [...encodeSharedRuns(state)],
  decodeState: (bytes) => decodeSharedRuns(Uint8Array.from(bytes)),
  symbolCount: (state) => sharedEmbedRGA.nodeCount(state),
  saveBytes: (state) => encodeSharedRuns(state).length,
};
