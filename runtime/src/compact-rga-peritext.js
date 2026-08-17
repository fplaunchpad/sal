// Certified per-state GC for PeritextRGA. It removes a settled dead insertion
// only when its delete is also settled and no live character or mark endpoint
// needs that insertion as an anchor ancestor. Coordinates are unchanged.

import { peritextRGA } from './datatypes/peritext.js';
import { PMap, PSet, eachEntry } from './pmap.js';
import { a3Pairs, peritextCutFromMeet } from './compact-peritext.js';

function compact(s, cut = {}, opts = {}) {
  const adds = s.text.shadow.adds, deleted = s.text.deleted;
  const settled = cut.settledIds ?? new Set(), settledDel = cut.settledDelIds ?? new Set();
  const inflightIns = cut.inflightIns ?? [], inflightMarks = cut.inflightMarks ?? [];
  const pairDrop = opts.pairDrop !== false && opts.noRetention !== true;
  let marks = s.marks, markPairsDropped = 0;
  if (pairDrop) {
    const pairs = a3Pairs([...marks.values()], adds, inflightIns, inflightMarks,
      cut.settledMarkMids ?? new Set(), opts.unguardedPairDrop === true);
    if (pairs.length) {
      const mt = marks.begin();
      for (const [m, r] of pairs) if (mt.has(m.mid) && mt.has(r.mid)) {
        mt.delete(m.mid); mt.delete(r.mid); markPairsDropped++;
      }
      marks = mt.freeze();
    }
  }
  const keep = new Set();
  eachEntry(adds, (id) => {
    if (!deleted.has(id) || !settled.has(id) || !settledDel.has(id)) keep.add(id);
  });
  // A mark boundary needs its exact birth position even when the character is
  // dead. Keeping its anchor chain also preserves the tree traversal order.
  eachEntry(marks, (_mid, m) => { keep.add(m.startId); keep.add(m.endId); });
  for (const id of [...keep]) {
    for (let p = adds.get(id)?.anchorId; p !== null && p !== undefined; p = adds.get(p)?.anchorId) {
      if (keep.has(p)) break;
      keep.add(p);
    }
  }
  const at = PMap.empty().begin(), dt = PSet.empty().begin(), gt = s.text.shadow.grave.begin();
  eachEntry(adds, (id, r) => { if (keep.has(id)) at.set(id, r); });
  for (const id of deleted) if (keep.has(id)) dt.add(id);
  for (const id of s.text.shadow.grave) if (!keep.has(id)) gt.delete(id);
  const shadow = Object.freeze({ adds: at.freeze(), grave: gt.freeze(), order: null });
  const state = Object.freeze({ text: { shadow, deleted: dt.freeze() }, marks });
  const dropped = adds.size - shadow.adds.size;
  return { state, translate: new Map(), stats: {
    symbolsBefore: adds.size + deleted.size, symbolsAfter: shadow.adds.size + state.text.deleted.size,
    recordsBefore: adds.size, recordsAfter: shadow.adds.size, recordsDropped: dropped,
    retainedForMarks: [...keep].filter((id) => deleted.has(id)).length,
    markRecords: marks.size, markPairsDropped,
  } };
}

export const compactiblePeritextRGA = {
  ...peritextRGA,
  name: 'peritext-rga-compactible',
  compact,
  cutFromMeet: peritextCutFromMeet,
  remapState: (s, _map) => s,
  inverseTranslate: (_before, _after, _cut) => new Map(),
  symbolCount: (s) => s.text.shadow.adds.size + s.text.deleted.size + s.marks.size,
};
