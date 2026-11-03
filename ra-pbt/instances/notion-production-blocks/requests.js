/**
 * Positional client requests on a displayed document, their validity, their
 * generation and their reduction for the shrinker.
 *
 *   { kind: 'create', after }               an empty block after displayed block `after`
 *   { kind: 'insert', block, index, text }   insert `text` at `index`
 *   { kind: 'split', block, index }          split the block at `index`
 *   { kind: 'merge', block }                 append the block to its predecessor
 *   { kind: 'bold', block, start, end }      toggle bold on [start, end)
 *
 * `block` and `after` index the displayed (alive) blocks; `after: -1` is
 * valid only on an empty display. Generated text is ASCII.
 *
 * Profiles: `structure` (split, merge), `blocks` (create, split, merge,
 * insert), `format` (split, merge, bold: no insertion, as in the demo
 * instance), `mixed` (create, split, merge, insert, bold). Half of the bold
 * toggles select a whole block.
 */
import { blocksOf } from './spec.js';

export const PROFILES = {
  structure: { split: 3, merge: 3 },
  blocks: { create: 1, split: 3, merge: 3, insert: 2 },
  format: { split: 3, merge: 3, bold: 3 },
  mixed: { create: 1, split: 3, merge: 3, insert: 2, bold: 2 },
};

/** Whether a request is valid on a displayed view. */
export function validOn(view, q) {
  const blocks = blocksOf(view);
  if (q.kind === 'create') return Number.isInteger(q.after) && (q.after === -1 ? blocks.length === 0 : q.after >= 0 && q.after < blocks.length);
  const b = blocks[q.block];
  if (!Number.isInteger(q.block) || !b) return false;
  const n = b.length;
  switch (q.kind) {
    case 'merge':
      return q.block > 0;
    case 'split':
      return Number.isInteger(q.index) && q.index >= 0 && q.index <= n;
    case 'insert':
      return Number.isInteger(q.index) && q.index >= 0 && q.index <= n && typeof q.text === 'string' && q.text.length > 0;
    case 'bold':
      return Number.isInteger(q.start) && Number.isInteger(q.end) && q.start >= 0 && q.start < q.end && q.end <= n;
    default:
      return false;
  }
}

const LETTERS = 'XYZWVUTS';

/** A request for a replica displaying `view`, or null. */
export function nextRequest(rnd, view, options = {}) {
  const blocks = blocksOf(view);
  const weights = { ...PROFILES[options.profile ?? 'structure'] };
  if (!PROFILES[options.profile ?? 'structure']) throw new Error('unknown profile ' + options.profile);
  if (blocks.length >= (options.maxBlocks ?? 6)) {
    if (weights.split) weights.split = 0.5;
    if (weights.create) weights.create = 0.2;
  }
  if (blocks.length === 0) return weights.create ? { kind: 'create', after: -1 } : null;
  for (let attempt = 0; attempt < 8; attempt++) {
    const total = Object.values(weights).reduce((a, b) => a + b, 0);
    let x = rnd.next() * total;
    let kind = 'merge';
    for (const [k, w] of Object.entries(weights))
      if ((x -= w) < 0) {
        kind = k;
        break;
      }
    const block = rnd.int(0, blocks.length - 1);
    const n = blocks[block].length;
    let q;
    if (kind === 'create') q = { kind, after: block };
    else if (kind === 'merge') q = { kind, block };
    else if (kind === 'split') q = { kind, block, index: rnd.int(0, n) };
    else if (kind === 'insert') q = { kind, block, index: rnd.int(0, n), text: rnd.pick([...LETTERS]) };
    else {
      if (n === 0) continue;
      if (rnd.next() < 0.5) q = { kind, block, start: 0, end: n };
      else {
        const start = rnd.int(0, n - 1);
        q = { kind, block, start, end: rnd.int(start + 1, n) };
      }
    }
    if (validOn(view, q)) return q;
  }
  return null;
}

/** Smaller requests for the shrinker, most reduced first. */
export function reduceRequest(q) {
  const out = [];
  if (q.kind === 'create') {
    for (let a = 0; a < q.after; a++) out.push({ ...q, after: a });
    return out;
  }
  if (q.kind === 'split' || q.kind === 'insert') for (let i = 0; i < q.index; i++) out.push({ ...q, index: i });
  if (q.kind === 'insert' && q.text.length > 1) out.push({ ...q, text: q.text[0] });
  if (q.kind === 'bold') {
    if (q.end - q.start > 1) out.push({ ...q, end: q.end - 1 }, { ...q, start: q.start + 1 });
    if (q.start > 0) out.push({ ...q, start: q.start - 1, end: q.end - 1 });
  }
  for (let b = 0; b < q.block; b++) out.push({ ...q, block: b });
  return out;
}

/** One-line rendering of a schedule step. */
export function renderStep(s) {
  if (s.type === 'deliver') return `deliver ${s.from}->${s.to}`;
  if (s.type === 'send') return `send ${s.from}#${s.op}->${s.to}`;
  if (s.type === 'open') return `open ${s.replica} from ${s.from}`;
  if (s.kind === 'create') return `${s.replica}: create after block ${s.after}`;
  const where = s.kind === 'merge' ? '' : s.kind === 'split' ? ` at ${s.index}` : s.kind === 'insert' ? ` ${JSON.stringify(s.text)} at ${s.index}` : ` [${s.start},${s.end})`;
  return `${s.replica}: ${s.kind} block ${s.block}${where}`;
}

/** Display of block lists: `a | b`, bold characters in brackets, `empty` for an empty block. */
export function renderBlocks(v) {
  return (
    blocksOf(v)
      .map((cs) => (cs.length ? cs.map((c) => (c.bold ? `[${c.text}]` : c.text)).join('') : 'empty'))
      .join(' | ') || '(no block)'
  );
}

/** Every valid request of a profile on a displayed view (insertions insert `X`). */
export function allRequests(view, profile = 'structure') {
  const blocks = blocksOf(view);
  const kinds = Object.keys(PROFILES[profile]);
  const out = [];
  if (kinds.includes('create')) blocks.forEach((_, after) => out.push({ kind: 'create', after }));
  blocks.forEach((cs, block) => {
    const n = cs.length;
    for (const kind of kinds) {
      if (kind === 'merge') {
        if (block > 0) out.push({ kind, block });
      } else if (kind === 'split' || kind === 'insert') {
        for (let index = 0; index <= n; index++) out.push(kind === 'insert' ? { kind, block, index, text: 'X' } : { kind, block, index });
      } else if (kind === 'bold') for (let start = 0; start < n; start++) for (let end = start + 1; end <= n; end++) out.push({ kind, block, start, end });
    }
  });
  return out;
}
