/**
 * Positional client requests on a displayed document, their validity, their
 * generation and their reduction for the shrinker.
 *
 *   { kind: 'insert', block, index, text }   insert `text` at `index`
 *   { kind: 'delete', block, start, end }    delete [start, end)
 *   { kind: 'split', block, index }          split the block at `index`
 *   { kind: 'merge', block }                 append the block to its predecessor
 *   { kind: 'bold', block, start, end }      toggle bold on [start, end)
 *
 * `block` indexes the displayed (alive) blocks. Indices count characters;
 * generated text is ASCII. Requests that the demo answers without a
 * transaction (empty text or range, merging the first block) are invalid.
 *
 * Generation profiles: `text` issues insert, delete, split and merge;
 * `structure` only split and merge; `format` split, merge, delete and bold
 * and no insertion: whether inserted text inherits bold is unspecified by
 * the positional contract, so the formatted instance never asks it. Half
 * of the bold toggles select a whole block.
 */
import { blocksOf } from './spec.js';

/** Whether a request is valid on a displayed view. */
export function validOn(view, q) {
  const blocks = blocksOf(view);
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
    case 'delete':
    case 'bold':
      return Number.isInteger(q.start) && Number.isInteger(q.end) && q.start >= 0 && q.start < q.end && q.end <= n;
    default:
      return false;
  }
}

const LETTERS = 'XYZWVU';
let letter = 0;

/** A request for a replica displaying `view`, or null. */
export function nextRequest(rnd, view, options = {}) {
  const blocks = blocksOf(view);
  const profile = options.profile ?? (options.format ? 'format' : 'text');
  const crowded = blocks.length >= (options.maxBlocks ?? 6);
  const split = crowded ? 0.5 : 3;
  const weights = { text: { split, merge: 3, delete: 1, insert: 2 }, structure: { split, merge: 3 }, format: { split, merge: 3, delete: 0.5, bold: 3 } }[profile];
  if (!weights) throw new Error('unknown profile ' + profile);
  for (let attempt = 0; attempt < 8; attempt++) {
    const total = Object.values(weights).reduce((a, b) => a + b, 0);
    let x = rnd.next() * total;
    let kind = 'merge';
    for (const [k, w] of Object.entries(weights)) {
      if ((x -= w) < 0) {
        kind = k;
        break;
      }
    }
    const block = rnd.int(0, blocks.length - 1);
    const n = blocks[block].length;
    let q;
    if (kind === 'merge') q = { kind, block };
    else if (kind === 'split') q = { kind, block, index: rnd.int(0, n) };
    else if (kind === 'insert') q = { kind, block, index: rnd.int(0, n), text: LETTERS[letter++ % LETTERS.length] };
    else {
      if (n === 0) continue;
      if (kind === 'bold' && rnd.next() < 0.5) q = { kind, block, start: 0, end: n };
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
  if (q.kind === 'split' || q.kind === 'insert') for (let i = 0; i < q.index; i++) out.push({ ...q, index: i });
  if (q.kind === 'insert' && q.text.length > 1) out.push({ ...q, text: q.text[0] });
  if (q.kind === 'delete' || q.kind === 'bold') {
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
  const where = s.kind === 'merge' ? '' : s.kind === 'split' ? ` at ${s.index}` : s.kind === 'insert' ? ` ${JSON.stringify(s.text)} at ${s.index}` : ` [${s.start},${s.end})`;
  return `${s.replica}: ${s.kind} block ${s.block}${where}`;
}

/** Display of block lists: `a | b`, bold characters upper-cased in brackets. */
export function renderBlocks(v) {
  return blocksOf(v)
    .map((cs) => (cs.length ? cs.map((c) => (c.bold ? `[${c.text}]` : c.text)).join('') : 'empty'))
    .join(' | ') || '(no block)';
}

/** Every valid request of a profile on a displayed view (insertions insert `X`). */
export function allRequests(view, profile = 'text') {
  const blocks = blocksOf(view);
  const kinds = { text: ['insert', 'delete', 'split', 'merge'], structure: ['split', 'merge'], format: ['delete', 'split', 'merge', 'bold'] }[profile];
  const out = [];
  blocks.forEach((cs, block) => {
    const n = cs.length;
    for (const kind of kinds) {
      if (kind === 'merge') {
        if (block > 0) out.push({ kind, block });
      } else if (kind === 'split' || kind === 'insert') {
        for (let index = 0; index <= n; index++) out.push(kind === 'insert' ? { kind, block, index, text: 'X' } : { kind, block, index });
      } else for (let start = 0; start < n; start++) for (let end = start + 1; end <= n; end++) out.push({ kind, block, start, end });
    }
  });
  return out;
}
