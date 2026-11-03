/**
 * Request generation and reduction for Loro text.
 *
 * Requests are index-level edits on the displayed text:
 *   { kind: 'insert', index, text }
 *   { kind: 'delete', index, len }
 *   { kind: 'mark', index, len, key, value }
 *   { kind: 'unmark', index, len, key }
 * Inserted text takes its attributes from the expand configuration; Loro's
 * insert takes none.
 *
 * Generation options: `withStyles` (default false) adds mark and unmark
 * requests; `styleKeys` (default every key of the expand table) restricts
 * them; `openedReplicas` defaults to `withStyles`.
 */
import { localEdit, viewsEqual, EXPAND } from './spec.js';

const ALPHABET = 'abcdefghijklmnopqrstuvwxyz';

/** Instance defaults for generation options. */
export function generateOptions(options) {
  const opts = { steps: 12, withStyles: false, partialDelivery: false, ...options };
  if (opts.openedReplicas === undefined) opts.openedReplicas = opts.withStyles;
  if (opts.styleKeys === undefined) opts.styleKeys = Object.keys(EXPAND);
  return opts;
}

/**
 * A request for a replica displaying `view`: an insert of one or two random
 * letters, a delete of one or two characters, or (with styles) a mark or
 * unmark of one to three characters with a key from `styleKeys`. A mark or
 * unmark that would change nothing yields null.
 */
export function nextRequest(rnd, view, opts) {
  const { int, pick } = rnd;
  const len = view.length;
  const kinds = len === 0 ? ['insert'] : opts.withStyles ? ['insert', 'insert', 'delete', 'mark', 'mark', 'unmark'] : ['insert', 'insert', 'delete'];
  const kind = pick(kinds);
  if (kind === 'insert') {
    const k = int(1, 2);
    let text = '';
    for (let i = 0; i < k; i++) text += pick([...ALPHABET]);
    return { kind, index: int(0, len), text };
  }
  const l = Math.min(int(1, kind === 'delete' ? 2 : 3), len);
  const index = int(0, len - l);
  if (kind === 'delete') return { kind, index, len: l };
  const key = pick(opts.styleKeys);
  const request = kind === 'mark' ? { kind, index, len: l, key, value: true } : { kind, index, len: l, key };
  if (viewsEqual(localEdit(view, request), view)) return null;
  return request;
}

/** Smaller requests: a delete or style one character shorter, an insert without its last character. */
export function reduceRequest(request) {
  if (request.kind !== 'insert' && request.len > 1) return [{ reduction: 'shorten-len', request: { ...request, len: request.len - 1 }, to: request.len - 1 }];
  if (request.kind === 'insert' && request.text.length > 1)
    return [{ reduction: 'shorten-text', request: { ...request, text: request.text.slice(0, -1) }, to: request.text.slice(0, -1) }];
  return [];
}

/** One-line rendering of a schedule step. */
export function renderStep(s) {
  if (s.type === 'deliver') return `deliver ${s.from}->${s.to}`;
  if (s.type === 'send') return `send ${s.from}#${s.op}->${s.to}`;
  if (s.type === 'open') return `open r${s.replica} from ${s.from}`;
  if (s.kind === 'insert') return `r${s.replica} insert ${s.index} "${s.text}"`;
  if (s.kind === 'delete') return `r${s.replica} delete [${s.index},${s.index + s.len})`;
  return `r${s.replica} ${s.kind} [${s.index},${s.index + s.len}) ${s.key}`;
}
