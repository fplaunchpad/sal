/**
 * Request generation and reduction for Y.Text.
 *
 * Requests are index-level edits on the displayed text:
 *   { kind: 'insert', index, text, attrs }
 *   { kind: 'delete', index, len }
 *   { kind: 'format', index, len, attrs }
 *
 * Generation options: `withFormat` (default false) adds format requests and
 * bold inserts; `openedReplicas` defaults to `withFormat`.
 */
import { localEdit, viewsEqual } from './spec.js';

const ALPHABET = 'abcdefghijklmnopqrstuvwxyz';
const INSERT_ATTRS = [{}, { bold: true }];
const FORMAT_ATTRS = [{ bold: true }, { bold: null }, { italic: true }, { italic: null }];

/** Instance defaults for generation options. */
export function generateOptions(options) {
  const opts = { steps: 12, withFormat: false, partialDelivery: false, ...options };
  if (opts.openedReplicas === undefined) opts.openedReplicas = opts.withFormat;
  return opts;
}

/**
 * A request for a replica displaying `view`: an insert of one or two random
 * letters (bold or plain with formatting on), a delete of one or two
 * characters, or a format of one or two characters with one of bold, unbold,
 * italic, unitalic. A format that would change nothing yields null.
 */
export function nextRequest(rnd, view, opts) {
  const { int, pick } = rnd;
  const len = view.length;
  const kinds = len === 0 ? ['insert'] : opts.withFormat ? ['insert', 'insert', 'delete', 'format', 'format'] : ['insert', 'insert', 'delete'];
  const kind = pick(kinds);
  if (kind === 'insert') {
    const k = int(1, 2);
    let text = '';
    for (let i = 0; i < k; i++) text += pick([...ALPHABET]);
    const attrs = opts.withFormat ? pick(INSERT_ATTRS) : {};
    return { kind, index: int(0, len), text, attrs };
  }
  const l = Math.min(int(1, 2), len);
  const index = int(0, len - l);
  if (kind === 'delete') return { kind, index, len: l };
  const attrs = pick(FORMAT_ATTRS);
  const request = { kind: 'format', index, len: l, attrs };
  if (viewsEqual(localEdit(view, request), view)) return null;
  return { kind, index, len: l, attrs };
}

/** Smaller requests: a delete or format one character shorter, an insert without its last character. */
export function reduceRequest(request) {
  if ((request.kind === 'delete' || request.kind === 'format') && request.len > 1)
    return [{ reduction: 'shorten-len', request: { ...request, len: request.len - 1 }, to: request.len - 1 }];
  if (request.kind === 'insert' && request.text.length > 1)
    return [{ reduction: 'shorten-text', request: { ...request, text: request.text.slice(0, -1) }, to: request.text.slice(0, -1) }];
  return [];
}

/** One-line rendering of a schedule step. */
export function renderStep(s) {
  if (s.type === 'deliver') return `deliver ${s.from}->${s.to}`;
  if (s.type === 'send') return `send ${s.from}#${s.op}->${s.to}`;
  if (s.type === 'open') return `open r${s.replica} from ${s.from}`;
  const attrs = s.attrs && Object.keys(s.attrs).length ? ' ' + JSON.stringify(s.attrs) : '';
  if (s.kind === 'insert') return `r${s.replica} insert ${s.index} "${s.text}"${attrs}`;
  return `r${s.replica} ${s.kind} [${s.index},${s.index + s.len})${attrs}`;
}
