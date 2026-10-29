/**
 * Request generation and reduction.
 *
 * Requests are index-level edits on the displayed text of the block:
 *   { kind: 'insert', index, text }     text of one or two lowercase letters
 *   { kind: 'delete', start, end }      the half-open range [start, end)
 *   { kind: 'bold', start, end }        a toggle of [start, end)
 *
 * Generation options: `withBold` (default false) adds bold requests;
 * `openedReplicas` defaults to false.
 */
const ALPHABET = 'abcdefghijklmnopqrstuvwxyz';

/** Instance defaults for generation options. */
export function generateOptions(options) {
  return { steps: 12, withBold: false, partialDelivery: false, openedReplicas: false, ...options };
}

/** A request for a replica displaying `view`. */
export function nextRequest(rnd, view, opts) {
  const { int, pick } = rnd;
  const n = view.length;
  const kinds = n === 0 ? ['insert'] : opts.withBold ? ['insert', 'insert', 'delete', 'bold', 'bold'] : ['insert', 'insert', 'delete'];
  const kind = pick(kinds);
  if (kind === 'insert') {
    let text = '';
    for (let i = int(1, 2); i > 0; i--) text += pick([...ALPHABET]);
    return { kind, index: int(0, n), text };
  }
  const len = Math.min(int(1, 2), n);
  const start = int(0, n - len);
  return { kind, start, end: start + len };
}

/** Smaller requests: a range one character shorter, an insert without its last letter. */
export function reduceRequest(request) {
  if ((request.kind === 'delete' || request.kind === 'bold') && request.end - request.start > 1)
    return [{ reduction: 'shorten-range', request: { ...request, end: request.end - 1 }, to: request.end - 1 }];
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
  return `r${s.replica} ${s.kind} [${s.start},${s.end})`;
}
