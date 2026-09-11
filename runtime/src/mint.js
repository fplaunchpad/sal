// Protocol-owned Lamport allocation for datatypes whose logical operation
// identifiers are scalar JavaScript integers.  Collision freedom is
// conditional on assigning each simultaneously-live logical replica a unique
// slot.  We make that precondition explicit instead of hashing a replica name
// and silently accepting collisions.

export const DEFAULT_MINT_STRIDE = 1_000_000;

function natural(n, label) {
  if (!Number.isSafeInteger(n) || n < 0) throw new TypeError(`${label} must be a non-negative safe integer`);
  return n;
}

export class LamportMint {
  constructor({ slot, counter = 0, stride = DEFAULT_MINT_STRIDE } = {}) {
    natural(stride, 'mint stride');
    if (stride < 2) throw new RangeError('mint stride must be at least 2');
    natural(slot, 'mint slot');
    if (slot === 0 || slot >= stride) throw new RangeError(`mint slot must be in [1, ${stride})`);
    this.slot = slot;
    this.counter = natural(counter, 'mint counter');
    this.stride = stride;
  }

  observe(time) {
    if (!Number.isSafeInteger(time) || time < 0) return;
    this.counter = Math.max(this.counter, Math.floor(time / this.stride));
  }

  next() {
    const counter = this.counter + 1;
    const time = counter * this.stride + this.slot;
    if (!Number.isSafeInteger(time)) throw new RangeError('Lamport mint exhausted JavaScript safe integers');
    this.counter = counter;
    return time;
  }

  snapshot() { return { slot: this.slot, counter: this.counter, stride: this.stride }; }
}

/** The event timestamp represented by a generated RGA/Peritext operation. */
export function operationTime(op) {
  if (!op || typeof op !== 'object') return null;
  if (op.type === 'ins') return op.id;
  if (op.type === 'addMark' || op.type === 'removeMark') return op.mid ?? op.ts;
  if (op.type === 'del') return op.time;
  return op.time;
}

export function observePayload(clock, payload) {
  for (const op of Array.isArray(payload) ? payload : [payload]) clock.observe(operationTime(op));
}

/** Stamp an operation template. Anchors/targets remain caller-selected; the
 * protocol owns only freshness and causal-clock evidence. */
export function stampOperation(clock, op) {
  if (!op || typeof op !== 'object') throw new TypeError('generated operation must be an object');
  const time = clock.next();
  switch (op.type) {
    case 'ins': return { ...op, id: time };
    case 'del': return { ...op, time };
    case 'addMark':
    case 'removeMark': return { ...op, mid: time, ts: time };
    default: return { ...op, time };
  }
}
