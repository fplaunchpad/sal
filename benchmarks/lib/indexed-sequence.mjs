// Mutable implicit treap used only by benchmark adapters to translate a
// visible list position into a stable datatype id. It avoids charging Sal an
// O(n) Array.splice that is not part of the replicated datatype.

const size = (n) => n?.size ?? 0;
const refresh = (n) => { if (n) n.size = 1 + size(n.left) + size(n.right); return n; };

// Deterministic 32-bit mixer. Serial numbers are unique, so equal priorities
// are harmless and resolved consistently by merge's left preference.
const priority = (x) => {
  x = (x + 0x9e3779b9) >>> 0;
  x ^= x >>> 16; x = Math.imul(x, 0x21f0aaad) >>> 0;
  x ^= x >>> 15; x = Math.imul(x, 0x735a2d97) >>> 0;
  return (x ^ (x >>> 15)) >>> 0;
};

const node = (value, serial) => ({ value, priority: priority(serial), size: 1, left: null, right: null });

function split(root, rank) {
  if (!root) return [null, null];
  if (size(root.left) >= rank) {
    const [a, b] = split(root.left, rank);
    root.left = b;
    return [a, refresh(root)];
  }
  const [a, b] = split(root.right, rank - size(root.left) - 1);
  root.right = a;
  return [refresh(root), b];
}

function merge(a, b) {
  if (!a) return b;
  if (!b) return a;
  if (a.priority >= b.priority) {
    a.right = merge(a.right, b);
    return refresh(a);
  }
  b.left = merge(a, b.left);
  return refresh(b);
}

export class IndexedSequence {
  #root = null;
  #serial = 0;

  static from(values) {
    const result = new IndexedSequence();
    for (const value of values) result.insert(result.length, value);
    return result;
  }

  get length() { return size(this.#root); }

  get(rank) {
    if (!Number.isInteger(rank) || rank < 0 || rank >= this.length) return undefined;
    let cur = this.#root, k = rank;
    while (cur) {
      const left = size(cur.left);
      if (k < left) cur = cur.left;
      else if (k === left) return cur.value;
      else { k -= left + 1; cur = cur.right; }
    }
    return undefined;
  }

  insert(rank, value) {
    if (!Number.isInteger(rank) || rank < 0 || rank > this.length) throw new RangeError(`insert rank ${rank}`);
    const [a, b] = split(this.#root, rank);
    this.#root = merge(merge(a, node(value, ++this.#serial)), b);
  }

  delete(rank) {
    if (!Number.isInteger(rank) || rank < 0 || rank >= this.length) throw new RangeError(`delete rank ${rank}`);
    const [a, tail] = split(this.#root, rank);
    const [removed, b] = split(tail, 1);
    this.#root = merge(a, b);
    return removed.value;
  }

  toArray() {
    const out = [];
    const visit = (n) => { if (n) { visit(n.left); out.push(n.value); visit(n.right); } };
    visit(this.#root);
    return out;
  }
}

