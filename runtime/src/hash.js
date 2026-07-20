// CONTENT ADDRESSING for the commit DAG (task #108): a pure-JS SHA-256 and the
// canonical content-id scheme the whole runtime mints commit ids with. This is
// the CORE hash; the p2p demo (git persistence, the wire) imports it, so WIRE
// and DISK name the same commit the same way. It supersedes the FNV model hash
// that src/sync.js's Peer used to carry (a merge-only base36 hash that disagreed
// with the demo's SHA, forcing an FNV-vs-SHA cross-check seam #108 removes).
//
// Pure-JS and dependency-free (browser + Node, no node:crypto, no Buffer), so
// src/ stays runnable unchanged in both. The SHA-256 is a standard FIPS-180-4
// implementation over a UTF-8 string, checked bit-for-bit against node:crypto
// (empty-string and "abc" NIST vectors plus randomized agreement) in
// test/hash.test.js -- the runtime does not rest on a hand-rolled hash being
// merely plausible.
//
// A commit is CONTENT-ADDRESSED as a Merkle DAG, git style: a commit's id folds
// in its parents' ids, so the same logical commit gets the same id on every
// replica AND on disk. commitContentId() is the single derivation both the
// separate-store Peer (src/sync.js) and the first-class DistributedReplica
// (src/replica.js) mint through; the `hash` argument is PLUGGABLE (defaulting to
// the SHA content id) so a deployment can swap the digest without touching the
// commit shape.

const K = new Uint32Array([
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]);

const rotr = (x, n) => (x >>> n) | (x << (32 - n));

/** SHA-256 of a UTF-8 string, returned as a 64-char lowercase hex digest. */
export function sha256hex(str) {
  const msg = new TextEncoder().encode(str);
  const bitLen = msg.length * 8;
  // pad: 0x80, then zeros, then 64-bit big-endian length, to a 64-byte multiple
  const withOne = msg.length + 1;
  const total = withOne + ((56 - (withOne % 64) + 64) % 64) + 8;
  const buf = new Uint8Array(total);
  buf.set(msg);
  buf[msg.length] = 0x80;
  // 64-bit length: high 32 bits (JS ints are safe past 2^32 via division)
  const hi = Math.floor(bitLen / 0x100000000);
  const lo = bitLen >>> 0;
  const dv = new DataView(buf.buffer);
  dv.setUint32(total - 8, hi);
  dv.setUint32(total - 4, lo);

  let h0 = 0x6a09e667, h1 = 0xbb67ae85, h2 = 0x3c6ef372, h3 = 0xa54ff53a;
  let h4 = 0x510e527f, h5 = 0x9b05688c, h6 = 0x1f83d9ab, h7 = 0x5be0cd19;
  const w = new Uint32Array(64);

  for (let off = 0; off < total; off += 64) {
    for (let i = 0; i < 16; i++) w[i] = dv.getUint32(off + i * 4);
    for (let i = 16; i < 64; i++) {
      const s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >>> 3);
      const s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >>> 10);
      w[i] = (w[i - 16] + s0 + w[i - 7] + s1) >>> 0;
    }
    let a = h0, b = h1, c = h2, d = h3, e = h4, f = h5, g = h6, h = h7;
    for (let i = 0; i < 64; i++) {
      const S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
      const ch = (e & f) ^ (~e & g);
      const t1 = (h + S1 + ch + K[i] + w[i]) >>> 0;
      const S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
      const maj = (a & b) ^ (a & c) ^ (b & c);
      const t2 = (S0 + maj) >>> 0;
      h = g; g = f; f = e; e = (d + t1) >>> 0;
      d = c; c = b; b = a; a = (t1 + t2) >>> 0;
    }
    h0 = (h0 + a) >>> 0; h1 = (h1 + b) >>> 0; h2 = (h2 + c) >>> 0; h3 = (h3 + d) >>> 0;
    h4 = (h4 + e) >>> 0; h5 = (h5 + f) >>> 0; h6 = (h6 + g) >>> 0; h7 = (h7 + h) >>> 0;
  }
  const hex = (x) => (x >>> 0).toString(16).padStart(8, '0');
  return hex(h0) + hex(h1) + hex(h2) + hex(h3) + hex(h4) + hex(h5) + hex(h6) + hex(h7);
}

/** Stable JSON: object keys sorted recursively, so two structurally equal
 *  values serialize to the same string regardless of key insertion order (the
 *  content-address must not depend on how a peer happened to build the op). */
export function stableStringify(v) {
  if (v === null || typeof v !== 'object') return JSON.stringify(v);
  if (Array.isArray(v)) return '[' + v.map(stableStringify).join(',') + ']';
  const keys = Object.keys(v).sort();
  return '{' + keys.map((k) => JSON.stringify(k) + ':' + stableStringify(v[k])).join(',') + '}';
}

/** Deterministic content id: SHA-256 of the canonical (stable) JSON of `obj`,
 *  truncated to `n` hex chars (default 40, git-oid width). Truncation only ever
 *  affects collision probability, never determinism. */
export function contentId(obj, n = 40) {
  return sha256hex(stableStringify(obj)).slice(0, n);
}

/** THE ONE COMMIT CONTENT-ID DERIVATION (a Merkle DAG folding in parents):
 *    root       -> hash({ root: true })                       (shared)
 *    authored   -> hash({ p, replica, seq, payload })
 *    merge      -> hash({ p: sorted parents })                (merge(a,b)==merge(b,a))
 *    compaction -> hash({ compact: true, p, fp })             (fp = state fingerprint)
 *  `parentGids` are the content-ids of `commit.parents`, in parent order.
 *  `fingerprint` is only consulted for compaction commits (single non-root
 *  parent, null op); a datatype that never compacts need not provide one.
 *  `hash` is pluggable, defaulting to the SHA-256 content id. */
export function commitContentId(commit, parentGids, { fingerprint, hash = contentId } = {}) {
  if (commit.parents.length === 0) return hash({ root: true });
  if (commit.op !== null) {
    return hash({ p: parentGids, replica: commit.op.replica, seq: commit.op.seq, payload: commit.op.payload });
  }
  if (commit.parents.length === 1) {
    if (typeof fingerprint !== 'function') {
      throw new Error('commitContentId: a compaction commit needs a fingerprint function');
    }
    return hash({ compact: true, p: parentGids, fp: fingerprint(commit.state) });
  }
  return hash({ p: parentGids.slice().sort() });
}
