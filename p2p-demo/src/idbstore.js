// The IndexedDB RefStore (task #95): a browser peer's durable local store, the
// non-node sibling of gitstore.js. Both persist a Node's commit DAG through the
// SAME record shape (`nodeRecords` / `rebuildNode`, exported from gitstore.js),
// so a doc saved by either backend round-trips identically: reads and the SHA
// head are preserved, and a tampered record trips the content-address gate on
// load (ingest recomputes each gid).
//
// WHY IndexedDB, not localStorage or the git dir: the #107 editor runs in a
// browser tab, where gitstore.js cannot (it shells out to `git`). A browser peer
// needs an origin-local store to survive tab close/reload and to open/edit
// offline. IndexedDB is async + transactional (persisting on each commit does
// not block typing, unlike synchronous localStorage), large-quota, stores
// structured records keyed by gid, and runs in a Web Worker. It is LOCAL-ONLY
// (the relay/hub still moves bytes) and evictable unless
// navigator.storage.persist() is called. See whiteboard/collab-design-note.md
// section 7.1.
//
// TESTABILITY: the store logic is written over a tiny async KV so it is unit
// tested headlessly against an in-memory backend (`MemoryKV`) with NO new
// dependency (node has no IndexedDB, and the demo's only dep is `ws`). The
// browser backend (`openIdbKV`) is a thin adapter over the real IndexedDB API,
// exercised in the browser/integration path, not the node unit test.

import { nodeRecords, rebuildNode } from './records.js'; // browser-safe (gitstore shells out to git)
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';

// objects are keyed `docId + SEP + sha`; refs are keyed `docId`. SEP is NUL,
// which never occurs in a hex sha (nor a sane docId), so the prefix test in
// getRecords isolates one doc and 'a' never matches 'ab's objects.
const SEP = String.fromCharCode(0);

/** In-memory KV: a Map of named stores, each a Map. Values are held as a
 *  structural clone (JSON round-trip) to mirror IndexedDB (which structured-
 *  clones on put) and so a caller cannot mutate a stored record in place. */
export class MemoryKV {
  #stores = new Map();
  #store(name) { if (!this.#stores.has(name)) this.#stores.set(name, new Map()); return this.#stores.get(name); }
  async get(store, key) { const v = this.#store(store).get(key); return v === undefined ? undefined : JSON.parse(v); }
  async put(store, key, val) { this.#store(store).set(key, JSON.stringify(val)); }
  async delete(store, key) { this.#store(store).delete(key); }
  async entries(store) { return [...this.#store(store).entries()].map(([k, v]) => [k, JSON.parse(v)]); }
}

/** IndexedDB KV (browser only): two object stores, 'refs' and 'objects', both
 *  with out-of-line string keys. Awaits transaction completion (the durability
 *  signal), not just request success. Throws in a non-browser environment. */
export function openIdbKV(dbName = 'sal-p2p') {
  if (typeof indexedDB === 'undefined') {
    throw new Error('openIdbKV: no IndexedDB here (browser only); use MemoryKV in node');
  }
  const dbP = new Promise((resolve, reject) => {
    const req = indexedDB.open(dbName, 1);
    req.onupgradeneeded = () => {
      const db = req.result;
      for (const s of ['refs', 'objects']) if (!db.objectStoreNames.contains(s)) db.createObjectStore(s);
    };
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error);
  });
  const withStore = (store, mode, fn) => dbP.then((db) => new Promise((resolve, reject) => {
    const t = db.transaction(store, mode);
    const rv = fn(t.objectStore(store));
    t.oncomplete = () => resolve(rv && typeof rv === 'object' && 'result' in rv ? rv.result : undefined);
    t.onerror = () => reject(t.error);
    t.onabort = () => reject(t.error);
  }));
  return {
    get: (store, key) => withStore(store, 'readonly', (os) => os.get(key)),
    put: (store, key, val) => withStore(store, 'readwrite', (os) => os.put(val, key)),
    delete: (store, key) => withStore(store, 'readwrite', (os) => os.delete(key)),
    entries: (store) => dbP.then((db) => new Promise((resolve, reject) => {
      const t = db.transaction(store, 'readonly');
      const os = t.objectStore(store);
      const kr = os.getAllKeys();
      const vr = os.getAll();
      t.oncomplete = () => resolve(kr.result.map((k, i) => [k, vr.result[i]]));
      t.onerror = () => reject(t.error);
    })),
  };
}

/** A durable RefStore over any KV (`MemoryKV` in node/tests, `openIdbKV()` in
 *  the browser). Objects are content-addressed records keyed `docId+SEP+sha`;
 *  `refs` holds the heads meta keyed `docId`. The whole-node convenience
 *  (`persistNode`/`loadNode`) mirrors gitstore's persist/load. */
export class RefStore {
  constructor(kv) { this.kv = kv; }

  // --- refs (mutable) ---
  async getHead(docId) { const h = await this.kv.get('refs', docId); return h ? h.head : null; }
  async getMeta(docId) { return (await this.kv.get('refs', docId)) ?? null; }
  async setMeta(docId, heads) { await this.kv.put('refs', docId, heads); }
  async listDocs() {
    const es = await this.kv.entries('refs');
    return es.map(([docId, h]) => ({ docId, head: h.head, replica: h.replica }));
  }

  // --- objects (immutable, content-addressed, idempotent by sha) ---
  async putObjects(docId, records) {
    for (const r of records) await this.kv.put('objects', docId + SEP + r.sha, r);
  }
  async getRecords(docId) {
    const pre = docId + SEP;
    const es = await this.kv.entries('objects');
    return es.filter(([k]) => k.startsWith(pre)).map(([, v]) => v);
  }

  // --- whole-node convenience (mirrors gitstore persist/load) ---
  async persistNode(docId, node, opts = {}) {
    const { records, heads } = nodeRecords(node, opts);
    await this.putObjects(docId, records); // idempotent: re-putting an existing sha is a no-op overwrite
    await this.setMeta(docId, heads);
    if (opts.pruneStored) {
      // mirror the dag exactly: drop stored records the node no longer holds
      // (epoch-base pruning removed them; content addressing keeps this safe)
      const keep = new Set(records.map((r) => r.sha));
      const pre = docId + SEP;
      for (const [k] of await this.kv.entries('objects')) {
        if (k.startsWith(pre) && !keep.has(k.slice(pre.length))) await this.kv.delete('objects', k);
      }
    }
    return { head: heads.head, commits: records.length };
  }
  async loadNode(docId, datatype = compactibleEmbedRGA, opts = {}) {
    const heads = await this.getMeta(docId);
    if (!heads) return null; // no such doc: do NOT fabricate an empty one
    const records = await this.getRecords(docId);
    // content-address gated in ingest; opts.name reopens as a new session name
    return rebuildNode(records, heads, datatype, opts);
  }

  async drop(docId) {
    await this.kv.delete('refs', docId);
    const pre = docId + SEP;
    const es = await this.kv.entries('objects');
    for (const [k] of es) if (k.startsWith(pre)) await this.kv.delete('objects', k);
  }
}
