// Trace loading for the josephg editing-trace corpus as checked into
// whiteboard/litmus/traces/ (*.json.gz). Format (see
// whiteboard/litmus/entropy_measure.py): doc.txns = [{patches: [[pos,
// ndel, content], ...], parents?, agent?, numChildren?}], doc.endContent,
// doc.kind ('concurrent' for the DAG-shaped ones; absent = sequential).
//
// flattenOps turns a SEQUENTIAL trace into per-char events, exactly the
// order entropy_measure.apply_patches applies them: for each patch, ndel
// single-char deletes at pos, then the content chars one at a time at
// pos, pos+1, ... This is the "per-char apply" workload of task #98.

import { readFileSync } from 'node:fs';
import { gunzipSync } from 'node:zlib';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const HERE = dirname(fileURLToPath(import.meta.url));
export const TRACES_DIR = join(HERE, '..', '..', 'whiteboard', 'litmus', 'traces');

export function loadTrace(name) {
  const path = join(TRACES_DIR, `${name}.json.gz`);
  return JSON.parse(gunzipSync(readFileSync(path)).toString('utf8'));
}

/** Per-char ops of a sequential trace: {t:'d', pos} | {t:'i', pos, ch}. */
export function flattenOps(doc) {
  if (doc.kind === 'concurrent') {
    throw new Error('flattenOps: sequential traces only');
  }
  const ops = [];
  for (const txn of doc.txns) {
    for (const patch of txn.patches) {
      const [pos, ndel, content] = patch;
      for (let k = 0; k < ndel; k++) ops.push({ t: 'd', pos });
      for (let i = 0; i < content.length; i++) {
        ops.push({ t: 'i', pos: pos + i, ch: content[i] });
      }
    }
  }
  return ops;
}

/** Deterministic PRNG (mulberry32) for the synthetic workloads. */
export function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a |= 0; a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

export const ALPHABET = 'abcdefghijklmnopqrstuvwxyz ABCDEFGHIJKLMNOPQRSTUVWXYZ.,';
export const randChar = (rng) => ALPHABET[Math.floor(rng() * ALPHABET.length)];
