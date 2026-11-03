import assert from 'node:assert/strict';
import { test } from 'node:test';
import { readFileSync, mkdtempSync, rmSync, linkSync, writeFileSync } from 'node:fs';
import { resolve, join } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';
import { extract, exportLibrary } from '../extract.mjs';
import { createRuntime } from '../runtime.mjs';
import { ProductionClient } from '../client.mjs';

const cache = process.env.NOTION_PRODUCTION_CACHE;
if (!cache) throw new Error('Set NOTION_PRODUCTION_CACHE to the hash-verified asset directory');
const extracted = extract(cache);
const spaceId = '00000000-0000-4000-8000-000000000100';
const block = n => ({ table: 'block', id: `00000000-0000-4000-8000-${String(n).padStart(12, '0')}`, spaceId });
const p = block(1), q = block(2);
function seeded(text = 'abc', session = 'seed') {
  const c = new ProductionClient(extracted, session);
  c.createBlock(p);
  if (text) c.apply(c.prepareInsert(p, 0, text));
  return c;
}

test('module bodies retain exact source ranges from verified production assets', () => {
  assert.ok(Object.keys(extracted.modules).length > 1000);
  const sources = new Map();
  for (const m of Object.values(extracted.modules)) {
    if (!sources.has(m.file)) sources.set(m.file, readFileSync(resolve(cache, m.file), 'utf8'));
    assert.equal(m.source, sources.get(m.file).slice(m.start, m.end));
    assert.notEqual(m.source, '');
  }
});

test('a same-length source modification fails the pinned hash check', () => {
  const temporary = mkdtempSync(join(tmpdir(), 'notion-integrity-control-'));
  try {
    const manifest = JSON.parse(readFileSync(new URL('../sources.json', import.meta.url)));
    for (const asset of manifest.assets) {
      const source = resolve(cache, asset.file), target = join(temporary, asset.file);
      if (asset.file === '79323.js') {
        const bytes = readFileSync(source); bytes[0] ^= 1; writeFileSync(target, bytes);
      } else linkSync(source, target);
    }
    assert.throws(() => extract(temporary), /Source mismatch: 79323.js/);
  } finally { rmSync(temporary, { recursive: true, force: true }); }
});

test('missing dependencies fail instead of using an editing fallback', () => {
  const r = createRuntime(extracted);
  assert.throws(() => r.require('not-a-module'), /Missing production module/);
  assert.equal(r.loaded.size, 0);
  const damaged = { ...extracted, modules: { ...extracted.modules } };
  delete damaged.modules['829138']; // Original text-item classes, required by the slice.
  assert.throws(() => {
    const c = new ProductionClient(damaged, 'A'); c.createBlock(p);
  }, /Missing production module 829138/);
});

test('runtime preserves constant as well as getter exports', () => {
  const r = createRuntime(extracted);
  assert.equal(r.require('490263').BQ.Bold, 'b');
  assert.notEqual(r.require('490263').BQ.Italic, 'b');
});

test('insert and delete use the original record handlers', () => {
  const c = seeded();
  assert.equal(c.text(p), 'abc');
  assert.notEqual(c.text(p), '');
  const deletion = c.prepareDelete(p, 1, 2);
  c.apply(deletion);
  assert.equal(c.text(p), 'ac');
  assert.notEqual(c.text(p), 'abc');
  c.apply(deletion);
  assert.equal(c.text(p), 'ac');
  assert.deepEqual(c.value(p).properties.title, [['ac']]);
});

test('bold covers only the requested characters and removal preserves text', () => {
  const c = seeded();
  c.apply(c.prepareBold(p, 0, 2));
  assert.deepEqual(c.rich(p), [['ab', [['b']]], ['c']]);
  assert.notDeepEqual(c.rich(p), [['abc', [['b']]]]);
  c.apply(c.prepareBold(p, 0, 2, false));
  assert.deepEqual(c.rich(p), [['abc']]);
  assert.notDeepEqual(c.rich(p), [['ab', [['b']]], ['c']]);
  assert.equal(c.text(p), 'abc');
});

test('insertion at the right bold boundary inherits formatting', () => {
  const c = seeded('ab');
  c.apply(c.prepareBold(p, 0, 1));
  c.apply(c.prepareInsert(p, 1, 'X'));
  assert.deepEqual(c.rich(p), [['aX', [['b']]], ['b']]);
  assert.notDeepEqual(c.rich(p), [['a', [['b']]], ['Xb']]);
});

test('concurrent inserts agree in both delivery orders and states are independent', () => {
  const base = seeded('ab').snapshot();
  const a = new ProductionClient(extracted, 'A', base);
  const b = new ProductionClient(extracted, 'B', base);
  const ax = a.prepareInsert(p, 1, 'X'), by = b.prepareInsert(p, 1, 'Y');
  a.apply(ax);
  assert.equal(a.text(p), 'aXb');
  assert.equal(b.text(p), 'ab');
  b.apply(by); a.apply(by); b.apply(ax);
  // Equal clocks sort by descending session ID: B's Y precedes A's X.
  assert.equal(a.text(p), 'aYXb');
  assert.equal(b.text(p), 'aYXb');
  assert.notEqual(a.text(p), 'aXYb');
});

test('split and cross-block movement preserve the complete suffix', () => {
  const c = seeded('abc'); c.createBlock(q);
  const split = c.prepareSplit(p, 1); c.apply(split);
  assert.equal(c.text(p), 'abc');
  c.apply(c.prepareMove(p, split[0], q));
  assert.equal(c.text(p), 'a');
  assert.equal(c.text(q), 'bc');
  assert.notEqual(c.text(q), 'b');
  assert.equal(c.text(p) + c.text(q), 'abc');
  assert.deepEqual(c.value(q).properties.title, [['bc']]);
});

test('a record-level merge appends the text before removing the source block', () => {
  const c = seeded('abc'); c.createBlock(q);
  c.apply(c.prepareInsert(q, 0, 'Z'));
  c.apply(c.prepareMerge(p, q));
  assert.equal(c.text(q), 'Zabc');
  assert.notEqual(c.text(q), 'Z');
  assert.equal(c.value(p).alive, false);
  assert.equal(c.value(q).alive, true);
  assert.notEqual(c.text(q), 'abcZ');
});

test('an insertion still addresses its instance after the suffix moves blocks', () => {
  const base = seeded('abc'); base.createBlock(q);
  const a = new ProductionClient(extracted, 'A', base.snapshot());
  const b = new ProductionClient(extracted, 'B', base.snapshot());
  const insertion = b.prepareInsert(p, 2, 'X');
  const split = a.prepareSplit(p, 1); a.apply(split);
  a.apply(a.prepareMove(p, split[0], q));
  a.apply(insertion);
  assert.equal(a.text(p), 'a');
  assert.equal(a.text(q), 'bXc');
  assert.notEqual(a.text(q), 'bc');
  assert.notEqual(a.text(p), 'aX');
});

test('formatting across instances leaves the other block unchanged', () => {
  const c = seeded('abc'); c.createBlock(q);
  c.apply(c.prepareInsert(q, 0, 'Z'));
  const split = c.prepareSplit(p, 1); c.apply(split);
  c.apply(c.prepareMove(p, split[0], q));
  assert.equal(c.text(q), 'Zbc');
  c.apply(c.prepareBold(q, 0, 3));
  assert.deepEqual(c.rich(q), [['Zbc', [['b']]]]);
  assert.deepEqual(c.rich(p), [['a']]);
  assert.notDeepEqual(c.rich(p), [['a', [['b']]]]);
});

test('formatting nonadjacent slices excludes the character in another block', () => {
  const c = seeded('abc'); c.createBlock(q);
  const first = c.prepareSplit(p, 1); c.apply(first);
  c.apply(c.prepareMove(p, first[0], q)); // a | bc
  const second = c.prepareSplit(q, 1); c.apply(second);
  c.apply(c.prepareMove(q, second[0], p)); // ac | b
  assert.equal(c.text(p), 'ac'); assert.equal(c.text(q), 'b');
  const marks = c.prepareBold(p, 0, 2);
  assert.equal(marks.length, 2);
  c.apply(marks);
  assert.deepEqual(c.rich(p), [['ac', [['b']]]]);
  assert.deepEqual(c.rich(q), [['b']]);
  assert.notDeepEqual(c.rich(q), [['b', [['b']]]]);
});

test('the exported library executes without Acorn, source cache or a server', async () => {
  const temporary = mkdtempSync(join(tmpdir(), 'notion-extraction-control-'));
  try {
    const destination = join(temporary, 'library');
    exportLibrary(cache, destination);
    assert.throws(() => exportLibrary(cache, destination), /EEXIST/);
    const { createClient } = await import(pathToFileURL(join(destination, 'index.mjs')));
    const c = createClient('standalone'); c.createBlock(p);
    c.apply(c.prepareInsert(p, 0, 'standalone'));
    assert.equal(c.text(p), 'standalone');
    assert.notEqual(c.text(p), '');
  } finally { rmSync(temporary, { recursive: true, force: true }); }
});
