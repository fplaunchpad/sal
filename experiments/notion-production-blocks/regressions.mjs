/**
 * Declared cases for the production block layer: the five demo schedules
 * N-001 to N-005 re-expressed through this instance, one minimal schedule
 * per failure class found by the search, the specification-reading and
 * harness artefacts, and controls that change one ingredient. Every case
 * states its predicted verdict (the exact set of failing checks and the
 * class of each failure) before it runs; expected displays and admitted
 * views are derived by hand from the positional contract and from the
 * specification's rules (comments), never read off the implementation.
 * Every equality has a companion inequality against the tempting wrong
 * answer.
 *
 * Notation: `a | b` is two displayed blocks, `empty` an empty block, `[a]`
 * a bold character; replica r has session A, B, ... unless stated.
 *
 *   NOTION_PRODUCTION_LIBRARY=<export> node regressions.mjs
 *
 * Writes results/regressions.json. Exit 0 when every case holds. The
 * library is verified before and after.
 */
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { execute, writeJson, sameViewSet } from '../../ra-pbt/src/index.js';
import { withVerifiedLibrary, productionBlocksInstance, textsOf, blocksOf } from '../../ra-pbt/instances/notion-production-blocks/index.js';
import { observeSchedule } from '../../ra-pbt/instances/notion-production-blocks/classify.js';
import { runClassified, shownAfter, admittedAt, split, merge, insert, bold, create, send, deliver, V, renderBlocks } from './lib.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const T = (v) => textsOf(v).map((t) => t || 'empty').join(' | ');

/** A case asserting the exact failing checks and, per failing check, the classes of its failures. */
function verdict(lib, { name, group, options, schedule, failing, classes = {}, finalSync = true, extra }) {
  return {
    name,
    group,
    expected: failing.length ? `fail: ${failing.map((c) => `${c} (${(classes[c] ?? []).join(', ')})`).join('; ')}` : 'pass',
    run(results) {
      const r = runClassified(lib, options, schedule, { finalSync });
      results.failing = r.failing;
      results.classes = r.classes;
      results.final = r.trace.snapshots.slice(-schedule.replicas).map((s) => `r${s.replica}: ${renderBlocks(s.visible)}`);
      assert.deepEqual(r.failing, failing, `failing checks ${JSON.stringify(r.failing)}, predicted ${JSON.stringify(failing)}`);
      for (const [check, cls] of Object.entries(classes)) assert.deepEqual(r.classes[check], cls, `${check} classes ${JSON.stringify(r.classes[check])}, predicted ${JSON.stringify(cls)}`);
      extra?.(r, results);
    },
  };
}

const finalTexts = (r) => r.trace.snapshots.slice(-1)[0].visible;

export function cases(lib) {
  const out = [];
  const add = (c) => out.push(verdict(lib, c));

  // ------------------------------------------------------------ the demo catalogue on the production path
  /*
   * N-001 (sessions S, A, B, C, D; seed `a`). S splits at 0 and types X
   * into the empty first block (`X | a`); A and B both merge the second
   * block (`Xa`); C splits at 0, D at 1; C receives D's split and merges
   * block 2 into its predecessor; C splits block 1 at 0. Positional
   * contract of the last request on C's display `empty | Xa`: `empty |
   * empty | Xa`. The demo's layout was `empty | aX` and its split left
   * `empty | X | a`. Predicted: every check passes.
   */
  const n001 = {
    replicas: 5,
    steps: [split(1, 0, 0), insert(1, 0, 0, 'X'), deliver(1, 2), deliver(1, 3), merge(2, 1), merge(3, 1), deliver(3, 2), deliver(2, 4), deliver(2, 5), split(4, 0, 0), split(5, 0, 1), send(5, 4, 0), merge(4, 2), split(4, 1, 0)],
  };
  const o001 = { texts: ['a'], profile: 'blocks', sessions: ['S', 'A', 'B', 'C', 'D'] };
  add({
    name: 'N-001: split after concurrent restructuring',
    group: 'N-001',
    options: o001,
    schedule: n001,
    failing: [],
    extra: () => {
      assert.equal(T(shownAfter(lib, o001, n001, 13, 4)), 'empty | Xa');
      assert.notEqual(T(shownAfter(lib, o001, n001, 13, 4)), 'empty | aX');
      assert.equal(T(shownAfter(lib, o001, n001, 14, 4)), 'empty | empty | Xa');
      assert.notEqual(T(shownAfter(lib, o001, n001, 14, 4)), 'empty | X | a');
    },
  });
  /*
   * N-001, six-request variant (sessions S, A, B, C; seed `ab`). C's
   * display before its last request is `empty | ab`, the demo's own
   * critical layout; the contract of splitting block 1 at 0 is `empty |
   * empty | ab` (the demo gave `empty | b | a`). Predicted: pass.
   */
  const six = { replicas: 4, steps: [split(1, 0, 0), split(1, 0, 0), deliver(1, 2), deliver(1, 3), split(2, 2, 1), merge(2, 2), merge(3, 2), deliver(2, 4), deliver(3, 4), merge(4, 2), split(4, 1, 0)] };
  const osix = { texts: ['ab'], profile: 'blocks', sessions: ['S', 'A', 'B', 'C'] };
  add({
    name: 'N-001: six-request variant reaches the demo layout and splits correctly',
    group: 'N-001',
    options: osix,
    schedule: six,
    failing: [],
    extra: () => {
      assert.equal(T(shownAfter(lib, osix, six, 10, 4)), 'empty | ab');
      assert.equal(T(shownAfter(lib, osix, six, 11, 4)), 'empty | empty | ab');
      assert.notEqual(T(shownAfter(lib, osix, six, 11, 4)), 'empty | b | a');
    },
  });
  /*
   * N-002 (seed `ab`). A splits at 0, B at 1; A receives B's split, shows
   * `empty | a | b`, merges block 2 (`empty | ab`) and bolds block 1 [0, 2).
   * Contract of the bold on `empty | ab`: `empty | [a][b]` (the demo, on its
   * layout `empty | ba`, bolded neither). Production: A's local effect is
   * the contract. The final sync delivers A's records to B, which applied
   * the two splits in the other order: its slice labels differ, and A's
   * bold names a label whose range at B does not hold the selection's
   * start, so B rejects it (`Unable to apply annotation operation due to
   * start missing`). Predicted: convergence and conservation fail, both
   * label-divergence; local meaning and RA-linearizability pass.
   */
  const n002 = { replicas: 2, steps: [split(1, 0, 0), split(2, 0, 1), send(2, 1, 0), merge(1, 2), bold(1, 1, 0, 2)] };
  const o002 = { texts: ['ab'], profile: 'format' };
  add({
    name: 'N-002: the bold has its local effect, then is rejected at the other replica',
    group: 'N-002',
    options: o002,
    schedule: n002,
    failing: ['convergence', 'conservation'],
    classes: { convergence: ['label-divergence'], conservation: ['label-divergence'] },
    extra: (r) => {
      assert.equal(renderBlocks(shownAfter(lib, o002, n002, 5, 1)), 'empty | [a][b]');
      assert.notEqual(renderBlocks(shownAfter(lib, o002, n002, 5, 1)), 'empty | ab');
      const fin = r.trace.snapshots.slice(-2).map((s) => renderBlocks(s.visible)).sort();
      assert.deepEqual(fin, ['empty | [a][b]', 'empty | ab']);
    },
  });
  add({
    name: 'N-002 control: B receives A split before splitting (no concurrent splits)',
    group: 'N-002',
    options: o002,
    schedule: { replicas: 2, steps: [split(1, 0, 0), deliver(1, 2), split(2, 1, 1), send(2, 1, 0), merge(1, 2), bold(1, 1, 0, 2)] },
    failing: [],
    extra: (r) => {
      assert.equal(renderBlocks(finalTexts(r)), 'empty | [a][b]');
      assert.notEqual(renderBlocks(finalTexts(r)), 'empty | ab');
    },
  });
  /*
   * N-003 (seed `abc`). A splits at 1, B at 2; A receives B's split
   * (`a | b | c`), merges block 1 (`ab | c`) and bolds block 0 [0, 2).
   * Contract: `[a][b] | c` (c stays plain; the demo also bolded the
   * character in the other block). Production: local effect as contracted,
   * then the bold is rejected at B by label divergence. Predicted as N-002.
   */
  const n003 = { replicas: 2, steps: [split(1, 0, 1), split(2, 0, 2), send(2, 1, 0), merge(1, 1), bold(1, 0, 0, 2)] };
  const o003 = { texts: ['abc'], profile: 'format' };
  add({
    name: 'N-003: the bold stays in its block, then is rejected at the other replica',
    group: 'N-003',
    options: o003,
    schedule: n003,
    failing: ['convergence', 'conservation'],
    classes: { convergence: ['label-divergence'], conservation: ['label-divergence'] },
    extra: (r) => {
      assert.equal(renderBlocks(shownAfter(lib, o003, n003, 5, 1)), '[a][b] | c');
      assert.notEqual(renderBlocks(shownAfter(lib, o003, n003, 5, 1)), '[a][b] | [c]');
      const fin = r.trace.snapshots.slice(-2).map((s) => renderBlocks(s.visible)).sort();
      assert.deepEqual(fin, ['[a][b] | c', 'ab | c']);
    },
  });
  /*
   * N-004 (seed `a | b | c`). A: merge c into b, split that block at 0,
   * merge it back. B: merge b into a, receive A's first two records, merge
   * its block 1, receive A's last merge. Split and merge never hide a
   * character, so every admitted view shows the multiset abc. The demo hid
   * the whole document; its B showed `empty | abc` before the last merge.
   * Production: B shows `a | bc` there, and `abc` at the end. Predicted:
   * pass.
   */
  const n004 = { replicas: 2, steps: [merge(1, 2), split(1, 1, 0), merge(1, 2), merge(2, 1), send(1, 2, 0), send(1, 2, 1), merge(2, 1), send(1, 2, 2)] };
  const o004 = { texts: ['a', 'b', 'c'], profile: 'structure' };
  add({
    name: 'N-004: abc stays visible',
    group: 'N-004',
    options: o004,
    schedule: n004,
    failing: [],
    extra: (r) => {
      assert.equal(T(shownAfter(lib, o004, n004, 6, 2)), 'a | bc');
      assert.notEqual(T(shownAfter(lib, o004, n004, 6, 2)), 'empty | abc');
      assert.equal(T(finalTexts(r)), 'abc');
      assert.notEqual(T(finalTexts(r)), '');
    },
  });
  /*
   * N-005 (seed `x`). A splits at 0; B splits at 1 and merges the new empty
   * block back; A receives B's split only, merges its block 2 into its
   * predecessor, then receives B's merge. Every linearization keeps x
   * visible. The demo showed `empty | empty | x` before A's merge and lost
   * x. Production: A shows `empty | x | empty` there, merges the trailing
   * empty block, and keeps `empty | x`. Predicted: pass.
   */
  const n005 = { replicas: 2, steps: [split(1, 0, 0), split(2, 0, 1), merge(2, 1), send(2, 1, 0), merge(1, 2), send(2, 1, 1)] };
  const o005 = { texts: ['x'], profile: 'structure' };
  add({
    name: 'N-005: x stays visible',
    group: 'N-005',
    options: o005,
    schedule: n005,
    failing: [],
    extra: (r) => {
      assert.equal(T(shownAfter(lib, o005, n005, 4, 1)), 'empty | x | empty');
      assert.notEqual(T(shownAfter(lib, o005, n005, 4, 1)), 'empty | empty | x');
      assert.equal(T(finalTexts(r)), 'empty | x');
      assert.notEqual(T(finalTexts(r)), 'empty');
    },
  });

  // ------------------------------------------------------------ defect classes
  /*
   * label-divergence (seed `abc`). A splits at 1 (labels: root L, A's
   * slice l), B splits at 2 (root L, B's slice l); each applies the other's
   * split afterwards, subdividing a different slice, so A's slice is `l`
   * at A and `T` at B. A types X at 0 of block 1; the insertion names label
   * l, whose range at B holds B's slice, not the origin: B rejects it.
   * Displays: A `a | Xb | c`, B `a | b | c`. Predicted: convergence and
   * conservation fail, label-divergence.
   */
  const ld = { replicas: 2, steps: [split(1, 0, 1), split(2, 0, 2), insert(1, 1, 0, 'X')] };
  add({
    name: 'label-divergence: an insertion into a concurrently split slice is rejected',
    group: 'label-divergence',
    options: { texts: ['abc'], profile: 'blocks' },
    schedule: ld,
    failing: ['convergence', 'conservation'],
    classes: { convergence: ['label-divergence'], conservation: ['label-divergence'] },
    extra: (r) => {
      const fin = r.trace.snapshots.slice(-2).map((s) => T(s.visible)).sort();
      assert.deepEqual(fin, ['a | Xb | c', 'a | b | c']);
      assert.notDeepEqual(fin, ['a | Xb | c', 'a | Xb | c']);
    },
  });
  add({
    name: 'label-divergence control: the splits are not concurrent',
    group: 'label-divergence',
    options: { texts: ['abc'], profile: 'blocks' },
    schedule: { replicas: 2, steps: [split(1, 0, 1), deliver(1, 2), split(2, 1, 1), insert(1, 1, 0, 'X')] },
    failing: [],
    extra: (r) => {
      assert.equal(T(finalTexts(r)), 'a | Xb | c');
      assert.notEqual(T(finalTexts(r)), 'a | b | c');
    },
  });
  /*
   * The same at one sequencing replica (replica 1, which issues nothing and
   * receives every record): B's split reaches it before A's, and A's
   * insertion, issued before A saw B's split, is rejected there. No final
   * sync: the point is the sequencing replica's own state.
   */
  {
    const star = { replicas: 3, steps: [split(2, 0, 1), split(3, 0, 2), send(3, 1, 0), send(2, 1, 0), insert(2, 1, 0, 'X'), send(2, 1, 1)] };
    const ctl = { replicas: 3, steps: [split(3, 0, 2), send(3, 1, 0), deliver(1, 2), split(2, 0, 1), send(2, 1, 0), insert(2, 1, 0, 'X'), send(2, 1, 1)] };
    const options = { texts: ['abc'], profile: 'blocks' };
    for (const [name, schedule, rejected] of [
      ['label-divergence at a sequencing replica', star, true],
      ['label-divergence at a sequencing replica, control: A saw B split first', ctl, false],
    ])
      out.push({
        name,
        group: 'label-divergence',
        expected: rejected ? 'the sequencing replica rejects the insertion' : 'the sequencing replica integrates the insertion',
        run(results) {
          const { events } = observeSchedule(lib, options, schedule, { finalSync: false });
          const rej = events.filter((e) => e.phase === 'apply' && !e.ok && e.replica === 1);
          results.rejected = rej.map((e) => `${e.key} ${e.kind}: ${e.message}`);
          assert.equal(rej.length, rejected ? 1 : 0);
          const shown = T(shownAfter(lib, options, schedule, schedule.steps.length, 1));
          results.sequencer = shown;
          assert.equal(shown, rejected ? 'a | b | c' : 'a | Xb | c');
          assert.notEqual(shown, rejected ? 'a | Xb | c' : 'a | b | c');
          if (rejected) assert.equal(rej[0].misaddressed, true);
        },
      });
  }
  /*
   * past-boundary (seed `a | b | c`). A splits b at 0 twice; B merges
   * b into a, whose own split marks b's start with a marker reserved 20
   * ticks ahead. At B, A's second split marker sorts after B's merge marker
   * among the siblings of b's start, past the end of the slice holding the
   * origin: rejected. A shows `a | empty | b | c`, B `a | b | c`. Predicted:
   * convergence and conservation fail, past-boundary.
   */
  add({
    name: 'past-boundary: a split concurrent with a merge of its block is rejected',
    group: 'past-boundary',
    options: { texts: ['a', 'b', 'c'], profile: 'structure' },
    schedule: { replicas: 2, steps: [split(1, 1, 0), split(1, 1, 0), merge(2, 1)] },
    failing: ['convergence', 'conservation'],
    classes: { convergence: ['past-boundary'], conservation: ['past-boundary'] },
    extra: (r) => {
      const fin = r.trace.snapshots.slice(-2).map((s) => T(s.visible)).sort();
      assert.deepEqual(fin, ['a | b | c', 'a | empty | b | c']);
    },
  });
  add({
    name: 'past-boundary control: one split only',
    group: 'past-boundary',
    options: { texts: ['a', 'b', 'c'], profile: 'structure' },
    schedule: { replicas: 2, steps: [split(1, 1, 0), merge(2, 1)] },
    failing: [],
  });
  /*
   * The same in a merge's own split (seed `ab | cd`): A splits cd at 0 and
   * merges the empty block into ab; B types W at 0 of cd and merges it into
   * ab. Both merge splits reserve 20 ticks and tie on the counter; B's
   * session sorts first, so A's merge split is rejected at B. Nothing
   * visible changes (A's merge moves an empty slice), so only conservation
   * (a record never integrated) fails.
   */
  add({
    name: 'past-boundary in a merge: concurrent merges of one block',
    group: 'past-boundary',
    options: { texts: ['ab', 'cd'], profile: 'blocks' },
    schedule: { replicas: 2, steps: [split(1, 1, 0), merge(1, 1), insert(2, 1, 0, 'W'), merge(2, 1)] },
    failing: ['conservation'],
    classes: { conservation: ['past-boundary'] },
    extra: (r) => {
      assert.equal(T(finalTexts(r)), 'abW | cd');
      assert.notEqual(T(finalTexts(r)), 'abWcd');
    },
  });
  /*
   * The same for an insertion (seed `ab | cd`): A splits cd at 0 and types
   * T at 0 of the emptied block (origin: the block's start); B merges cd
   * into ab. At B, T's identifier sorts after B's merge marker among the
   * siblings of the start, past the end of the slice holding it: rejected
   * (`Failed to find target text slice after backfilling`). At A, B's
   * merge moves the emptied block's content, T, into ab: `abT | cd` (the
   * order split, insert, merge). B shows `ab | cd`. Predicted: convergence
   * and conservation fail, past-boundary. Control: A does not type.
   */
  add({
    name: 'past-boundary for an insertion: typing into a block concurrently merged',
    group: 'past-boundary',
    options: { texts: ['ab', 'cd'], profile: 'blocks' },
    schedule: { replicas: 2, steps: [split(1, 1, 0), insert(1, 1, 0, 'T'), merge(2, 1)] },
    failing: ['convergence', 'conservation'],
    classes: { convergence: ['past-boundary'], conservation: ['past-boundary'] },
    extra: (r) => {
      const fin = r.trace.snapshots.slice(-2).map((s) => T(s.visible)).sort();
      assert.deepEqual(fin, ['ab | cd', 'abT | cd']);
      assert.notDeepEqual(fin, ['abT | cd', 'abT | cd']);
    },
  });
  add({
    name: 'past-boundary for an insertion, control: A does not type',
    group: 'past-boundary',
    options: { texts: ['ab', 'cd'], profile: 'blocks' },
    schedule: { replicas: 2, steps: [split(1, 1, 0), merge(2, 1)] },
    failing: [],
  });
  /*
   * stale-merge (seed `a | b | c`). A merges c into b; B also merges c into
   * b and then splits `bc` at 1. In every linearization the second merge of
   * c finds c a tombstone and is a no-op, and B's split leaves c in a new
   * block: admitted = { a | b | c }. Production: A's merge, applied at B
   * after B removed c, still splits c's instance and moves the slice now
   * holding c back under b: `a | bc | empty` at both replicas. Predicted:
   * RA-linearizability fails (stale-merge); no text is lost.
   */
  const stale = { replicas: 2, steps: [merge(1, 2), merge(2, 2), split(2, 1, 1)] };
  const ostale = { texts: ['a', 'b', 'c'], profile: 'structure' };
  add({
    name: 'stale-merge: a late duplicate merge undoes a later split',
    group: 'stale-merge',
    options: ostale,
    schedule: stale,
    failing: ['raLinearizability'],
    classes: { raLinearizability: ['stale-merge'] },
    extra: (r, results) => {
      assert.equal(T(finalTexts(r)), 'a | bc | empty');
      assert.notEqual(T(finalTexts(r)), 'a | b | c');
      const withSync = { replicas: 2, steps: [...stale.steps, send(1, 2, 0)] };
      const { admitted, witness, shown } = admittedAt(lib, ostale, withSync, 2);
      results.admitted = admitted.map(renderBlocks);
      assert(sameViewSet(productionBlocksInstance(lib, ostale).spec, admitted, [V('a', 'b', 'c')]));
      assert.equal(witness, false);
      assert.equal(T(shown), 'a | bc | empty');
    },
  });
  add({
    name: 'stale-merge control: a single merge, then a split',
    group: 'stale-merge',
    options: ostale,
    schedule: { replicas: 2, steps: [merge(1, 2), split(2, 2, 0)] },
    failing: [],
    extra: (r) => {
      assert.equal(T(finalTexts(r)), 'a | b | c');
      assert.notEqual(T(finalTexts(r)), 'a | bc | empty');
    },
  });
  /*
   * removed-anchor (seed `ab | cd`). A splits cd at 0 (`ab | empty | cd`)
   * and merges the empty block into ab (`ab | cd`). B splits cd at 0 and
   * creates a block after its block 1 (the original cd block). At A, both of
   * B's new blocks are listed after a block no longer in the page's content,
   * so they go to the end: `ab | empty | cd | empty`. Linearizations place
   * them after the holder of the split point or after the tombstone:
   * admitted = { ab | empty | empty | cd }. Predicted: RA-linearizability
   * fails (removed-anchor) and the replicas list the blocks in different
   * orders (convergence, list-order).
   */
  add({
    name: 'removed-anchor: blocks listed after a removed block go to the end of the page',
    group: 'removed-anchor',
    options: { texts: ['ab', 'cd'], profile: 'blocks' },
    schedule: { replicas: 2, steps: [split(1, 1, 0), merge(1, 1), split(2, 1, 0), create(2, 1)] },
    failing: ['convergence', 'raLinearizability'],
    classes: { convergence: ['list-order'], raLinearizability: ['removed-anchor'] },
    extra: (r) => {
      const fin = r.trace.snapshots.slice(-2).map((s) => T(s.visible)).sort();
      assert.deepEqual(fin, ['ab | empty | cd | empty', 'ab | empty | empty | cd']);
    },
  });
  add({
    name: 'removed-anchor control: A does not merge',
    group: 'removed-anchor',
    options: { texts: ['ab', 'cd'], profile: 'blocks' },
    schedule: { replicas: 2, steps: [split(1, 1, 0), split(2, 1, 0), create(2, 1)] },
    failing: [],
  });
  /*
   * order-mismatch (seed `a`). A creates a block after block 0 and types Y
   * at 0 of block 0; B splits block 0 at 0. At B: the split's new block is
   * listed first, A's block is listed directly after block 0 when it
   * arrives, and Y, inserted at the start concurrently with the split,
   * sorts after the split marker and lands in the split's block: `empty |
   * empty | Ya`. Y in the split's block needs the insertion before the split;
   * A's block before the split's block needs the split before the creation;
   * and A created before typing. No order satisfies all three: admitted =
   * { empty | Ya | empty, Y | empty | a, Y | a | empty }. Predicted:
   * RA-linearizability fails (order-mismatch); the replicas also list the
   * blocks differently (convergence, list-order).
   */
  const order = { replicas: 2, steps: [create(1, 0), insert(1, 0, 0, 'Y'), split(2, 0, 0)] };
  const oorder = { texts: ['a'], profile: 'blocks' };
  add({
    name: 'order-mismatch: block order by application, text division by identifier',
    group: 'order-mismatch',
    options: oorder,
    schedule: order,
    failing: ['convergence', 'raLinearizability'],
    classes: { convergence: ['list-order'], raLinearizability: ['order-mismatch'] },
    extra: (r, results) => {
      const withSync = { replicas: 2, steps: [...order.steps, deliver(1, 2)] };
      const { admitted, witness, shown } = admittedAt(lib, oorder, withSync, 2);
      results.admitted = admitted.map(renderBlocks);
      assert.equal(T(shown), 'empty | empty | Ya');
      assert(sameViewSet(productionBlocksInstance(lib, oorder).spec, admitted, [V('', 'Ya', ''), V('Y', '', 'a'), V('Y', 'a', '')]));
      assert.equal(witness, false);
    },
  });
  add({
    name: 'order-mismatch control: A saw the split first',
    group: 'order-mismatch',
    options: oorder,
    schedule: { replicas: 2, steps: [split(2, 0, 0), deliver(2, 1), create(1, 0), insert(1, 0, 0, 'Y')] },
    failing: [],
    extra: (r) => assert.equal(T(finalTexts(r)), 'Y | empty | a'),
  });

  /*
   * concurrent-move (seed `a | b | c`). B merges b into a and A receives
   * it (`ab | c`; b's text is a slice starting at B's merge marker M under
   * a). B splits `ab` at 1, the end of a's root node: the builder emits no
   * split, only a move of the slice starting at M into B's new block, and
   * B merges that block back (`ab | c`). Concurrently A splits `ab` at 1,
   * emitting the same move of the slice starting at M into A's new block.
   * Whichever move a replica applies last decides where b goes: A ends
   * with B's merge after both moves (`ab | empty | c`), B with A's move
   * last (`a | b | c`). Each display is some order of the requests; the
   * replicas never converge. Predicted: convergence fails
   * (concurrent-move); RA-linearizability and conservation pass.
   */
  const cmove = { replicas: 2, steps: [merge(2, 1), send(2, 1, 0), split(2, 0, 1), merge(2, 1), split(1, 0, 1)] };
  const ocmove = { texts: ['a', 'b', 'c'], profile: 'structure' };
  add({
    name: 'concurrent-move: two splits move the same slice, and the replicas never converge',
    group: 'concurrent-move',
    options: ocmove,
    schedule: cmove,
    failing: ['convergence'],
    classes: { convergence: ['concurrent-move'] },
    extra: (r) => {
      const fin = r.trace.snapshots.slice(-2).map((s) => `r${s.replica} ${T(s.visible)}`).sort();
      assert.deepEqual(fin, ['r1 ab | empty | c', 'r2 a | b | c']);
      assert.notEqual(fin[0].slice(3), fin[1].slice(3));
    },
  });
  add({
    name: 'concurrent-move control: B does not merge back',
    group: 'concurrent-move',
    options: ocmove,
    schedule: { replicas: 2, steps: [merge(2, 1), send(2, 1, 0), split(2, 0, 1), split(1, 0, 1)] },
    failing: [],
    extra: (r) => assert.equal(T(finalTexts(r)), 'a | empty | b | c'),
  });
  add({
    name: 'concurrent-move control: A sees B records before splitting',
    group: 'concurrent-move',
    options: ocmove,
    schedule: { replicas: 2, steps: [merge(2, 1), send(2, 1, 0), split(2, 0, 1), merge(2, 1), deliver(2, 1), split(1, 0, 1)] },
    failing: [],
    extra: (r) => assert.equal(T(finalTexts(r)), 'a | b | c'),
  });

  // ------------------------------------------------------------ artefacts
  /*
   * list-order (seed `a`), a delivery-model artefact. Both replicas create a
   * block after block 0 and type into it; the page's content array places
   * each `listAfter` immediately after block 0 when applied, so each
   * replica lists the other's block first: A `a | Y | X`, B `a | X | Y`.
   * Each display is a linearization (RA-linearizability passes); only
   * convergence fails. Record lists are ordered by Notion's server, which
   * applies them in one order.
   */
  add({
    name: 'list-order: concurrent creations after one block, peer-to-peer',
    group: 'list-order',
    options: { texts: ['a'], profile: 'blocks' },
    schedule: { replicas: 2, steps: [create(1, 0), insert(1, 1, 0, 'X'), create(2, 0), insert(2, 1, 0, 'Y')] },
    failing: ['convergence'],
    classes: { convergence: ['list-order'] },
    extra: (r) => {
      const fin = r.trace.snapshots.slice(-2).map((s) => T(s.visible)).sort();
      assert.deepEqual(fin, ['a | X | Y', 'a | Y | X']);
    },
  });
  add({
    name: 'list-order control: the creations are not concurrent',
    group: 'list-order',
    options: { texts: ['a'], profile: 'blocks' },
    schedule: { replicas: 2, steps: [create(1, 0), insert(1, 1, 0, 'X'), deliver(1, 2), create(2, 0), insert(2, 1, 0, 'Y')] },
    failing: [],
    extra: (r) => assert.equal(T(finalTexts(r)), 'a | Y | X'),
  });
  /*
   * Split placement reading (seed `a | b | c`). A splits b at 0 (`a | empty
   * | b | c`); B merges b into a and splits `ab` at 2. Production shows `a
   * | b | empty | c`: A's new block follows the block holding b's start
   * (a), B's empty block follows it. Under splitPlacement 'holder' the
   * order merge, split(B), split(A) gives exactly that; under 'source' A's
   * block goes after b's tombstone, behind B's: admitted = { a | empty | b
   * | c }. Predicted: 'holder' passes, 'source' fails RA-linearizability.
   */
  const place = { replicas: 2, steps: [split(1, 1, 0), merge(2, 1), split(2, 0, 2)] };
  add({ name: 'split placement after the holder: pass', group: 'reading', options: { texts: ['a', 'b', 'c'], profile: 'structure' }, schedule: place, failing: [], extra: (r) => assert.equal(T(finalTexts(r)), 'a | b | empty | c') });
  add({
    name: 'split placement after the issuer source: fails',
    group: 'reading',
    options: { texts: ['a', 'b', 'c'], profile: 'structure', splitPlacement: 'source' },
    schedule: place,
    failing: ['raLinearizability'],
    classes: { raLinearizability: ['order-mismatch', 'removed-anchor'] },
  });
  /*
   * Inheritance reading (seed `ab | c`). A types V after c; B bolds c. The
   * production text shows `ab | [c][V]`: the mark extends over the
   * concurrent insertion at its right boundary. Under inherit 'apply'
   * (bold first, then V after the bold c) that is admitted; under 'issue'
   * V keeps the plain flag A saw: admitted = { ab | [c]V }. Predicted:
   * 'apply' passes, 'issue' fails RA-linearizability (bold-flags).
   */
  const inherit = { replicas: 2, steps: [insert(1, 1, 1, 'V'), bold(2, 1, 0, 1)] };
  add({ name: 'inheritance at application: pass', group: 'reading', options: { texts: ['ab', 'c'], profile: 'mixed' }, schedule: inherit, failing: [], extra: (r) => assert.equal(renderBlocks(finalTexts(r)), 'ab | [c][V]') });
  add({
    name: 'inheritance as issued: fails',
    group: 'reading',
    options: { texts: ['ab', 'c'], profile: 'mixed', inherit: 'issue' },
    schedule: inherit,
    failing: ['raLinearizability'],
    classes: { raLinearizability: ['bold-flags'] },
  });
  /*
   * format-carry (seed `ab | c`, one replica). Bold c, split block 1 at 1
   * (`ab | [c] | empty`), type X into the new block. Contract: X is plain
   * (nothing precedes it in its block). Production: `[X]`; the insertion
   * inherits the bold of c, which precedes it in the text instance across
   * the block boundary, as editors commonly carry formatting over Enter.
   * Predicted: local meaning (format-carry) and RA-linearizability
   * (bold-flags) fail.
   */
  add({
    name: 'format-carry: typing after a split at the end of bold text',
    group: 'reading',
    options: { texts: ['ab', 'c'], profile: 'mixed' },
    schedule: { replicas: 1, steps: [bold(1, 1, 0, 1), split(1, 1, 1), insert(1, 2, 0, 'X')] },
    failing: ['raLinearizability', 'localMeaning'],
    classes: { raLinearizability: ['bold-flags'], localMeaning: ['format-carry'] },
    extra: (r) => {
      assert.equal(renderBlocks(finalTexts(r)), 'ab | [c] | [X]');
      assert.notEqual(renderBlocks(finalTexts(r)), 'ab | [c] | X');
    },
  });
  /*
   * Harness control: clocks (seed `abc`, one replica). Split at 2, split
   * block 1 at 0, split block 0 at 1 (`a | b | empty | c`), merge block 3
   * into the empty block. Contract: `a | b | c`. With the library's
   * record-model trees (per-tree clocks), the third split reuses the
   * second's marker identifier and the merge lands in a: `ac | b | empty`.
   * With the editor's per-instance clocks (the default) the history is
   * correct.
   */
  const clocks = { replicas: 1, steps: [split(1, 0, 2), split(1, 1, 0), split(1, 0, 1), merge(1, 3)] };
  add({
    name: 'live clocks: a sequential split/merge history is correct',
    group: 'harness',
    options: { texts: ['abc'], profile: 'structure' },
    schedule: clocks,
    failing: [],
    extra: (r) => {
      assert.equal(T(finalTexts(r)), 'a | b | c');
      assert.notEqual(T(finalTexts(r)), 'ac | b | empty');
    },
  });
  add({
    name: 'record-model clocks: duplicate marker identifiers misplace a merge',
    group: 'harness',
    options: { texts: ['abc'], profile: 'structure', liveClock: false },
    schedule: clocks,
    failing: ['localMeaning'],
    classes: { localMeaning: ['duplicate-marker'] },
    extra: (r) => assert.equal(T(finalTexts(r)), 'ac | b | empty'),
  });
  /*
   * Harness control: shared runtime. The same schedules executed with one
   * runtime per client (the library's own createClient) and with one
   * shared runtime give identical displays after every step.
   */
  out.push({
    name: 'shared and isolated runtimes give identical traces',
    group: 'harness',
    expected: 'identical displays and failing checks',
    run(results) {
      const runs = [
        [{ texts: ['abc'], profile: 'blocks' }, ld],
        [ostale, stale],
        [oorder, order],
        [{ texts: ['ab'], profile: 'format' }, n002],
      ];
      results.compared = runs.length;
      for (const [o, s] of runs) {
        const views = (isolated) => {
          const t = execute(productionBlocksInstance(lib, { ...o, isolated }), s, { checks: ['convergence', 'conservation', 'raLinearizability'] });
          return { visible: t.snapshots.map((x) => renderBlocks(x.visible)), failing: Object.entries(t.checks).filter(([, c]) => !c.pass).map(([k]) => k) };
        };
        assert.deepEqual(views(true), views(false));
      }
    },
  });
  return out;
}

export async function main() {
  return withVerifiedLibrary(async (lib) => {
    const results = [];
    for (const c of cases(lib)) {
      const r = {};
      try {
        c.run(r);
        results.push({ name: c.name, group: c.group, expected: c.expected, pass: true, results: r });
      } catch (e) {
        results.push({ name: c.name, group: c.group, expected: c.expected, pass: false, error: e.message, results: r });
      }
    }
    writeJson(join(here, 'results', 'regressions.json'), { library: lib.manifest.files, cases: results });
    return results;
  });
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  const results = await main();
  for (const r of results) console.log(`${r.pass ? 'ok  ' : 'FAIL'} [${r.group}] ${r.name}${r.pass ? '' : `\n     ${r.error}`}`);
  const failed = results.filter((r) => !r.pass).length;
  console.log(`${results.length - failed}/${results.length} cases hold`);
  process.exit(failed ? 1 : 0);
}
