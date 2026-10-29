/**
 * Source-level diagnosis of failures. This reads the model's internal state
 * (slice trees, block liveness), so it is separate from the checks, which
 * compare displays with the independent specification only.
 *
 * `diagnose(model, transactions)` replays an archive transaction by
 * transaction in the model's replay order and reports
 *   losses     every transaction whose replay shrinks the multiset of visible
 *              characters without deleting any, with the code path of a
 *              demo block merge (split, moveTextSlice, removeBlock): the
 *              anchored slice lies in a removed block (`removed-target`), or
 *              in the source's own tree, so the move is the cycle no-op
 *              (`cycle-no-op`)
 *   branching  whether some slice node of an alive block has two children
 *              (a slice tree that is not a chain)
 *   paths      the code path of every demo block merge in the archive, with
 *              or without loss: `removed-target`, `cycle-no-op` or `live`
 *   frontCreates
 *              every block creation (a split's new block) replayed after a
 *              block that is no longer in the display order, which the demo
 *              places at the front of the document
 *
 * `classifyFailure(instance, schedule, failure)` names the catalogue entry a
 * check failure exhibits, from its check, request and diagnosis:
 *   N-001  a split whose local effect is wrong, or a placement-only
 *          RA-linearizability failure, in an archive whose slice forest
 *          branches (a moved subtree is not the displayed suffix)
 *   N-002  a bold toggle that misses selected characters
 *   N-003  a bold toggle that changes characters outside the selection
 *   N-004  text hidden by a block merge into a removed block
 *   N-005  text hidden by a block merge whose move is the cycle no-op
 * and two outcomes outside the catalogue:
 *   spec-stuck            an RA-linearizability failure with no admitted view:
 *                         the specification gives the history no meaning (the
 *                         decoder gives a demo merge's own split marker no
 *                         position, so a later merge anchored at it is stuck)
 *   split-after-removal   an RA-linearizability failure without text loss in an
 *                         archive where a split's new block was created after a
 *                         removed block
 *   N-004-path, N-005-path
 *                         an RA-linearizability failure without text loss and
 *                         without the mechanisms above, in an archive where a
 *                         demo merge took the code path of N-004 (removed
 *                         target) or N-005 (cycle no-op of a live source):
 *                         the same defect hiding only empty blocks
 * A RA-linearizability failure of the formatted instance inherits the
 * catalogue entries of the bold requests among its records whose local
 * meaning failed.
 */
import { Execution, execute } from '../../src/index.js';
import { blocksOf } from './spec.js';

const bag = (doc) =>
  doc
    .aliveBlocks()
    .flatMap((b) => doc.blockText(b.id).split(''))
    .sort()
    .join('');

function owner(model, doc, instance, endItem) {
  for (const block of doc.blocks.values())
    for (const node of model.iterateTextSliceTree(block.title))
      if (node.textSlice.textInstanceId === instance && model.sameId(node.textSlice.endItemId, endItem)) return block;
  return null;
}

export function diagnose(model, transactions) {
  const sorted = [...transactions].sort((a, b) => model.compareOpIds(a.id, b.id));
  const losses = [];
  const frontCreates = [];
  const paths = [];
  let before = new model.CrdtDocument([]);
  for (let i = 0; i < sorted.length; i++) {
    const tx = sorted[i];
    const after = new model.CrdtDocument(sorted.slice(0, i + 1));
    for (const o of tx.operations)
      if (o.command === 'createBlock' && o.args.afterBlockId && !before.blockOrder.includes(o.args.afterBlockId))
        frontCreates.push({ transaction: `${tx.id.sessionId}:${tx.id.counter}`, block: o.args.blockId, after: o.args.afterBlockId });
    const deletes = tx.operations.some((o) => o.command === 'deleteText');
    const b0 = bag(before);
    const b1 = bag(after);
    const move = tx.operations.find((o) => o.command === 'moveTextSlice');
    const remove = tx.operations.find((o) => o.command === 'removeBlock');
    let path = 'other';
    if (move && remove) {
      const holder = owner(model, before, move.args.targetTextInstanceId, move.args.targetTextSliceEndItemId);
      path = holder && !holder.alive ? 'removed-target' : holder && holder.id === remove.args.blockId ? 'cycle-no-op' : 'live';
      paths.push({ transaction: `${tx.id.sessionId}:${tx.id.counter}`, path, source: remove.args.blockId, sourceWasAlive: !!before.blocks.get(remove.args.blockId)?.alive });
    }
    if (!deletes && b1.length < b0.length) {
      losses.push({ transaction: `${tx.id.sessionId}:${tx.id.counter}`, path, visibleBefore: b0, visibleAfter: b1 });
    }
    before = after;
  }
  let branching = false;
  for (const block of before.aliveBlocks()) for (const node of model.iterateTextSliceTree(block.title)) if (node.children.length > 1) branching = true;
  return { losses, branching, frontCreates, paths };
}

/** The archive a replica held at a failure: the seed and the transactions of its integrated records. */
export function archiveAt(instance, schedule, failure) {
  const ex = new Execution(instance, schedule.replicas, { checks: [] });
  const upto = failure.final ? schedule.steps.length : failure.step + 1;
  for (const s of schedule.steps.slice(0, upto)) ex.apply(s);
  if (failure.final) ex.finish();
  return [...instance.seed, ...failure.opKeys.map((k) => ex.byKey.get(k).update.tx)];
}

function boldSide(failure) {
  const q = failure.request;
  const exp = blocksOf(failure.expected);
  const act = blocksOf(failure.actual);
  let missing = 0;
  let extra = 0;
  for (let b = 0; b < act.length; b++)
    for (let i = 0; i < act[b].length; i++)
      if (exp[b]?.[i] && act[b][i].text === exp[b][i].text && act[b][i].bold !== exp[b][i].bold) {
        if (b === q.block && q.start <= i && i < q.end) missing++;
        else extra++;
      }
  return { missing, extra };
}

/** The N-004 and N-005 code paths taken by demo merges of an archive. */
export function pathClasses(d) {
  const out = [];
  if (d.paths.some((p) => p.path === 'removed-target')) out.push('N-004-path');
  if (d.paths.some((p) => p.path === 'cycle-no-op' && p.sourceWasAlive)) out.push('N-005-path');
  return out;
}

export function classifyFailure(instance, schedule, failure) {
  const archive = archiveAt(instance, schedule, failure);
  const d = diagnose(instance.model, archive);
  const out = { check: failure.check, losses: d.losses, branching: d.branching, frontCreates: d.frontCreates, catalogue: [] };
  const stuck = failure.check === 'raLinearizability' && failure.expected.admittedViews.length === 0;
  if (stuck) out.catalogue.push('spec-stuck');
  if (failure.check === 'localMeaning' && failure.request.kind === 'bold') {
    const { missing, extra } = boldSide(failure);
    out.bold = { missing, extra };
    if (missing) out.catalogue.push('N-002');
    if (extra) out.catalogue.push('N-003');
  } else if (failure.check === 'localMeaning' && failure.request.kind === 'split') {
    if (d.branching || d.losses.length === 0) out.catalogue.push('N-001');
  }
  for (const l of d.losses) {
    if (l.path === 'removed-target') out.catalogue.push('N-004');
    if (l.path === 'cycle-no-op') out.catalogue.push('N-005');
  }
  if (failure.check === 'raLinearizability' && !stuck && d.losses.length === 0) {
    if (instance.format) {
      const t = execute(instance, { ...schedule, steps: schedule.steps.slice(0, failure.step + 1) }, { checks: ['localMeaning'], finalSync: false });
      const keyAt = new Map(t.ops.map((o) => [o.step, o.key]));
      for (const f of t.checks.localMeaning.details.failures)
        if (f.request.kind === 'bold' && failure.opKeys.includes(keyAt.get(f.step))) {
          const { missing, extra } = boldSide(f);
          if (missing) out.catalogue.push('N-002');
          if (extra) out.catalogue.push('N-003');
        }
    }
    if (d.branching) out.catalogue.push('N-001');
    if (d.frontCreates.length) out.catalogue.push('split-after-removal');
    if (!out.catalogue.length) out.catalogue.push(...pathClasses(d));
  }
  out.catalogue = [...new Set(out.catalogue)].sort();
  if (out.catalogue.length === 0) out.catalogue.push('unclassified');
  return out;
}
