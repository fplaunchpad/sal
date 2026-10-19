// Preloaded with `node --import ./ra-hook.mjs harness.mjs ...`: installs the
// RA check on every document a harness builds, leaving the harness unchanged,
// and writes the counts to $RA_REPORT when the process exits.
//
// It also checks every issued deletion against the positional delete contract
// and counts separately the deletions whose range spans more than one text
// instance (in the design, a range crossing a merged boundary).
import fs from 'node:fs';
import {Replica} from './replica.js';
import {request} from './positional-spec.mjs';
import {installHook, summary} from './ra-check.mjs';

const state = installHook(Replica);
globalThis.__raState = state;

// Structural diagnostic: the largest number of children of any slice node, the
// number of archives in which some node has more than one child, and, per
// specification mode, how many disagreements occur in such archives.
state.shape = {archives: 0, branching: 0, maxChildren: 0, disagreements: {}};
let branchingNow = false;
state.listeners.push((mode, r) => {
  const d = state.shape.disagreements[mode] ??= {branching: 0, chain: 0};
  d[branchingNow ? 'branching' : 'chain']++;
});
state.archiveListeners.push((txs, document) => {
  state.shape.archives++;
  let most = 0;
  for (const block of document.blocks.values()) {
    if (block.title.parent) continue;
    const stack = [block.title];
    while (stack.length) { const n = stack.pop(); most = Math.max(most, n.children.length); stack.push(...n.children); }
  }
  branchingNow = most > 1;
  if (most > 1) state.shape.branching++;
  state.shape.maxChildren = Math.max(state.shape.maxChildren, most);
});

const chars = r => {
  const d = r.document();
  return d.aliveBlocks().map(b => d.blockCharacters(b.id).map(c => ({text: c.text, bold: !!c.bold})));
};
state.deletes = {single: {checked: 0, agree: 0}, crossing: {checked: 0, agree: 0}, crossingExample: null, disagreements: []};
const deleteText = Replica.prototype.deleteText;
Replica.prototype.deleteText = function (blockId, start, end) {
  const block = this.document().aliveBlocks().findIndex(b => b.id === blockId);
  const before = block >= 0 ? chars(this) : null;
  const transaction = deleteText.call(this, blockId, start, end);
  if (!transaction || !before) return transaction;
  const instances = new Set(transaction.operations.map(o => o.args.textInstanceId));
  const kind = instances.size > 1 ? 'crossing' : 'single';
  const expected = request(before, {kind: 'delete', block, start, end}), actual = chars(this);
  const agree = JSON.stringify(expected) === JSON.stringify(actual);
  state.deletes[kind].checked++;
  if (agree) state.deletes[kind].agree++;
  else if (state.deletes.disagreements.length < 5) state.deletes.disagreements.push({kind, before, request: {block, start, end}, expected, actual});
  if (kind === 'crossing' && !state.deletes.crossingExample) {
    state.deletes.crossingExample = {before: before.map(b => b.map(c => c.text).join('')), request: {block, start, end},
      instances: [...instances], after: actual.map(b => b.map(c => c.text).join(''))};
  }
  return transaction;
};

process.on('exit', () => {
  if (process.env.RA_REPORT) fs.writeFileSync(process.env.RA_REPORT, JSON.stringify(summary(state)));
});
