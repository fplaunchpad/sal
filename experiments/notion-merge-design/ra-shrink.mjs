// Shrink a network-search history that contains an RA disagreement.
// Usage: node --import ./ra-hook.mjs ra-shrink.mjs network-output.json [mode]
// For each disagreement category in the given specification mode (default
// absorb, see ra-check.mjs), the first
// trial showing it is replayed through network-lib with fresh issuance, then
// reduced to a fixed point under the criterion of network-lib's minimiser:
// remove one edit together with its deliveries, or one delivery; requests are
// reissued and invalid or noncausal candidates are rejected. A prefix is cut
// first. No global minimality is claimed.
import fs from 'node:fs';
import {replay} from './network-lib.mjs';

const state = globalThis.__raState;
const saved = JSON.parse(fs.readFileSync(process.argv[2], 'utf8')), MODE = process.argv[3] ?? 'absorb';
let attempts = 0, rejected = 0;

function disagreement(trace, category) {
  attempts++;
  state.seen.clear();
  let found = null;
  const listener = (mode, r, txs) => { if (mode === MODE && !found && (!category || r.category === category)) found = {category: r.category, result: r, transactions: structuredClone(txs)}; };
  state.listeners.push(listener);
  try { replay(trace, {verify: false}); }
  catch (e) { rejected++; found = null; }
  finally { state.listeners.pop(); }
  return found;
}

function shrink(trace, category) {
  let best = structuredClone(trace);
  // Shortest failing prefix.
  for (let n = 1; n <= best.events.length; n++) {
    const t = {...best, events: best.events.slice(0, n)};
    if (disagreement(t, category)) { best = t; break; }
  }
  let changed = true;
  while (changed) {
    changed = false;
    for (let i = 0; i < best.events.length; i++) {
      const ev = best.events[i], t = structuredClone(best);
      t.events.splice(i, 1);
      if (ev.kind === 'edit') t.events = t.events.filter(x => x.kind !== 'deliver' || x.edit !== ev.id);
      if (disagreement(t, category)) { best = t; changed = true; break; }
    }
  }
  const final = disagreement(best, category);
  return {trace: best, disagreement: final};
}

const findings = [];
const categories = new Set();
for (const t of saved.traces) {
  const d = disagreement(t.trace);
  if (!d || categories.has(d.category)) continue;
  categories.add(d.category);
  findings.push({trial: t.trial, category: d.category, ...shrink(t.trace, d.category)});
}
console.log(JSON.stringify({mode: MODE, findings, shrink: {attempts, rejected,
  criterion: 'shortest failing prefix, then fixed point under removing one edit plus its deliveries or one delivery; requests reissued; no global minimality claim'}}));
