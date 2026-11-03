/**
 * The versions that fail RA-linearizability under the anchors reading,
 * checked again under the persistent reading.
 *
 *   node residues.mjs
 *
 * Reads results/campaign/*-anchors.json (written by campaign.mjs), and for
 * every raLinearizability failure record searches for a witness of the same
 * version (the same integrated records and the same displayed view with
 * identities) under the persistent reading. Writes results/residues.json.
 */
import { readdirSync, readFileSync } from 'node:fs';
import { writeJson } from '../../ra-pbt/src/index.js';
import { verifySources, findWitness, interpret } from '../../ra-pbt/instances/loro/index.js';
import { renderView } from './render.mjs';

function main() {
  const m = verifySources();
  console.log(`sources verified: ${m.package}@${m.version}`);
  const out = [];
  for (const file of readdirSync('results/campaign').filter((f) => f.endsWith('-anchors.json')).sort()) {
    const data = JSON.parse(readFileSync(`results/campaign/${file}`, 'utf8'));
    for (const t of data.failing) {
      const fails = t.checks.raLinearizability.details.failures;
      if (!fails.length) continue;
      const byKey = new Map(t.ops.map((o) => [o.key, o]));
      const versions = fails.map((f) => {
        const keys = new Set(f.opKeys);
        const events = f.opKeys.map((k) => byKey.get(k)).map((o) => ({ key: o.key, deps: o.deps.filter((d) => keys.has(d)), specOps: o.kind === 'cleanup' ? [] : interpret(o) }));
        const w = findWitness(events, f.actual, { attrs: 'persistent' });
        return { replica: f.replica, step: f.step, actual: renderView(f.actual), persistentWitness: w.found, order: w.order };
      });
      out.push({ run: file.replace(/\.json$/, ''), trial: t.trial, seed: t.seed, versions });
      console.log(`${file} trial ${t.trial}: ${versions.filter((x) => x.persistentWitness).length}/${versions.length} failing versions have a persistent witness`);
    }
  }
  writeJson('results/residues.json', { package: `${m.package}@${m.version}`, trials: out });
  verifySources();
  console.log('sources verified after run');
}

main();
