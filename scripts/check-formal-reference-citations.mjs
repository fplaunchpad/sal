import assert from 'node:assert/strict';
import { readFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { repoRoot, runLean } from './check-public-certificates.mjs';

// Resolve the names actually printed in the paper, not a second manual list.
export function citationSource(tex) {
  const citations = [...tex.matchAll(/\\anchor\{([^{}]+)\}\s*\{([^{}]+)\}/g)];
  assert.ok(citations.length > 0, 'No theorem citations found');
  assert.equal(citations.length, [...tex.matchAll(/\\anchor\{/g)].length,
    'Unparsed theorem citation: do not silently omit malformed anchors');
  const names = new Set();
  for (const [, path, labels] of citations) {
    assert.ok(existsSync(join(repoRoot, path)), `Missing citation file: ${path}`);
    for (const label of labels.split(',')) {
      const name = label.replaceAll('\\_', '_').replace(/\\allowbreak\s*/g, '').trim();
      assert.match(name, /^[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/,
        `Unsupported citation syntax: ${label}`);
      names.add(name);
    }
  }
  return { count: names.size, source: `import Sal.MRDTs.Metatheory.FormalReferenceLedger
namespace Sal.MRDTs
open Foundation Instances
${[...names].map((name) => `#check ${name}`).join('\n')}
end Sal.MRDTs
` };
}

export function checkCoverage(tex, manifest) {
  const count = manifest.contracts.length;
  assert.ok(tex.includes(`production registry contains ${count} \\lean{PackagedMRDT}`),
    'Formal-reference production count differs from public contracts');
  assert.ok(tex.includes(`same ${count}-entry`),
    'Formal-reference state-GC count differs from public contracts');
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const tex = readFileSync(join(repoRoot, 'docs/formal-reference/main.tex'), 'utf8');
  checkCoverage(tex, JSON.parse(readFileSync(join(repoRoot, 'public-contracts.json'), 'utf8')));
  const { count, source } = citationSource(tex);
  const result = runLean(source);
  if (result.status !== 0) {
    process.stderr.write(result.stdout + result.stderr);
    process.exit(1);
  }
  console.log(`Formal reference: ${count} distinct citations resolve; coverage counts agree.`);
}
