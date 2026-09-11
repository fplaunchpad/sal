import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

export const repoRoot = fileURLToPath(new URL('..', import.meta.url));
export const readJSON = (path) => JSON.parse(readFileSync(join(repoRoot, path), 'utf8'));

export function validateContracts(manifest, runtime) {
  assert.equal(manifest.schemaVersion, 1);
  assert.equal(manifest.reviewStatus, 'pending-semantic-audit',
    'Human approval must not be inferred from a passing proof gate; change the review protocol explicitly.');
  assert.ok(Array.isArray(manifest.contracts) && manifest.contracts.length > 0);
  const ids = new Set();
  for (const c of manifest.contracts) {
    assert.match(c.id, /^[a-z][a-z0-9-]*$/);
    assert.ok(!ids.has(c.id), `duplicate contract: ${c.id}`);
    ids.add(c.id);
    for (const key of ['certificate', 'implementation', 'issuance', 'rc', 'spec', 'relation']) {
      assert.equal(typeof c[key], 'string', `${c.id}: missing ${key}`);
      assert.ok(c[key].trim().length > 0, `${c.id}: empty ${key}`);
      // These are trusted, source-controlled Lean terms, not inferred projections.
      assert.ok(!/[\n\r;]/.test(c[key]), `${c.id}: ${key} must be a single-line term`);
    }
    assert.match(c.certificate, /^Instances\.[A-Za-z0-9_.]+(?: |$)/);
    for (const key of ['implementation', 'issuance', 'rc', 'spec', 'relation']) {
      assert.ok(!/verified|Verified|certificate/.test(c[key]),
        `${c.id}: select ${key} independently of the certificate`);
    }
    if (c.obligations !== undefined) {
      assert.ok(Array.isArray(c.obligations) && c.obligations.length > 0,
        `${c.id}: obligations must be a nonempty list`);
      const names = new Set();
      for (const obligation of c.obligations) {
        for (const key of ['name', 'statement', 'proof']) {
          assert.equal(typeof obligation[key], 'string', `${c.id}: missing obligation ${key}`);
          assert.ok(obligation[key].trim().length > 0 && !/[\n\r;]/.test(obligation[key]),
            `${c.id}: invalid obligation ${key}`);
        }
        assert.ok(!names.has(obligation.name), `${c.id}: duplicate obligation ${obligation.name}`);
        names.add(obligation.name);
      }
    }
  }
  const runtimeIds = new Set();
  for (const entry of runtime.production) {
    assert.ok(!runtimeIds.has(entry.id), `duplicate runtime entry: ${entry.id}`);
    runtimeIds.add(entry.id);
    const c = manifest.contracts.find((c) => c.id === entry.publicContract);
    assert.ok(c, `${entry.id}: missing public contract ${entry.publicContract}`);
    assert.equal(entry.verifiedMRDT, `Sal.MRDTs.${c.certificate.split(' ')[0]}`,
      `${entry.id}: runtime certificate does not match its public contract`);
  }
}

export function contractSource(manifest) {
  // Spell out the conclusion: weakening IsSpecLinearizable during a framework
  // refactor must not silently weaken this gate along with it.
  const conclusion = `(v : Version) (s : implementation.State)
    (E : Set (Op implementation.AppOp)) (hver : C.ver v = some (s, E)) :
    ∃ π : List (Op implementation.AppOp),
      listPermOf π E ∧
      respects π (@loOn implementation.toUpdateSig rc C.replayContext E) ∧
      spec.Legal π ∧ rel s (spec.run π) ∧
      ∀ q, implementation.query s q = spec.query (spec.run π) q`;
  const entries = manifest.contracts.map((c, i) => `
namespace Entry${i}
noncomputable def implementation : MRDTSig := ${c.implementation}
noncomputable def issuance : Issuance implementation := ${c.issuance}
noncomputable def rc : ReplayPolicy implementation.toUpdateSig := ${c.rc}
noncomputable def spec : SequentialSpec implementation := ${c.spec}
noncomputable def rel : implementation.State → spec.State → Prop := ${c.relation}
noncomputable def certificate : VerifiedMRDT implementation := ${c.certificate}
example : certificate.issuance = issuance := by rfl
example : certificate.rc = rc := by rfl
example : certificate.Spec = spec := by rfl
example : certificate.Rel = rel := by rfl
example : @ReplayAdequacyCertificate implementation issuance rc := certificate.replayAdequacy
example : SequentialCorrectnessCertificate implementation issuance rc spec rel :=
  certificate.sequentialCorrectness
theorem ordinary {C : Configuration implementation}
    (h : MintCertifiedReach implementation issuance C)
    ${conclusion} := certificate.correct h v s E hver
theorem virtual {C : Configuration implementation}
    (h : MintCertifiedReachV implementation (canonicalVirtualMergeBase implementation) issuance C)
    ${conclusion} := certificate.correctV h v s E hver
#print axioms certificate
#print axioms ordinary
#print axioms virtual
${(c.obligations ?? []).map((o, j) => `
theorem obligation${j} : ${o.statement} := ${o.proof}
#print axioms obligation${j}
`).join('')}
end Entry${i}
`).join('\n');
  const registry = manifest.contracts.map((c, i) =>
    `PackagedMRDT.of "${c.id}" Entry${i}.certificate`).join(',\n    ');
  return `import Sal.MRDTs.Metatheory.PublicCertificateGate
namespace Sal.MRDTs.PublicContractCheck
open Sal.EmbedRGA Sal.MRDTs.Foundation
set_option autoImplicit false
noncomputable section
${entries}
-- Exact list equality: omitted, extra, reordered or substituted packages fail.
example : Production.registry = [${registry}] := by rfl
end
end Sal.MRDTs.PublicContractCheck
`;
}

export function checkAxioms(output, count, obligations = []) {
  const allowed = new Set(['propext', 'Classical.choice', 'Quot.sound']);
  const reports = [...output.matchAll(/'Sal\.MRDTs\.PublicContractCheck\.(Entry\d+\.(?:certificate|ordinary|virtual|obligation\d+))' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)/g)];
  assert.equal(reports.length, count * 3 + obligations.length, 'missing public-certificate axiom reports');
  const expected = new Set(Array.from({ length: count }, (_, i) =>
    ['certificate', 'ordinary', 'virtual'].map((name) => `Entry${i}.${name}`)).flat());
  for (const name of obligations) expected.add(name);
  for (const report of reports) {
    assert.ok(expected.delete(report[1]), `unexpected or duplicate axiom report: ${report[1]}`);
    for (const axiom of (report[2] ?? '').split(',').map((s) => s.trim()).filter(Boolean)) {
      assert.ok(allowed.has(axiom), `unapproved axiom in public certificate: ${axiom}`);
    }
  }
  assert.equal(expected.size, 0, 'missing public-certificate axiom reports');
}

export function runLean(source) {
  // Keep Lean's temporary input inside the project so its module root is valid.
  const directory = mkdtempSync(join(repoRoot, '.lake/public-contract-check-'));
  try {
    const path = join(directory, 'Check.lean');
    writeFileSync(path, source);
    const result = spawnSync('lake', ['env', 'lean', path], {
      cwd: repoRoot, encoding: 'utf8', timeout: 180000, maxBuffer: 16 * 1024 * 1024,
    });
    if (result.error) throw result.error;
    return result;
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

export function checkPublicCertificates() {
  const manifest = readJSON('public-contracts.json');
  validateContracts(manifest, readJSON('runtime/evidence-manifest.json'));
  const result = runLean(contractSource(manifest));
  assert.equal(result.status, 0, `public contract type checking failed:\n${result.stdout}\n${result.stderr}`);
  checkAxioms(result.stdout, manifest.contracts.length, manifest.contracts.flatMap((c, i) =>
    (c.obligations ?? []).map((_, j) => `Entry${i}.obligation${j}`)));
  console.log(`Public certificate gate: ${manifest.contracts.length} exact contracts; ordinary + virtual correctness; axiom audit passed. Semantic review remains pending.`);
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  checkPublicCertificates();
}
