import assert from 'node:assert/strict';
import test from 'node:test';
import { checkAxioms, contractSource, readJSON, runLean, validateContracts } from './check-public-certificates.mjs';

const contracts = readJSON('public-contracts.json');
const runtime = readJSON('runtime/evidence-manifest.json');

test('the contract selection and runtime mappings are well formed', () => {
  validateContracts(contracts, runtime);
});

test('missing obligations, duplicate identities and certificate-derived specs are rejected', () => {
  for (const key of ['certificate', 'implementation', 'issuance', 'rc', 'spec', 'relation']) {
    const bad = structuredClone(contracts);
    delete bad.contracts[0][key];
    assert.throws(() => validateContracts(bad, runtime), new RegExp(`missing ${key}`));
  }
  const duplicate = structuredClone(contracts);
  duplicate.contracts.push(duplicate.contracts[0]);
  assert.throws(() => validateContracts(duplicate, runtime), /duplicate contract/);
  const circular = structuredClone(contracts);
  circular.contracts[0].spec = 'Instances.GSet.verified.Spec';
  assert.throws(() => validateContracts(circular, runtime), /independently/);
});

test('runtime cannot name an unregistered or different certificate', () => {
  const absent = structuredClone(runtime);
  absent.production[0].publicContract = 'unregistered-queue';
  assert.throws(() => validateContracts(contracts, absent), /missing public contract/);
  const different = structuredClone(runtime);
  different.production[0].verifiedMRDT = 'Sal.MRDTs.Instances.Queue.replayAdequate';
  assert.throws(() => validateContracts(contracts, different), /does not match/);
});

test('axiom audit fails closed, including for hidden assumptions', () => {
  const reports = ['certificate', 'ordinary', 'virtual'].map((name) =>
    `'Sal.MRDTs.PublicContractCheck.Entry0.${name}' depends on axioms: [propext, Classical.choice, Quot.sound]`).join('\n');
  checkAxioms(reports, 1);
  assert.throws(() => checkAxioms('', 1), /missing.*axiom reports/);
  assert.throws(() => checkAxioms(reports.replace('Entry0.virtual', 'Entry0.ordinary'), 1), /duplicate axiom report/);
  for (const axiom of ['sorryAx', 'Sal.hiddenAssumption', 'Lean.trustCompiler']) {
    assert.throws(() => checkAxioms(reports.replaceAll('Quot.sound', axiom), 1), /unapproved axiom/);
  }
  assert.throws(() => checkAxioms(reports, 1, ['Entry0.obligation0']), /missing.*axiom reports/);
  checkAxioms(`${reports}\n'Sal.MRDTs.PublicContractCheck.Entry0.obligation0' depends on axioms: [propext]`,
    1, ['Entry0.obligation0']);
});

test('declared semantic obligations require an explicit statement and proof', () => {
  for (const key of ['statement', 'proof']) {
    const bad = structuredClone(contracts);
    delete bad.contracts.find((c) => c.id === 'queue').obligations[0][key];
    assert.throws(() => validateContracts(bad, runtime), new RegExp(`missing obligation ${key}`));
  }
});

test('Lean rejects a missing registry entry, even if all remaining contracts typecheck', () => {
  const bad = structuredClone(contracts);
  bad.contracts.pop();
  const result = runLean(contractSource(bad));
  assert.equal(result.status, 1, result.stderr);
  assert.match(result.stdout, /error:.*(?:rfl|Tactic)/);
  assert.match(result.stdout, /Production.registry/);
});

test('Lean rejects a changed semantic rc without changing the public certificate', () => {
  const bad = structuredClone(contracts);
  const lww = bad.contracts.find((c) => c.id === 'lww-register');
  lww.rc = 'ReplayPolicy.unconstrained Instances.LWWRegister.D.toUpdateSig';
  const result = runLean(contractSource(bad));
  assert.equal(result.status, 1, result.stderr);
  assert.match(result.stdout, /error:/);
  assert.match(result.stdout, /certificate.rc = rc|SequentialCorrectnessCertificate/);
});

test('Lean rejects the older OR-set certificate for the efficient implementation', () => {
  const bad = structuredClone(contracts);
  bad.contracts.find((c) => c.id === 'efficient-or-set').certificate =
    'Instances.ORSet.verified (α := Nat)';
  validateContracts(bad, runtime);
  const result = runLean(contractSource(bad));
  assert.equal(result.status, 1, result.stderr);
  assert.match(result.stdout, /error:.*Type mismatch/);
  assert.match(result.stdout, /VerifiedMRDT/);
});

test('Lean rejects Queue evidence that drops the concurrent FIFO obligations', () => {
  const bad = structuredClone(contracts);
  const queue = bad.contracts.find((c) => c.id === 'queue');
  queue.obligations[0].proof = 'fun C exec => (Instances.Queue.queue_correct exec).1';
  validateContracts(bad, runtime);
  const result = runLean(contractSource(bad));
  assert.equal(result.status, 1, result.stderr);
  assert.match(result.stdout, /error:.*Type mismatch/);
  assert.match(result.stdout, /IsSpecLinearizable/);
});

test('Lean rejects MVR evidence that drops causally maximal writes', () => {
  const bad = structuredClone(contracts);
  const mvr = bad.contracts.find((c) => c.id === 'mvr');
  mvr.obligations[0].proof = 'fun C exec => (Instances.MVRLive.mvr_correct exec).1';
  validateContracts(bad, runtime);
  const result = runLean(contractSource(bad));
  assert.equal(result.status, 1, result.stderr);
  assert.match(result.stdout, /error:.*Type mismatch/);
  assert.match(result.stdout, /IsSpecLinearizable/);
});

test('Lean rejects the grow-only MVR certificate for the compact implementation', () => {
  const bad = structuredClone(contracts);
  bad.contracts.find((c) => c.id === 'mvr').certificate = 'Instances.MVR.verified';
  validateContracts(bad, runtime);
  const result = runLean(contractSource(bad));
  assert.equal(result.status, 1, result.stderr);
  assert.match(result.stdout, /error:.*Type mismatch/);
  assert.match(result.stdout, /VerifiedMRDT/);
});

test('Lean rejects FugueMax replay and non-interleaving without the plain-list contract', () => {
  const bad = structuredClone(contracts);
  bad.contracts.find((c) => c.id === 'fugue-max').obligations[0].proof =
    '@Instances.SidedEmbedRGA.FugueMax.replay_noninterleaving unaryCode';
  validateContracts(bad, runtime);
  const result = runLean(contractSource(bad));
  assert.equal(result.status, 1, result.stderr);
  assert.match(result.stdout, /error:.*Type mismatch/);
});

test('Lean rejects FugueMax list correctness without same-witness non-interleaving', () => {
  const bad = structuredClone(contracts);
  bad.contracts.find((c) => c.id === 'fugue-max').obligations[0].proof =
    'fun C exec => by cases exec with | ordinary h => exact (Instances.SidedEmbedRGA.FugueMax.verified unaryCode).correct h | virtual h => exact (Instances.SidedEmbedRGA.FugueMax.verified unaryCode).correctV h';
  validateContracts(bad, runtime);
  const result = runLean(contractSource(bad));
  assert.equal(result.status, 1, result.stderr);
  assert.match(result.stdout, /error:.*Type mismatch/);
});
