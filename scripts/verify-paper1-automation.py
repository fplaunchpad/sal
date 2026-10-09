#!/usr/bin/env python3
"""Build and audit the existing production proof paths for all 23 named cases.

Counts are named cases, not independent implementations: GSet/AddStore share a
family; Counter/IOC share delta one. Queue's obstructed native API is outside
this 23-case raw-VC coverage. Fugue is represented-state convergence plus a
checked criterion obstruction, never an RA certificate.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'experiments/vc-automation/results'
P = 'Sal.MRDTs.Paper1.'
VERIFY = P + 'Automation.CommonVerification.verify'
JOIN = P + 'ConcreteMRDT.Raw.join_at_sizes'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
CASES = []

def case(identifier, endpoint, vc, bridge, suffixes=('executions', 'executionsV')):
    CASES.append(dict(id=identifier, endpoints=[P + endpoint + '.' + s for s in suffixes],
                      vc_roots=[P + vc], required_bridge=[P + bridge],
                      claim='existing production certificate'))

for identifier, name, family in [
        ('grow-only-set', 'gset', 'Add'), ('add-store', 'addStore', 'Add'),
        ('finite-add-store', 'finiteAdd', 'Finite'), ('counter', 'counter', 'Delta'),
        ('increment-only-counter', 'ioc', 'Delta'), ('pn-counter', 'pn', 'Delta'),
        ('flat-grow-only-set', 'booleanSet', 'Boolean'), ('flat-grow-only-map', 'booleanMap', 'Boolean')]:
    CASES.append(dict(id=identifier,
        endpoints=[P + 'ConcreteMRDT.SimplePorts.' + name + 'Executions' + s for s in ('', 'V')],
        vc_roots=[P + 'ConcreteMRDT.SimplePorts.' + name + 'Conditions'],
        required_bridge=[P + 'SimpleEventPorts.' + family + '.simulation'],
        claim='existing production certificate',
        vc_root_kind='existing conditions bundle; no separate named datatype raw-VC theorem'))
case('lww-register', 'LWW.GuardedPort', 'LWW.GuardedPort.certificate', 'LWW.GuardedPort.history')
case('rga', 'RGA.ConcretePort', 'RGA.ConcretePort.conditions', 'RGA.ConcretePort.history')
for identifier, family in [('bounded-counter', 'Bounded'), ('tree-move', 'Tree'), ('aegis-sheet', 'Sheet')]:
    case(identifier, 'ConcreteMRDT.GuardedPorts.' + family,
         'ConcreteMRDT.GuardedPorts.' + family + '.conditions',
         'ConcreteMRDT.GuardedPorts.' + family + '.history')
case('ordinary-or-set-paper-example', 'ORSet.RawExecution', 'ORSet.GuardedRawVC.mergeVCs', 'ORSet.EventSpec.foldHistorySound')
case('efficient-or-set', 'EfficientORSet.RawCertificate', 'EfficientORSet.GuardedRawVC.mergeVCs', 'EfficientORSet.EventSpec.foldHistorySound')
case('mvr', 'CertifiedQueueMVR.MVR.Certificate', 'CertifiedQueueMVR.MVR.RawVC.mergeVCs', 'CertifiedMVRHistory.replay_history')
case('embed-rga', 'CertifiedRGAInvariantCertificate', 'CertifiedRGAVC.Embedded.mergeVCs', 'CertifiedRGAInvariantHistory.canonical_valid_history')
case('sided-embed-rga', 'CertifiedSidedInvariantCertificate', 'CertifiedRGAVC.Sided.mergeVCs', 'CertifiedSidedInvariantHistory.canonical_valid_history')
case('peritext-embed-rga', 'CertifiedPeritextInvariantCertificate', 'CertifiedPeritextVC.mergeVCs', 'CertifiedRGAInvariantHistory.canonical_valid_history')
case('sided-peritext-core', 'CertifiedRGACoreCertificate', 'CertifiedRGACoreMergeVC.mergeVCs', 'CertifiedRGACoreCertificate.history')
case('sided-peritext-rich-core', 'CertifiedRGARichCertificate', 'CertifiedRGARichVC.mergeVCs', 'CertifiedRGARichCertificate.history')
case('anchored-queue-paper-variant', 'AnchoredQueue.History', 'AnchoredQueue.mergeVCs', 'AnchoredQueue.History.schedule_publicWitness')
CASES.append(dict(id='fugue-max', endpoints=[P + 'CertifiedFugueVCExecution.representedVersions'],
    vc_roots=[P + 'CertifiedFugueVC.mergeVCs'], required_bridge=[],
    controls=[P + 'CertifiedFugueRawOrderObstruction.certified_raw_criterion_failure',
              P + 'CertifiedFugueRawOrderObstruction.admitted_history_control',
              P + 'CertifiedFugueInvariantObstruction.valid_execution_counterexample'],
    claim='represented-state convergence and checked raw/invariant criterion obstruction; no RA claim'))
# Also inspect existing facade endpoints; these once rebuilt the obsolete
# scoped law bundle instead of reusing the concrete conditions.
for c in CASES:
    if c['id'] in {'grow-only-set','add-store','finite-add-store','counter','increment-only-counter','pn-counter','flat-grow-only-set','flat-grow-only-map'}:
        c['endpoints'] += [n.replace('ConcreteMRDT.SimplePorts.', 'ConcreteMRDT.Guarded.SimplePorts.') for n in c['endpoints']]
    facade = {'bounded-counter':'bounded', 'tree-move':'tree', 'aegis-sheet':'sheet', 'rga':'rga'}.get(c['id'])
    if facade:
        c['endpoints'] += [P + 'ConcreteMRDT.Guarded.ScopedPorts.' + facade + 'Executions' + suffix for suffix in ('','V')]
assert len(CASES) == 23 and len({c['id'] for c in CASES}) == 23

# Existing Ledger already rejects each family's old correctness path. This
# standalone audit additionally checks every selected root, including bundle
# definitions, and rejects prototype namespaces and the dormant commuting VC.
FORBIDDEN = {P + 'ConcreteMRDT.CommutingPort.mergeVCs'}
ledger = (ROOT / 'Sal/MRDTs/Paper1/Ledger.lean').read_text()
for command in ('assert_raw_vc_dependencies', 'assert_commuting_vc_dependencies',
                'assert_certified_mvr_dependencies', 'assert_certified_rga_dependencies'):
    section = ledger.split('elab "' + command + ' ', 1)[1].split('\nassert_', 1)[0]
    for block in re.findall(r'let forbidden := \[(.*?)\]\.map String.toName', section, re.S):
        FORBIDDEN.update(re.findall(r'"([^"]+)"', block))


LEAN_AUDIT = r'''
open Lean in
partial def auditVerifierApps (verifier : Name) : Expr → List Expr
  | e@(.app f a) =>
    if e.getAppFn.isConstOf verifier then
      e :: e.getAppArgs.toList.flatMap (auditVerifierApps verifier)
    else auditVerifierApps verifier f ++ auditVerifierApps verifier a
  | .lam _ t b _ | .forallE _ t b _ => auditVerifierApps verifier t ++ auditVerifierApps verifier b
  | .letE _ t v b _ => auditVerifierApps verifier t ++ auditVerifierApps verifier v ++ auditVerifierApps verifier b
  | .mdata _ e | .proj _ _ e => auditVerifierApps verifier e
  | _ => []

open Lean Elab Command in
elab "audit_verifier_traversal_control" : command => do
  let verifier := ``Sal.MRDTs.Paper1.Automation.CommonVerification.verify
  let first := mkApp (mkConst verifier) (mkConst `FIRST_VC_INPUT)
  let second := mkApp (mkConst verifier) (mkConst `SECOND_VC_INPUT)
  let tree := mkApp2 (mkConst ``And.intro) first second
  let apps := auditVerifierApps verifier tree
  unless apps.length == 2 && apps[0]!.getUsedConstants.contains `FIRST_VC_INPUT &&
      apps[1]!.getUsedConstants.contains `SECOND_VC_INPUT do
    throwError "VC traversal dropped one of two submitted verification applications"
  unless (auditVerifierApps verifier (mkConst ``True.intro)).isEmpty do
    throwError "VC traversal invented an absent verification application"
  logInfo "PROD_VC_TRAVERSAL_CONTROL pass: both applications retained; absent application excluded"

open Lean Elab Command in
elab "audit_production " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let axioms ← liftCoreM <| Lean.collectAxioms root
  logInfo m!"PROD_AXIOMS {root} {axioms}"
  let mut seen : NameSet := {}
  let mut pending := [root]
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      if let some info := env.find? current then
        if current.toString.startsWith "Sal." || current.toString.startsWith "_private.Sal." || current.toString.startsWith "NeemExpansion." ||
            current.toString.startsWith "EfficientReplayAdapter." || current.toString.startsWith "CausalEventClassification." then
          logInfo m!"PROD_DEP {root} {current}"
          if let some moduleIdx := env.getModuleIdxFor? current then
            if let some ranges ← findDeclarationRanges? current then
              let kind := match info with | .thmInfo _ => "theorem" | _ => "definition"
              logInfo m!"PROD_SOURCE {current} {env.header.moduleNames[moduleIdx.toNat]!} {ranges.range.pos.line} {ranges.range.endPos.line} {kind}"
        pending := info.getUsedConstantsAsSet.toList ++ pending

  logInfo m!"PROD_COMPLETE {root}"

open Lean Elab Command in
elab "audit_production_vc_evidence " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let verifier := ``Sal.MRDTs.Paper1.Automation.CommonVerification.verify
  let mut visited : NameSet := {}
  let mut pending := [root]
  let mut evidence : NameSet := {}
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless visited.contains current do
      visited := visited.insert current
      if let some info := env.find? current then
        let value := match info with
          | .thmInfo i => some i.value
          | .defnInfo i => some i.value
          | _ => none
        let applications := value.toList.flatMap (auditVerifierApps verifier)
        if !applications.isEmpty then
          logInfo m!"PROD_VC_APP {root} {current}"
          for proof in applications do
            for dependency in proof.getUsedConstants do
              evidence := evidence.insert dependency
        else
          pending := info.getUsedConstantsAsSet.toList ++ pending
  if evidence.isEmpty then
    throwError "{root} has no actual CommonVerification.verify application"
  visited := {}
  pending := evidence.toList
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless visited.contains current do
      visited := visited.insert current
      if let some info := env.find? current then
        if current.toString.startsWith "Sal." || current.toString.startsWith "_private.Sal." then
          logInfo m!"PROD_VC_DEP {root} {current}"
        pending := info.getUsedConstantsAsSet.toList ++ pending
  logInfo m!"PROD_VC_COMPLETE {root}"
'''



def audit_imports():
    """Inspect the actual repository import graph before invoking the kernel."""
    roots = ['Sal.MRDTs.Paper1.Ledger', 'Sal.MRDTs.Paper1.Automation.Controls',
             'Sal.MRDTs.Paper1.Automation.ORSetAutomationControls',
             'Sal.MRDTs.Paper1.Automation.OrderedAutomationControls',
             'Sal.MRDTs.Paper1.Automation.CodeCompositionControls',
             'Sal.MRDTs.Paper1.Automation.SidedFugueAutomationControls']
    pending = list(roots)
    local = {}
    external = set()
    packages = ('Mathlib', 'Lean', 'Init', 'Std', 'Batteries', 'Aesop', 'Blaster', 'Qq', 'ProofWidgets')
    while pending:
        module = pending.pop()
        if module in local or module in external:
            continue
        path = ROOT / (module.replace('.', '/') + '.lean')
        if not path.is_file():
            assert any(module == p or module.startswith(p + '.') for p in packages), ('unexpected non-package import', module)
            external.add(module)
            continue
        file = path.relative_to(ROOT).as_posix()
        assert not file.startswith('experiments/'), ('experimental import', module, file)
        imports = re.findall(r'^import\s+(\S+)', path.read_text(), re.M)
        local[module] = dict(file=file, imports=imports)
        pending.extend(imports)
    return dict(status='pass', root_modules=roots, local_modules=local,
                external_modules=sorted(external), forbidden_imports=[],
                external_evidence='package modules checked by lake build; repository modules source-scanned')

def run(command, logfile):
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (OUT / logfile).write_text(result.stdout)
    if result.returncode:
        print(result.stdout[-18000:])
        raise SystemExit(result.returncode)
    return result.stdout



def audit_orset_author_interface(evidence):
    """Exclude cached compatibility proofs from the generated OR-set VC inputs."""
    prefixes = (P + 'Automation.AutomatedORSet.',
                P + 'Automation.AutomatedEfficientORSet.')
    data = {prefixes[1] + 'maskDescription', prefixes[1] + 'birth'}
    report = {}
    for c in CASES:
        if c['id'] not in {'ordinary-or-set-paper-example', 'efficient-or-set'}:
            continue
        used, bad = set(), set()
        for root in c['vc_roots']:
            for dependency in evidence[root]['dependencies']:
                if not any(prefix in dependency for prefix in prefixes):
                    continue
                # Compiler-generated equations for a raw data definition may be
                # used by simp; a cached proof/kit/shape theorem may not be used.
                allowed = any(dependency == name or
                              dependency.startswith(name + '.eq_') or
                              dependency.startswith(name + '._eq_') for name in data)
                if c['id'] == 'ordinary-or-set-paper-example' or not allowed:
                    bad.add(dependency)
                else:
                    used.add(dependency)
        assert not bad, (c['id'], 'cached datatype proof dependency', sorted(bad))
        report[c['id']] = dict(status='pass', permitted_data_dependencies=sorted(used),
                              cached_proof_dependencies=[])
    return report

def audit_ordered_author_interface(evidence):
    """Inspect submitted ordered evidence, rather than only facade ancestry."""
    prefix = P + 'Automation.AutomatedRGA.Embedded.'
    eliminated = {prefix + n for n in
                  ('provenance_step', 'membership_step', 'ordered_step', 'merge_cell', 'adapter')}
    primitive_prefix = 'Sal.MRDTs.Instances.EmbedRGA.'
    eliminated.update(primitive_prefix + n for n in
                      ('mem_eInsert', 'mem_eMerge2', 'eInsert_sorted', 'eMerge2_sorted', 'eMerge_sorted', 'esorted_ext'))
    eliminated.update('Sal.EmbedRGA.' + n for n in
                      ('keyLt_irrefl', 'keyLt_asymm', 'keyLt_trans', 'keyLt_total',
                       'key_inj', 'coordOf_inj', 'enc_ne_nil'))
    report = {}
    for c in CASES:
        if c['id'] not in {'embed-rga', 'anchored-queue-paper-variant', 'peritext-embed-rga'}:
            continue
        dependencies = set().union(*(set(evidence[root]['dependencies']) for root in c['vc_roots']))
        bad = dependencies & eliminated
        bad.update(d for d in dependencies if 'Automation.AutomatedRGA.' in d and d.endswith('.id_mem'))
        assert not bad, (c['id'], 'eliminated ordered compatibility proof reused', sorted(bad))
        assert P + 'Automation.OrderedRecords.ChainMapping.unique_keys' in dependencies, (c['id'], 'missing generic issuance derivation')
        author = sorted(d for d in dependencies if prefix in d)
        report[c['id']] = dict(status='pass', datatype_author_dependencies=author,
            eliminated_compatibility_proofs=sorted(eliminated),
            residual_boundary='Generic comparator, sorted-list and prefix-code laws derive correctness from kernel-checked raw recursive equations and datatype data mappings.')
    return report

def audit_sided_author_interface(evidence):
    """Reject cached datatype law dispatch in the actual submitted VC inputs."""
    prefix = P + 'Automation.AutomatedRGA.Sided.'
    eliminated = {prefix + n for n in
        ('provenance_step', 'membership_step', 'ordered_step', 'merge_cell', 'adapter')}
    eliminated.update('Sal.MRDTs.Instances.SidedEmbedRGA.' + n for n in
        ('mem_sInsert', 'mem_sMerge2', 'sInsert_sorted', 'sMerge2_sorted', 'sMerge_sorted', 'ssorted_ext', 'sKey_inj'))
    eliminated.update('Sal.EmbedRGA.' + n for n in ('sKey_inj', 'sidedCoordOf_inj', 'keyLt_irrefl', 'keyLt_asymm', 'keyLt_trans',
         'keyLt_total', 'enc_ne_nil', 'sBlock_eq', 'sideSym_inj', 'sideSym_band_ne',
         'map_prefix_reflect', 'sBlock_ne_nil'))
    report = {}
    for case in CASES:
        if case['id'] not in {'sided-embed-rga', 'sided-peritext-core', 'sided-peritext-rich-core'}:
            continue
        dependencies = set().union(*(set(evidence[root]['dependencies']) for root in case['vc_roots']))
        bad = dependencies & eliminated
        assert not bad, (case['id'], 'cached sided datatype law dependency', sorted(bad))
        assert P + 'Automation.OrderedRecords.ChainMapping.unique_keys' in dependencies, (case['id'], 'missing generic issuance derivation')
        report[case['id']] = dict(status='pass',
            datatype_author_dependencies=sorted(d for d in dependencies if prefix in d),
            eliminated_compatibility_proofs=sorted(eliminated))
    return report

def audit_fugue_author_interface(evidence):
    """Separate generated archive/code laws from still-retained issuance lemmas."""
    eliminated = {'Sal.EmbedRGA.' + n for n in (
        'keyLt_irrefl', 'keyLt_asymm', 'keyLt_trans', 'keyLt_total', 'enc_ne_nil',
        'fmCoordOf_inj', 'fwTag_cancel', 'fw_group_inj', 'map_prefix_reflect',
        'tagOK_prefixFree', 'tagOK_key', 'key_body_prefixFree')}
    eliminated.update('Sal.MRDTs.Instances.SidedEmbedRGA.' + n for n in (
        'mem_sInsert', 'mem_sMerge2', 'sInsert_sorted', 'sMerge2_sorted',
        'sMerge_sorted', 'ssorted_ext', 'sKey_inj',
        'mGenInsAfter_none', 'mGenInsAfter_someTrue', 'mGenInsAfter_someFalse',
        'mRecOfId_of_minted', 'mChainOf_zero', 'mChainOf_eq_of_rec', 'succOfM_mem',
        'succOfM_pair', 'succCandM_sub', 'mKeys_shape', 'foldl_maxKey_mem'))
    eliminated.update('Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.' + n for n in (
        'insert_position_finite', 'delete_position_finite',
        'canIssue_insert_iff', 'canIssue_delete_iff'))
    eliminated.add(P + 'Automation.AutomatedFugue.provenance_step')
    case = next(c for c in CASES if c['id'] == 'fugue-max')
    dependencies = set().union(*(set(evidence[root]['dependencies']) for root in case['vc_roots']))
    bad = dependencies & eliminated
    assert not bad, ('fugue-max', 'cached archived/code datatype law dependency', sorted(bad))
    required = {P + 'Automation.' + n for n in (
        'ArchivedOrderedRecords.Equations.kit', 'PrefixCodes.encode_injective',
        'CertifiedIssuance.creator_of_mint', 'append_delta_valid')}
    assert required <= dependencies, ('fugue-max', 'missing generic archive/code/issuance derivation', sorted(required - dependencies))
    return dict(status='pass', eliminated_compatibility_proofs=sorted(eliminated),
        generic_derivation_markers=sorted(required),
        retained_issuance_dependencies=sorted(d for d in dependencies if
            d.startswith('Sal.MRDTs.Instances.SidedEmbedRGA.') or d.startswith('Sal.EmbedRGA.')),
        claim='represented-state convergence; separate sequential-specification obstruction remains')

def main():
    OUT.mkdir(exist_ok=True)
    import_audit = audit_imports()
    imported_hashes = {entry['file']: hashlib.sha256((ROOT / entry['file']).read_bytes()).hexdigest()
                       for entry in import_audit['local_modules'].values()}
    print('Building production Ledger and automation controls', flush=True)
    run(['lake', 'build', 'Sal.MRDTs.Paper1.Ledger', 'Sal.MRDTs.Paper1.Automation.Controls',
         'Sal.MRDTs.Paper1.Automation.ORSetAutomationControls',
             'Sal.MRDTs.Paper1.Automation.OrderedAutomationControls',
             'Sal.MRDTs.Paper1.Automation.CodeCompositionControls',
             'Sal.MRDTs.Paper1.Automation.SidedFugueAutomationControls'], 'production-build.log')
    run([sys.executable, 'scripts/check-paper1-automation-contracts.py'], 'production-source-contracts.log')
    run([sys.executable, 'scripts/check-paper1-automation-contracts.py', '--baseline', '7880732',
         '--output', str(OUT / 'orset-derivation-contracts.json')], 'orset-derivation-source-contracts.log')
    run([sys.executable, 'scripts/check-paper1-automation-contracts.py', '--baseline', 'ffec6e9',
         '--output', str(OUT / 'ordered-derivation-contracts.json')], 'ordered-derivation-source-contracts.log')
    run([sys.executable, 'scripts/check-paper1-automation-contracts.py', '--baseline', '7e7ec86',
         '--output', str(OUT / 'sided-derivation-contracts.json')], 'sided-derivation-source-contracts.log')
    run([sys.executable, 'experiments/vc-automation/test_sided_contract_source.py'], 'sided-source-controls.log')
    run([sys.executable, 'experiments/vc-automation/test_sided_evidence_audit.py'], 'sided-evidence-controls.log')
    run([sys.executable, 'experiments/vc-automation/test_ordered_contract_source.py'], 'ordered-source-controls.log')
    run([sys.executable, 'experiments/vc-automation/test_contract_audit.py'], 'production-contract-controls.log')
    roots = sorted({name for c in CASES for key in ('endpoints', 'vc_roots', 'controls') for name in c.get(key, [])})
    program = ('import Sal.MRDTs.Paper1.Ledger\nimport Sal.MRDTs.Paper1.Automation.Controls\n'
               'import Sal.MRDTs.Paper1.Automation.ORSetAutomationControls\n'
               'import Sal.MRDTs.Paper1.Automation.OrderedAutomationControls\n'
               'import Sal.MRDTs.Paper1.Automation.CodeCompositionControls\n'
               'import Sal.MRDTs.Paper1.Automation.SidedFugueAutomationControls\n' + LEAN_AUDIT)
    program += 'audit_verifier_traversal_control\n'
    program += '\n'.join('audit_production ' + name for name in roots) + '\n'
    vc_roots = sorted({name for c in CASES for name in c['vc_roots']})
    program += '\n'.join('audit_production_vc_evidence ' + name for name in vc_roots) + '\n'
    print(f'Auditing {len(CASES)} named cases, {len(roots)} distinct existing roots', flush=True)
    with tempfile.TemporaryDirectory(prefix='sal-production-audit-') as tmp:
        path = Path(tmp) / 'ProductionAudit.lean'
        path.write_text(program)
        log = run(['lake', 'env', 'lean', str(path)], 'production-audit.log')
    assert 'PROD_VC_TRAVERSAL_CONTROL pass:' in log, 'Missing verifier traversal control'
    complete = re.findall(r'PROD_COMPLETE (\S+)', log)
    assert complete == roots, 'Missing or duplicate root audits'
    declarations = {}
    for name, module, start, end, kind in re.findall(r'PROD_SOURCE (\S+) (\S+) (\d+) (\d+) (\S+)', log):
        file = module.replace('.', '/') + '.lean'
        if not (ROOT / file).exists():
            continue
        declarations[name] = dict(file=file, module=module, start_line=int(start), end_line=int(end), kind=kind)
    audited = {name: dict(dependencies=[], axioms=[]) for name in roots}
    for name, dependency in re.findall(r'PROD_DEP (\S+) (\S+)', log):
        audited[name]['dependencies'].append(dependency)
    axiom_rows = re.findall(r'PROD_AXIOMS (\S+) \[(.*?)\]', log, re.S)
    assert [name for name, _ in axiom_rows] == roots, 'Missing or duplicate axiom audits'
    vc_complete = re.findall(r'PROD_VC_COMPLETE (\S+)', log)
    assert vc_complete == vc_roots, 'Missing or duplicate raw-VC evidence audits'
    for name, axioms in axiom_rows:
        audited[name]['axioms'] = [a.strip() for a in axioms.split(',') if a.strip()]
    for name, data in audited.items():
        data['dependencies'] = sorted(set(data['dependencies']))
        assert set(data['axioms']) <= STANDARD, (name, data['axioms'])
        bad = [d for d in data['dependencies'] if d in FORBIDDEN or not d.startswith(('Sal.', '_private.Sal.'))]
        assert not bad, (name, 'legacy/prototype dependencies', bad)
    for c in CASES:
        for name in c['vc_roots']:
            assert VERIFY in audited[name]['dependencies'], (name, 'missing common verification')
        for name in c['endpoints']:
            required = [VERIFY, JOIN] + c['required_bridge']
            assert set(required) <= set(audited[name]['dependencies']), (name, 'missing', set(required) - set(audited[name]['dependencies']))
    evidence = {name: dict(dependencies=[], source_verification_declarations=[]) for name in vc_roots}
    for name, dependency in re.findall(r'PROD_VC_DEP (\S+) (\S+)', log):
        evidence[name]['dependencies'].append(dependency)
    for name, declaration in re.findall(r'PROD_VC_APP (\S+) (\S+)', log):
        evidence[name]['source_verification_declarations'].append(declaration)
    for name, data in evidence.items():
        assert data['source_verification_declarations'], (name, 'missing actual verification application')
        assert VERIFY in data['dependencies'], (name, 'missing raw evidence verifier')
        data['dependencies'] = sorted(set(data['dependencies']))
        data['source_verification_declarations'] = sorted(set(data['source_verification_declarations']))
    orset_author_interface = audit_orset_author_interface(evidence)
    ordered_author_interface = audit_ordered_author_interface(evidence)
    sided_author_interface = audit_sided_author_interface(evidence)
    fugue_author_interface = audit_fugue_author_interface(evidence)
    files = sorted({d['file'] for d in declarations.values()} | set(imported_hashes))
    source_hashes = {file: hashlib.sha256((ROOT / file).read_bytes()).hexdigest() for file in files}
    assert all(source_hashes[file] == digest for file, digest in imported_hashes.items()), 'Source changed during production audit'
    report = dict(schema_version=1, status='pass', named_case_count=23,
        unique_endpoint_count=len({n for c in CASES for n in c['endpoints']}),
        counting_note=__doc__, cases=CASES, roots=audited,
        declaration_sources=declarations, vc_evidence_closures=evidence,
        orset_author_interface=orset_author_interface, ordered_author_interface=ordered_author_interface,
        sided_author_interface=sided_author_interface, fugue_author_interface=fugue_author_interface,
        source_sha256=source_hashes,
        controls=['Sal/MRDTs/Paper1/Automation/Controls.lean',
                  'Sal/MRDTs/Paper1/Automation/ORSetAutomationControls.lean',
                  'Sal/MRDTs/Paper1/Automation/OrderedAutomationControls.lean',
                  'Sal/MRDTs/Paper1/Automation/CodeCompositionControls.lean',
                  'Sal/MRDTs/Paper1/Automation/SidedFugueAutomationControls.lean',
                  'experiments/vc-automation/test_ordered_contract_source.py',
                  'experiments/vc-automation/test_sided_contract_source.py',
                  'experiments/vc-automation/test_sided_evidence_audit.py',
                  'experiments/vc-automation/test_contract_audit.py',
                  'scripts/check-paper1-automation-contracts.py'],
        forbidden_dependencies=sorted(FORBIDDEN),
        import_audit=import_audit,
        experiments_imported=bool(import_audit['forbidden_imports']), fugue_ra_claim=False)
    (OUT / 'production-audit.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Production automation audit passed: 23 named cases, {len(roots)} roots.')


if __name__ == '__main__':
    main()
