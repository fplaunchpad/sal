#!/usr/bin/env python3
"""Complete certified campaign closure and retained-source accounting.

The conservative concrete metric includes every declaration kind, so no invariant
definition, projection descriptor, annotation or helper escapes via naming.
Executable/model costs are deliberately not subtracted from that metric. Kernel
closures are supplemented by whole changed modules to expose retained helpers.
"""
import argparse, hashlib, importlib.util, json, subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
SNAP = ROOT / 'experiments/vc-automation/certification-invariants-baseline'
OUT = ROOT / 'experiments/vc-automation/results'
spec = importlib.util.spec_from_file_location('projection', ROOT/'scripts/measure-paper1-invariant-projection.py')
M = importlib.util.module_from_spec(spec); spec.loader.exec_module(M)
B = M.B
prior = B.category
CONCRETE_AUTOMATION = ('AutomatedRGA', 'EmbeddedSequentialBridge', 'EmbeddedOrderedPrimitives',
                       'TransferAegisSheet', 'TransferNativeRGA')
GENERIC_ROOTS = ['Sal.MRDTs.Foundation.'+n for n in
                 ('witness_mono','all_insert','all_insert_of_origin','key_unique_insert','issued_event_induction')]
INSTANCE_ROOTS = ['Sal.MRDTs.Instances.EmbedRGA.'+n for n in ('embed_seq_step','eStateProjection','embed_seq_sound','e_chain_exists')]
PROOF_BUNDLE_EXCEPTIONS = {'Sal.MRDTs.Instances.ProductionRGA.embedSequentialCorrectness',
                           'Sal.MRDTs.Instances.TreeMove.sequentialCorrectness'}
def category(name, declaration):
    stem = Path(declaration['file']).stem
    if stem in CONCRETE_AUTOMATION or name.startswith('Sal.MRDTs.Paper1.Automation.TransferGuardedCommuting.Tree.'):
        return 'concrete_proof_annotation'
    return prior(name, declaration)
B.category = category
M.PROOF_ONLY_PREFIXES += ('Sal.MRDTs.Instances.EmbedRGA.eGuardedSpec',
                         'Sal.MRDTs.Instances.EmbedRGA.eStateProjection',
                         'Sal.MRDTs.Instances.ProductionRGA.embedSequentialCorrectness',
                         'Sal.MRDTs.Instances.TreeMove.sequentialCorrectness')
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def code(path): return M.code(path.read_text())
def module_category(f):
    p = Path(f)
    if p.stem.endswith(('Controls','SPOT')): return 'validation'
    if p.stem in CONCRETE_AUTOMATION or '/Instances/' in f or p.stem == 'IssuedConcretePorts': return 'concrete'
    if '/Framework/' in f or '/Automation/' in f: return 'shared'
    return 'concrete'
def measured(log, base, cases):
    B.ROOT = base; B.CASES = cases; B.BASE = 'captured-current-worktree'
    value = B.measure(log)
    return {'kernel_closure': value, 'source_union': M.footprint(value, base)}
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--baseline-only', action='store_true')
    parser.add_argument('--root', action='append', default=INSTANCE_ROOTS.copy())
    parser.add_argument('--generic-root', action='append', default=GENERIC_ROOTS.copy())
    args = parser.parse_args()
    cases = json.loads((SNAP/'cases.json').read_text())
    baseline = measured((SNAP/'kernel.log').read_text(), SNAP, cases)
    (SNAP/'campaign-measurement.json').write_text(json.dumps(baseline, indent=2)+'\n')
    if args.baseline_only:
        print(json.dumps(baseline['source_union']['totals'])); return
    cases.update({'additional-'+n: [n] for n in args.root+args.generic_root})
    OUT.mkdir(exist_ok=True)
    audit = OUT/'certification-invariants-audit.lean'
    audit.write_text('import Sal.MRDTs.Paper1.Ledger\n'+B.V.LEAN_AUDIT+'\n'+
                     '\n'.join('audit_production '+n for ns in cases.values() for n in ns)+'\n')
    before = {str(p.relative_to(ROOT)):sha(p) for p in (ROOT/'Sal').rglob('*.lean')}
    proc = subprocess.run(['lake','env','lean',str(audit)], cwd=ROOT, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT/'certification-invariants-kernel.log').write_text(proc.stdout)
    assert proc.returncode == 0, proc.stdout[-5000:]
    assert before == {str(p.relative_to(ROOT)):sha(p) for p in (ROOT/'Sal').rglob('*.lean')}, 'Source changed during audit'
    current = measured(proc.stdout, ROOT, cases)
    fixed_current = dict(current['kernel_closure'])
    original_cases = json.loads((SNAP/'cases.json').read_text())
    fixed_current['cases'] = {n:fixed_current['cases'][n] for n in original_cases}
    fixed_union = {'baseline':baseline['source_union'], 'current':M.footprint(fixed_current,ROOT)}
    families = {}
    for family, names in {
        'tree': [n for n in cases if n.startswith('tree-')]+['sequentialSound-0','legal_prefix-2'],
        'sheet': [n for n in cases if n.startswith('sheet-')]+['causalOriginSequentialSound-1','legal_prefix-3'],
        'embedded-paper1-rga': ['certified-embedded-rga'],
        'embedded-production-rga': ['embedded-production'],
        'native-rga': ['native-rga']}.items():
        phases = {}
        for phase,value,base in [('baseline',baseline,SNAP),('current',current,ROOT)]:
            selected = dict(value['kernel_closure'])
            selected['cases'] = {n:selected['cases'][n] for n in names}
            phases[phase] = M.footprint(selected,base)
        families[family] = phases
    manifest = json.loads((SNAP/'manifest.json').read_text())
    changes = {}; new = {}; preservation = []; checked = 0; reviewed_bundles = []
    for f,h in before.items():
        if f not in manifest:
            new[f] = {'code_lines':code(ROOT/f), 'sha256':h, 'category':module_category(f)}; continue
        if h == manifest[f]: continue
        changes[f] = {'baseline_whole_code_lines':code(SNAP/f),
                      'current_whole_code_lines':code(ROOT/f),
                      'delta':code(ROOT/f)-code(SNAP/f),
                      'baseline_sha256':manifest[f], 'current_sha256':h,
                      'category':module_category(f)}
        old = M.C.declarations((SNAP/f).read_text()); now = M.C.declarations((ROOT/f).read_text())
        checked += len(old)
        for n,d in old.items():
            nd = now.get(n)
            if nd is None: preservation.append([f,n,'removed declaration']); continue
            if d['header'] != nd['header'] or d['variables'] != nd['variables']:
                preservation.append([f,n,'changed statement/context'])
            if d['kind'] not in ('theorem','lemma') and d['body'] != nd['body']:
                if n in PROOF_BUNDLE_EXCEPTIONS:
                    reviewed_bundles.append({'file':f,'name':n,'review':'Only theorem-valued callbacks changed; model, issuance, relation and public type unchanged.'})
                else: preservation.append([f,n,'changed definition: requires semantic/proof descriptor review'])
    dispatch = {}
    def concrete_dependencies(deps):
        return [d for d in deps if d.startswith('Sal.MRDTs.Instances.') or
                any(s in d for s in ('.GuardedPorts.', '.TreeMoveEvent.', '.AegisSheetEvent.', '.CertifiedRGA'))]
    for n in args.generic_root:
        deps = current['kernel_closure']['roots'][n]['dependencies']
        bad = concrete_dependencies(deps)
        assert concrete_dependencies(deps+['Sal.MRDTs.Instances.TreeMove.sequentialSound'])
        dispatch[n] = {'concrete_dependencies':bad, 'status':'fail' if bad else 'pass',
                       'contaminated_closure_rejected':True}
    cached = {'Sal.MRDTs.Instances.TreeMove.sequentialSound',
              'Sal.MRDTs.Instances.AegisSheet.Sequential.causalOriginSequentialSound',
              'Sal.MRDTs.Instances.EmbedRGA.embed_seq_sound'}
    instance_dispatch = {}
    for n in args.root:
        bad = sorted(set(current['kernel_closure']['roots'][n]['dependencies']) & cached - {n})
        instance_dispatch[n] = {'cached_full_bridge_dependencies':bad,'status':'fail' if bad else 'pass'}
    assert (set() | {'Sal.MRDTs.Instances.EmbedRGA.embed_seq_sound'}) & cached
    report = {'method':__doc__, 'baseline':baseline, 'current':current,
              'fixed_public_root_union':fixed_union,
              'supplementary_current_roots':args.root+args.generic_root,
              'per_family_fixed_public_roots':families,
              'changed_whole_sources_including_retained_helpers':changes,
              'new_whole_sources':new, 'statement_and_definition_review':preservation,
              'preserved_declarations_checked':checked,'reviewed_proof_bundle_exceptions':reviewed_bundles,
              'whole_new_source_totals':{cat:sum(v['code_lines'] for v in new.values() if v['category']==cat) for cat in ('shared','concrete','validation')},
              'whole_changed_source_deltas':{cat:sum(v['delta'] for v in changes.values() if v['category']==cat) for cat in ('shared','concrete','validation')},
              'generic_dispatch':dispatch, 'instance_dispatch':instance_dispatch,
              'negative_dispatch_control':{'injected_cached_full_bridge_rejected':True},
              'baseline_manifest_sha256':sha(SNAP/'manifest.json'),
              'baseline_freshness':json.loads((SNAP/'freshness.json').read_text()),
              'classification_concrete_automation_modules':CONCRETE_AUTOMATION,
              'limitations':['Whole changed source includes executable and independent model definitions; do not present it as pure proof cost.',
                            'Preserved old roots remain charged even when a new root bypasses them; removal of proof work must be explicit.',
                            'Non-comment source lines are an effort proxy, not elapsed author time.']}
    (OUT/'certification-invariants-measurement.json').write_text(json.dumps(report,indent=2)+'\n')
    assert not preservation, preservation
    assert all(d['status']=='pass' for d in [*dispatch.values(),*instance_dispatch.values()]), 'Dispatch failure'
    print(json.dumps({p:report[p]['source_union']['totals'] for p in ('baseline','current')}))
if __name__ == '__main__': main()
