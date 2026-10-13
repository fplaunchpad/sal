#!/usr/bin/env python3
"""Worktree-baseline invariant projection audit: complete source ranges, all kinds charged.

Concrete burden includes defs, invariant/projection/spec descriptors, annotations and
proof helpers; generic cost is reported separately. Existing semantic source is
preserved, with individually named proof descriptor exceptions recorded explicitly.
"""
import argparse, hashlib, importlib.util, json, subprocess, tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
SNAP=ROOT/'experiments/vc-automation/invariant-projection-baseline'
def load(n,p):
 s=importlib.util.spec_from_file_location(n,ROOT/p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
S=load('seq','scripts/measure-paper1-sequential-bridges.py');B=S.B;C=B.C
PROOF_ONLY_PREFIXES=('Sal.MRDTs.Instances.TreeMove.sortingSpec', 'Sal.MRDTs.Instances.TreeMove.sortingStateProjection', 'Sal.MRDTs.Instances.TreeMove.stateProjection', 'Sal.MRDTs.Instances.TreeMove.stateRel', 'Sal.MRDTs.Instances.AegisSheet.Sequential.ProjectionInvariant', 'Sal.MRDTs.Instances.AegisSheet.Sequential.materializeProjection', 'Sal.MRDTs.Instances.AegisSheet.Sequential.CausalHistoryFacts', 'Sal.MRDTs.Instances.AegisSheet.Sequential.HistoryFacts', 'Sal.MRDTs.Instances.AegisSheet.Sequential.ObservationInvariant', 'Sal.MRDTs.Instances.AegisSheet.Sequential.SeenValid', 'Sal.MRDTs.Instances.AegisSheet.Sequential.CellAxesKnown', 'Sal.MRDTs.Instances.AegisSheet.Sequential.inplaceStateRel', 'Sal.MRDTs.Instances.AegisSheet.Sequential.materializedStateRel', 'Sal.MRDTs.Instances.AegisSheet.GC.StateValid', 'Sal.MRDTs.Instances.AegisSheet.GC.TimestampUnique', 'Sal.MRDTs.Paper1.ConcreteMRDT.CanonicalUnique', 'Sal.MRDTs.Instances.AegisSheet.Sequential.CoveredWitnessed', 'Sal.MRDTs.Instances.TreeMove.TreeSafe', 'Sal.MRDTs.Paper1.GuardedReplay.Laws', 'Sal.MRDTs.Paper1.RestrictedLaws')
def proof_only(n):return any(n==p or n.startswith(p+".") for p in PROOF_ONLY_PREFIXES)
prior_category=B.category
def projection_category(n,d):
 if Path(d['file']).stem=='GuardedProjectionHistory':return 'shared_framework_or_kernel'
 return prior_category(n,d)
B.category=projection_category

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def code(raw):return sum(bool(l.strip()) for l in C.strip_comments(raw).splitlines())
def footprint(measurement,base):
 ranges={};proof_ranges={};excluded={}
 for r in measurement['cases'].values():
  for cat,metric in r['metrics'].items():
   for d in metric['declarations']:
    f=d['file'];path=base/f
    if not path.exists():path=ROOT/f
    raw=path.read_text().splitlines();first=d['start']-1
    while first>0 and raw[first-1].lstrip().startswith('@['):first-=1
    group='generic' if cat=='shared_framework_or_kernel' else 'concrete_all_declaration_kinds'
    ranges.setdefault(group,{}).setdefault(f,set()).update(range(first,d['end']))
    if group!='generic':
     if cat=='concrete_proof_annotation' or proof_only(d['name']):proof_ranges.setdefault(f,set()).update(range(first,d['end']))
     else:excluded[d['name']]={'file':f,'kind':d['kind'],'reason':'existing executable, independent model, or public semantic guard definition'}
 result={}
 for group,fs in ranges.items():
  result[group]={}
  for f,ix in fs.items():
   p=base/f
   if not p.exists():p=ROOT/f
   raw=C.strip_comments(p.read_text()).splitlines()
   result[group][f]=sum(bool(raw[i].strip()) for i in ix)
 proof_cost={}
 for f,ix in proof_ranges.items():
  p=base/f
  if not p.exists():p=ROOT/f
  raw=C.strip_comments(p.read_text()).splitlines();proof_cost[f]=sum(bool(raw[i].strip()) for i in ix)
 return {'by_file':result,'totals':{k:sum(v.values()) for k,v in result.items()},'primary_proof_and_description':{'by_file':proof_cost,'total':sum(proof_cost.values()),'excluded_semantic_declarations':excluded,'explicit_proof_only_prefixes':PROOF_ONLY_PREFIXES}}

def main():
 a=argparse.ArgumentParser();a.add_argument('--generic-root',action='append',default=['Sal.MRDTs.GuardedStateProjection.'+n for n in ('run_facts','run_project','query_agrees','restrict','admits','witness')]+['Sal.MRDTs.Paper1.MachineProjection.toGuarded']);a.add_argument('--instance-root',action='append',default=['Sal.MRDTs.Instances.TreeMove.stateProjection','Sal.MRDTs.Instances.TreeMove.sortingStateProjection','Sal.MRDTs.Instances.AegisSheet.Sequential.materializeProjection']);a.add_argument('--proof-descriptor-exception',action='append',default=[]);args=a.parse_args()
 args.generic_root=list(dict.fromkeys(args.generic_root));args.instance_root=list(dict.fromkeys(args.instance_root))
 B.CASES=json.loads((SNAP/'cases.json').read_text());B.BASE='captured-current-worktree'
 baseline=json.loads((SNAP/'measurement.json').read_text())
 B.CASES.update({'generic-'+n:[n] for n in args.generic_root});B.CASES.update({'instance-'+n:[n] for n in args.instance_root})
 roots=[n for ns in B.CASES.values() for n in ns]
 before={str(p.relative_to(ROOT)):sha(p) for p in (ROOT/'Sal').rglob('*.lean')}
 with tempfile.TemporaryDirectory(prefix='sal-projection-audit-') as t:
  f=Path(t)/'Audit.lean';f.write_text('import Sal.MRDTs.Paper1.Ledger\n'+B.V.LEAN_AUDIT+'\n'+'\n'.join('audit_production '+n for n in roots)+'\n')
  r=subprocess.run(['lake','env','lean',str(f)],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 out=ROOT/'experiments/vc-automation/results';out.mkdir(exist_ok=True);(out/'invariant-projection-kernel.log').write_text(r.stdout)
 assert r.returncode==0,r.stdout[-5000:]
 assert before=={str(p.relative_to(ROOT)):sha(p) for p in (ROOT/'Sal').rglob('*.lean')},'Source changed during audit'
 current=B.measure(r.stdout)
 manifest=json.loads((SNAP/'manifest.json').read_text());preservation=[];failures=[]
 scope=json.loads((SNAP/'preservation-scope.json').read_text())
 for f,h in manifest.items():
  if f in scope['excluded_unrelated_untracked_sources']:continue
  p=ROOT/f;old=SNAP/f
  if not old.exists():
   if not p.exists() or sha(p)!=h:failures.append([f,'uncaptured source changed'])
   continue
  olddecl=C.declarations(old.read_text());new=C.declarations(p.read_text()) if p.exists() else {}
  for n,b in olddecl.items():
   v=new.get(n)
   if not v:failures.append([f,n,'deleted']);continue
   if b['header']!=v['header'] or b['variables']!=v['variables']:failures.append([f,n,'header/context changed'])
   if b['kind'] not in ('theorem','lemma') and b['body']!=v['body'] and n not in args.proof_descriptor_exception:failures.append([f,n,'semantic body changed'])
  preservation.append({'file':f,'declarations':len(olddecl)})
 changed_source={}
 for f,h in before.items():
  if f in manifest and h != manifest[f]:
   old=SNAP/f
   if not old.exists():old=Path('/tmp/sal-projection-start')/f
   changed_source[f]={'before_code_lines':code(old.read_text()),'current_code_lines':code((ROOT/f).read_text()),'delta_code_lines':code((ROOT/f).read_text())-code(old.read_text()),'current_sha256':h,'baseline_sha256':manifest[f]}
 libraries={}
 for f,h in before.items():
  if f not in manifest:
   p=ROOT/f;libraries[f]={'code_lines':code(p.read_text()),'sha256':h,'category':'validation' if p.stem.endswith('Controls') else 'generic' if '/Framework/' in f or '/Automation/' in f or p.stem=='GuardedProjectionHistory' else 'concrete'}
 def forbidden_concrete(ds):
  return [d for d in ds if d.startswith('Sal.MRDTs.Instances.') or any(k in d for k in ('.GuardedPorts.','.TreeMoveEvent.','.AegisSheetEvent.','.ORSet.EventSpec.'))]
 generic_dispatch={}
 for n in args.generic_root:
  deps=current['roots'][n]['dependencies'];bad=forbidden_concrete(deps)
  assert forbidden_concrete(deps+['Sal.MRDTs.Instances.TreeMove.sequentialSound']), 'contaminated generic closure accepted'
  generic_dispatch[n]={'forbidden_transitive_dependencies':bad,'contaminated_closure_rejected':True,'status':'fail' if bad else 'pass'}
 forbidden={'TreeMove.sequentialSound','AegisSheet.Sequential.causalOriginSequentialSound','ORSet.view_fold','ORSet.history_bridge'}
 instance_dispatch={}
 for case in ('tree-history','sheet-history'):
  deps=current['cases'][case]['dependencies']
  bad=[d for d in deps if any(d.endswith(k) for k in forbidden)]
  instance_dispatch[case]={'cached_full_bridge_dependencies':bad,'status':'fail' if bad else 'pass'}
 for n in args.instance_root:
  bad=[d for d in current['roots'][n]['dependencies'] if any(d.endswith(k) for k in forbidden)]
  instance_dispatch[n]={'cached_full_bridge_dependencies':bad,'status':'fail' if bad else 'pass'}
 report={'method':__doc__,'baseline':baseline,'current':current,'baseline_full_union':footprint(baseline,SNAP),'current_full_union':footprint(current,ROOT),'changed_whole_sources_including_retained_helpers':changed_source,'new_whole_modules':libraries,'new_whole_module_totals':{k:sum(v['code_lines'] for v in libraries.values() if v['category']==k) for k in ('generic','concrete','validation')},'preservation':{'checked':preservation,'failures':failures,'explicit_proof_descriptor_exceptions':args.proof_descriptor_exception,'scope':scope},'generic_transitive_dispatch':generic_dispatch,'instance_transitive_dispatch':instance_dispatch,'negative_dispatch_control':{'injected_cached_bridge':'Sal.MRDTs.Instances.TreeMove.sequentialSound','rejected':any('Sal.MRDTs.Instances.TreeMove.sequentialSound'.endswith(k) for k in forbidden)},'snapshot_manifest_sha256':sha(SNAP/'manifest.json')}
 (out/'invariant-projection-measurement.json').write_text(json.dumps(report,indent=2)+'\n')
 assert not failures,failures
 assert all(x['status']=='pass' for x in [*generic_dispatch.values(),*instance_dispatch.values()])
 print(json.dumps({'primary_proof_and_description':{phase:report[phase+'_full_union']['primary_proof_and_description']['total'] for phase in ('baseline','current')},'all_concrete_source':{phase:report[phase+'_full_union']['totals'] for phase in ('baseline','current')},'new_modules':report['new_whole_module_totals']}))
if __name__=='__main__':main()
