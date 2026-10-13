#!/usr/bin/env python3
"""Compare full sequential-bridge closures against a captured WORKTREE, never HEAD.

Charges all concrete proof helpers/descriptions by complete kernel source range.
ConcreteMRDT namespace is not itself a shared-code classification. Semantic
source is reported separately, and full new generic module cost is also charged.
"""
import argparse, hashlib, importlib.util, json, re, subprocess, tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def load(n,p):
 s=importlib.util.spec_from_file_location(n,ROOT/p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
B=load('bridges','scripts/measure-paper1-bridges.py');C=B.C
P='Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.'
B.CASES={f.lower()+'-'+n:[P+f+'.'+n] for f in ('Tree','Sheet') for n in ('originLegal','history','conditions','executions','executionsV')}
B.CASES.update({n.rsplit('.',1)[-1]+'-'+str(i):[n] for i,n in enumerate([
 'Sal.MRDTs.Instances.TreeMove.sequentialSound',
 'Sal.MRDTs.Instances.AegisSheet.Sequential.causalOriginSequentialSound',
 'Sal.MRDTs.Paper1.TreeMoveEvent.legal_prefix',
 'Sal.MRDTs.Paper1.AegisSheetEvent.legal_prefix'])})
B.SHARED=tuple(p for p in B.SHARED if p != 'Sal.MRDTs.Paper1.ConcreteMRDT.')
GENERIC_FILES={'ConcreteReplay','ConcreteVCExecution','ConcreteCommutingVCReplay','ConcreteFormalism','ConcreteMetadata','ConcreteJoin','CommutingAssembly'}
old_category=B.category
def category(n,d):
 if d['file']=='Sal/MRDTs/Paper1/IssuedConcretePorts.lean':return 'concrete_proof_annotation'
 if Path(d['file']).stem in GENERIC_FILES:return 'shared_framework_or_kernel'
 return old_category(n,d)
B.category=category

def preservation(start):
 failures=[]; checked=[]
 scope=json.loads((start/'preservation-scope.json').read_text())['files'] if (start/'preservation-scope.json').exists() else json.loads((start/'manifest.json').read_text())
 for f, original in json.loads((start/'manifest.json').read_text()).items():
  if f not in scope:continue
  if not (start/f).exists():
   path=ROOT/f
   if not path.exists() or hashlib.sha256(path.read_bytes()).hexdigest()!=original['sha256']:failures.append([f,'source','unlisted original file changed'])
   continue
  old=C.declarations((start/f).read_text()); path=ROOT/f;new=C.declarations(path.read_text()) if path.exists() else {}
  for n,b in old.items():
   a=new.get(n)
   if a is None:failures.append([f,n,'deleted declaration']);continue
   if b['header']!=a['header'] or b['variables']!=a['variables']:failures.append([f,n,'header/context changed'])
   if b['kind'] not in ('theorem','lemma') and b['body']!=a['body']:failures.append([f,n,'semantic definition changed'])
  if old:checked.append({'file':f,'declarations':len(old)})
 return {'checked':checked,'failures':failures,'status':'fail' if failures else 'pass'}

def main():
 a=argparse.ArgumentParser();a.add_argument('--snapshot',type=Path,default=ROOT/'experiments/vc-automation/sequential-bridge-baseline');a.add_argument('--baseline-only',action='store_true');args=a.parse_args();start=args.snapshot
 B.BASE='captured-current-worktree';B.ROOT=start
 baseline=json.loads((start/'measurement.json').read_text()) if (start/'measurement.json').exists() else B.measure((start/'kernel.log').read_text());B.ROOT=ROOT
 out=ROOT/'experiments/vc-automation/results';out.mkdir(parents=True,exist_ok=True)
 (out/'sequential-bridge-worktree-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n')
 if args.baseline_only:print('Captured baseline measured');return
 generic_roots=['Sal.MRDTs.Foundation.'+n for n in ('legal_snoc_induction','snoc_fold_fusion','split_guard_prefix')]+['Sal.MRDTs.Paper1.Automation.'+n for n in ('mint_origin_prefix','guarded_replay_witness')]
 roots=sorted([n for ns in B.CASES.values() for n in ns]+generic_roots)
 hashes={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in (ROOT/'Sal').rglob('*.lean')}
 with tempfile.TemporaryDirectory(prefix='sal-seq-bridge-') as t:
  f=Path(t)/'Audit.lean';f.write_text('import Sal.MRDTs.Paper1.Ledger\n'+B.V.LEAN_AUDIT+'\n'+'\n'.join('audit_production '+n for n in roots)+'\n')
  r=subprocess.run(['lake','env','lean',str(f)],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (out/'sequential-bridge-kernel.log').write_text(r.stdout);assert r.returncode==0,r.stdout[-5000:]
 assert hashes=={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in (ROOT/'Sal').rglob('*.lean')},'Source changed during audit'
 B.CASES.update({'generic-'+n.rsplit('.',1)[-1]:[n] for n in generic_roots})
 current=B.measure(r.stdout);contracts=preservation(start)
 libraries={}
 for f in (ROOT/'Sal').rglob('*.lean'):
  rel=str(f.relative_to(ROOT))
  if rel not in json.loads((start/'manifest.json').read_text()) or rel.endswith('/Automation/GenericGuardedFold.lean'):libraries[rel]={'category':'validation_only' if f.stem.endswith('Controls') else 'shared_library','code_lines':sum(bool(x.strip()) for x in C.strip_comments(f.read_text()).splitlines()),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()}
 # Traverse actual kernel dependencies: wrappers cannot hide concrete proof dispatch.
 dispatch={}
 def concrete_dependencies(dependencies):
  return sorted(n for n in dependencies if n.startswith('Sal.MRDTs.Instances.') or any(part in n for part in ('.GuardedPorts.','.TreeMoveEvent.','.AegisSheetEvent.')))
 for name in generic_roots:
  used=current['roots'][name]['dependencies'];found=concrete_dependencies(used)
  assert concrete_dependencies(used+['Sal.MRDTs.Instances.TreeMove.sequentialSound']), 'dispatch mutation was accepted'
  dispatch[name]={'forbidden_concrete_dependencies':found,'status':'fail' if found else 'pass','contaminated_closure_rejected':True}
 def union_cost(measurement, baseline_source):
  ranges={}
  for case in ('tree-history','sheet-history'):
   for d in measurement['cases'][case]['metrics'].get('concrete_proof_annotation',{}).get('declarations',[]):
    filename=d['file']; path=(start/filename) if baseline_source and (start/filename).exists() else ROOT/filename
    raw=path.read_text().splitlines(); first=d['start']-1
    while first>0 and raw[first-1].lstrip().startswith('@['):first-=1
    ranges.setdefault(filename,set()).update(range(first,d['end']))
  total=0
  for filename,indices in ranges.items():
   path=(start/filename) if baseline_source and (start/filename).exists() else ROOT/filename
   lines=C.strip_comments(path.read_text()).splitlines()
   total+=sum(bool(lines[i].strip()) for i in indices)
  return total
 union={'baseline_concrete_history_code_lines':union_cost(baseline,True),'current_concrete_history_code_lines':union_cost(current,False)}
 report={'method':__doc__,'snapshot_manifest_sha256':hashlib.sha256((start/'manifest.json').read_bytes()).hexdigest(),'baseline':baseline,'current':current,'deduplicated_history_union':union,'preservation':contracts,'whole_new_shared_modules':libraries,'whole_new_shared_module_code_lines':sum(x['code_lines'] for x in libraries.values() if x['category']=='shared_library'),'old_completed_dispatch_controls':dispatch}
 (out/'sequential-bridge-measurement.json').write_text(json.dumps(report,indent=2)+'\n')
 assert not contracts['failures'],contracts['failures']
 assert all(x['status']=='pass' for x in dispatch.values()),dispatch
 print('Sequential bridge full closures, worktree contracts, and dispatch controls passed')
if __name__=='__main__':main()
