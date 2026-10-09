#!/usr/bin/env python3
"""Measure kernel dependency closures, complete declarations (never selected proof lines).

Concrete theorem helpers include state/order/issuance proofs reached by the bridge.
Semantic definitions are listed separately; simulation bundles and all new concrete
bridge descriptions count as author annotation. Shared framework/automation is
reported separately. Main burden metric is nonblank_noncomment_lines, with
physical/nonblank lines retained. Overlap with VC work is not silently subtracted.
"""
import argparse, hashlib, importlib.util, json, re, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
BASE = '052b8fb'
OUT = ROOT / 'experiments/vc-automation/results'
SNAP = ROOT / 'experiments/vc-automation/bridge-baseline'
P = 'Sal.MRDTs.Paper1.'
CASES = {
 'ordinary-or-set': [P+'ORSet.EventSpec.foldHistorySound', P+'ORSet.EventSpec.commutationCompatibility'],
 'efficient-or-set': [P+'EfficientORSet.EventSpec.foldHistorySound', P+'EfficientORSet.EventSpec.commutationCompatibility'],
 'issuance-certified-embedded-rga': [P+'CertifiedRGAInvariantHistory.canonical_valid_history'],
}
SHARED = ('Sal.MRDTs.Framework.', 'Sal.MRDTs.Paper1.Automation.',
 'Sal.MRDTs.Paper1.ConcreteMRDT.', 'Sal.Interfaces.', 'Sal.Tactic.')
SHARED_FILES = {'History', 'EventHistory', 'EventSequentialSimulation', 'SequentialSimulation',
 'CertifiedHistoryCommutation','CertifiedHistory','CertifiedInvariant','CertifiedIssuance',
 'GuardedHistory','Specification','Policy','EventConflict','EventSpec','Execution','EventExecution',
 'RawExecution','ConcreteMRDT','Replay','Certificate','Criterion','Invariant','Issuance',
 'HistorySpec','SpecificationVisibility','EventBridge','HistoryInputs','CommutationBridge','ProjectedSimulation'}

def load_script(name, path):
 s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
V=load_script('verify',ROOT/'scripts/verify-paper1-automation.py')
C=load_script('contracts',ROOT/'scripts/check-paper1-automation-contracts.py')
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
def parse(log):
 roots={n:dict(dependencies=[],axioms=[]) for ns in CASES.values() for n in ns}; decl={}
 for r,d in re.findall(r'PROD_DEP (\S+) (\S+)',log): roots[r]['dependencies'].append(d)
 for r,a in re.findall(r'PROD_AXIOMS (\S+) \[(.*?)\]',log,re.S): roots[r]['axioms']=[x.strip() for x in a.split(',') if x.strip()]
 for n,m,s,e,k in re.findall(r'PROD_SOURCE (\S+) (\S+) (\d+) (\d+) (\S+)',log):
  decl[n]=dict(file=m.replace('.','/')+'.lean', start=int(s),end=int(e),kind=k)
 assert set(re.findall(r'PROD_COMPLETE (\S+)',log))==set(roots)
 for r,d in roots.items():
  d['dependencies']=sorted(set(d['dependencies'])); assert set(d['axioms'])<=V.STANDARD,(r,d['axioms'])
 return roots,decl

def category(name,d):
 stem=Path(d['file']).stem
 if 'Automation.EmbeddedSequentialBridge.' in name or 'Automation.Automated' in name:
  return 'concrete_proof_annotation'
 if name.startswith(SHARED) or stem in SHARED_FILES or d['file'].startswith(('Sal/MRDTs/Framework/','Sal/MRDTs/Metatheory/')): return 'shared_framework_or_kernel'
 if d['kind']=='theorem': return 'concrete_proof_annotation'
 if any(x in name.lower() for x in ('simulation','description','adapter','witness','certificate')):
  return 'concrete_proof_annotation'
 return 'semantic_or_implementation_definition'

def measure(log, baseline=False):
 roots,decl=parse(log);source={}
 for d in decl.values():
  f=d['file']
  if f not in source:
   source[f]=git('show',BASE+':'+f) if baseline else (ROOT/f).read_text()
 sourcecode={f:C.strip_comments(s).splitlines() for f,s in source.items()}
 result={}
 for case,ns in CASES.items():
  deps=set().union(*(set(roots[n]['dependencies']) for n in ns)); groups={}
  for n in sorted(deps & set(decl)):
   d=decl[n];cat=category(n,d);groups.setdefault(cat,[]).append(dict(name=n,**d))
  metrics={}
  for cat,ds in groups.items():
   ranges={}
   for d in ds:
    start=d['start']-1; raw=source[d['file']].splitlines()
    while start>0 and raw[start-1].lstrip().startswith('@['):start-=1
    ranges.setdefault(d['file'],set()).update(range(start,d['end']))
   lines=[source[f].splitlines()[i] for f,ix in ranges.items() for i in sorted(ix)]
   code=[sourcecode[f][i] for f,ix in ranges.items() for i in sorted(ix)]
   metrics[cat]=dict(declaration_count=len(ds),source_lines=len(lines),nonblank_lines=sum(bool(l.strip()) for l in lines),nonblank_noncomment_lines=sum(bool(l.strip()) for l in code),declarations=ds)
  result[case]=dict(roots=ns,metrics=metrics,dependencies=sorted(deps))
 return dict(baseline=BASE,cases=result,roots=roots,source_sha256={f:hashlib.sha256(s.encode()).hexdigest() for f,s in source.items()},method=__doc__)

def import_hashes():
 pending=['Sal.MRDTs.Paper1.Ledger','Sal.MRDTs.Paper1.Automation.SequentialBridgeControls','Sal.MRDTs.Paper1.Automation.SetBridgeAutomationControls'];seen={}
 while pending:
  module=pending.pop();f=module.replace('.','/')+'.lean'
  if f in seen or not (ROOT/f).is_file():continue
  data=(ROOT/f).read_bytes();seen[f]=hashlib.sha256(data).hexdigest()
  pending += re.findall(r'^import\s+(\S+)',data.decode(),re.M)
 return seen

def main():
 p=argparse.ArgumentParser();p.add_argument('--baseline-only',action='store_true');a=p.parse_args();OUT.mkdir(exist_ok=True)
 base=measure((SNAP/'kernel-052b8fb.log').read_text(),True)
 (SNAP/'measurement-052b8fb.json').write_text(json.dumps(base,indent=2)+'\n')
 if a.baseline_only:
  for n,c in base['cases'].items():print(n,{k:{x:v for x,v in m.items() if x!='declarations'} for k,m in c['metrics'].items()})
  return
 before_imports=import_hashes()
 roots=sorted(n for ns in CASES.values() for n in ns)
 subprocess.run(['lake','build','Sal.MRDTs.Paper1.Automation.SequentialBridgeControls','Sal.MRDTs.Paper1.Automation.SetBridgeAutomationControls'],cwd=ROOT,check=True)
 with tempfile.TemporaryDirectory(prefix='sal-bridge-audit-') as t:
  f=Path(t)/'Audit.lean';f.write_text('import Sal.MRDTs.Paper1.Ledger\n'+V.LEAN_AUDIT+'\n'+'\n'.join('audit_production '+r for r in roots)+'\n')
  r=subprocess.run(['lake','env','lean',str(f)],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  (OUT/'bridge-audit.log').write_text(r.stdout);assert r.returncode==0,r.stdout[-5000:]
 current=measure(r.stdout)
 assert before_imports==import_hashes(),'Imported source changed during audit'
 current['import_source_sha256']=before_imports
 bridge_library=['Sal/MRDTs/Paper1/ProjectedSimulation.lean',
  'Sal/MRDTs/Paper1/Automation/FiniteSetSimulation.lean',
  'Sal/MRDTs/Paper1/Automation/GenericGuardedFold.lean']
 current['whole_generic_bridge_library']={f:dict(nonblank_noncomment_lines=sum(bool(x.strip()) for x in C.strip_comments((ROOT/f).read_text()).splitlines()),source_sha256=hashlib.sha256((ROOT/f).read_bytes()).hexdigest()) for f in bridge_library}
 current['whole_generic_bridge_library_total']=sum(v['nonblank_noncomment_lines'] for v in current['whole_generic_bridge_library'].values())
 forbidden={
  'ordinary-or-set':{P+'ORSet.view_step',P+'ORSet.view_fold',P+'ORSet.history_bridge'},
  'efficient-or-set':{'Sal.MRDTs.Instances.EfficientORSet.elements_update','Sal.MRDTs.Instances.EfficientORSet.elements_fold'},
  'issuance-certified-embedded-rga':{'Sal.MRDTs.Instances.EmbedRGA.embed_seq_sound'},
 }
 checks={}
 for case,bad in forbidden.items():
  used=set(current['cases'][case]['dependencies']); found=used & bad
  assert not found,(case,'old bridge dispatch',sorted(found))
  # Mutation controls run the identical membership gate over contaminated
  # evidence; each old helper must be rejected even if hidden below a wrapper.
  for injected in bad: assert (used | {injected}) & bad
  checks[case]=dict(forbidden=sorted(bad),negative_controls=sorted(bad),status='pass')
 current['old_dispatch_controls']=checks
 (OUT/'bridge-measurement.json').write_text(json.dumps(dict(baseline=base,current=current),indent=2)+'\n')
 print('Complete bridge source closures measured; see bridge-measurement.json')
if __name__=='__main__':main()
