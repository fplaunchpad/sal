#!/usr/bin/env python3
"""Preserve baseline theorem headers/contexts and semantic definition bodies.

Proof bodies may change; only the three known simulation certificates may
change non-theorem bodies. New Lean files are checked by kernel/axiom audit.
This source check is complementary to kernel checking, not definitional equality.
"""
import importlib.util,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
s=importlib.util.spec_from_file_location('contracts',ROOT/'scripts/check-paper1-automation-contracts.py');C=importlib.util.module_from_spec(s);s.loader.exec_module(C)
BASE='052b8fb'
PROOFS={'Sal.MRDTs.Paper1.ORSet.simulation','Sal.MRDTs.Paper1.ORSet.EventSpec.simulation','Sal.MRDTs.Paper1.EfficientORSet.EventSpec.simulation'}
def reason(name,before,after,current=None):
 if after is None:return 'deleted declaration'
 if before['header']!=after['header']:return 'changed declaration header'
 if before['variables']!=after['variables']:return 'changed variable context'
 if before['body']!=after['body'] and before['kind'] not in ('theorem','lemma'):
  if name not in PROOFS:return 'changed semantic definition'
  if not C.bridge_simulation_data(name,before,after,current or {}):return 'changed simulation relation or projection/generator wiring'
 return None

def controls():
 # Same checker must reject a weaker premise, altered initial/spec/update data,
 # deleted contract, and modified variable/instance context. A proof-only edit passes.
 ds=C.declarations('namespace N\nvariable {α : Type}\ndef spec : Nat := 0\ntheorem bridge (h : False) : True := by trivial\nend N\n')
 for field,value in [('header','theorem bridge : True'),('variables',()),('body','def spec : Nat := 1')]:
  name='N.spec' if field=='body' else 'N.bridge';a=dict(ds[name]);a[field]=value
  assert reason(name,ds[name],a),(field,'mutation accepted')
 assert reason('N.bridge',ds['N.bridge'],None)
 a=dict(ds['N.bridge']);a['body']='theorem bridge (h : False) : True := True.intro'
 assert reason('N.bridge',ds['N.bridge'],a) is None
 # Exercise the same source gate on real baseline and current descriptions.
 for name in PROOFS:
  f={'Sal.MRDTs.Paper1.ORSet.simulation':'ORSetVerified',
     'Sal.MRDTs.Paper1.ORSet.EventSpec.simulation':'ORSetEventSpec',
     'Sal.MRDTs.Paper1.EfficientORSet.EventSpec.simulation':'EfficientORSetEventSpec'}[name]
  path='Sal/MRDTs/Paper1/'+f+'.lean'
  before=C.declarations(C.git('show',BASE+':'+path))[name]
  current=C.declarations((ROOT/path).read_text());after=current[name]
  assert C.bridge_simulation_data(name,before,after,current)
  altered=dict(after);altered['body']=altered['body'].replace('derive_projected_simulation','derive_other_simulation')
  assert not C.bridge_simulation_data(name,before,altered,current)
  descriptor=name.rsplit('.',1)[0]+'.projectionDescription'
  poisoned={**current,descriptor:{**current[descriptor],'body':current[descriptor]['body'].replace('project := '+C.BRIDGE_SIMULATIONS[name],'project := fun _ => ∅')}}
  assert not C.bridge_simulation_data(name,before,after,poisoned)
 return ['mutated projection map','mutated simulation generator','weakened premise','altered semantic definition','deleted declaration','altered variable context','proof-only positive control']

def main():
 baseline=set(C.git('ls-tree','-r','--name-only',BASE,'--','Sal').splitlines())
 changed=C.git('diff','--no-renames','--name-only',BASE,'--','Sal/**/*.lean').splitlines()
 failures=[];checked=[]
 for f in changed:
  if f not in baseline:continue
  old=C.declarations(C.git('show',BASE+':'+f));new=C.declarations((ROOT/f).read_text()) if (ROOT/f).exists() else {}
  for n,b in old.items():
   why=reason(n,b,new.get(n),new)
   if why:failures.append(dict(file=f,name=n,reason=why))
  checked.append(dict(file=f,declarations=len(old)))
 report=dict(baseline=BASE,checked=checked,negative_controls=controls(),failures=failures,status='pass' if not failures else 'fail')
 out=ROOT/'experiments/vc-automation/results/bridge-contracts.json';out.parent.mkdir(exist_ok=True);out.write_text(json.dumps(report,indent=2)+'\n')
 assert not failures,failures
 print('Bridge contracts preserved; premise/spec/definition negative controls passed.')
if __name__=='__main__':main()
