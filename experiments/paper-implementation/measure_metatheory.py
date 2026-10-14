#!/usr/bin/env python3
"""Count selected generic metatheory dependencies using Lean declaration ranges."""
from pathlib import Path
import argparse,importlib.util,json,re,subprocess
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,default=Path.cwd())
parser.add_argument('--out',type=Path,default=Path('/private/tmp'))
parser.add_argument('--reuse-log',action='store_true',help='Reprocess the existing audit log without invoking Lean')
args=parser.parse_args()
root=args.repo.resolve();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
def load(name,f):
 s=importlib.util.spec_from_file_location(name,root/f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
V=load('audit','scripts/verify-paper1-automation.py')
C=load('contracts','scripts/check-paper1-automation-contracts.py')
roots=[
'Sal.MRDTs.Paper1.ConcreteMRDT.Raw.representationJoin_of_vcs',
'Sal.MRDTs.Paper1.ConcreteMRDT.ScopedVCConditions.executionsV',
'Sal.MRDTs.Paper1.ConcreteMRDT.VCConditions.executionsV',
'Sal.MRDTs.Paper1.ConcreteMRDT.replay_equal',
'Sal.MRDTs.Paper1.CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV',
'Sal.MRDTs.Paper1.PaperPresentation.uniform_versionsRA_of_paperOrder_witness',
'Sal.MRDTs.Paper1.InvariantReplay.convergence_on',
'Sal.MRDTs.Paper1.SplitPolicy.Concrete.ScopedVCConditions.executionsV',
'Sal.MRDTs.Paper1.Automation.CommonVerification.verify',
'Sal.MRDTs.Paper1.event_certified_of_fiveVCs_execution']
f=(out/'sal-metatheory-count.lean');f.write_text('import Sal.MRDTs.Paper1.Ledger\nimport Sal.MRDTs.Paper1.SplitSoundness\nimport Sal.MRDTs.Paper1.Automation.CommonVerification\n'+V.LEAN_AUDIT+'\n'+'\n'.join('audit_production '+r for r in roots))
if args.reuse_log:
 from types import SimpleNamespace
 r=SimpleNamespace(stdout=(out/'sal-metatheory-count.log').read_text())
else:
 r=subprocess.run(['lake','env','lean',str(f)],cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (out/'sal-metatheory-count.log').write_text(r.stdout)
 if r.returncode: print(r.stdout[-4000:]);raise SystemExit(r.returncode)
assert set(re.findall(r'PROD_COMPLETE (\S+)',r.stdout))==set(roots)
assert all(set(x.strip() for x in a.split(',') if x.strip())<=V.STANDARD for a in re.findall(r'PROD_AXIOMS \S+ \[(.*?)\]',r.stdout,re.S))
items={}
for n,m,s,e,k in re.findall(r'PROD_SOURCE (\S+) (\S+) (\d+) (\d+) (\S+)',r.stdout):
 p=m.replace('.','/')+'.lean'
 if not p.startswith('Sal/'):continue
 items[n]={'file':p,'start':int(s),'end':int(e),'kind':k}
ranges={}
for n,d in items.items():
 p=d['file'];group='automation' if '/Automation/' in p else 'datatype' if '/Instances/' in p else 'generic_metatheory' if '/Paper1/' in p or '/Metatheory/' in p else 'shared_framework_interfaces'
 key=(group,d['kind']); ranges.setdefault(key,{}).setdefault(p,set()).update(range(d['start']-1,d['end']))
# Generated recursors/projections may reuse enclosing theorem source ranges.
# Assign any overlap to theorem-source lines, never charge it again as definitions.
for (group,kind),files in ranges.items():
 if kind=='definition':
  for p,ids in files.items(): ids.difference_update(ranges.get((group,'theorem'),{}).get(p,set()))
sourcecode={p:C.strip_comments((root/p).read_text()).splitlines() for files in ranges.values() for p in files}
metrics={}
for (group,kind),files in ranges.items():
 lines=sum(sum(bool(sourcecode[p][i].strip()) for i in ids) for p,ids in files.items())
 metrics[group+'.'+kind]={'nonblank_noncomment_lines':lines,'files':len(files),'declarations':sum(1 for d in items.values() if d['file'] in files and d['kind']==kind),'file_counts':{p:sum(bool(sourcecode[p][i].strip()) for i in ids) for p,ids in files.items()}}
report={'repo_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'roots':roots,'method':'Union of Lean-reported declaration source ranges in transitive kernel dependency closure of listed roots; count nonblank lines after repository nested-comment stripper; theorem kind includes complete statement and proof, definition kind includes structures, definitions, generated recursors/projections; shared automation and framework separately. Generated declaration ranges are deduplicated; overlaps between theorem and definition ranges are assigned to theorem source. Not whole-repo LOC.', 'metrics':metrics,'declarations':items,'axioms':re.findall(r'PROD_AXIOMS (\S+) \[(.*?)\]',r.stdout,re.S)}
(out/'sal-metatheory-count.json').write_text(json.dumps(report,indent=2))
print(json.dumps({k:{x:v for x,v in m.items() if x!='file_counts'} for k,m in metrics.items()},indent=2))
