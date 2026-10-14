#!/usr/bin/env python3
import json,re,hashlib,importlib.util,subprocess,argparse
from pathlib import Path
parser=argparse.ArgumentParser(description='Current MRDT declaration-footprint measurement')
parser.add_argument('--repo',type=Path,default=Path.cwd())
parser.add_argument('--out',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--reuse-audit',action='store_true',help='Reuse logs only after checking previous measured source hashes')
args=parser.parse_args();ROOT=args.repo.resolve();OUT=args.out.resolve();OUT.mkdir(parents=True,exist_ok=True)
if args.reuse_audit:
 previous=json.loads((OUT/'measurement.json').read_text())
 assert all(hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h for f,h in previous['source_sha256'].items()),'Source changed: rerun without --reuse-audit'
def module(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
V=module('V',ROOT/'scripts/verify-paper1-automation.py'); C=module('C',ROOT/'scripts/check-paper1-automation-contracts.py')
P='Sal.MRDTs.Paper1.';I='Sal.MRDTs.Instances.'
impl={
'grow-only-set':('AddStore.D','AddStore.generation','SimpleEventPorts.setMachine'),
'finite-add-store':('FinsetStore.D','FinsetStore.generation','SimpleEventPorts.finiteMachine'),
'counter':('FlatCounters.Counter','FlatCounters.generation','SimpleEventPorts.deltaMachine'),
'flat-grow-only-set':('FlatGrowOnly.GOSet','FlatGrowOnly.generation','SimpleEventPorts.booleanMachine'),
'flat-grow-only-map':('FlatGrowOnly.GOMap','FlatGrowOnly.generation','SimpleEventPorts.booleanMachine'),
'lww-register':('LWWRegister.D','LWWRegister.issuance','LWW.GuardedPort.language'),
'rga':('RGA.RGAM','RGA.generation','RGA.EventSpec.spec'),
'embed-rga':('EmbedRGA.E','EmbedRGA.generation','@ProductionRGA.embedClientSpec'),
'sided-embed-rga':('SidedEmbedRGA.S','SidedEmbedRGA.generation','@ProductionRGA.sidedClientSpec'),
'peritext-embed-rga':('Peritext.D','EmbedRGA.generation','CertifiedPeritextInvariantCertificate.language'),
'sided-peritext-core':('SidedPeritext.Core','SidedPeritext.generation','CertifiedRGACoreCertificate.language'),
'sided-peritext-rich-core':('SidedPeritext.RichCore','SidedPeritext.richGeneration','CertifiedRGARichCertificate.language'),
'tree-move':('TreeMove.D','TreeMove.generation','TreeMoveEvent.spec'),
'aegis-sheet':('AegisSheet.D','AegisSheet.generation','AegisSheetEvent.spec'),
'efficient-or-set':('EfficientORSet.D','EfficientORSet.issuance','EfficientORSet.EventSpec.spec'),
'mvr':('MVRLive.D','MVRLive.issuance','CertifiedMVRHistory.language'),
'fugue-max':('SidedEmbedRGA.FugueMax.datatype','SidedEmbedRGA.FugueMax.generation','FugueMaxNaturalCertificate.eventSpec'),
'ordinary-or-set-paper-example':('@ORSet.D','@ORSet.issuance','ORSet.EventSpec.spec'),
'anchored-queue-paper-variant':('@AnchoredQueue.publicQueue','@AnchoredQueue.issuance','AnchoredQueue.Public.language'),
'balegas-bounded-counter':('BalegasBoundedCounter.D','BalegasBoundedCounter.generation','BalegasBoundedCounterEvent.spec'),
'enable-wins-flag':('EnableWinsFlag.D','EnableWinsFlag.generation','EnableWinsFlagEvent.spec'),
'disable-wins-flag':('DisableWinsFlag.D','DisableWinsFlag.generation','DisableWinsFlagEvent.spec'),
'notion-core':('NotionCoreMRDT.D','NotionCoreMRDT.issuance','@NotionCoreMRDT.spec')}
# @ on implementation/issuer means Paper1; @ on spec means Instances.
rows={}
for case in V.CASES:
 ident=case['id'];d,g,s=impl[ident]
 prefix=lambda x: P+x[1:] if x.startswith('@') else I+x
 rows[ident]={'implementation':[prefix(d),prefix(g)],'specification':[I+s[1:] if s.startswith('@') else P+s], 'vc':case['vc_roots'], 'bridge':case['required_bridge']+case['endpoints']}
rows['fugue-max']['bridge']=[P+'FugueMaxNaturalCertificate.executions',P+'FugueMaxNaturalCertificate.executionsV']
for ident,vc,bridge in [('balegas-bounded-counter','BalegasBoundedCounterVC.fiveVC','BalegasBoundedCounterEvent.certifiedV'),('enable-wins-flag','NeemFlagVC.certifiedFiveVCFor','EnableWinsFlagEvent.certifiedV'),('disable-wins-flag','NeemFlagVC.certifiedFiveVCFor','DisableWinsFlagEvent.certifiedV')]:
 d,g,s=impl[ident];rows[ident]={'implementation':[I+d,I+g],'specification':[P+s],'vc':[P+vc],'bridge':[P+bridge]}
# One Notion case retains its reference protocol/local-effect evidence and
# charges the structural renderer and executable refinement as additional work.
# The deployed typed driver/codec definitions are counted, without claiming a
# universal codec theorem. The original independent history spec is unchanged.
d,g,s=impl['notion-core']; rows['notion-core']={
 'implementation':[I+d,I+g,I+'NotionCoreStructuralMRDT.D']+
   [I+'NotionCoreRuntimeEngine.'+n for n in ('empty','receive','receiveMany','merge','gap')]+
   [I+'NotionCoreRuntimeAdapter.observeState']+
   [I+'NotionCoreRuntimeMain.'+n for n in ('decodeRequest','execute','encodeReply')]+
   [I+'NotionCoreRuntimeWire.encodeTransaction'],
 'specification':[I+s[1:]],
 'vc':[I+'NotionCoreMRDT.fiveVCs',I+'NotionCoreStructuralMRDT.fiveVCs'],
 'bridge':['Sal.MRDTs.Research.NotionCoreLedger.entry',
   'Sal.MRDTs.Research.NotionCoreStructuralRuntimeLedger.entry']+
   [I+'NotionCoreStructuralMRDT.'+n for n in
     ('renderer','versions_witness','specification_ra','operational_reach','registered_query')]+
   [I+'NotionCoreRuntimeEngine.'+n for n in
     ('empty_refines','gap_refines','receive_refines','receiveMany_refines','merge_refines')]+
   [I+'NotionCoreRuntimeHonestProgress.'+n for n in
     ('receive_honest','receiveMany_honest','merge_honest')]+
   [I+'NotionCoreRuntimeTheorem.'+n for n in
     ('closed_version_query','closed_version_reference','registered_query')]+
   [I+'NotionCoreRuntimeEndToEnd.load_closed_version']}
rows['set-wins-map']={'implementation':[I+'SetWinsMap.D',I+'SetWinsMap.issuance'],'specification':[P+'SetWinsMap.spec'],'vc':[P+'SetWinsMap.fiveVC'],'bridge':[P+'SetWinsMap.executions',P+'SetWinsMap.executionsV']}
rows['remove-wins-set']={'implementation':[I+'RemoveWinsSet.D',P+'RemoveWinsSet.generation'],'specification':[P+'RemoveWinsSet.spec'],'vc':[P+'RemoveWinsSet.fiveVC'],'bridge':[P+'RemoveWinsSet.executions',P+'RemoveWinsSet.executionsV']}
rows['optional-register']={'implementation':[I+'OptionalRegister.D',I+'OptionalRegister.generation'],'specification':[P+'OptionalRegister.spec'],'vc':[P+'OptionalRegister.fiveVC'],'bridge':[P+'OptionalRegister.executions',P+'OptionalRegister.executionsV',P+'OptionalRegister.sourceWellFormed']}
# Current anchored queue language is in AnchoredQueue.Public namespace.
rows['anchored-queue-paper-variant']['specification']=[P+'AnchoredQueue.Public.language']
roots=sorted({n for r in rows.values() for ns in r.values() for n in ns})
(OUT/'roots.json').write_text(json.dumps(rows,indent=2)+'\n')
(OUT/'Audit.lean').write_text('import Sal.MRDTs.Metatheory.RefactorLedger\n'+V.LEAN_AUDIT+'\n'+'\n'.join('audit_production '+r for r in roots)+'\n')
print('Extracting',len(roots),'current roots',flush=True)
if args.reuse_audit and (OUT/'kernel.log').exists():
 r=type('Result',(),{'stdout':(OUT/'kernel.log').read_text(),'returncode':0})()
else:
 r=subprocess.run(['lake','env','lean',str(OUT/'Audit.lean')],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/'kernel.log').write_text(r.stdout)
 if r.returncode:raise SystemExit(r.stdout[-6000:])
# The structural carrier discharges EmptyPastKernels with TransferSimple.assemble
# directly, rather than invoking CommonVerification.verify. Charge its complete
# VC dependency closure; do not invent verifier-application evidence for it.
direct_vc_roots={I+'NotionCoreStructuralMRDT.fiveVCs'}
vc_roots=sorted({n for case in V.CASES for n in case['vc_roots']} |
                (set(rows['notion-core']['vc'])-direct_vc_roots))
(OUT/'VCEvidence.lean').write_text('import Sal.MRDTs.Metatheory.RefactorLedger\n'+V.LEAN_AUDIT+'\n'+'\n'.join('audit_production_vc_evidence '+n for n in vc_roots)+'\n')
if not args.reuse_audit or not (OUT/'vc-evidence.log').exists():
 evidence=subprocess.run(['lake','env','lean',str(OUT/'VCEvidence.lean')],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/'vc-evidence.log').write_text(evidence.stdout)
 if evidence.returncode:raise SystemExit(evidence.stdout[-6000:])
vcdeps={n:{n} for n in vc_roots}
for root,d in re.findall(r'PROD_VC_DEP (\S+) (\S+)',(OUT/'vc-evidence.log').read_text()):vcdeps[root].add(d)
assert set(re.findall(r'PROD_VC_COMPLETE (\S+)',(OUT/'vc-evidence.log').read_text()))==set(vc_roots)
deps={n:set() for n in roots};decl={}
for root,d in re.findall(r'PROD_DEP (\S+) (\S+)',r.stdout):deps[root].add(d)
for n,m,s,e,k in re.findall(r'PROD_SOURCE (\S+) (\S+) (\d+) (\d+) (\S+)',r.stdout):decl[n]={'file':m.replace('.','/')+'.lean','start':int(s),'end':int(e),'kind':k}
assert set(re.findall(r'PROD_COMPLETE (\S+)',r.stdout))==set(roots)
for root,a in re.findall(r'PROD_AXIOMS (\S+) \[(.*?)\]',r.stdout,re.S):assert {x.strip() for x in a.split(',') if x.strip()}<=V.STANDARD,(root,a)
# Explicit concrete files keep datatype bridges in ConcreteMRDT namespaces concrete.
concrete_stems={'SimpleConcretePorts','IssuedConcretePorts','SimpleEventPorts','TreeSheetEventSpec','GuardedLWWPort','RGAConcretePort','ConcreteSimplePorts'}
generic_stems={'ProjectedCriterion','SequentialAbstraction','CertifiedPolicy','CertifiedHistoryBridge','Common','History','EventHistory','EventSequentialSimulation','SequentialSimulation','CertifiedHistoryCommutation','CertifiedHistory','CertifiedInvariant','CertifiedIssuance','GuardedHistory','Specification','Policy','EventConflict','EventSpec','Execution','EventExecution','RawExecution','ConcreteMRDT','Replay','Certificate','Criterion','Invariant','Issuance','HistorySpec','SpecificationVisibility','EventBridge','HistoryInputs','CommutationBridge','ProjectedSimulation','ConcreteFormalism','ConcreteMetadata','ConcreteJoin','ConcreteReplay','ConcreteHistoryBridge','ConcreteVCExecution','RestrictedReplay','GuardedReplay','GuardedOrder','InvariantOrder','InvariantReplay','CertifiedReplay','CertifiedPrefixScope','CertifiedScopeRestriction','CertifiedClosedExecution','SplitPolicy','SplitCertificates','SplitSoundness','GuardedEqualityVC','GuardedConvergence','GuardedProjectionHistory','Soundness','RALinearizability','ExecutionTrace','ConcreteHistoryBridge','ConcreteCommutingVCReplay','GuardedHistory'}
def shared(n,d):
 f=d['file'];stem=Path(f).stem
 # These ledgers package one concrete protocol/refinement, not reusable laws.
 if stem in {'NotionCoreLedger','NotionCoreStructuralRuntimeLedger'}:return False
 if f.startswith(('Sal/MRDTs/Framework/','Sal/MRDTs/Metatheory/','Sal/Interfaces/','Sal/Tactic/')):return True
 if '/Automation/' in f:return not stem.startswith(('Automated','Transfer')) and stem not in {'SimpleInputs','MVRInput','ORSetInputs','FugueCodePrimitives','EmbeddedOrderedPrimitives','SidedOrderedPrimitives'}
 if stem in concrete_stems:return False
 if stem in generic_stems:return True
 if not f.startswith(('Sal/MRDTs/Instances/','Sal/MRDTs/Paper1/')):return True
 return False
theorem_lines={(d['file'],i) for d in decl.values() if d['kind']=='theorem' for i in range(d['start'],d['end']+1)}
source={d['file']:(ROOT/d['file']).read_text() for d in decl.values()};code={f:C.strip_comments(s).splitlines() for f,s in source.items()}
def lines(names,only_def=False,shared_value=False):
 out={}
 for n in names:
  if n not in decl:continue
  d=decl[n]
  if shared(n,d)!=shared_value or (only_def and d['kind']=='theorem'):continue
  start=d['start']-1;raw=source[d['file']].splitlines()
  while start>0 and raw[start-1].lstrip().startswith('@['):start-=1
  for i in range(start,d['end']):
   if i<len(code[d['file']]) and code[d['file']][i].strip() and not (only_def and (d['file'],i+1) in theorem_lines):out.setdefault(d['file'],set()).add(i+1)
 return {(f,i) for f,ns in out.items() for i in ns}
report={};union=set();shared_union=set()
for ident,row in rows.items():
 seen=set();metrics={};ranges={};categories={}
 for role,ns in row.items():
  ds=set().union(*((vcdeps.get(n,deps[n]) if role=='vc' else deps[n]) for n in ns));categories[role]=ds
  raw=lines(ds,role in ('implementation','specification'));exclusive=raw-seen;seen|=exclusive;metrics[role]=len(exclusive)
  ranges[role]=sorted(exclusive)
  shared_union|=lines(ds,shared_value=True)
 union|=seen
 report[ident]={'roots':row,'loc':metrics,'exclusive_code_lines':ranges,'dependencies':{k:sorted(v) for k,v in categories.items()}}
# Consolidate three grow-only carriers in one row using physical-line unions, preserving same priority.
gsetids=['grow-only-set','finite-add-store','flat-grow-only-set']; combined={'roots':{},'loc':{},'exclusive_code_lines':{}};seen=set()
for role in ['implementation','specification','vc','bridge']:
 raw=set().union(*(set(map(tuple,report[c]['exclusive_code_lines'][role])) for c in gsetids));exclusive=raw-seen;seen|=exclusive
 combined['roots'][role]=sum((report[c]['roots'][role] for c in gsetids),[]);combined['loc'][role]=len(exclusive);combined['exclusive_code_lines'][role]=sorted(exclusive)
paper={k:v for k,v in report.items() if k not in gsetids};paper={'grow-only-set-three-carriers':combined,**paper}
result={'method':'Kernel dependencies of explicitly listed current declaration roots; union complete declaration source ranges, exclude blank/comment lines; generated source-range overlaps are attributed to theorem/support roles rather than definition/specification roles; disjoint per-row roles priority implementation definitions then specification definitions then actual CommonVerification.verify application/evidence closure (root declaration packaging included) then remaining bridge/execution closure; shared libraries excluded. Counts are dependency-footprint LOC, not author handwritten proof bodies or person-hours. Cross-row overlap not subtracted.','git_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'configuration_rows':report,'paper_rows':paper,'deduplicated_concrete_total':len(union),'deduplicated_shared_dependency_total':len(shared_union),'shared_code_lines':sorted(shared_union),'source_sha256':{f:hashlib.sha256(s.encode()).hexdigest() for f,s in source.items()},'source_locations':decl}
result['direct_vc_dependency_roots']=sorted(direct_vc_roots)
result['method'] += ' Direct carrier VC assemblies without CommonVerification.verify are explicitly listed and charged their complete kernel dependency closures.'
(OUT/'measurement.json').write_text(json.dumps(result,indent=2)+'\n')
md=['| Configuration | Definition | Spec | VC support | Bridge + execution support |','|---|---:|---:|---:|---:|']
for ident,row in paper.items():md.append('| '+ident+' | '+' | '.join(str(row['loc'][k]) for k in ['implementation','specification','vc','bridge'])+' |')
md+=['','Deduplicated concrete source: '+str(len(union))+' LOC. Shared dependency source: '+str(len(shared_union))+' LOC.']
(OUT/'table.md').write_text('\n'.join(md)+'\n');print('\n'.join(md))
