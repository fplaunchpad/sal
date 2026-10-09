#!/usr/bin/env python3
"""Estimate the earlier direct-five-VC source footprint from a checked snapshot.

Use --baseline-dir PATH for a git-archive snapshot of --baseline, with its lake
packages/toolchain available and `lake build Sal.MRDTs.Paper1.Ledger` completed.
No checkout/build is created automatically. Counts are nonblank, noncomment
source lines in kernel dependency closures, not person-hours. Commuting cases
use specialized old raw VC applications, excluding certificate history fields.
"""
import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
P = 'Sal.MRDTs.Paper1.'
STANDARD = {'propext','Classical.choice','Quot.sound'}
DECL = re.compile(r'\s*(?:@\[[\s\S]*?\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:def|abbrev|theorem|lemma|structure|inductive|instance)\b')
THEOREM = re.compile(r'\s*(?:@\[[\s\S]*?\]\s*)?(?:(?:private|protected)\s+)*(?:theorem|lemma)\b')
DATATYPE_PREFIXES = ('ORSet.', 'EfficientORSet.', 'CertifiedQueueMVR.MVR.',
 'CertifiedRGAVC', 'CertifiedRGASidedVC', 'CertifiedRGACore', 'CertifiedRGARichVC',
 'CertifiedFugueVC', 'CertifiedRGAIssuance.', 'CertifiedRGAScope.', 'LWW.GuardedPort.')
PROOF_DEFS = {'CertifiedRGAVCAlgebra', 'CertifiedRGASidedVCAlgebra',
              'CertifiedRGACoreAlgebra', 'CertifiedFugueVCAlgebra'}
EXCLUDED_NAMES = {'representation','policy','scheme','NativeInsertOnly'}


def uncomment(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        pair=text[i:i+2]
        if pair=='/-': depth+=1;out.extend('  ');i+=2
        elif depth and pair=='-/':depth-=1;out.extend('  ');i+=2
        elif not depth and pair=='--':
            while i<len(text) and text[i]!='\n':out.append(' ');i+=1
        else:out.append(text[i] if not depth or text[i]=='\n' else ' ');i+=1
    return ''.join(out)


LEAN = r'''
open Lean Elab Command in
private def emitSource (env : Environment) (n : Name) : CommandElabM Unit := do
  if let some moduleIdx := env.getModuleIdxFor? n then
    if let some ranges ← findDeclarationRanges? n then
      logInfo m!"MAN_SOURCE {n} {env.header.moduleNames[moduleIdx.toNat]!} {ranges.range.pos.line} {ranges.range.endPos.line}"

open Lean Elab Command in
private def emitManual (label : String) (seeds : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut axioms : NameSet := {}
  for seed in seeds do
    for axiomName in (← liftCoreM <| Lean.collectAxioms seed) do
      axioms := axioms.insert axiomName
  logInfo m!"MAN_AXIOMS {label} {axioms.toList}"
  let mut seen : NameSet := {}
  let mut pending := seeds
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      if let some info := env.find? current then
        if current.toString.startsWith "Sal." || current.toString.startsWith "_private.Sal." then
          logInfo m!"MAN_DEP {label} {current}"
          emitSource env current
        pending := info.getUsedConstantsAsSet.toList ++ pending
  logInfo m!"MAN_COMPLETE {label}"

open Lean Elab Command in
elab "manual_expr " label:str " := " value:term : command => do
  let expression ← liftTermElabM <| Lean.Elab.Term.elabTerm value none
  emitManual label.getString expression.getUsedConstants.toList

open Lean Elab Command in
elab "manual_const " label:str " := " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  emitManual label.getString [root]

open Lean Elab Command in
elab "manual_source " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  emitSource (←getEnv) root
'''


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-dir',type=Path,required=True)
    parser.add_argument('--baseline',default='e89cd6d')
    parser.add_argument('--output',type=Path,default=HERE/'results/manual-effort.json')
    args=parser.parse_args();snapshot=args.baseline_dir.resolve()
    audit=json.loads((HERE/'results/production-audit.json').read_text())
    current=json.loads((HERE/'results/production-effort.json').read_text())
    labels=[c['id'] for c in audit['cases']]
    expressions={}; wrappers={}; raw_roots={}
    def commuting(label,comm,merge,delta,peel,wrapper):
        expressions[label]=f'(ConcreteMRDT.CommutingPort.mergeVCs {comm} {merge} {delta} {peel})'
        wrappers[label]=[P+wrapper]
    simple=[('grow-only-set','AddStore','(α := Nat)','Add'),('add-store','AddStore','(α := Nat)','Add'),
            ('finite-add-store','FinsetStore','(α := Nat)','Finite'),
            ('flat-grow-only-set','FlatGrowOnly','(A := Nat)','Boolean'),
            ('flat-grow-only-map','FlatGrowOnly','(A := Nat × Nat)','Boolean')]
    for label,fam,ty,port in simple:
        n='Instances.'+fam+'.'
        commuting(label,'('+n+'all_comm '+ty+')',n+'mergeLaws',n+'deltaLaws',n+'commutingPeelLaw','ConcreteMRDT.SimplePorts.'+port+'.conditions')
    for label,delta in [('counter','(fun _ : Unit => (1 : Int))'),('increment-only-counter','(fun _ : Instances.FlatCounters.IOCOp => (1 : Int))'),('pn-counter','Instances.FlatCounters.pnDelta')]:
        n='Instances.FlatCounters.'
        commuting(label,'('+n+'all_comm '+delta+')','('+n+'mergeLaws '+delta+')','('+n+'deltaLaws '+delta+')','('+n+'commutingPeelLaw '+delta+')','ConcreteMRDT.SimplePorts.Delta.conditions')
    commuting('lww-register','Instances.LWWRegister.all_comm','LWW.GuardedPort.emptyMergeLaws','Instances.LWWRegister.deltaLaws','Instances.LWWRegister.commutingPeelLaw','LWW.GuardedPort.certificate')
    wrappers['lww-register'].append(P+'LWW.GuardedPort.history')
    for label,fam,comm,merge,delta,peel,port in [
        ('rga','RGA','RGAM_all_comm','RGAM_mergeLaws','RGAM_deltaLaws','RGAM_commutingPeelLaw','RGA.ConcretePort.conditions'),
        ('bounded-counter','BoundedCounter','BC_all_comm','BC_mergeLaws','BC_deltaLaws','BC_commutingPeelLaw','ConcreteMRDT.GuardedPorts.Bounded.conditions'),
        ('tree-move','TreeMove','all_comm','mergeLaws','deltaLaws','commutingPeelLaw','ConcreteMRDT.GuardedPorts.Tree.conditions'),
        ('aegis-sheet','AegisSheet','all_comm','mergeLaws','deltaLaws','commutingPeelLaw','ConcreteMRDT.GuardedPorts.Sheet.conditions')]:
        n='Instances.'+fam+'.';commuting(label,n+comm,n+merge,n+delta,n+peel,port)
    for c in audit['cases']:
        if c['id'] not in expressions:raw_roots[c['id']]=c['vc_roots'][0]
    code='import Sal.MRDTs.Paper1.Ledger\n'+LEAN+'\nopen Sal.MRDTs Sal.MRDTs.Paper1\n'
    for label in labels:
        code+=(f'manual_expr "{label}" := {expressions[label]}\n' if label in expressions else f'manual_const "{label}" := {raw_roots[label]}\n')
    code+='\n'.join('manual_source '+n for n in sorted({n for names in wrappers.values() for n in names}))+'\n'
    print('Extracting checked baseline raw-VC closures for23 named cases',flush=True)
    with tempfile.TemporaryDirectory(prefix='sal-manual-effort-') as tmp:
        path=Path(tmp)/'ManualEffortAudit.lean';path.write_text(code)
        result=subprocess.run(['lake','env','lean',str(path)],cwd=snapshot,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if result.returncode:
        Path('/tmp/sal-manual-effort-failure.log').write_text(result.stdout)
        raise SystemExit(result.stdout[-10000:])
    log=result.stdout
    Path('/tmp/sal-manual-effort-kernel.log').write_text(log)
    assert re.findall(r'MAN_COMPLETE (\S+)',log)==labels,'Missing/duplicate baseline audit'
    rows=re.findall(r'MAN_AXIOMS (\S+) \[(.*?)\]',log,re.S)
    assert [n for n,_ in rows]==labels,'Missing/duplicate baseline axiom audit'
    for n,axioms in rows:assert {a.strip() for a in axioms.split(',') if a.strip()}<=STANDARD,(n,axioms)
    dependencies={n:set() for n in labels}
    for label,name in re.findall(r'MAN_DEP (\S+) (\S+)',log):dependencies[label].add(name)
    for label, names in dependencies.items():
        assert not any(P + 'Automation.' in n for n in names), (label, 'baseline uses new automation')
    locations={}
    for n,module,start,end in re.findall(r'MAN_SOURCE (\S+) (\S+) (\d+) (\d+)',log):
        file=module.replace('.','/')+'.lean'
        if (snapshot/file).exists():locations[n]=dict(file=file,start_line=int(start),end_line=int(end))
    source={};hashes={}
    def read(file):
        if file not in source:
            raw=(snapshot/file).read_text();source[file]=uncomment(raw).splitlines();hashes[file]=hashlib.sha256(raw.encode()).hexdigest()
            before=subprocess.check_output(['git','show',args.baseline+':'+file],cwd=ROOT)
            assert hashlib.sha256(before).hexdigest()==hashes[file],('snapshot differs from baseline',file)
        return source[file]
    def classify(n,file,text):
        theorem=bool(THEOREM.match(text))
        if n == 'Sal.EmbedRGA.unaryCode':return 'datatype_proof_packaging'
        if Path(file).stem=='FugueMaxReplayProof' and n.rsplit('.',1)[-1] in {'project','written','birthsFirst'}:return 'datatype_helper'
        if (file.startswith('Sal/MRDTs/Instances/') or file.startswith('Sal/EmbedRGA/')) and theorem:return 'datatype_helper'
        specific=any(P+p in n for p in DATATYPE_PREFIXES)
        if specific and theorem:return 'manual_datatype_proof'
        if specific and Path(file).stem in PROOF_DEFS and n.rsplit('.',1)[-1] not in EXCLUDED_NAMES:return 'manual_datatype_proof_definition'
        if file.startswith('Sal/') and theorem:return 'shared_framework'
        if Path(file).stem=='GuardedEqualityVC' and n.rsplit('.',1)[-1]=='merge':return 'shared_framework'
        return None
    inventory={};cases={};calls={}
    for label in labels:
        entries=set()
        for name in sorted(dependencies[label]):
            loc=locations.get(name)
            if not loc:continue
            lines=read(loc['file']);start,end=loc['start_line'],loc['end_line'];text='\n'.join(lines[start-1:end])
            if not DECL.match(text):continue
            cat=classify(name,loc['file'],text)
            if not cat:continue
            key=f"{loc['file']}:{start}:{end}"
            if key not in inventory:inventory[key]=dict(**loc,category=cat,constants=[],consumers=[],code_lines=[i for i in range(start,end+1) if lines[i-1].strip() and
                    (cat != 'datatype_proof_packaging' or re.match(r'\s*(?:mono|prefixFree) :=', lines[i-1]))])
            entry=inventory[key];entry['constants'].append(name);entry['consumers'].append(label);entries.add(key)
        wrapper_keys=[]
        for name in wrappers.get(label,[]):
            loc=locations[name];lines=read(loc['file'])
            for i in range(loc['start_line'],loc['end_line']+1):
                if not re.search(r'CommutingPort\.(?:vcReplayConditions|scopedConditions|vcCanonicalConfig|vcJoinAt)',lines[i-1]):continue
                indices=[i];j=i+1
                while j<=loc['end_line'] and lines[j-1].startswith(' ') and lines[j-1].strip() and not re.match(r'\s*(?:compatibility|historySound|history|laws|unique|supportedVersions|canonicalVersions|toVCReplayConditions|have|obtain|exact|refine|·)',lines[j-1]):
                    indices.append(j);j+=1
                key=f"{loc['file']}:{i}:{indices[-1]}"
                calls.setdefault(key,dict(file=loc['file'],code_lines=indices,consumers=[]))['consumers'].append(label);wrapper_keys.append(key)
        def count(cats):return len({(inventory[k]['file'],i) for k in entries if inventory[k]['category'] in cats for i in inventory[k]['code_lines']})
        main=count({'datatype_helper','manual_datatype_proof','manual_datatype_proof_definition','datatype_proof_packaging'})+len({(calls[k]['file'],i) for k in wrapper_keys for i in calls[k]['code_lines']})
        cases[label]=dict(baseline_combined_lines=main,current_combined_lines=current['cases'][label]['author_and_retained_helper_lines'],
            baseline_shared_framework_lines=count({'shared_framework'}),declaration_keys=sorted(entries),wrapper_call_keys=wrapper_keys,
            baseline_raw_expression=expressions.get(label),baseline_raw_root=raw_roots.get(label))
    datatype={(e['file'],i) for e in inventory.values() if e['category']!='shared_framework' for i in e['code_lines']}
    wrapper_lines={(e['file'],i) for e in calls.values() for i in e['code_lines']}
    shared={(e['file'],i) for e in inventory.values() if e['category']=='shared_framework' for i in e['code_lines']}
    report=dict(baseline=args.baseline,method=__doc__,status='pass',named_cases=23,cases=cases,
      unique_campaign=dict(baseline_combined_lines=len(datatype|wrapper_lines),baseline_datatype_proof_lines=len(datatype),baseline_wrapper_call_lines=len(wrapper_lines),baseline_excluded_shared_framework_lines=len(shared),current_combined_lines=sum(current['unique_campaign'][k] for k in ('instance_lines','retained_helper_lines','registration_annotation_lines'))),
      declarations=inventory,wrapper_calls=calls,source_sha256=hashes,
      standard_axioms_by_case={name:[a.strip() for a in axioms.split(',') if a.strip()] for name,axioms in rows},
      baseline_commit=subprocess.check_output(['git','rev-parse',args.baseline],cwd=ROOT,text=True).strip(),
      classification=dict(datatype_theorem_prefixes=list(DATATYPE_PREFIXES),proof_only_definition_modules=sorted(PROOF_DEFS),proof_packaging_fields={'Sal.EmbedRGA.unaryCode':['mono','prefixFree']},excluded_contract_definition_names=sorted(EXCLUDED_NAMES)),
      limitations=['Source footprint estimate, not development time or independent implementation count.','Actual raw-VC closures include complete declaration headers/bodies; implementation and contract definitions, shared framework, and independent sequential bridge fields are excluded.','Named-case rows overlap; only campaign union is additive.','Old commuting callers are measured from actual original call lines, while proof terms specialize their old law-bundle assembler.'],
      current_effort_sha256=hashlib.sha256((HERE/'results/production-effort.json').read_bytes()).hexdigest())
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report['unique_campaign'],indent=2))
    for name,row in cases.items():print(name,row['baseline_combined_lines'],row['current_combined_lines'])


if __name__=='__main__':main()
