#!/usr/bin/env python3
"""Audit complete required sequential bridge closures for the 23 registered cases.

Nonblank noncomment source ranges are deduplicated, include all declaration kinds
and preceding attribute annotations. The proof/descriptor subtotal additionally
uses explicit classification; the all-concrete column is the conservative guard
against missing proof-only definitions. Per-case closures overlap and are not
summable. VC-overlap is reported rather than subtracted.
"""
import argparse, hashlib, importlib.util, json, subprocess, tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/'results'
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path)
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module); return module
A=load('cert_measure','scripts/measure-paper1-certification-invariants.py')
B,M,V=A.B,A.M,A.B.V
prior=B.category
CONCRETE_STEMS={'EmbeddedOrderedPrimitives','SidedOrderedPrimitives','TransferAegisSheet','TransferLWW','TransferNativeRGA',
 'ConcreteSimplePorts','ConcreteProductPorts','ConcreteBooleanPorts','ConcreteGuardedPorts','IssuedConcretePorts'}
def category(name,d):
    stem=Path(d['file']).stem
    if stem in CONCRETE_STEMS or (stem=='TransferGuardedCommuting' and any('.'+ns+'.' in name for ns in ('Tree','Bounded'))):
        return 'concrete_proof_annotation'
    return prior(name,d)
B.category=category

def hashes():
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (ROOT/'Sal').rglob('*.lean')}
def select(measurement,ids):
    return dict(measurement,cases={key:measurement['cases'][key] for key in ids})
def stats(measurement,ids):
    footprint=M.footprint(select(measurement,ids),ROOT)
    concrete_files=footprint['by_file'].get('concrete_all_declaration_kinds',{})
    whole={f:M.code((ROOT/f).read_text()) for f in concrete_files}
    return dict(proof_and_descriptor_lines=footprint['primary_proof_and_description']['total'],
        all_concrete_source_lines=footprint['totals'].get('concrete_all_declaration_kinds',0),
        conservative_whole_concrete_module_lines=sum(whole.values()), whole_concrete_modules=whole,
        shared_source_lines=footprint['totals'].get('generic',0), by_file=footprint['by_file'])
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=OUT/'seq-bridge-effort.json')
    parser.add_argument('--reuse-kernel',action='store_true',help='Reuse saved kernel log only when the previous full Sal source hashes match.')
    args=parser.parse_args(); OUT.mkdir(exist_ok=True)
    cases=V.CASES
    B.ROOT=ROOT; B.BASE='current-source'
    B.CASES={c['id']:c['required_bridge'] for c in cases if c['required_bridge']}
    B.CASES.update({'vc:'+c['id']:c['vc_roots'] for c in cases})
    roots=sorted({n for ns in B.CASES.values() for n in ns})
    before=hashes()
    if args.reuse_kernel:
        previous=json.loads(args.output.read_text())
        assert previous['import_source_sha256']==before,'Stale saved sequential bridge audit'
        log=(OUT/'seq-bridge-effort-kernel.log').read_text()
    else:
        with tempfile.TemporaryDirectory(prefix='sal-seq-effort-') as tmp:
            path=Path(tmp)/'Audit.lean'
            path.write_text('import Sal.MRDTs.Paper1.Ledger\n'+V.LEAN_AUDIT+'\n'+
                            '\n'.join('audit_production '+n for n in roots)+'\n')
            proc=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,text=True,
                stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (OUT/'seq-bridge-effort-kernel.log').write_text(proc.stdout)
        assert proc.returncode==0,proc.stdout[-5000:]
        assert before==hashes(),'Source changed during sequential bridge audit'
        log=proc.stdout
    measurement=B.measure(log)
    rows={}
    for c in cases:
        name=c['id']
        if not c['required_bridge']:
            rows[name]={'status':'obstructed_no_public_bridge','roots':[],
                'proof_and_descriptor_lines':None,'all_concrete_source_lines':None,
                'shared_source_lines':None,'conservative_whole_concrete_module_lines':None,'vc_overlap_all_concrete_lines':None}; continue
        row=stats(measurement,[name]); row.update(status='checked',roots=c['required_bridge'])
        bridge=measurement['cases'][name]; vc=measurement['cases']['vc:'+name]
        common=set(bridge['dependencies']) & set(vc['dependencies'])
        overlap=dict(bridge,metrics={cat:dict(metric,declarations=[d for d in metric['declarations'] if d['name'] in common])
            for cat,metric in bridge['metrics'].items()})
        overlap_measure=dict(measurement,cases={'overlap':overlap})
        row['vc_overlap_all_concrete_lines']=stats(overlap_measure,['overlap'])['all_concrete_source_lines']
        row['shared_bridge_roots_with']=[o['id'] for o in cases if o['id']!=name and o['required_bridge']==c['required_bridge']]
        rows[name]=row
    bridge_ids=[c['id'] for c in cases if c['required_bridge']]
    report={'schema_version':1,'status':'pass','method':__doc__,'cases':rows,
        'unique_bridge_root_count':len({r for c in cases for r in c['required_bridge']}),
        'deduplicated_bridge_campaign':stats(measurement,bridge_ids),
        'source_sha256':measurement['source_sha256'],
        'import_source_sha256':before,'kernel_closures':measurement,
        'classifier_concrete_stems':sorted(CONCRETE_STEMS),
        'limitations':['Source lines measure footprint, not author time.',
            'Proof/descriptor classification is explicit but may omit unnamed proof-only semantic definitions; use all-concrete as conservative column.',
            'All-concrete includes executable implementations and independent specifications.',
            'Shared cost is full reached source ranges, including preexisting kernel support, not incremental new-library cost.',
            'Per-case rows and VC overlaps are not additive; aliases share bridge roots.']}
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    for name,row in rows.items():
        print(name,row['proof_and_descriptor_lines'],row['all_concrete_source_lines'],row['vc_overlap_all_concrete_lines'])
if __name__=='__main__':main()
