#!/usr/bin/env python3
"""Run isolated, bounded Lean trials; retain source, log, timing and proof audit."""
import argparse, functools, hashlib, json, os, pathlib, signal, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parents[2]
HERE=pathlib.Path(__file__).resolve().parent
FIELDS=['merge_comm','init','causal_delta','local_redistribute','shared']
def output(cmd,cwd=ROOT):
    return cached_output(tuple(cmd),str(cwd))
@functools.lru_cache(maxsize=None)
def cached_output(cmd,cwd):
    return subprocess.check_output(cmd,cwd=cwd,text=True).strip()
def trial(tool,case,tier,seconds,out,helper_mode="polymorphic"):
    family,field=case.split('.')
    base=HERE/'lean-auto' if tool.startswith('auto-') else HERE/'lean-smt' if tool=='smt' else ROOT
    env=os.environ.copy()
    rootpath=output(['lake','env','printenv','LEAN_PATH'])
    env['LEAN_PATH']=output(['lake','env','printenv','LEAN_PATH'],base)+':'+rootpath
    solver_seconds=min(20,seconds)
    cmd=[output(['lake','env','which','lean'],base)]
    pre=''
    tac=''
    if tool=='grind': tac='grind only'
    elif tool=='blaster': pre='import Blaster\n'; tac=f'blaster (timeout: {solver_seconds}) (random-seed: 1)'
    elif tool.startswith('auto-'):
        name={'auto-duper':'Duper','auto-z3':'Z3','auto-cvc5':'Cvc5'}[tool]
        pre=(base/f'Preamble{name}.lean').read_text()
        tac='auto'
        cfg=base/'environment.json'
        if cfg.exists(): env.update(json.loads(cfg.read_text()))
        env['PATH']='/tmp/sal-vc-auto-cvc5-dist/cvc5-macOS-arm64-static/bin:'+env['PATH']
    else:
        pre=(base/'Preamble.lean').read_text();tac=f'smt +mono (timeout := some {solver_seconds}) [*]'
        cmd+=['--plugin='+str(base/'.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.dylib')]
    if tool.startswith('auto-'): pre+=f'\nset_option auto.smt.timeout {solver_seconds}\n'
    # Put all imports first, then options/adapter declarations.
    cases=(HERE/'Cases.lean').read_text()
    imports=[]; bodies=[]
    for text in [pre,cases]:
        imports += [l for l in text.splitlines() if l.startswith('import ')]
        bodies.append('\n'.join(l for l in text.splitlines() if not l.startswith('import ')))
    if tier=='helpers': imports += ['import Sal.MRDTs.Paper1.CertifiedRGAVCAlgebra']
    header='\n'.join(dict.fromkeys(imports))+'\n'+'\n'.join(bodies)
    binders='{α : Type} [DecidableEq α]'+(' [Inhabited α] (Γ : Sal.EmbedRGA.OrderedPrefixCode)' if family=='Embedded' else '')
    goal=f'VCAutomation.{case} (α := α)'+(' Γ' if family=='Embedded' else '')
    prefix=f'  unfold VCAutomation.{case} VCAutomation.{field}_goal\n'
    names={'merge_comm':'C E₁ E₂ l a b h₁ h₂ h₃ h₄ h₅ h₆ h₇', 'init':'C E s h₁ h₂ h₃',
           'causal_delta':'C U s B e', 'local_redistribute':'C E₁ E₂ l B t b e', 'shared':'C E₁ E₂ t₀ t₁ t₂ B e'}
    prefix+='  intro '+names[field]+'\n'
    if field not in ['merge_comm','init']: prefix+='  intros\n'
    if family in ['Exact','Efficient']:
        ns='Sal.MRDTs.Paper1.ORSet' if family=='Exact' else 'Sal.MRDTs.Instances.EfficientORSet'
        if field=='merge_comm': prefix+='  clear h₁ h₂ h₃ h₄ h₅ h₆ h₇ C E₁ E₂\n'
        if field=='init': prefix+='  clear h₁ h₂ h₃ C E\n'
        prefix+=f'  dsimp only [{ns}.D]\n'
        if tier!='definitions':
            prefix+='  apply Finset.ext\n  intro p\n'
            prefix+=f'  simp only [{ns}.merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty, Finset.mem_empty]\n'.replace(', Finset.mem_empty','')
            if field in ['merge_comm','init','shared']: prefix+='  clear * - p\n'
        else: prefix+=f'  dsimp only [{ns}.merge]\n'
    elif tier!='definitions':
        prefix+='  dsimp only [Sal.MRDTs.Instances.EmbedRGA.E] at *\n'
    if tier=='helpers':
        hints=json.loads((HERE/'premises.json').read_text())['tiers']['helpers']['additional_theorem_hints']
        hints=[h for h in hints if ('Embedded.' in h)==(family=='Embedded') and (family!='Exact' or '.EfficientORSet.' not in h) and (family!='Efficient' or '.ORSet.' not in h)]
        applications=json.loads((HERE/'premises.json').read_text())['tiers']['helpers']['helper_application']
        if helper_mode=='specialized' and family!='Embedded' and field in ['merge_comm','init','shared']: hints=[]
        prefix+=''.join(f'  have vc_hint{i} := '+(applications[h] if helper_mode=='specialized' else '@'+h)+'\n' for i,h in enumerate(hints))
    source=header+'\n'+(HERE/'Audit.lean').read_text()+f'\nset_option maxHeartbeats 1000000\nset_option maxRecDepth 2048\ntheorem trial {binders} : {goal} := by\n'+prefix+'  all_goals '+tac+'\naudit_vc trial\n'
    name=f'{family}-{field}-{tier}-{tool}'
    path=out/(name+'.lean'); path.write_text(source)
    log=out/(name+'.log')
    start=time.monotonic();timeout=False
    with log.open('w') as f:
        proc=subprocess.Popen(cmd+[str(path)],cwd=base,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        try: rc=proc.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            timeout=True;os.killpg(proc.pid,signal.SIGKILL);rc=proc.wait()
    elapsed=time.monotonic()-start
    data=log.read_text()
    audited='VC_AUDIT_COMPLETE' in data
    ax=[l.split('VC_AXIOMS',1)[1].strip() for l in data.splitlines() if 'VC_AXIOMS' in l]
    deps=[l.split('VC_DEP',1)[1].strip() for l in data.splitlines() if 'VC_DEP' in l]
    banned=json.loads((HERE/'premises.json').read_text())['explicitly_forbidden']
    forbidden=[d for d in deps if d in banned or any(x in d for x in ['mergeVCs','representationJoin','join_at_sizes','causal_replay_eq','local_replay_eq','shared_replay_eq','ORSet.join','ORSet.live_join'])]
    axnames={x.strip() for a in ax for x in a.strip('[]').split(',') if x.strip()}
    unexpected=axnames-{'propext','Quot.sound','Classical.choice'}
    untrusted=bool(unexpected)
    solver_trust=unexpected <= {'sorryAx','Auto.Solver.SMT.autoSMTSorry','autoSMTSorry'}
    status='timeout' if timeout else 'checked' if rc==0 and audited and not untrusted and not forbidden else 'solver_only' if rc==0 and audited and untrusted and solver_trust and not forbidden else 'failed'
    direct=[l.split('VC_DIRECT',1)[1].strip() for l in data.splitlines() if 'VC_DIRECT' in l]
    stage=('timeout' if timeout else 'solver_timeout' if 'Reason: TIMEOUT' in data else 'solver_response' if any(x in data for x in ['Incomplete input','Malformed (prefix of) input']) else 'complete' if status in ['checked','solver_only'] else
      'translation' if any(x in data for x in ['optimizeExpr:', 'translateNonOpaqueType:', 'incorrect number of universe', 'not a forall', 'already declared', 'Auto.LamReif', 'ConstInst.ofExpr', 'is not a `∀`', 'translateApp:', 'translateExpr:']) else
      'reconstruction' if 'reconstruct' in data.lower() else 'search_or_preprocessing')
    row=dict(helper_mode=helper_mode,unexpected_axioms=sorted(unexpected),failure_stage=stage,solver_limit_seconds=solver_seconds,direct_dependencies=direct,tool=tool,case=case,tier=tier,wall_seconds=round(elapsed,3),limit_seconds=seconds,returncode=rc,status=status,axioms=ax,dependencies=deps,forbidden_dependencies=forbidden,source_sha256=hashlib.sha256(source.encode()).hexdigest(),source=path.name,log=log.name)
    (out/(name+'.json')).write_text(json.dumps(row,indent=2)+'\n')
    print(json.dumps({k:row[k] for k in ['tool','case','tier','wall_seconds','status']}),flush=True)
    return row
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--tools',default='grind,blaster');p.add_argument('--families',default='Exact,Efficient');p.add_argument('--fields',default=','.join(FIELDS));p.add_argument('--tiers',default='definitions');p.add_argument('--seconds',type=int,default=30);p.add_argument('--out',default='results/pilot');p.add_argument('--helper-mode',choices=['polymorphic','specialized'],default='polymorphic');a=p.parse_args()
    out=HERE/a.out;out.mkdir(parents=True,exist_ok=True)
    for fam in a.families.split(','):
      for field in a.fields.split(','):
       for tier in a.tiers.split(','):
        for tool in a.tools.split(','): trial(tool,fam+'.'+field,tier,a.seconds,out,a.helper_mode)
