#!/usr/bin/env python3
"""Package immutable trial inputs/logs and audited summary data for publication."""
import collections,hashlib,json,pathlib,tarfile
HERE=pathlib.Path(__file__).resolve().parent
for name,expected in [('campaign',270),('specialized',54)]:
 p=HERE/'results'/name
 rows=[json.loads(f.read_text()) for f in sorted(p.glob('*.json'))]
 assert len(rows)==expected,(name,len(rows))
 keys={(r['tool'],r['case'],r['tier']) for r in rows};assert len(keys)==expected
 expected_cases={f'{f}.{v}' for f in ['Exact','Efficient','Embedded'] for v in ['merge_comm','init','causal_delta','local_redistribute','shared']}
 if name=='specialized':expected_cases={x for x in expected_cases if x.startswith('Embedded.') or x.endswith(('causal_delta','local_redistribute'))}
 expected_tiers=['definitions','generic','helpers'] if name=='campaign' else ['helpers']
 expected_keys={(t,c,l) for t in ['grind','blaster','auto-duper','auto-z3','auto-cvc5','smt'] for c in expected_cases for l in expected_tiers}
 assert keys==expected_keys
 for r in rows:
  source=(p/r['source']).read_bytes();log=(p/r['log']).read_text()
  assert hashlib.sha256(source).hexdigest()==r['source_sha256']
  assert f'VCAutomation.{r["case"]} (α := α)' in source.decode()
  if r['status']=='checked':
   ax={x.strip() for a in r['axioms'] for x in a.strip('[]').split(',') if x.strip()}
   assert ax <= {'propext','Quot.sound','Classical.choice'}
   assert r['returncode']==0 and not r['forbidden_dependencies'] and 'VC_AUDIT_COMPLETE' in log
  r['diagnosis']=( 'whole_process_timeout' if r['status']=='timeout' else
    'complete_checked' if r['status']=='checked' else 'complete_unchecked' if r['status']=='solver_only' else
    'solver_timeout' if 'Reason: TIMEOUT' in log else
    'solver_response' if any(x in log for x in ['Incomplete input','Malformed (prefix of) input']) else
    'translation' if any(x in log for x in ['optimizeExpr:','translateNonOpaqueType:','translateApp:','translateExpr:','Auto.LamReif','ConstInst.ofExpr','incorrect number of universe','is not a `∀`','already declared']) else
    'proof_reconstruction' if 'reconstruct' in log.lower() else 'search_or_preprocessing')
 data={'schema_version':1,'experiment':name,'count':len(rows),'outcomes':dict(collections.Counter(r['status'] for r in rows)),'diagnoses':dict(collections.Counter(r['diagnosis'] for r in rows)),'records':rows}
 (HERE/'results'/f'{name}.json').write_text(json.dumps(data,indent=2)+'\n')
 with tarfile.open(HERE/'results'/f'{name}.tar.gz','w:gz') as tf:
  for f in sorted(p.iterdir()):tf.add(f,arcname=f'{name}/{f.name}')
 print(name,data['outcomes'],data['diagnoses'])
with tarfile.open(HERE/'results/exploratory.tar.gz','w:gz') as tf:
 for name in ['pilot','definitions','normalized','smoke']:
  for f in sorted((HERE/'results'/name).iterdir()):tf.add(f,arcname=f'{name}/{f.name}')
