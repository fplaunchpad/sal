#!/usr/bin/env python3
"""Verify stored trial source hashes and summarize outcomes without promoting failures."""
import collections,hashlib,json,pathlib,sys
p=pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else pathlib.Path(__file__).parent/'results/campaign'
rows=[]
for f in sorted(p.glob('*.json')):
 r=json.loads(f.read_text())
 assert hashlib.sha256((p/r['source']).read_bytes()).hexdigest()==r['source_sha256'],f
 assert (p/r['log']).is_file(),f
 if r['status']=='checked':
  names={x.strip() for a in r['axioms'] for x in a.strip('[]').split(',') if x.strip()}
  assert names <= {'propext','Quot.sound','Classical.choice'},(f,names)
  assert r['returncode']==0 and not r['forbidden_dependencies'],f
 rows.append(r)
print(f'{len(rows)} recorded trials; source hashes and checked-result axiom audits verified.')
print('| Pipeline | Tier | Checked | Solver only | Failed / timed out |')
print('|---|---|---:|---:|---:|')
for tool in sorted({r['tool'] for r in rows}):
 for tier in ['definitions','generic','helpers']:
  rr=[r for r in rows if r['tool']==tool and r['tier']==tier]
  if rr:
   c=collections.Counter(r['status'] for r in rr)
   print(f"| {tool} | {tier} | {c['checked']} | {c['solver_only']} | {len(rr)-c['checked']-c['solver_only']} |")
print('\nChecked cases:')
for case in sorted({r['case'] for r in rows}):
 good=[r['tool']+'/'+r['tier'] for r in rows if r['case']==case and r['status']=='checked']
 if good:print(case+': '+', '.join(good))
