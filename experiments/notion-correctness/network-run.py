#!/usr/bin/env python3
"""Offline persistent-session correctness search of hash-pinned demo sources."""
import argparse, hashlib, json, shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent
ORACLE = ROOT.parent / 'notion-oracle'
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--cache', required=True, type=Path)
p.add_argument('--output', required=True, type=Path)
p.add_argument('--seed', type=int, default=27001)
p.add_argument('--trials', type=int, default=100)
p.add_argument('--steps', type=int, default=40)
p.add_argument('--input', type=Path)
p.add_argument('--diagnose', action='store_true')
a=p.parse_args()
if a.output.exists(): p.error('output already exists')
if not 0<a.seed<2**32 or min(a.trials,a.steps)<1: p.error('invalid seed, trials or steps')
manifest=json.loads((ORACLE/'sources.json').read_text())
with tempfile.TemporaryDirectory(prefix='notion-network-') as d:
 w=Path(d);(w/'package.json').write_text('{"type":"module"}\n')
 for m in manifest['modules']:
  b=(a.cache/m['file']).read_bytes()
  if hashlib.sha256(b).hexdigest()!=m['sha256']: raise ValueError('source hash mismatch: '+m['file'])
  (w/m['file']).write_bytes(b)
 for f in ROOT.glob('*.mjs'): shutil.copyfile(f,w/f.name)
 shutil.copyfile(ORACLE/'positional-spec.mjs',w/'positional-spec.mjs')
 shutil.copyfile(ORACLE/'regressions.mjs',w/'original-regressions.mjs')
 for control in ['controls.mjs','regressions.mjs','original-regressions.mjs','network-controls.mjs']:
  subprocess.run(['node',control],cwd=w,check=True,stdout=subprocess.DEVNULL)
 cmd=['node','network-search.mjs',str(a.seed),str(a.trials),str(a.steps)]
 if a.input: shutil.copyfile(a.input,w/'input.json');cmd.append('replay')
 if a.diagnose:
  if not a.input: p.error('--diagnose requires --input')
  cmd=['node','network-diagnose.mjs']
 result=json.loads(subprocess.run(cmd,cwd=w,check=True,text=True,stdout=subprocess.PIPE).stdout)
 result['sourceManifest']=manifest
 with a.output.open('x') as out: json.dump(result,out,indent=2);out.write('\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ['traces','findings','sourceManifest']},indent=2))
 print('Findings:',len(result['findings']),'Output:',a.output)
