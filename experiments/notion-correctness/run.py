#!/usr/bin/env python3
"""Run the correctness campaign offline against hash-verified public-demo sources."""
import argparse, hashlib, json, shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent
ORACLE = ROOT.parent / 'notion-oracle'
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--cache', required=True, type=Path)
p.add_argument('--output', required=True, type=Path, help='new output JSON file')
p.add_argument('--mode', choices=['search', 'replay', 'minimize', 'structural', 'sequential', 'classify', 'regressions'], default='search')
p.add_argument('--seed', type=int, default=17001)
p.add_argument('--trials', type=int, default=60)
p.add_argument('--input', type=Path, help='saved campaign JSON for replay')
a = p.parse_args()
if a.output.exists(): p.error('output already exists')
if a.mode in ['replay','minimize','classify'] and not a.input: p.error(a.mode+' requires --input')
if a.trials < 1: p.error('--trials must be positive')
if not 0 < a.seed < 2**32: p.error('--seed must be a nonzero unsigned 32-bit integer')
manifest = json.loads((ORACLE/'sources.json').read_text())
with tempfile.TemporaryDirectory(prefix='notion-correctness-') as d:
 w = Path(d)
 (w/'package.json').write_text('{"type":"module"}\n')
 for m in manifest['modules']:
  b = (a.cache/m['file']).read_bytes()
  if hashlib.sha256(b).hexdigest() != m['sha256']: raise ValueError('source hash mismatch: '+m['file'])
  (w/m['file']).write_bytes(b)
 for f in ROOT.glob('*.mjs'): shutil.copyfile(f,w/f.name)
 shutil.copyfile(ORACLE/'regressions.mjs',w/'original-regressions.mjs')
 shutil.copyfile(ORACLE/'positional-spec.mjs',w/'positional-spec.mjs')
 if a.input: shutil.copyfile(a.input,w/'input.json')
 # Calibration asserts all three known failures and their passing control.
 subprocess.run(['node','original-regressions.mjs'],cwd=w,check=True,stdout=subprocess.DEVNULL)
 subprocess.run(['node','regressions.mjs'],cwd=w,check=True,stdout=subprocess.DEVNULL)
 subprocess.run(['node','controls.mjs'],cwd=w,check=True,stdout=subprocess.DEVNULL)
 cmd=['node',a.mode+'.mjs'] if a.mode in ['structural','classify','regressions'] else ['node','campaign.mjs',a.mode,str(a.seed),str(a.trials)]
 r=subprocess.run(cmd,cwd=w,check=True,stdout=subprocess.PIPE,text=True)
 result=json.loads(r.stdout)
 if a.mode == 'regressions': result={'mode':'regressions','findings':[result]}
 result['sourceManifest']=manifest
 with a.output.open('x') as out: json.dump(result,out,indent=2);out.write('\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ['findings','failureStates','sourceManifest']},indent=2))
 print('Findings:',len(result['findings']), 'Output:',a.output)
