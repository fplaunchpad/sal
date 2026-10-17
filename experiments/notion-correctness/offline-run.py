#!/usr/bin/env python3
"""Run persistent-replica experiments using hash-pinned cached demo modules."""
import argparse,hashlib,json,shutil,subprocess,tempfile
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--cache',required=True,type=Path)
p.add_argument('--output',required=True,type=Path)
p.add_argument('--seed',type=int,default=17101)
p.add_argument('--trials',type=int,default=30)
p.add_argument('--steps',type=int,default=150)
p.add_argument('--mode',choices=['mixed','structural','minimize','regression'],default='mixed')
p.add_argument('--input',type=Path)
a=p.parse_args();root=Path(__file__).resolve().parent
if a.output.exists():p.error('output must not exist')
if not 0<a.seed<2**32 or a.trials<1 or a.steps<1:p.error('seed must be nonzero uint32; trials and steps must be positive')
if a.mode=='minimize' and not a.input:p.error('minimize requires --input')
manifest=json.loads((root.parent/'notion-oracle/sources.json').read_text())
with tempfile.TemporaryDirectory(prefix='notion-offline-') as d:
 w=Path(d);(w/'package.json').write_text('{"type":"module"}\n')
 for m in manifest['modules']:
  b=(a.cache/m['file']).read_bytes()
  if hashlib.sha256(b).hexdigest()!=m['sha256']:raise ValueError('hash mismatch '+m['file'])
  (w/m['file']).write_bytes(b)
 for name in ['offline-search.mjs','offline-replay.mjs','offline-regression.mjs','campaign-lib.mjs']:shutil.copyfile(root/name,w/name)
 shutil.copyfile(root.parent/'notion-oracle/positional-spec.mjs',w/'positional-spec.mjs')
 if a.input:shutil.copyfile(a.input,w/'input.json')
 cmd=['node','offline-regression.mjs'] if a.mode=='regression' else ['node','offline-replay.mjs'] if a.mode=='minimize' else ['node','offline-search.mjs',str(a.seed),str(a.trials),str(a.steps),a.mode]
 r=subprocess.run(cmd,cwd=w,check=True,stdout=subprocess.PIPE,text=True)
 result=json.loads(r.stdout);result['sourceManifest']=manifest
 with a.output.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ['findings','sourceManifest']}));print('Findings:',len(result.get('findings',[])),'Output:',a.output)
