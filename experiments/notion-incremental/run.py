#!/usr/bin/env python3
"""Fetch unchanged hash-pinned oracle modules, stage named research adapters, run."""
import argparse,hashlib,json,pathlib,shutil,subprocess,tempfile
root=pathlib.Path(__file__).resolve().parent
manifest=json.loads((root.parent/'notion-oracle/sources.json').read_text())
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--cases',type=int,default=100)
p.add_argument('--sizes',default='32,128,512')
p.add_argument('--repeats',type=int,default=5)
p.add_argument('--output',type=pathlib.Path)
p.add_argument('--display-fold-only',action='store_true')
p.add_argument('--heap-comparison',action='store_true')
p.add_argument('--native-binary',type=pathlib.Path)
p.add_argument('--native-fixtures-only',action='store_true')
p.add_argument('--native-controls-only',action='store_true')
a=p.parse_args()
with tempfile.TemporaryDirectory(prefix='sal-notion-incremental-') as d:
 work=pathlib.Path(d);(work/'package.json').write_text('{"type":"module"}\n')
 for f in root.glob('*.mjs'):shutil.copy(f,work/f.name)
 for module in manifest['modules']:
  target=work/module['file'];subprocess.run(['curl','-fsSL',module['url'],'-o',str(target)],check=True)
  if hashlib.sha256(target.read_bytes()).hexdigest()!=module['sha256']:raise SystemExit(f"Source changed: {module['file']}")
 command=['node','--expose-gc',str(work/'benchmark.mjs'),'--cases',str(a.cases),'--sizes',a.sizes,'--repeats',str(a.repeats)]
 if a.native_binary or a.native_fixtures_only:
  command=['node',str(work/'native-harness.mjs'),'--cases',str(a.cases),'--sizes',a.sizes,'--repeats',str(a.repeats)]
  if a.native_binary:command.extend(['--binary',str(a.native_binary.resolve())])
  if a.native_fixtures_only:command.append('--fixtures-only')
  if a.native_controls_only:command.append('--controls-only')
 if a.heap_comparison:
  output=a.output.open('w') if a.output else None
  try:
   for size in a.sizes.split(','):
    for mode in ['insertion','mixed']:
     for repeat in range(a.repeats):
      for engine in ['full-replay','indexed-structure']:
       result=subprocess.run(['node','--expose-gc',str(work/'benchmark.mjs'),'--heap-engine',engine,'--heap-size',size,'--heap-mode',mode],capture_output=True,text=True,check=True)
       for line in result.stdout.splitlines():
        record=json.loads(line);record['repeat']=repeat
        print(json.dumps(record),file=output)
  finally:
   if output:output.close()
  raise SystemExit(0)
 if a.display_fold_only:command.append('--display-fold-only')
 if a.output:
  with a.output.open('w') as f:subprocess.run(command,stdout=f,check=True)
 else:subprocess.run(command,check=True)
