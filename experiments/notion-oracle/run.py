#!/usr/bin/env python3
"""Run discovery probes against the pinned public Notion demo modules."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'sources.json').read_text())
with tempfile.TemporaryDirectory(prefix='sal-notion-oracle-') as directory:
    work = Path(directory)
    (work / 'package.json').write_text('{"type":"module"}\n')
    shutil.copy(root / 'traces.mjs', work / 'traces.mjs')
    for module in manifest['modules']:
        target = work / module['file']
        subprocess.run(['curl', '-fsSL', module['url'], '-o', str(target)], check=True)
        if hashlib.sha256(target.read_bytes()).hexdigest() != module['sha256']:
            raise SystemExit(f"Source changed: {module['file']}; review before updating the snapshot")
    subprocess.run(['node', str(work / 'traces.mjs')], check=True)
