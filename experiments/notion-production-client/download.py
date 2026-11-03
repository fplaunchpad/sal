#!/usr/bin/env python3
"""Download only manifest-listed public assets and verify every byte."""
import argparse
import hashlib
import json
from pathlib import Path
from urllib.request import urlopen

parser = argparse.ArgumentParser()
parser.add_argument("--cache", type=Path, required=True)
args = parser.parse_args()
manifest = json.loads(Path(__file__).with_name("sources.json").read_text())
args.cache.mkdir(parents=True, exist_ok=True)
for asset in manifest["assets"]:
    path = args.cache / asset["file"]
    data = path.read_bytes() if path.exists() else None
    if data is None:
        with urlopen(asset["url"], timeout=40) as response:
            data = response.read(asset["bytes"] + 1)
    if len(data) != asset["bytes"] or hashlib.sha256(data).hexdigest() != asset["sha256"]:
        raise SystemExit(f"Source mismatch: {asset['url']}; refusing this version")
    if not path.exists():
        path.write_bytes(data)
print(f"Verified {len(manifest['assets'])} production assets in {args.cache}")
