#!/usr/bin/env python3
"""Acquire the hash-pinned public demo, or reproduce its five known bugs offline."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
INPUTS = ROOT / "notion"


def checked_bytes(path, module):
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != module["sha256"]:
        raise ValueError(f"SHA-256 mismatch for {path}: expected {module['sha256']}, got {digest}")
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--download", type=Path, metavar="DIR",
                      help="download and verify the seven modules into DIR, then exit")
    mode.add_argument("--vendor-cache", type=Path, metavar="DIR",
                      help="read modules from DIR without network access (default: vendor/notion)")
    parser.add_argument("--output", type=Path, metavar="FILE",
                        help="save fresh JSONL to a new FILE instead of stdout; never overwrite")
    args = parser.parse_args()
    if args.download and args.output:
        parser.error("--output applies only to a regression run")
    manifest = json.loads((INPUTS / "sources.json").read_text())
    modules = manifest["modules"]
    if args.download:
        args.download.mkdir(parents=True, exist_ok=True)
        for module in modules:
            target = args.download / module["file"]
            if target.exists():
                checked_bytes(target, module)
                print(f"Verified existing {target}", file=sys.stderr)
                continue
            data = subprocess.run(
                ["curl", "--fail", "--silent", "--show-error", "--location",
                 "--max-time", "60", module["url"]],
                check=True, stdout=subprocess.PIPE,
            ).stdout
            digest = hashlib.sha256(data).hexdigest()
            if digest != module["sha256"]:
                raise ValueError(f"Source changed: {module['file']}; expected {module['sha256']}, got {digest}")
            with target.open("xb") as output:
                output.write(data)
            print(f"Downloaded and verified {target}", file=sys.stderr)
        return
    cache = args.vendor_cache or ROOT / "vendor" / "notion"
    # Verify all inputs before executing any downloaded code. No download occurs
    # in this branch, including when a module is absent or has a wrong digest.
    sources = [(module["file"], checked_bytes(cache / module["file"], module))
               for module in modules]
    if args.output and args.output.exists():
        raise FileExistsError(f"Refusing to overwrite {args.output}")
    with tempfile.TemporaryDirectory(prefix="sal-paper1-notion-") as directory:
        work = Path(directory)
        (work / "package.json").write_text('{"type":"module"}\n')
        for name in ("regressions.mjs", "positional-spec.mjs"):
            shutil.copyfile(INPUTS / name, work / name)
        for name, data in sources:
            (work / name).write_bytes(data)
        result = subprocess.run(["node", "regressions.mjs"], cwd=work,
                                check=True, stdout=subprocess.PIPE, text=True)
    records = [json.loads(line) for line in result.stdout.splitlines() if line]
    expected = {
        "reversed-bold-selected-effect-failure": False,
        "bold-control": True,
        "bold-outside-selected-block-failure": False,
        "split-zero-leaves-suffix-sibling-failure": False,
        "merge-into-removed-block-loses-document-failure": False,
        "cyclic-merge-removal-hides-character-failure": False,
    }
    actual = {record["name"]: record["specAgreement"] for record in records}
    if len(records) != 6 or actual != expected:
        raise ValueError(f"Unexpected regression records: {actual}")
    if args.output:
        with args.output.open("x") as output:
            output.write(result.stdout)
    else:
        sys.stdout.write(result.stdout)
    print("Reproduced 5 known demo bugs and 1 passing control (6 records).", file=sys.stderr)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Notion reproduction failed: {error}", file=sys.stderr)
        sys.exit(1)
