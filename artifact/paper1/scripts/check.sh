#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
python3 scripts/check-manifest.py
lake build Sal.Artifact.Guide
