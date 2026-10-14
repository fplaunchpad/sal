#!/usr/bin/env sh
set -eu

# Isolated research check. The production catalogue and ledger are unchanged.
lake build \
  Sal.MRDTs.Instances.NotionCoreStructuralMRDT \
  Sal.MRDTs.Instances.NotionCoreStructuralDisplayTree \
  Sal.MRDTs.Instances.NotionCoreStructuralIssuanceBoundary \
  Sal.MRDTs.Instances.NotionCoreIncrementalMRDT \
  Sal.MRDTs.Instances.NotionCoreIncrementalCounterexample

# Fetches hash-pinned oracle sources; needs network access.
result=$(mktemp -t notion-incremental-check.XXXXXX)
trap 'rm -f "$result"' EXIT HUP INT TERM
python3 experiments/notion-incremental/run.py --cases 10 --sizes 16 --repeats 1 --output "$result"
