#!/bin/sh
set -eu

lake build \
  Sal.ConditionedMRDTs.Metatheory.GC_CompressedDAG \
  Sal.ConditionedMRDTs.Metatheory.Distributed_GC

(
  cd runtime
  node --test test/gc.test.js test/replica.test.js test/gc-pbt.test.js
)

if rg -n '\b(sorry|admit)\b' \
  Sal/ConditionedMRDTs/Metatheory/GC_CompressedDAG.lean \
  Sal/ConditionedMRDTs/Metatheory/Distributed_GC.lean; then
  echo 'unexpected proof placeholder in Priority 6 artifacts' >&2
  exit 1
fi
