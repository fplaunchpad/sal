#!/usr/bin/env sh
set -eu

lake build Sal.MRDTs.Metatheory.RefactorLedger
npm test --prefix runtime

if rg -n 'Sal\.ConditionedMRDTs|LegacyBridge' \
    Sal/MRDTs/Framework Sal/MRDTs/Metatheory Sal/MRDTs/Instances Sal/MRDTs/GC; then
  echo 'obsolete conditioned-framework dependency remains' >&2
  exit 1
fi

if rg -n '\bsorry\b|sorryAx' \
    Sal/MRDTs/Framework Sal/MRDTs/Metatheory Sal/MRDTs/Instances Sal/MRDTs/GC; then
  echo 'unproved production theorem remains' >&2
  exit 1
fi

if [ -e Sal/ConditionedMRDTs ] || [ -e Sal/MRDTs/RGA_Embed ]; then
  echo 'historical MRDT source tree remains in the refactored checkout' >&2
  exit 1
fi

if git ls-files | rg -q '^(Sal/ConditionedMRDTs|Sal/MRDTs/RGA_Embed)/'; then
  echo 'historical MRDT source remains tracked' >&2
  exit 1
fi

if git ls-files Sal/CRDTs | rg -v -q \
    '^Sal/CRDTs/Metatheory/(Assoc_CounterModel|Convergence_CounterModel|JoinLemma_Of_CD|Linearization_Basics|Merge_Linearization_Set|RA_Lin_Of_Join|RA_Linearizability)\.lean$'; then
  echo 'standalone historical CRDT artifact remains tracked' >&2
  exit 1
fi
