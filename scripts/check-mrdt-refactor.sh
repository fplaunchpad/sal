#!/usr/bin/env sh
set -eu

lake build \
  Sal.MRDTs.Metatheory.ProductionLedger \
  Sal.MRDTs.Metatheory.NegativeLedger \
  Sal.MRDTs.Metatheory.RefactorLedger
npm test --prefix runtime
npm run validate --prefix benchmarks

if rg -n 'replayVerified|FMSig|fmGeneration|Instances\.MVR|Instances\.Queue' \
    Sal/MRDTs/Metatheory/ProductionLedger.lean; then
  echo 'incomplete or negative evidence entered the production registry' >&2
  exit 1
fi

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

if git ls-files Sal/CRDTs | rg -q .; then
  echo 'unexpected top-level CRDT source remains tracked' >&2
  exit 1
fi
