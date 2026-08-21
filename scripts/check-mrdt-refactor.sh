#!/usr/bin/env sh
set -eu

lake build Sal.MRDTs.Metatheory.RefactorLedger

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
