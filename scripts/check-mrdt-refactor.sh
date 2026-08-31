#!/usr/bin/env sh
set -eu

lake build \
  Sal.MRDTs.Metatheory.ProductionLedger \
  Sal.MRDTs.Metatheory.NegativeLedger \
  Sal.MRDTs.Metatheory.RefactorLedger

# Guard the two representation-mirroring regressions found by the sequential
# specification audit.  The theorem ledgers above check the positive bridges;
# these source checks keep the retired proof-only state shapes from returning.
rg -q -F 'State := Finset α' Sal/MRDTs/Instances/ORSet.lean
rg -q -F '| .remove element _ => state.erase element' \
  Sal/MRDTs/Instances/ORSet.lean
if rg -n '\bSeqState\b|seqLiveTags|seqContains' \
    Sal/MRDTs/Instances/ORSet.lean; then
  echo 'OR-set tagged implementation state re-entered the sequential specification' >&2
  exit 1
fi

rg -q -F 'State := Tree' Sal/MRDTs/Instances/TreeMove.lean
if rg -n '^structure SeqState|^  events : Finset Event' \
    Sal/MRDTs/Instances/TreeMove.lean; then
  echo 'TreeMove event-set mirror re-entered the sequential specification' >&2
  exit 1
fi

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

if rg -n '\bConditionalJoin\b|ofConditionalJoin|\bRGASeqState\b|Instances\.RGA\.spec|Instances\.RGA\.replayAdequate' \
    Sal/MRDTs docs README.md PRIORITIZED_REMAINING_WORK.md; then
  echo 'retired Join or RGA specification terminology remains' >&2
  exit 1
fi

if rg -n '\bmergeL\b|merge_init_slice|sMergeL|eMergeL|qMergeL|bcMergeL|mvrMergeL|prodSig_mergeL' \
    Sal/MRDTs docs README.md PRIORITIZED_REMAINING_WORK.md; then
  echo 'obsolete duplicate MRDT merge interface remains' >&2
  exit 1
fi

if rg -n 'LCA|\blca\b|lca_|_lca|VirtualLca|virtualLca' \
    Sal/MRDTs --glob '*.lean'; then
  echo 'ambiguous LCA terminology remains in the live Lean development' >&2
  exit 1
fi

if rg -n '\bCommonAnc\b|\bIsMCA\b|mcaFinset|commonAnc_reaches_mca|mca_events_cover' \
    Sal/MRDTs --glob '*.lean'; then
  echo 'retired support-set MCA interface remains in the live Lean development' >&2
  exit 1
fi

if awk '/^structure Configuration/{inside=1} /^namespace Configuration/{inside=0} inside' \
    Sal/MRDTs/Framework/Execution.lean | \
    rg -n '^  (N|L|dom_eq|head_coherent)\s*:'; then
  echo 'derived head observations were reintroduced as configuration caches' >&2
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
