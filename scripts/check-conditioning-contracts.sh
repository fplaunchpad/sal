#!/bin/sh
set -eu

# Fail when a known nontrivial issuer-guard chain is no longer represented by
# the public generation-contract catalogue.  This is intentionally a small
# explicit manifest: adding another `*Applicable`/`*Honest` production chain
# requires adding its public contract here as part of the same change.
contract_file="Sal/ConditionedMRDTs/MRDT_Instances/ProductionGenerationContracts.lean"

check_chain() {
  guard="$1"
  bridge="$2"
  package="$3"
  rg -q "Guard := ${guard}" "$contract_file"
  rg -q "$bridge" "$contract_file"
  rg -q "def ${package}" "$contract_file"
}

check_chain bcApplicable bcGenHonest_of_mintHonest boundedCounterGeneration
check_chain qApplicable qHonest_of_applicable queueGeneration
check_chain eApplicable eHonest_of_applicable embedGeneration
check_chain sApplicable sHonest_of_applicable sidedGeneration

rg -q "def boundedCounterSequentialRefinement" "$contract_file"
rg -q "def boundedCounterSafety" "$contract_file"
rg -q "def boundedCounterUnified" "$contract_file"

# Canonical Peritext must remain an explicit Embed-contract instantiation.
rg -q "def peritextEmbedGeneration" "$contract_file"

# Negative designs must not silently acquire a production unified package.
if rg -q "(rehoming|budgetCart|shesha)Unified" "$contract_file"; then
  echo "refuted or gated design promoted to a production unified certificate" >&2
  exit 1
fi

flat_file="Sal/ConditionedMRDTs/MRDT_Instances/FlatUnifiedCertificates.lean"
for package in counter ioc pn orset orsete goset gomap lww fww awpq; do
  rg -q "def ${package}Unified" "$flat_file"
done
rg -q "fwwApplicable" "$flat_file"
rg -q "intentionally absent" "$flat_file"
if rg -q "def (rgaWithTombstones|peritextTombstone)Unified" "$flat_file"; then
  echo "gated flat datatype promoted without its missing certificate" >&2
  exit 1
fi
rg -q "def ewflagUnifiedF" "$flat_file"

mvr_file="Sal/ConditionedMRDTs/MRDT_Instances/MVR/MVR_Unified.lean"
rg -q "def mvrApplicable" "$mvr_file"
rg -q "def MVRMintHistory" "$mvr_file"
rg -q "def mvrGeneration" "$mvr_file"
rg -q "def mvrUnified" "$mvr_file"

pt_file="Sal/ConditionedMRDTs/MRDT_Instances/Peritext_WithTombstones/Peritext_Intent.lean"
rg -q "def ptApplicable" "$pt_file"
rg -q "inductive PtHistoryOK" "$pt_file"
rg -q "def ptHistorySequentialRefinement" "$pt_file"
rg -q "def ptGeneration" "$pt_file"
rg -q "def ptUnified" "$pt_file"

rga_file="Sal/ConditionedMRDTs/MRDT_Instances/RGA_WithTombstones/RGA_Intent.lean"
rg -q "def rgaApplicable" "$rga_file"
rg -q "def rgaHistorySequentialRefinement" "$rga_file"
rg -q "def rgaGeneration" "$rga_file"
rg -q "def rgaUnified" "$rga_file"
