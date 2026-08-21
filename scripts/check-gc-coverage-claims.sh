#!/bin/sh
set -eu

gc="Sal/ConditionedMRDTs/Metatheory/GC_Safety.lean"
compressed="Sal/ConditionedMRDTs/Metatheory/GC_CompressedDAG.lean"
distributed="Sal/ConditionedMRDTs/Metatheory/Distributed_GC_Refinement.lean"
interaction="Sal/ConditionedMRDTs/MRDT_Instances/Peritext_Sided/PeritextSided_Interaction.lean"
final="Sal/ConditionedMRDTs/MRDT_Instances/Peritext_Sided/PeritextSided_Final.lean"
audit="Sal/ConditionedMRDTs/GC_COVERAGE_AUDIT.md"

# Positive signature witnesses.
rg -q '^theorem gc_safetyV ' "$gc"
rg -q 'hRun : StepsV ' "$gc"
rg -q '^theorem gc_safety_compressed ' "$compressed"
rg -q 'def PayloadTraceSafe ' "$compressed"
rg -q 'hRun : Steps D ' "$compressed"
rg -q 'theorem compressed_isLCA_iff_of_mcaClosed' "$compressed"
rg -q 'mca_closed :' "Sal/ConditionedMRDTs/Metatheory/Distributed_GC.lean"
if rg -q 'common_closed :' "Sal/ConditionedMRDTs/Metatheory/Distributed_GC.lean"; then
  echo "distributed GC regressed to retaining every common ancestor" >&2
  exit 1
fi
rg -q '^theorem distributedConfig_refines_Step3' "$distributed"
rg -q 'Steps D S₀.core' "$distributed"
rg -q '^theorem combinedSteps_refines_Step3 ' "$interaction"
rg -Fq 'Steps (Core Γ) S.semantic.core' "$interaction"
rg -q 'interactionRefines : ' "$final"
rg -q 'combinedSteps_refines_Step3 run' "$final"

# The audit must keep the global compressed-carrier boundary visible and
# resolve the Peritext virtual composition cell to checked declarations.
rg -Fq 'virtual LCA (`Step3V`) | global | root-free compressed commit history' "$audit"
rg -Fq 'virtual LCA (`Step3V`) | distributed physical stores | commit history + state' "$audit"

rg -q 'theorem distributedConfig_refines_Step3V' "$distributed"
rg -q 'theorem combinedStepsV_refines_Step3V' "$interaction"
rg -q 'interactionRefinesV :' "$final"

rg -q 'theorem stepAvailableV_merge_after_repair' "$distributed"
rg -q 'theorem fetchResult_virtualMerge_ready' "$interaction"
rg -q 'theorem HeadOnlyMergeCertificate.related' "$interaction"
rg -q 'theorem MaterializationDelta.headOnlyMergeInstall' "$interaction"
rg -q 'virtualRepairReady :' "$final"
rg -q 'headOnlyVirtualMerge :' "$final"
rg -q 'headOnlyMerge: true' runtime/src/compact-peritext.js
rg -q "kind: 'base'" runtime/src/replica.js
rg -q 'certified GC boundary bootstraps' runtime/test/gc-boundary.test.js
rg -q 'commitGCs > 0' runtime/test/crossepoch-crisscross.test.js

echo "GC coverage claim/signature checks passed"
