#!/usr/bin/env sh
set -eu

doc='docs/formal-reference/main.tex'

# Certificates precede collection; concrete profiles follow both frameworks.
node --input-type=module -e '
import { readFileSync } from "node:fs";
import assert from "node:assert/strict";
const text = readFileSync(process.argv[1], "utf8");
const labels = ["sec:certificates", "sec:history-gc", "sec:state-gc", "sec:instances"];
const positions = labels.map(label => text.indexOf("\\label{" + label + "}"));
assert(positions.every((p, i) => p >= 0 && (i === 0 || positions[i - 1] < p)),
  "Certificates, history collection, state collection, and profiles must occur in that order");
assert(!text.includes("\\subsection{Per-datatype collection profiles}"),
  "Collection profiles belong with their datatype contracts");
for (const label of ["fig:local-redistribute", "fig:redistribute"]) {
  const p = text.indexOf("\\label{" + label + "}");
  assert(p >= 0 && p < positions[0], "Merge diagrams must remain beside the main-text laws");
}
' "$doc"

check_symbol() {
  symbol="$1"
  introduction="$2"

  occurrences=$(rg -n -F "$symbol" "$doc" || true)
  if [ -z "$occurrences" ]; then
    echo "formal-reference order check: missing symbol: $symbol" >&2
    exit 1
  fi

  introduction_hit=$(rg -n -F "$introduction" "$doc" || true)
  if [ -z "$introduction_hit" ]; then
    echo "formal-reference order check: missing introduction for: $symbol" >&2
    exit 1
  fi

  first_line=$(printf '%s\n' "$occurrences" | sed -n '1s/:.*//p')
  last_line=$(printf '%s\n' "$occurrences" | sed -n '$s/:.*//p')
  introduction_line=$(printf '%s\n' "$introduction_hit" | sed -n '1s/:.*//p')

  if [ "$first_line" -ne "$introduction_line" ]; then
    echo "formal-reference order check: $symbol is used at line $first_line before its introduction at line $introduction_line" >&2
    exit 1
  fi
  if [ "$last_line" -le "$introduction_line" ]; then
    echo "formal-reference order check: $symbol is introduced at line $introduction_line but never used later" >&2
    exit 1
  fi
}

check_symbol '\lean{UpdateSig}' 'Lean calls this derived structure \lean{UpdateSig}'
check_symbol 'C.\mathsf{events}' 'C.\mathsf{events}&\equiv'
check_symbol 'ReplayContext' '\mathsf{ReplayContext}(D)='
check_symbol 'TimestampUnique' '\mathsf{TimestampUnique}(L)\Longleftrightarrow'
check_symbol 'SameReplicaTotal' '\mathsf{SameReplicaTotal}(L,\vis)\Longleftrightarrow'
check_symbol 'R_C' 'Write $R_C=\mathsf{replayContext}(C)$'
check_symbol '\mathsf{distinct}' '\mathsf{distinct}(a,b)\Longleftrightarrow'
check_symbol 'NoncommCovered' '\mathsf{NoncommCovered}(D,P)\Longleftrightarrow'
check_symbol '\mathsf{Acyclic}' '\mathsf{Acyclic}(Q)\Longleftrightarrow'
check_symbol 'RcAcyclic' '\mathsf{RcAcyclic}(D,P)\Longleftrightarrow'
check_symbol 'CondCommLift' '\mathsf{CondCommLift}(D,P)\Longleftrightarrow'
check_symbol 'ReplayLaws' '\mathsf{ReplayLaws}(D,P)\Longleftrightarrow'
check_symbol '\loOn^{\ne}' 'a\;\loOn^{\ne}_{R,E}\;b'
check_symbol 'CanonicalConfig' '$\mathsf{CanonicalConfig}(C)$ consists of:'
check_symbol 'JoinOn' '\mathsf{JoinOn}(D,P,G)\Longleftrightarrow'
check_symbol 'JoinCoreLaws' '\mathsf{JoinCoreLaws}(D)=\langle'
check_symbol 'FeasibleDeltaLaws' 'The canonical delta component, \lean{FeasibleDeltaLaws}, contains'
check_symbol 'CausalDeltaLaw' '\mathsf{CausalDeltaLaw}(D)\Longleftrightarrow'
check_symbol 'CanonicalJoinLaws' '\mathsf{CanonicalJoinLaws}(D)=\langle'
check_symbol '\lean{MergeLaws}' 'The universal merge bundle \lean{MergeLaws} contains'
check_symbol '\lean{DeltaLaws}' 'The bundle \lean{DeltaLaws} contains'
check_symbol 'CommutingPeelLaw' 'The auxiliary \lean{CommutingPeelLaw} states'
check_symbol 'JoinProof.ofArbitraryStateLaws' 'The adapter \lean{JoinProof.ofArbitraryStateLaws} first constructs'
check_symbol '\loOn_{' 'e_1\;\loOn_{R,E}\;e_2\Longleftrightarrow'
check_symbol 'IsSpecLinearizable' '$\mathsf{IsSpecLinearizable}(D,P,\mathit{Spec},\mathsf{Rel},C)$ means'
check_symbol 'I.\mathsf{CanIssue}' 'I.\mathsf{CanIssue}:\Event(O)\to\State\to\mathsf{Prop}'
check_symbol 'IssuedStep' '$\mathsf{IssuedStep}(D,I,C,'
check_symbol 'MintHonest' 'A separate condition, $\mathsf{MintHonest}$'
check_symbol 'MintCertifiedReach}' 'Certified reachability $\mathsf{MintCertifiedReach}(D,I,C)$'
check_symbol 'MintCertifiedReachV' '\lean{MintCertifiedReachV D V I C} is'
check_symbol 'IssuanceEstablishes' '\mathsf{IssuanceEstablishes}(D,I,G)\Longleftrightarrow'
check_symbol 'canonicalVirtualMergeBase' '$\mathsf{canonicalVirtualMergeBase}(D)$.'
check_symbol 'CertifiedExecution' 'Let $\mathsf{CertifiedExecution}(D,I,C)$ mean'
check_symbol 'VerifiedMRDT' '\mathsf{VerifiedMRDT}(D)='
check_symbol 'StateGCCertificate' '\lean{StateGCCertificate}.  The generic'
check_symbol 'StateGCProtocol' 'The more general \lean{StateGCProtocol}'
check_symbol 'EvidenceComplete' '\mathsf{EvidenceComplete}(P,A,R,r_s,L)\Longleftrightarrow'
check_symbol 'IsGCARel' '\mathsf{IsGCARel}(R_V,v_1,v_2,v_T)\Longleftrightarrow'
check_symbol 'CompressedReaches' '\mathsf{CompressedReaches}_{P,K}'
check_symbol 'RuntimeSteps' 'Let $\mathsf{RuntimeSteps}$ be'
check_symbol 'CoreSteps' 'let $\mathsf{CoreSteps}$ be'
check_symbol 'SemanticSteps' 'Write $\mathsf{SemanticSteps}_V$ for'
check_symbol 'CombinedSteps' '$\mathsf{CombinedSteps}$ for the list-labelled closure'

# The sufficient laws use the absorber introduced by the linearization relation.
linearization_line=$(rg -n -F '\subsection{Resolve-conflict relation and set-relative linearization}' "$doc" | cut -d: -f1)
absorber_line=$(rg -n -F '\emph{absorber}' "$doc" | head -1 | cut -d: -f1)
laws_line=$(rg -n -F '\subsection{Sufficient replay laws and convergence}' "$doc" | cut -d: -f1)
if [ -z "$linearization_line" ] || [ -z "$absorber_line" ] || [ -z "$laws_line" ] ||
   [ "$linearization_line" -ge "$absorber_line" ] || [ "$absorber_line" -ge "$laws_line" ]; then
  echo 'formal-reference order check: define linearization and its absorber before the sufficient laws' >&2
  exit 1
fi

if rg -n 'RcNonComm|rc\\_non\\_comm' "$doc"; then
  echo 'formal-reference check: concrete noncommutation returned as the definition of semantic rc' >&2
  exit 1
fi

if rg -n 'HeadOnlyMergeCapability' "$doc"; then
  echo 'formal-reference order check: unused head-only state-GC interface returned to the main narrative' >&2
  exit 1
fi

if rg -n -F '\mathsf{CanIssue}\Longrightarrow\mathsf{MintHonest}' "$doc"; then
  echo 'formal-reference check: local issuance is not by itself mint honesty' >&2
  exit 1
fi
