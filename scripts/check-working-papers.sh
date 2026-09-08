#!/usr/bin/env sh
set -eu

sources='docs/paper-preamble.tex docs/framework-paper/main.tex docs/collaborative-editing-paper/main.tex docs/formal-reference/main.tex docs/formal-reference/claim-ledger.md docs/README.md'

sh scripts/check-formal-reference-order.sh
node scripts/check-formal-reference-profiles.mjs
node --test scripts/test-formal-reference-profiles.mjs

# Every datatype profile must expose the four public-contract components.
# This checks presentation structure, not semantic equivalence to Lean.
node <<'NODE'
const fs = require('node:fs');
const tex = fs.readFileSync('docs/formal-reference/main.tex', 'utf8');
const section = tex.split('\\subsection{Formal instance profiles}')[1]
  ?.split('\\subsection{Proof routes and evidence status}')[0];
if (!section) throw new Error('Missing instance-profile section');
const labels = ['Datatype $D$.', 'Resolve-conflict relation $rc$.',
  'Issuance.', 'Sequential specification.'];
for (const profile of section.split('\\paragraph{').slice(1)) {
  let previous = -1;
  for (const label of labels) {
    const position = profile.indexOf('\\emph{' + label + '}');
    if (position <= previous) {
      throw new Error(profile.split('}')[0] + ': missing or misplaced ' + label);
    }
    previous = position;
  }
}
if (section.includes('packedWrite')) {
  throw new Error('Use the explicitly defined write key in instance profiles');
}
NODE

if rg -n 'Sal/ConditionedMRDTs|UnifiedVerifiedMRDT|ConditionedMRDTSig|GuardedStep3|MintCertifiedReach3|\bStep3V?\b|RGA_Rehoming|Shesha|BudgetCart|working-papers\.tex' \
    $sources; then
  echo 'retired framework name remains in a working-paper source' >&2
  exit 1
fi

if rg -n 'ConditionalJoin|ofConditionalJoin|Instances\.RGA\.spec|RGASeqState' \
    $sources; then
  echo 'retired Join or RGA specification terminology remains in a working-paper source' >&2
  exit 1
fi

rg -q -F '\lean{Instances.RGA.listSpec}' docs/collaborative-editing-paper/main.tex
rg -q -F '\lean{Instances.RGA.birthGraveMachine}' docs/collaborative-editing-paper/main.tex

if rg -ni 'KC Sivaramakrishnan|kc@kcsrk|PACMPL|Sal_paper|fplaunchpad' $sources; then
  echo 'non-anonymous or private-repository metadata remains in a paper source' >&2
  exit 1
fi

paper_lean_log="${TMPDIR:-/tmp}/sal-paper-ledger.log"
if ! lake build Sal.MRDTs.Metatheory.PaperLedger >"$paper_lean_log" 2>&1; then
  cat "$paper_lean_log"
  exit 1
fi

formal_reference_lean_log="/tmp/sal-formal-reference-ledger.log"
if ! lake build Sal.MRDTs.Metatheory.FormalReferenceLedger \
    >"$formal_reference_lean_log" 2>&1; then
  cat "$formal_reference_lean_log"
  exit 1
fi

node scripts/check-formal-reference-citations.mjs
node --test scripts/test-formal-reference-citations.mjs

build_paper() {
  paper_dir="$1"
  paper_name="$2"
  build_log="${TMPDIR:-/tmp}/sal-${paper_name}-tectonic.log"
  tex="$paper_dir/main.tex"
  pdf="$paper_dir/main.pdf"

  # Tectonic's macOS network backend can panic while returning status 0.
  # Accept an attempt only when both its status and diagnostics are clean.
  if tectonic -C "$tex" >"$build_log" 2>&1 &&
      ! rg -q 'panicked at|thread .* panicked|^error:' "$build_log"; then
    :
  elif tectonic "$tex" >"$build_log" 2>&1 &&
      ! rg -q 'panicked at|thread .* panicked|^error:' "$build_log"; then
    :
  elif tectonic -C "$tex" >"$build_log" 2>&1 &&
      ! rg -q 'panicked at|thread .* panicked|^error:' "$build_log"; then
    :
  else
    cat "$build_log"
    exit 1
  fi

  if [ ! -s "$pdf" ] || [ ! "$pdf" -nt "$tex" ]; then
    echo "paper build did not refresh $pdf" >&2
    exit 1
  fi
}

build_paper docs/framework-paper framework-paper
build_paper docs/collaborative-editing-paper collaborative-editing-paper
build_paper docs/formal-reference formal-reference

test -s docs/framework-paper/main.pdf
test -s docs/collaborative-editing-paper/main.pdf
test -s docs/formal-reference/main.pdf

formal_reference_text="${TMPDIR:-/tmp}/sal-formal-reference.txt"
pdftotext -layout docs/formal-reference/main.pdf "$formal_reference_text"
# The former summary table was folded into per-datatype formal profiles.
# Check the current presentation and semantic-rc criterion, not the retired
# table heading.
for required_instance_text in \
    'Formal instance profiles' \
    'NoncommCovered' \
    'LWW register.' \
    'Multi-value register.' \
    'Grow-only stores.' \
    'Counters.' \
    'Bounded counter.' \
    'observed-remove set.' \
    'RGA.' \
    'TreeMove.' \
    'AegisSheet.' \
    'EmbedRGA and Peritext.' \
    'SidedEmbedRGA and SidedPeritext.' \
    'Queue.' \
    'FugueMax.' \
    'Proof routes and evidence status'; do
  if ! rg -q -F "$required_instance_text" "$formal_reference_text"; then
    echo "formal-reference PDF is missing current instance/replay material: $required_instance_text" >&2
    exit 1
  fi
done

for required_gc_text in \
    'Datatype-state collection.' \
    'RGA.' \
    'The rich package has an operational collector.' \
    'observed-remove set.'; do
  if ! rg -q -F "$required_gc_text" "$formal_reference_text"; then
    echo "formal-reference PDF is missing GC profile: $required_gc_text" >&2
    exit 1
  fi
done

for pdf in docs/framework-paper/main.pdf docs/collaborative-editing-paper/main.pdf docs/formal-reference/main.pdf; do
  if pdftotext "$pdf" - | rg -ni 'KC Sivaramakrishnan|kc@kcsrk|PACMPL|Sal_paper|fplaunchpad'; then
    echo "non-anonymous or private-repository metadata remains in $pdf" >&2
    exit 1
  fi
done
