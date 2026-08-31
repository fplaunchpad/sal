#!/usr/bin/env sh
set -eu

sources='docs/paper-preamble.tex docs/framework-paper/main.tex docs/collaborative-editing-paper/main.tex docs/formal-reference/main.tex docs/formal-reference/claim-ledger.md docs/README.md'

sh scripts/check-formal-reference-order.sh

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

if ! pdftotext -layout docs/formal-reference/main.pdf - | \
    rg -q 'RDT[[:space:]]+Merge theorem[[:space:]]+Issuance policy'; then
  echo 'formal-reference PDF does not contain the current RDT-first table' >&2
  exit 1
fi

for pdf in docs/framework-paper/main.pdf docs/collaborative-editing-paper/main.pdf docs/formal-reference/main.pdf; do
  if pdftotext "$pdf" - | rg -ni 'KC Sivaramakrishnan|kc@kcsrk|PACMPL|Sal_paper|fplaunchpad'; then
    echo "non-anonymous or private-repository metadata remains in $pdf" >&2
    exit 1
  fi
done
