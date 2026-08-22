#!/usr/bin/env sh
set -eu

sources='docs/paper-preamble.tex docs/framework-paper/main.tex docs/collaborative-editing-paper/main.tex docs/README.md'

if rg -n 'Sal/ConditionedMRDTs|UnifiedVerifiedMRDT|ConditionedMRDTSig|GuardedStep3|MintCertifiedReach3|\bStep3V?\b|RGA_Rehoming|Shesha|BudgetCart|working-papers\.tex' \
    $sources; then
  echo 'retired framework name remains in a working-paper source' >&2
  exit 1
fi

if rg -ni 'KC Sivaramakrishnan|kc@kcsrk|PACMPL|Sal_paper|fplaunchpad' $sources; then
  echo 'non-anonymous or private-repository metadata remains in a paper source' >&2
  exit 1
fi

paper_lean_log="${TMPDIR:-/tmp}/sal-paper-ledger.log"
if ! lake build Sal.MRDTs.Metatheory.PaperLedger >"$paper_lean_log" 2>&1; then
  cat "$paper_lean_log"
  exit 1
fi

(
  cd docs/framework-paper
  tectonic main.tex
)

(
  cd docs/collaborative-editing-paper
  tectonic main.tex
)

test -s docs/framework-paper/main.pdf
test -s docs/collaborative-editing-paper/main.pdf

for pdf in docs/framework-paper/main.pdf docs/collaborative-editing-paper/main.pdf; do
  if pdftotext "$pdf" - | rg -ni 'KC Sivaramakrishnan|kc@kcsrk|PACMPL|Sal_paper|fplaunchpad'; then
    echo "non-anonymous or private-repository metadata remains in $pdf" >&2
    exit 1
  fi
done
