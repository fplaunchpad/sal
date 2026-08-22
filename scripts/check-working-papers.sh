#!/usr/bin/env sh
set -eu

if rg -n 'Sal/ConditionedMRDTs|UnifiedVerifiedMRDT|ConditionedMRDTSig' \
    docs/working-papers.tex docs/framework-paper/main.tex \
    docs/collaborative-editing-paper/main.tex; then
  echo 'retired framework name remains in a working-paper source' >&2
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
