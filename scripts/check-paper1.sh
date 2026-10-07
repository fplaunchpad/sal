#!/usr/bin/env sh
set -eu

# The ledger checks theorem dependencies against the standard Lean axiom set.
lake build Sal.MRDTs.Paper1.Ledger

if rg -n '\bsorry\b|sorryAx|^axiom\s' Sal/MRDTs/Paper1 --glob '*.lean'; then
  echo 'unproved or axiom-backed paper1 declaration remains' >&2
  exit 1
fi
