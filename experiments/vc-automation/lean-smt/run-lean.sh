#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
exec lake env lean --plugin=.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.dylib "$@"
