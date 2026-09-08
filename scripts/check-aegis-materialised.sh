#!/usr/bin/env sh
set -eu

if rg -n '\bsorry\b|sorryAx|native_decide|^axiom ' \
    Sal/MRDTs/Instances/AegisSheetMaterialised*.lean; then
  echo 'unproved declaration or native fixture entered a materialised proof module' >&2
  exit 1
fi

lake build Sal.MRDTs.Instances.AegisSheetPortSPOT
audit_log=$(mktemp)
trap 'rm -f "$audit_log"' EXIT HUP INT TERM
lake env lean Sal/MRDTs/Instances/AegisSheetMaterialisedAudit.lean > "$audit_log"
node - "$audit_log" <<'NODE'
const fs = require('fs');
const out = fs.readFileSync(process.argv[2], 'utf8');
const expected = new Set(['joinTarget', 'replayAdequacy', 'observationEquivalence',
  'update_preserves_canon_of_past', 'Issued.fold', 'cross_model', 'converse',
  'verified', 'retirement', 'Represents.applicable_iff', 'retire_applicable_iff',
  'update_represents_of_compact']);
const allowed = new Set(['propext', 'Classical.choice', 'Quot.sound']);
for (const m of out.matchAll(/'Sal\.MRDTs\.Instances\.AegisSheet\.Materialised\.([^']+)' depends on axioms:\s*\[([^\]]*)\]/g)) {
  if (!expected.delete(m[1])) throw new Error(`Unexpected or duplicate axiom check: ${m[1]}`);
  for (const ax of m[2].split(',').map(x => x.trim()).filter(Boolean)) {
    if (!allowed.has(ax)) throw new Error(`${m[1]} uses forbidden axiom ${ax}`);
  }
}
if (expected.size) throw new Error(`Missing axiom checks: ${[...expected]}`);
console.log('12 materialised theorem axiom checks passed; native fixtures isolated.');
NODE
