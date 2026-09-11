import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';

// Structural regression guard, not a proof that the equations express the
// intended contract. Citation resolution and human semantic review are separate.
export function checkProfiles(tex) {
  assert.ok(!tex.includes('\\paragraph{Tagged observed-remove set.}'),
    'Retired tagged OR-set must not return to the datatype catalogue');
  const section = tex.split('\\subsection{Formal instance profiles}')[1]
    ?.split('\\subsection{Proof routes and evidence status}')[0];
  assert.ok(section, 'Missing instance-profile section');
  const profiles = section.split('\\emph{Datatype $D$.}').slice(1);
  assert.ok(profiles.length > 0, 'No datatype definitions');
  for (const [index, profile] of profiles.entries()) {
    const parts = profile.split('\\emph{Sequential specification.}');
    assert.equal(parts.length, 2, `Profile ${index + 1}: missing or duplicate sequential specification`);
    const spec = parts[1];
    for (const [name, pattern] of [
      ['initial state', /q_0/],
      ['operation step', /\\mathsf\{step\}/],
      ['legality', /\\mathsf\{Legal\}/],
      ['query', /\\mathsf\{query\}_\{\\rm seq\}/],
      ['representation relation', /\\mathsf\{(?:Rel|listRel)\}/],
    ]) {
      assert.match(spec, pattern, `Profile ${index + 1}: missing explicit ${name}`);
    }
    assert.match(spec, /\\anchor\{/, `Profile ${index + 1}: missing Lean evidence`);
    assert.match(spec, /\\emph\{Datatype-state collection\.\}/,
      `Profile ${index + 1}: missing datatype-state collection status`);
  }
  return profiles.length;
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const count = checkProfiles(readFileSync('docs/formal-reference/main.tex', 'utf8'));
  console.log(`Formal reference: ${count} datatype profiles have explicit sequential components (structural check only).`);
}
