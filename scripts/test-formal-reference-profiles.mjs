import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { checkProfiles } from './check-formal-reference-profiles.mjs';

const tex = readFileSync('docs/formal-reference/main.tex', 'utf8');
const start = tex.indexOf('\\subsection{Formal instance profiles}');
const end = tex.indexOf('\\subsection{Proof routes and evidence status}', start);

test('all current profiles pass the component check', () => {
  assert.ok(checkProfiles(tex) > 0);
});

test('retired tagged OR-set profile is rejected', () => {
  assert.throws(() => checkProfiles(tex + '\\paragraph{Tagged observed-remove set.}'),
    /Retired tagged OR-set/);
});

for (const token of ['q_0', '\\mathsf{step}', '\\mathsf{Legal}', '\\mathsf{query}_{\\rm seq}', '\\mathsf{Rel}']) {
  test(`missing ${token} is rejected even when the specification heading remains`, () => {
    const broken = tex.slice(0, start) + tex.slice(start, end).replaceAll(token, 'omitted') + tex.slice(end);
    assert.throws(() => checkProfiles(broken), /missing explicit/);
  });
}

test('missing per-datatype collection status is rejected', () => {
  assert.throws(() => checkProfiles(tex.replaceAll('\\emph{Datatype-state collection.}', 'omitted')),
    /missing datatype-state collection/);
});
