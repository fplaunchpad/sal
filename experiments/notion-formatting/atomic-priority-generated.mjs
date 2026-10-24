// Exhaustive finite character/sticky-gap oracle. Expected marks are computed by
// direct paint and splice on current arrays, never by source annotation replay.
import assert from 'node:assert/strict';
import {Replica} from './replica.js';
import {idKey} from './ids.js';
import {atomicToggle, identity} from './atomic-priority-adapter.mjs';

const key = (instance, id) => `${instance}/${idKey(id)}`;
const clone = text => ({cells: text.cells.map(cell => ({...cell})), gaps: [...text.gaps]});
function paint(text, lower, upper, value) {
  const result = clone(text);
  for (let i = lower; i < upper; i++) result.cells[i].bold = value;
  for (let gap = lower + 1; gap <= upper; gap++) result.gaps[gap] = value;
  return result;
}
function insert(text, gap, fresh) {
  const result = clone(text), inherited = result.gaps[gap];
  result.cells.splice(gap, 0, ...fresh.map(cell => ({...cell, bold: inherited})));
  result.gaps.splice(gap, 1, ...Array(fresh.length + 1).fill(inherited));
  assert.equal(result.gaps.length, result.cells.length + 1);
  return result;
}
function semanticFormat(text, range, value) {
  const lower = text.cells.findIndex(cell => cell.id === range.lower);
  const upper = range.upper === null ? text.cells.length
    : text.cells.findIndex(cell => cell.id === range.upper);
  assert(lower >= 0 && upper >= lower);
  return paint(text, lower, upper, value);
}
function semanticInsert(text, instance, transaction) {
  const args = transaction.operations[0].args;
  const gap = args.originId === 'start' ? 0
    : text.cells.findIndex(cell => cell.id === key(instance, args.originId)) + 1;
  assert(args.originId === 'start' || gap > 0, 'natural source origin still retained');
  const fresh = [...args.content].map((value, offset) => ({id: key(instance,
    {sessionId: args.id.sessionId, counter: args.id.counter + offset}), value}));
  return insert(text, gap, fresh);
}
function observations(replica) {
  const document = replica.document();
  return document.aliveBlocks().flatMap(block => document.blockCharacters(block.id))
    .map(character => ({id: identity(character), value: character.text, bold: character.bold}));
}
function compare(replica, oracle, label) {
  assert.deepEqual(observations(replica), oracle.cells, label);
  // Every observation has a paired false oracle: negating the fresh cell's
  // mark must disagree, even when the legitimate result is entirely plain.
  const probe = oracle.cells.findIndex(cell => cell.value === 'Y');
  const fresh = probe >= 0 ? probe : oracle.cells.findIndex(cell => cell.value === 'X');
  assert(fresh >= 0);
  const rejected = oracle.cells.map((cell, i) => ({...cell, bold: i === fresh ? !cell.bold : cell.bold}));
  assert.notDeepEqual(observations(replica), rejected, `${label}/negative`);
}
function receiver(base, transactions) {
  const replica = new Replica('R', 'R', base);
  for (const transaction of transactions) replica.receive(transaction);
  return replica;
}
const count = {baseCases: 0, latentGapCases: 0, patterns: 0, discarded: 0};
const byLength = [], examples = [];
for (let n = 1; n <= 4; n++) {
  const startCounts = {...count};
  for (let pattern = 0; pattern < 2 ** n; pattern++) {
    const seed = new Replica('S', 'S', []), root = seed.createBlock().newBlockId;
    seed.insertText(root, 0, 'abcd'.slice(0, n));
    const characters = seed.document().blockCharacters(root), instance = characters[0].textInstanceId;
    let initial = {cells: characters.map(character => ({id: identity(character),
      value: character.text, bold: false})), gaps: Array(n + 1).fill(false)};
    const bits = Array.from({length: n}, (_, i) => !!(pattern & (1 << i)));
    for (let i = 0; i < n;) {
      if (!bits[i]) { i++; continue; }
      let end = i + 1;
      while (end < n && bits[end]) end++;
      const prepared = atomicToggle(seed, root, i, end);
      assert.equal(prepared.value, true);
      initial = paint(initial, i, end, true);
      i = end;
    }
    assert.deepEqual(observations(seed), initial.cells, 'initial direct marks');
    count.patterns++;
    for (let lo = 0; lo < n; lo++) for (let hi = lo + 1; hi <= n; hi++) {
      const range = {lower: initial.cells[lo].id, upper: hi === n ? null : initial.cells[hi].id};
      const value = !bits.slice(lo, hi).every(Boolean);
      for (let gap = 0; gap <= n; gap++) for (const formatSession of ['A', 'B']) {
        for (const priorityMode of ['tie', 'format-counter-first', 'insert-counter-first']) {
        const insertSession = formatSession === 'A' ? 'B' : 'A';
        const formatter = new Replica(formatSession, formatSession, seed.transactions());
        const inserter = new Replica(insertSession, insertSession, seed.transactions());
        // Advance the relevant real source clock by an ordinary empty-block
        // creation. Its payload is archived and delivered with the event.
        if (priorityMode === 'format-counter-first') inserter.createBlock();
        if (priorityMode === 'insert-counter-first') formatter.createBlock();
        const prepared = atomicToggle(formatter, root, lo, hi);
        assert.equal(prepared.value, value, 'issuer computes one independent Boolean');
        const birth = inserter.insertText(root, gap, 'X');
        const origin = gap === 0 ? 'start' : idKey(characters[gap - 1].item.id);
        assert.equal(idKey(birth.operations[0].args.originId), origin, 'physical origin is unchanged');
        const formatFirst = priorityMode === 'tie' ? formatSession === 'A'
          : priorityMode === 'format-counter-first';
        if (priorityMode === 'tie') assert.equal(prepared.transaction.id.counter, birth.id.counter);
        else if (formatFirst) assert(prepared.transaction.id.counter < birth.id.counter);
        else assert(birth.id.counter < prepared.transaction.id.counter);
        let expected = clone(initial);
        if (formatFirst) {
          expected = semanticFormat(expected, range, value);
          expected = semanticInsert(expected, instance, birth);
        } else {
          expected = semanticInsert(expected, instance, birth);
          expected = semanticFormat(expected, range, value);
        }
        for (const reverseDelivery of [false, true]) {
          const label = `n${n}/p${pattern}/${lo}-${hi}/gap${gap}/${formatSession}/${priorityMode}/${reverseDelivery}`;
          const formatEvents = formatter.transactions().filter(transaction =>
            !seed.transactions().some(old => idKey(old.id) === idKey(transaction.id)));
          const insertEvents = inserter.transactions().filter(transaction =>
            !seed.transactions().some(old => idKey(old.id) === idKey(transaction.id)));
          const events = reverseDelivery ? [...insertEvents, ...formatEvents] : [...formatEvents, ...insertEvents];
          const final = receiver(seed.transactions(), events);
          compare(final, expected, label);
          count.baseCases++;
          // Current output alone cannot observe a latent wrong gap. Probe all
          // n+2 retained gaps using a causally later natural-origin insertion.
          for (let probe = 0; probe <= expected.cells.length; probe++) {
            const observed = new Replica('P', 'P', final.transactions());
            const later = observed.insertText(root, probe, 'Y');
            const laterOrigin = later.operations[0].args.originId;
            assert.equal(laterOrigin === 'start' ? 'start' : key(instance, laterOrigin),
              probe === 0 ? 'start' : expected.cells[probe - 1].id,
              'probe preserves the chosen physical gap');
            const after = semanticInsert(expected, instance, later);
            compare(observed, after, `${label}/latent${probe}`);
            count.latentGapCases++;
          }
          if (examples.length < 4 && pattern === 0 && gap === hi && lo === 0)
            examples.push({label, expected: expected.cells.map(cell => +cell.bold).join(''),
              gapMarks: expected.gaps.map(Number).join(''), sourceOrigin: origin});
        }
        }
      }
    }
  }
  byLength.push({length: n, patterns: count.patterns - startCounts.patterns,
    baseCases: count.baseCases - startCounts.baseCases,
    latentGapCases: count.latentGapCases - startCounts.latentGapCases});
}
console.log(JSON.stringify({schema: 'notion-atomic-priority-generated-v1',
  oracle: 'direct current character and sticky-gap arrays; stable identity boundaries; natural physical origins',
  enumeration: {minLength: 1, maxLength: 4, initialPatterns: 'all Boolean patterns',
    formatRanges: 'all nonempty contiguous ranges', insertions: 'every physical gap',
    arbitration: 'both session orders, equal counter and unequal counter in either direction using actual creates', delivery: 'both orders',
    latentGaps: 'every final gap via a causally later insertion', random: false, seeds: [], discarded: 0},
  summary: {...count, pairedControls: count.baseCases + count.latentGapCases, allPassed: true}, byLength, examples}));
