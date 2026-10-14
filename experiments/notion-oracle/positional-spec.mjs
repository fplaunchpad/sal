// Independent ordinary sequential request semantics. No transaction replay,
// search labels, Lamport ordering, RGA or demo imports occur in this file.
// Each block contains visible Unicode scalar values and their bold flags.
export const plain = text => [...text].map(text => ({text, bold: false}));
export const textView = blocks => blocks.map(block => block.map(c => c.text).join(''));
export function request(blocks, operation) {
  const out = structuredClone(blocks), {kind, block = 0, index, start, end, text} = operation;
  const chars = out[block];
  if (!chars) throw Error('unknown block');
  if (kind === 'split') out.splice(block, 1, chars.slice(0, index), chars.slice(index));
  else if (kind === 'insert') chars.splice(index, 0, ...plain(text));
  else if (kind === 'delete') chars.splice(start, end - start);
  else if (kind === 'bold') {
    const selected = chars.slice(start, end), remove = selected.every(c => c.bold);
    for (const char of selected) char.bold = !remove;
  } else if (kind === 'merge') {
    if (block === 0) return out;
    out.splice(block - 1, 2, [...out[block - 1], ...chars]);
  } else throw Error('unknown request');
  return out;
}
// Independent expected outcome for splitting initial characters while deleting
// a concurrently selected original interval: deletion preserves selection IDs.
// This is a candidate identity-aware contract, not the positional history spec.
export function splitDelete(text, split, start, end) {
  const chars = [...text];
  return [chars.slice(0, split).filter((_, i) => i < start || i >= end).join(''),
    chars.slice(split).filter((_, i) => i + split < start || i + split >= end).join('')];
}
