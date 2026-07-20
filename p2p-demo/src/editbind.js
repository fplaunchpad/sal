// Editor binding (browser-safe, no DOM): translate a textarea edit into embed-
// RGA ops. Extracted from the browser app so it can be tested headlessly
// (test/editbind.test.js drives arbitrary contiguous edits and asserts the RGA
// read reproduces the target text under a single author).
//
// A normal textarea edit -- typing, backspace, or paste-over-a-selection -- is
// ONE contiguous replacement: a common prefix, a changed middle, a common
// suffix. We delete the middle's records and insert the new middle after the
// character to the left of the change (RGA "insert after anchor"), chaining
// successive characters so they land in typing order.

/** Apply the edit oldText -> newText to `node`, given the display-order ids of
 *  oldText (ids[i] is the record shown at oldText[i]). `mint()` returns a fresh
 *  strictly-increasing globally-unique id. Commits each op as it goes so a
 *  state-based mint() stays consistent. Returns { dels, inss }. */
export function applyTextEdit(node, ids, oldText, newText, mint) {
  let p = 0;
  while (p < oldText.length && p < newText.length && oldText[p] === newText[p]) p++;
  let s = 0;
  while (s < oldText.length - p && s < newText.length - p &&
    oldText[oldText.length - 1 - s] === newText[newText.length - 1 - s]) s++;
  const delCount = oldText.length - p - s;
  const insStr = newText.slice(p, newText.length - s);

  for (let i = 0; i < delCount; i++) node.commit({ type: 'del', id: ids[p + i] });
  let anchor = p > 0 ? ids[p - 1] : null; // the character to the LEFT of the change
  for (const ch of insStr) {
    const id = mint();
    node.commit({ type: 'ins', id, el: ch, anchorId: anchor });
    anchor = id;
  }
  return { dels: delCount, inss: insStr.length };
}
