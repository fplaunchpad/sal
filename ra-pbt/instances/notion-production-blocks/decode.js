/**
 * Decoding of production record operations into specification commands
 * (spec.js). One request's operations become one atomic command group. The
 * decoder reads the wire format only; it imports no Notion code.
 *
 * Item identifiers are `"start"`, `"end"` or `[session, counter]`; their
 * keys are `start`, `end` and `session:counter`, and a character of an
 * insertion run `[s, c]` of length n has the keys `s:c` to `s:(c + n - 1)`.
 *
 *   set [] (a block value with crdt_data) followed by listAfter on the page's
 *       content                          create block instance after
 *   insertText                           insert instance origin characters
 *   splitText s + moveTextSliceIntoBlock starting at s
 *                                        split instance origin s target
 *   moveTextSliceIntoBlock without a split (the builder's splitNodeEnd case)
 *                                        splitAt instance start target
 *   splitText s + moveTextSlice with isMerge starting at s
 *                                        mark instance origin s, then merge
 *   moveTextSlice with isMerge           merge source target anchor, with the
 *                                        anchor (targetTextInstanceId,
 *                                        targetTextSliceEndItemId)
 *   moveTextSlice without isMerge        nothing: the split builder's moves of
 *                                        following slice-tree siblings under
 *                                        the node being split, which keep the
 *                                        displayed order
 *   set alive false, listRemove          nothing: part of the merge command,
 *                                        whose source becomes a tombstone
 *   addAnnotation, removeAnnotation      nothing: formatting is given by the
 *                                        issuer's selection (adapter.js)
 *
 * Anything else throws: the specification gives it no meaning.
 */
export const itemKey = (id) => (typeof id === 'string' ? id : `${id[0]}:${id[1]}`);

/** The text instance of a block value's serialised title tree (its root slice). */
export function instanceOfValue(value) {
  const title = value?.crdt_data?.title;
  if (!title || !title.n?.[title.r]) throw new Error('block value without a serialised title tree');
  return title.n[title.r].s.x;
}

/** Characters of an insertText operation: [{ id, text }] with item keys. */
export function insertedCharacters(args) {
  return [...args.content].map((text, i) => ({ id: `${args.id[0]}:${args.id[1] + i}`, text }));
}

/**
 * The command group of one request's operations. `pageId` names the page
 * whose content lists the blocks; `insertBold` is the flag inserted
 * characters take (spec.js, difference 2).
 */
export function decodeOps(ops, { pageId, insertBold = false } = {}) {
  const out = [];
  const instances = new Map();
  const consumed = new Set();
  let merges = 0;
  let removals = 0;
  ops.forEach((op, i) => {
    const a = op.args;
    switch (op.command) {
      case 'set':
        if (op.path.length === 0) instances.set(op.pointer.id, instanceOfValue(a));
        else if (op.path.length === 1 && op.path[0] === 'alive' && a === false) removals++;
        else if (!(op.pointer.id === pageId && (op.path[0] === 'type' || op.path[0] === 'content'))) throw new Error(`set ${op.path.join('.')} outside the specification`);
        return;
      case 'listAfter': {
        if (op.pointer.id !== pageId || op.path[0] !== 'content') throw new Error('listAfter outside the page content');
        if (!instances.has(a.id)) throw new Error(`listAfter of ${a.id} without its block value`);
        out.push({ kind: 'create', block: a.id, instance: instances.get(a.id), ...(a.after ? { after: a.after } : {}) });
        return;
      }
      case 'listRemove':
        if (op.pointer.id !== pageId) throw new Error('listRemove outside the page content');
        removals++;
        return;
      case 'insertText':
        out.push({ kind: 'insert', instance: a.textInstanceId, origin: itemKey(a.originId), characters: insertedCharacters(a), bold: insertBold });
        return;
      case 'splitText': {
        const start = itemKey(a.id);
        const j = ops.findIndex((o, k) => k > i && (o.command === 'moveTextSliceIntoBlock' || o.command === 'moveTextSlice') && o.args.textInstanceId === a.textInstanceId && itemKey(o.args.textSliceStartItemId) === start);
        if (j < 0) throw new Error('splitText without a move of its slice');
        const move = ops[j];
        if (move.command === 'moveTextSliceIntoBlock') {
          consumed.add(j);
          out.push({ kind: 'split', instance: a.textInstanceId, origin: itemKey(a.originId), marker: start, target: move.args.targetBlockId });
        } else if (move.args.isMerge) out.push({ kind: 'mark', instance: a.textInstanceId, origin: itemKey(a.originId), marker: start });
        else throw new Error('splitText moved without a merge or a new block');
        return;
      }
      case 'moveTextSliceIntoBlock':
        if (!consumed.has(i)) out.push({ kind: 'splitAt', instance: a.textInstanceId, start: itemKey(a.textSliceStartItemId), target: a.targetBlockId });
        return;
      case 'moveTextSlice':
        if (a.isMerge) {
          merges++;
          out.push({ kind: 'merge', source: op.pointer.id, target: a.targetBlockId, anchor: { instance: a.targetTextInstanceId, end: itemKey(a.targetTextSliceEndItemId) } });
        }
        return;
      case 'addAnnotation':
      case 'removeAnnotation':
        return;
      default:
        throw new Error('operation outside the specification: ' + op.command);
    }
  });
  if (removals && removals !== 2 * merges) throw new Error('block removal without a merge');
  return out;
}

/** Whether a request's operations include the split builder's sibling moves. */
export const siblingMoves = (ops) => ops.filter((o) => o.command === 'moveTextSlice' && !o.args.isMerge).length;
