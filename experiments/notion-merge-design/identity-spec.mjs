// Independent sequential specification of identity-addressed block editing,
// extended with block merge, and a decoder from replicated transactions to its
// commands. This file imports no demo module: it has no slice trees, search
// labels, RGA sibling order or replay code.
//
// A document is an ordered list of blocks, each with an `alive` flag and
// retained slots {address, value, visible}; an address is `instance/localId`.
// A block's head slot is the invisible root `instance/start`. Commands follow
// Sal/MRDTs/Instances/NotionCoreSpec.lean, plus merge:
//
//   create block instance after   new alive block [root], immediately after
//                                 `after` (alive or not) or first
//   insert origin characters      visible slots immediately after `origin`
//   delete targets                hide every slot whose address is a target
//   split origin marker target    move the suffix after `origin`, preceded by
//                                 an invisible marker slot, to the end of the
//                                 (freshly created, alive) target block
//   merge source target           the holder is the block whose slots contain
//                                 the target's root slot (the target itself
//                                 if alive, else the block that absorbed it);
//                                 if the source is alive and the holder exists
//                                 and is not the source, holder.slots ++
//                                 source.slots and the source keeps its place
//                                 in the list as a tombstone (not alive, no
//                                 slots); otherwise no change
//
// The view lists the alive blocks in order. The owner of an origin is the
// block whose slots contain it, so after a merge it is the absorbing block.
// No alive check on the target is needed: tombstones hold no slots.
// A command whose Lean counterpart returns `none` raises SpecStuck: the
// specification gives the history no meaning.
//
// Option `removeMergedSource` gives the reading in which the merged source
// leaves the list. Under it, a later `create ... after source` is stuck.
// Option `merge: 'skip'` gives the earlier meaning: a no-op unless the target
// itself is alive and distinct from the source.
//
// Option `merge: 'sliceFollow'` gives the meaning of the demo's own targeting.
// The decoded merge carries an anchor (instance, end): the instance of the
// target's last slice at issue time and the end item of that slice, either a
// split marker or `end`. The anchor denotes a position, the end of the slice
// ending there, not a slot: for `end` it is the position after the last slot
// of the instance, and for a marker m it is the position immediately before
// m in the instance. The slot m itself heads the next slice, so reading the
// anchor as the slot m would make merging a split-off block back into its
// origin a no-op. In this mode the specification records these positions as
// invisible end slots: a created block is [instance/start, instance/^end],
// and a split at origin o with marker m leaves instance/^m immediately after
// o in the block that keeps the prefix. Then
//
//   merge source target (instance, end)
//                                 the holder is the block whose slots contain
//                                 instance/^end; a no-op when the source is
//                                 not alive or the holder is the source;
//                                 otherwise the source's slots are appended at
//                                 the end of the holder (option `placement:
//                                 'end'`, the default) or immediately after
//                                 instance/^end (`placement: 'anchor'`), and
//                                 the source becomes a tombstone
//
// Neither placement is the implementation's rule in general. The
// implementation attaches the source as the last child of the slice node, so
// it renders after that node's whole subtree. That is the holder's end when
// the subtree is a suffix of the holder, and right after the anchor when the
// node has no children. Two concurrent merges into one anchor give the node
// two children, and then the slots alone do not determine the subtree.

export class SpecStuck extends Error {
  constructor(message, command) { super(message); this.command = command; }
}

export const address = (instance, local) => `${instance}/${local}`;

export class IdentitySpec {
  constructor({removeMergedSource = false, merge = 'absorb', placement = 'end'} = {}) {
    if (!['absorb', 'skip', 'sliceFollow'].includes(merge)) throw new Error('unknown merge meaning ' + merge);
    if (placement !== 'end' && placement !== 'anchor') throw new Error('unknown placement ' + placement);
    this.blocks = [];
    this.instanceOf = {};
    this.removeMergedSource = removeMergedSource;
    this.merge = merge;
    this.placement = placement;
    this.ends = merge === 'sliceFollow';
  }
  clone() {
    const s = new this.constructor({removeMergedSource: this.removeMergedSource, merge: this.merge, placement: this.placement});
    s.blocks = structuredClone(this.blocks);
    s.instanceOf = {...this.instanceOf};
    return s;
  }
  live(id) { return this.blocks.find(b => b.id === id && b.alive); }
  owner(addr) { return this.blocks.find(b => b.slots.some(s => s.address === addr)); }
  step(command) {
    const c = command;
    switch (c.kind) {
      case 'create': {
        if (this.blocks.some(b => b.id === c.block)) throw new SpecStuck('block already exists', c);
        this.instanceOf[c.block] = c.instance;
        const fresh = {id: c.block, alive: true, slots: [{address: address(c.instance, 'start'), value: '', visible: false}]};
        if (this.ends) fresh.slots.push({address: address(c.instance, '^end'), value: '', visible: false});
        if (c.after === undefined || c.after === null) { this.blocks.unshift(fresh); break; }
        const at = this.blocks.findIndex(b => b.id === c.after);
        if (at < 0) throw new SpecStuck('create after a block that is not in the document', c);
        this.blocks.splice(at + 1, 0, fresh);
        break;
      }
      case 'insert': {
        const origin = address(c.instance, c.origin), block = this.owner(origin);
        if (!block) throw new SpecStuck('insert origin has no owner', c);
        const at = block.slots.findIndex(s => s.address === origin);
        block.slots.splice(at + 1, 0, ...c.characters.map(x =>
          ({address: address(c.instance, x.id), value: x.text, visible: true})));
        break;
      }
      case 'delete': {
        const targets = new Set(c.ids.map(id => address(c.instance, id)));
        for (const b of this.blocks) for (const s of b.slots) if (targets.has(s.address)) s.visible = false;
        break;
      }
      case 'split': {
        const origin = address(c.instance, c.origin), source = this.owner(origin), target = this.live(c.target);
        if (!source) throw new SpecStuck('split origin has no owner', c);
        if (!target || target === source) throw new SpecStuck('split target not alive or equal to source', c);
        const at = source.slots.findIndex(s => s.address === origin);
        const suffix = source.slots.splice(at + 1);
        if (this.ends) source.slots.push({address: address(c.instance, '^' + c.marker), value: '', visible: false});
        target.slots.push({address: address(c.instance, c.marker), value: '', visible: false}, ...suffix);
        break;
      }
      case 'merge': {
        if (this.merge === 'sliceFollow') { this.sliceMerge(c); break; }
        const source = this.live(c.source), instance = this.instanceOf[c.target];
        const target = this.merge === 'skip' ? this.live(c.target)
          : instance === undefined ? undefined : this.owner(address(instance, 'start'));
        if (!source || !target || source === target) break;
        target.slots.push(...source.slots);
        if (this.removeMergedSource) this.blocks.splice(this.blocks.indexOf(source), 1);
        else { source.slots = []; source.alive = false; }
        break;
      }
      default: throw new Error('unknown command ' + c.kind);
    }
    return this;
  }
  sliceMerge(c) {
    if (!c.anchor) throw new SpecStuck('merge without an anchor', c);
    const source = this.live(c.source);
    if (!source) return;
    const end = address(c.anchor.instance, '^' + c.anchor.end), holder = this.owner(end);
    if (!holder) throw new SpecStuck('merge anchor has no owner', c);
    if (holder === source) return;
    const at = this.placement === 'anchor' ? holder.slots.findIndex(s => s.address === end) + 1 : holder.slots.length;
    holder.slots.splice(at, 0, ...source.slots);
    if (this.removeMergedSource) this.blocks.splice(this.blocks.indexOf(source), 1);
    else { source.slots = []; source.alive = false; }
  }
  // An atomic group: either every command applies or the document is unchanged.
  group(commands) {
    const trial = this.clone();
    for (const c of commands) trial.step(c);
    this.blocks = trial.blocks;
    this.instanceOf = trial.instanceOf;
    return this;
  }
  view() {
    return this.blocks.filter(b => b.alive).map(b =>
      [b.id, b.slots.filter(s => s.visible).map(s => s.value).join('')]);
  }
  addresses() { return this.blocks.flatMap(b => b.slots.map(s => s.address)); }
}

// ---------------------------------------------------------------- decoding

const key = id => typeof id === 'string' ? id : `${id.sessionId}:${id.counter}`;
const shift = (id, k) => ({sessionId: id.sessionId, counter: id.counter + k});

// One transaction becomes one atomic command group. Merge transactions of the
// demo (split at the source root, move, remove), of the design (mergeBlock) and
// of the control variants (mergeBlock plus removeBlock) all decode to the
// request's intent: merge source target. When the transaction records the end
// item of the target's last slice (the demo's move and the slice-following
// mergeBlock), the command also carries it as `anchor`. Formatting operations
// are outside the specification and decode to nothing.
export function decode(transaction) {
  const ops = transaction.operations, out = [], has = c => ops.some(o => o.command === c);
  if (has('mergeBlock') || has('moveTextSlice')) {
    let source, target, args;
    if (has('mergeBlock')) ({sourceBlockId: source, targetBlockId: target} = args = ops.find(o => o.command === 'mergeBlock').args);
    else { source = ops.find(o => o.command === 'removeBlock').args.blockId; ({targetBlockId: target} = args = ops.find(o => o.command === 'moveTextSlice').args); }
    const allowed = new Set(['mergeBlock', 'moveTextSlice', 'splitText', 'removeBlock']);
    if (!ops.every(o => allowed.has(o.command))) throw new Error('unexpected operation in a merge transaction');
    const command = {kind: 'merge', source, target};
    if (args.targetTextSliceEndItemId !== undefined)
      command.anchor = {instance: args.targetTextInstanceId, end: key(args.targetTextSliceEndItemId)};
    return [command];
  }
  for (const op of ops) {
    const a = op.args;
    switch (op.command) {
      case 'createBlock': out.push({kind: 'create', block: a.blockId, instance: a.titleTextInstanceId, after: a.afterBlockId}); break;
      case 'insertText': out.push({kind: 'insert', instance: a.textInstanceId, origin: key(a.originId),
        characters: [...a.content].map((text, i) => ({id: key(shift(a.id, i)), text}))}); break;
      case 'deleteText': out.push({kind: 'delete', instance: a.textInstanceId,
        ids: a.idRanges.flatMap(([first, n]) => Array.from({length: n}, (_, i) => key(shift(first, i))))}); break;
      case 'splitText': {
        const move = ops.find(o => o.command === 'moveTextSliceIntoBlock');
        if (!move) throw new Error('split without a move into a new block');
        out.push({kind: 'split', instance: a.textInstanceId, origin: key(a.originId), marker: key(a.id), target: move.args.targetBlockId});
        break;
      }
      case 'moveTextSliceIntoBlock': case 'addAnnotation': case 'removeAnnotation': break;
      default: throw new Error('operation outside the specification: ' + op.command);
    }
  }
  return out;
}

// Replay order: transaction identifiers by counter, then session.
export function replayOrder(transactions) {
  return [...transactions].sort((a, b) => a.id.counter - b.id.counter ||
    (a.id.sessionId < b.id.sessionId ? -1 : a.id.sessionId > b.id.sessionId ? 1 : 0));
}

// Fold the specification over an archive. Returns the view, or the first
// transaction at which the specification is stuck.
export function fold(transactions, options = {}, Spec = IdentitySpec) {
  const spec = new Spec(options);
  for (const tx of replayOrder(transactions)) {
    try { spec.group(decode(tx)); }
    catch (e) {
      if (e instanceof SpecStuck) return {stuck: {transaction: key(tx.id), reason: e.message, command: e.command}, spec};
      throw e;
    }
  }
  return {view: spec.view(), spec};
}
