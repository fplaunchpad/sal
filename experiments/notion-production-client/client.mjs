import { createRuntime } from './runtime.mjs';

const copy = value => JSON.parse(JSON.stringify(value));

// This adapter supplies records and names the original module exports. Every
// text edit, serialisation, record update and rich-text read uses shipped code.
export class ProductionClient {
  constructor(extracted, session, snapshot) {
    this.runtime = createRuntime(extracted);
    this.session = session;
    this.recordMap = this.runtime.require('412951').RecordMap.create(snapshot && copy(snapshot));
  }
  module(id) { return this.runtime.require(id); }
  createBlock(pointer) {
    const tree = this.module('300957').y.createEmpty({
      textInstanceId: this.module('540180').F(pointer.id, 'title'),
      sessionId: this.session, searchLabel: '',
    });
    this.recordMap.setValue(pointer, {
      id: pointer.id, space_id: pointer.spaceId, type: 'text', alive: true, version: 1,
      properties: { title: [] }, crdt_data: { title: this.module('409788').g(tree) },
      crdt_format_version: 1,
    });
  }
  tree(pointer) {
    const model = this.recordMap.getModel(pointer);
    if (!model) throw new Error(`Unknown block ${pointer.id}`);
    return model.getBlockTitleTextSliceTree(this.session);
  }
  value(pointer) { return copy(this.recordMap.getValue(pointer)); }
  text(pointer) { return this.tree(pointer).getText(); }
  rich(pointer) { return copy(this.module('798132').w4(this.tree(pointer))); }
  snapshot() { return copy(this.recordMap.toJson()); }
  wrap(pointer, operations) {
    return operations.map(crdtOperation => this.module('166029').qA({ pointer, crdtOperation }));
  }
  prepareInsert(pointer, index, content) {
    const operation = this.module('769718').H(this.tree(pointer), { index, content, includePrevItems: true });
    return operation ? this.wrap(pointer, [operation]) : [];
  }
  prepareDelete(pointer, start, end) {
    if (start >= end) throw new Error('Deletion requires a nonempty range');
    return this.wrap(pointer, this.module('55709').Q(this.tree(pointer), start, end - 1).operations);
  }
  prepareBold(pointer, start, end, add = true) {
    if (start >= end) throw new Error('Formatting requires a nonempty range');
    const options = { startIndex: start, endIndex: end - 1 };
    const builder = this.module('709022');
    const result = add ? builder.eR(this.tree(pointer), { ...options, annotation: ['b'] }) :
      builder.D3(this.tree(pointer), { ...options, annotationKey: 'b' });
    return this.wrap(pointer, result.operations);
  }
  prepareSplit(pointer, index) {
    const result = this.tree(pointer).getOperationsForSplitAtIndex(index);
    if (result.type !== 'splitWithinNode') throw new Error(`Split preparation returned ${result.type}`);
    return this.wrap(pointer, [result.splitOp]);
  }
  // A wire-level handler input, not a reconstruction of Enter/Backspace's full
  // UI transaction. The source slice must already have a non-root boundary.
  prepareMove(pointer, splitOperation, targetPointer, isMerge = false) {
    const source = splitOperation.args;
    const target = this.tree(targetPointer).getTextSlice();
    return [{ command: 'moveTextSlice', pointer, path: [], opVersion: 2, args: {
      textInstanceId: source.textInstanceId, sourceSearchLabel: source.searchLabel,
      textSliceStartItemId: source.id, targetTextInstanceId: target.textInstanceId,
      targetSearchLabel: target.getSearchLabel(), targetTextSliceEndItemId: target.getEndItem().id,
      targetBlockId: targetPointer.id, isMerge,
    } }];
  }
  prepareMerge(pointer, targetPointer) {
    const result = this.tree(pointer).getOperationsForSplitForMerge();
    if (result.type !== 'splitWithinNode') throw new Error(`Merge preparation returned ${result.type}`);
    const [split] = this.wrap(pointer, [result.splitOp]);
    return [split, ...this.prepareMove(pointer, split, targetPointer, true),
      { command: 'set', pointer, path: ['alive'], args: false }];
  }
  apply(operations) {
    return this.module('971340').N({ recordMap: this.recordMap, operations: copy(operations) });
  }
}
