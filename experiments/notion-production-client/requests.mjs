// Original UI split/merge request builders, observed at the transaction sink.
// Fixture stores expose records; the original shared record handlers apply
// each emitted operation. The full optimistic-client cache pipeline is not run.
export class RequestBuilder {
  constructor(client) {
    this.client = client;
    this.operations = [];
    this.stores = new Map();
    this.builder = client.runtime.instantiate('701590', {
      '955631': { k: ({ operation }) => {
        this.operations.push(JSON.parse(JSON.stringify(operation)));
        client.apply([operation]);
      } },
    });
  }
  store(pointer) {
    if (this.stores.has(pointer.id)) return this.stores.get(pointer.id);
    const c = this.client;
    const store = Object.create(c.module('970831').B.prototype);
    const title = { getValue: () => c.rich(pointer), getRecordStoreUIParent: () => store };
    const fields = {
      pointer, id: pointer.id,
      isCrdtEnabled: () => c.recordMap.getModel(pointer).isCrdtEnabled(),
      getBlockTitleStore: () => title,
      getBlockTitleTextSliceTree: () => c.tree(pointer),
      getReadOnlyBlockTitleTextSliceTree: () => c.tree(pointer),
    };
    for (const [key, value] of Object.entries(fields)) Object.defineProperty(store, key, { value });
    this.stores.set(pointer.id, store);
    return store;
  }
  split(source, target, index, moveIntoNewBlock = true) {
    this.builder.X0({ sourceBlockStore: this.store(source), targetBlockStore: this.store(target),
      splitAtGraphemeIndex: index, transaction: {}, moveIntoNewBlock });
    return this.operations;
  }
  merge(source, target) {
    this.builder.LT({ sourceBlockStore: this.store(source),
      targetStore: this.store(target).getBlockTitleStore(), transaction: {} });
    return this.operations;
  }
}
