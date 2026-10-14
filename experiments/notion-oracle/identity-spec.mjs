// Independent sequential command specification for the split/insert/delete fragment.
// State is an ordered list of blocks with retained semantic slots. There are no
// transaction logs, clocks, replay sorting, parent trees, slices or search labels.
// A hidden slot remains an address after deletion. A split boundary is an
// address at the beginning of its new block; insertions after the old predecessor
// remain in the old block when the split precedes the insertion in the witness.
export class IdentityDocument {
  constructor() { this.blocks = []; }
  locate(instance, id) {
    for (const block of this.blocks) {
      const index = block.slots.findIndex(s => s.instance === instance && s.id === id);
      if (index >= 0) return {block,index};
    }
    throw Error(`missing semantic anchor ${instance}/${id}`);
  }
  step(command) {
    const {kind, instance, origin} = command;
    if (kind === 'create') {
      if (this.blocks.some(b => b.id === command.block)) throw Error('duplicate block');
      const after = command.after === undefined ? -1 : this.blocks.findIndex(b => b.id === command.after);
      if (command.after !== undefined && after < 0) throw Error('missing predecessor block');
      this.blocks.splice(after + 1, 0, {id:command.block,
        slots:[{instance, id:'start', text:'', visible:false}]});
    } else if (kind === 'insert') {
      const {block,index} = this.locate(instance, origin);
      block.slots.splice(index+1, 0, ...command.characters.map(c =>
        ({instance,id:c.id,text:c.text,visible:true})));
    } else if (kind === 'delete') {
      for (const block of this.blocks) for (const slot of block.slots)
        if (slot.instance === instance && command.ids.includes(slot.id)) slot.visible=false;
    } else if (kind === 'split') {
      const {block,index} = this.locate(instance, origin);
      const target=this.blocks.find(b => b.id === command.target);
      if (!target || target === block) throw Error('invalid split target');
      const suffix=block.slots.splice(index+1);
      target.slots.push({instance,id:command.id,text:'',visible:false},...suffix);
    } else throw Error(`unsupported semantic command ${kind}`);
    return this;
  }
  view() { return this.blocks.map(b=>[b.id,b.slots.filter(s=>s.visible).map(s=>s.text).join('')]); }
}
