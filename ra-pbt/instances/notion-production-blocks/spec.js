/**
 * Sequential specification of block editing for the production Notion
 * instance.
 *
 * The specification is the one of the demo instance (`../notion/spec.js`):
 * the identity-addressed block document of
 * `experiments/notion-merge-design/identity-spec.mjs` in its `sliceFollow`
 * merge meaning, with the demo instance's `bold` and `mark` commands
 * (`FormattedIdentitySpec`, imported). A state is an ordered list of blocks,
 * each alive or a tombstone, holding slots `{ address, value, visible, bold }`
 * with addresses `instance/local`; the view lists the alive blocks with their
 * visible characters. Commands, as there:
 *
 *   create block instance after     a new alive block [i/start, i/^end]
 *                                   immediately after `after` (alive or a
 *                                   tombstone), or first
 *   insert instance origin chars    visible slots immediately after the
 *                                   slot `instance/origin`, wherever it is
 *   split instance origin marker target
 *                                   in the block holding `instance/origin`,
 *                                   the slots after it move, headed by the
 *                                   invisible marker slot, to the end of the
 *                                   alive target block; the end slot
 *                                   `instance/^marker` stays behind
 *   mark instance origin marker     the end and marker slots of a merge's
 *                                   own split, immediately after the origin
 *   merge source target anchor      the holder is the block holding the
 *                                   anchor's end slot; unless the source is
 *                                   a tombstone or is the holder, the
 *                                   source's slots are appended to the
 *                                   holder and the source becomes a
 *                                   tombstone
 *   bold addresses value            the bold flag of exactly those slots
 *
 * A command group is atomic; a command that has no meaning (an origin with
 * no holder, a dead or identical split target) makes the history stuck.
 *
 * Differences from the demo instance's specification, each forced by the
 * production operations:
 *
 * 1. `splitAt instance start target`. The production split builder emits no
 *    split operation when the split index is the end of a slice-tree node
 *    (`splitNodeEnd`); it moves the following slice, which starts at an
 *    existing marker. The command moves the slots from `instance/start`
 *    (inclusive) to the end of their holder into the alive target block.
 *    Its meaning is the `split` rule with the marker already in place.
 * 2. `insert` carries `bold`, the flag the inserted characters take: the
 *    flag of the character before the insertion index on the issuer's
 *    display, plain at index 0. This is the production editor's inheritance
 *    rule; the demo instance avoided it by issuing no insertion in its
 *    formatted profile.
 * 3. The local meaning (`localEdit`) is `positional-spec.mjs`'s `request`,
 *    extended by `create` (an empty block after the displayed block `after`)
 *    and by the inheritance rule of (2) for insertions.
 * 4. The initial state is the fold of the seed's decoded command groups
 *    (decode.js), not of demo transactions.
 *
 * Two readings are options, because the production behaviour differs from
 * the demo instance's reading and both are natural:
 *
 *   splitPlacement  'holder' (default): after a split or splitAt, the
 *                   target block is moved to immediately after the block
 *                   that holds the split point, so a split's new block
 *                   always follows the text it was split from. 'source':
 *                   the target stays where `create` put it, immediately
 *                   after the block the issuer split (alive or a
 *                   tombstone), as in the demo instance.
 *   inherit         'apply' (default): inserted characters take the bold
 *                   flag of the nearest visible slot before them in their
 *                   block, in the state the insertion is applied to.
 *                   'issue': they take the flag the issuer saw (difference
 *                   2), so a concurrent bold of the left neighbour does not
 *                   extend over them.
 *
 * Sequentially (on the issuer's own state) the readings coincide; they
 * differ only on concurrent histories.
 */
import { FormattedIdentitySpec, blocksOf, textsOf } from '../notion/spec.js';
import { SpecStuck } from '../../../experiments/notion-merge-design/identity-spec.mjs';
import { request as positionalRequest, plain } from '../../../experiments/notion-oracle/positional-spec.mjs';

export { blocksOf, textsOf, SpecStuck };
export const MODE = { merge: 'sliceFollow' };

/** The demo instance's formatted identity specification with `splitAt` and inheriting insertion. */
export class ProductionBlockSpec extends FormattedIdentitySpec {
  constructor(options = {}) {
    super(options);
    this.splitPlacement = options.splitPlacement ?? 'holder';
    this.inherit = options.inherit ?? 'apply';
    if (!['holder', 'source'].includes(this.splitPlacement)) throw new Error('unknown split placement ' + this.splitPlacement);
    if (!['apply', 'issue'].includes(this.inherit)) throw new Error('unknown inheritance ' + this.inherit);
  }
  clone() {
    const s = super.clone();
    s.splitPlacement = this.splitPlacement;
    s.inherit = this.inherit;
    return s;
  }
  /** Moves the target block to immediately after the block holding `address` (splitPlacement 'holder'). */
  follow(address, targetId) {
    if (this.splitPlacement !== 'holder') return;
    const holder = this.owner(address);
    const target = this.blocks.find((b) => b.id === targetId);
    if (!holder || holder === target) return;
    this.blocks.splice(this.blocks.indexOf(target), 1);
    this.blocks.splice(this.blocks.indexOf(holder) + 1, 0, target);
  }
  step(command) {
    if (command.kind === 'splitAt') {
      const start = `${command.instance}/${command.start}`;
      const source = this.owner(start);
      const target = this.live(command.target);
      if (!source) throw new SpecStuck('splitAt start has no owner', command);
      if (!target || target === source) throw new SpecStuck('splitAt target not alive or equal to source', command);
      const at = source.slots.findIndex((s) => s.address === start);
      target.slots.push(...source.slots.splice(at));
      if (this.splitPlacement === 'holder') {
        this.blocks.splice(this.blocks.indexOf(target), 1);
        this.blocks.splice(this.blocks.indexOf(source) + 1, 0, target);
      }
      return this;
    }
    super.step(command);
    if (command.kind === 'split') this.follow(`${command.instance}/^${command.marker}`, command.target);
    if (command.kind === 'insert') {
      const first = `${command.instance}/${command.characters[0].id}`;
      const block = this.owner(first);
      const at = block.slots.findIndex((s) => s.address === first);
      let bold = !!command.bold;
      if (this.inherit === 'apply') {
        bold = false;
        for (let i = at - 1; i >= 0; i--)
          if (block.slots[i].visible) {
            bold = !!block.slots[i].bold;
            break;
          }
      }
      for (let i = 0; i < command.characters.length; i++) block.slots[at + i].bold = bold;
    }
    return this;
  }
}

/** One specification state from command groups, in order. */
export function foldGroups(groups, mode = MODE) {
  const s = new ProductionBlockSpec({ ...MODE, ...mode });
  for (const g of groups) s.group(g);
  return s;
}

/** The local meaning of a positional request on a displayed block list. */
export function localEdit(view, request) {
  const blocks = blocksOf(view);
  if (request.kind === 'create') {
    const out = structuredClone(blocks);
    out.splice(request.after + 1, 0, []);
    return out;
  }
  const out = positionalRequest(blocks, request);
  if (request.kind === 'insert') {
    const inherit = request.index > 0 && blocks[request.block][request.index - 1].bold;
    for (let i = 0; i < [...request.text].length; i++) out[request.block][request.index + i].bold = inherit;
  }
  return out;
}

/**
 * The specification for a document whose seed command groups are
 * `seedGroups`. Operations are `{ key, commands }`. With `format`, views
 * are compared with bold flags; otherwise on block texts.
 */
export function specFor({ seedGroups, format = false, mode = MODE, splitPlacement = 'holder', inherit = 'apply' }) {
  const initial = foldGroups(seedGroups, { ...mode, splitPlacement, inherit });
  const key = format ? (v) => JSON.stringify(blocksOf(v).map((cs) => cs.map((c) => [c.text, c.bold]))) : (v) => JSON.stringify(textsOf(v));
  return {
    format,
    reading: { splitPlacement, inherit },
    init: () => initial,
    apply(state, op) {
      const next = state.clone();
      try {
        next.group(op.commands);
      } catch (e) {
        if (e instanceof SpecStuck) return null;
        throw e;
      }
      return next;
    },
    view: (state) =>
      state.blocks.filter((b) => b.alive).map((b) => ({ id: b.id, chars: b.slots.filter((s) => s.visible).map((s) => ({ text: s.value, bold: !!s.bold })) })),
    serialise: (state) => JSON.stringify([state.blocks, Object.entries(state.instanceOf).sort()]),
    viewKey: key,
    normalise: blocksOf,
    localEdit,
  };
}

export { plain };
