/**
 * Sequential specification of block editing for the Notion instances.
 *
 * The specification is the identity-addressed block document of
 * `experiments/notion-merge-design/identity-spec.mjs` (imported, not copied;
 * it imports no demo code), in its `sliceFollow` merge meaning: the meaning
 * of a merge anchored at the end of the target's last slice, under which the
 * corrected merge agrees with every archive of the merge design gate. A
 * replicated transaction denotes one atomic command group, given by the
 * file's own `decode`.
 *
 * Formatting. The decoder gives annotation operations no meaning, because
 * their anchors are positions in the text instance's internal order. The
 * formatted specification adds one command, `bold addresses value`, which
 * sets the bold flag of every slot at those addresses: the characters the
 * issuer selected, with the value of an ordinary toggle on its own view
 * (remove when every selected character is bold, otherwise add). The
 * adapter derives it from the request and the issuer's view, not from the
 * annotation the implementation emitted.
 *
 * The demo's merge transaction splits the source at its start before moving
 * it, so its marker m ends the source's (empty) left slice, and a later merge
 * can be anchored at m. The decoder collapses the transaction into one merge
 * command and gives m no position, which leaves such a later merge stuck.
 * `decodeTx` applies the specification's own rule for a split in the
 * `sliceFollow` meaning (the prefix keeps the end slot `instance/^m`, and the
 * moved part is headed by the marker slot `instance/m`): a demo merge decodes
 * to `mark instance start m`, which places the invisible slots
 * `instance/^m`, `instance/m` immediately after `instance/start`, followed
 * by the merge command, which moves all of them with the source. The
 * corrected merge emits no split and decodes unchanged.
 *
 * Views. A view lists the alive blocks as `{ id, chars: [{ text, bold }] }`.
 * Block identities are kept for reports and for the adapter, but views are
 * compared on what a reader sees: the text of each block in order, and with
 * `format` also each character's bold flag. `normalise` drops identities,
 * giving the block lists of `experiments/notion-oracle/positional-spec.mjs`,
 * whose `request` is the local meaning of a request on the issuer's view.
 */
import { IdentitySpec, SpecStuck, decode, replayOrder } from '../../../experiments/notion-merge-design/identity-spec.mjs';
import { request as positionalRequest } from '../../../experiments/notion-oracle/positional-spec.mjs';

export { decode, replayOrder, SpecStuck };
export const MODE = { merge: 'sliceFollow' };

/** The identity specification with a bold flag per slot. */
export class FormattedIdentitySpec extends IdentitySpec {
  step(command) {
    if (command.kind === 'mark') {
      const origin = `${command.instance}/${command.origin}`;
      const block = this.owner(origin);
      if (!block) throw new SpecStuck('merge split origin has no owner', command);
      const at = block.slots.findIndex((x) => x.address === origin);
      block.slots.splice(
        at + 1,
        0,
        { address: `${command.instance}/^${command.marker}`, value: '', visible: false },
        { address: `${command.instance}/${command.marker}`, value: '', visible: false },
      );
      return this;
    }
    if (command.kind !== 'bold') return super.step(command);
    const targets = new Set(command.addresses);
    for (const b of this.blocks) for (const s of b.slots) if (targets.has(s.address)) s.bold = command.value;
    return this;
  }
}

/** The command group of a transaction (see above). */
export function decodeTx(tx) {
  const commands = decode(tx);
  const move = tx.operations.find((o) => o.command === 'moveTextSlice');
  const split = tx.operations.find((o) => o.command === 'splitText');
  if (move && split) {
    const a = split.args;
    const origin = typeof a.originId === 'string' ? a.originId : `${a.originId.sessionId}:${a.originId.counter}`;
    commands.unshift({ kind: 'mark', instance: a.textInstanceId, origin, marker: `${a.id.sessionId}:${a.id.counter}` });
  }
  return commands;
}

/** The address of a character in the specification: `instance/session:counter`. */
export const addressOf = (instance, id) => `${instance}/${id.sessionId}:${id.counter}`;

/** Block lists of a view or of normalised blocks: arrays of { text, bold }. */
export const blocksOf = (v) => v.map((b) => (Array.isArray(b) ? b : b.chars).map((c) => ({ text: c.text, bold: !!c.bold })));
export const textsOf = (v) => blocksOf(v).map((cs) => cs.map((c) => c.text).join(''));

/** One specification state from a list of command groups, in order. */
export function foldGroups(groups, mode = MODE) {
  const s = new FormattedIdentitySpec(mode);
  for (const g of groups) s.group(g);
  return s;
}

/**
 * The specification for documents seeded by `seedTransactions` (honest
 * transactions of a seed session, folded in replay order into the initial
 * state). Operations are `{ tx, commands }`. With `format`, views are compared
 * with bold flags.
 */
export function specFor({ seedTransactions, format = false, mode = MODE }) {
  const initial = foldGroups(replayOrder(seedTransactions).map(decodeTx), mode);
  const key = format ? (v) => JSON.stringify(blocksOf(v).map((cs) => cs.map((c) => [c.text, c.bold]))) : (v) => JSON.stringify(textsOf(v));
  return {
    format,
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
    localEdit: (view, request) => positionalRequest(blocksOf(view), request),
  };
}
