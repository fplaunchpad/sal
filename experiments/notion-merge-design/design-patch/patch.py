#!/usr/bin/env python3
"""Source-level patches that turn the pinned demo into the merge design and its controls.

Each hunk is an exact replacement of a text that must occur exactly once in the
hash-pinned module, so a changed upstream source fails loudly instead of being
patched approximately. Variants:

  demo         the unmodified pinned demo.
  design       the design: one mergeBlock operation, derived liveness, merged
               blocks kept in the display order. The source tree is attached
               under the last node of the tree holding the target's root (the
               target's own tree, or its absorber's); a no-op when the source
               is not alive or that tree is the source's own.
  skip         the earlier rule: a no-op whenever the target is not alive.
  no-source-check
               the design without the source liveness check: a merged source
               is detached from its host and attached under the holder's last
               node; if the holder is then the source itself it is restored.
  remove-independently
               the design plus a removeBlock operation in every merge
               transaction; removal hides the source whether or not the
               attachment happened.
  skip-remove-independently
               the skip rule plus the independent removeBlock operation.
  design-order-splice
               the design, except that a merge also deletes the source from
               the display order (the demo's removeBlock bookkeeping), so a
               later block created after the source goes to the front.

Run `python3 patch.py --emit DIR --cache CACHE --variant design` to write the
patched modules for inspection.
"""
import argparse, hashlib, json
from pathlib import Path

VARIANTS = ['demo', 'design', 'skip', 'no-source-check', 'remove-independently', 'skip-remove-independently', 'design-order-splice']

# ---------------------------------------------------------------- document.js

BLOCK_RECORD_OLD = '''		this.type = "text"
		this.alive = true
		this.title = createEmptyTextSliceTree(titleTextInstanceId)
	}
}'''

BLOCK_RECORD_DESIGN = '''		this.type = "text"
		this.title = createEmptyTextSliceTree(titleTextInstanceId)
	}

	// Liveness is derived: a block is alive iff its title root has no parent.
	get alive() {
		return !this.title.parent
	}
}'''

BLOCK_RECORD_REMOVE = '''		this.type = "text"
		this.removed = false
		this.title = createEmptyTextSliceTree(titleTextInstanceId)
	}

	// Control: liveness also requires that no removeBlock operation hid the block.
	get alive() {
		return !this.title.parent && !this.removed
	}
}'''

RECREATE_OLD = '''			existing.alive = true
			return'''
RECREATE_NEW = '''			return'''

APPLY_REMOVE_OLD = '''			case "removeBlock":
				this.#removeBlock(operation.args.blockId)
				break'''
APPLY_MERGE = '''			case "mergeBlock":
				this.#mergeBlock(operation.args)
				break'''
APPLY_MERGE_AND_REMOVE = APPLY_MERGE + '''
			case "removeBlock":
				this.#removeBlock(operation.args.blockId)
				break'''

REMOVE_BLOCK_OLD = '''	#removeBlock(blockId) {
		const block = this.blocks.get(blockId)
		if (!block) return
		block.alive = false
		const index = this.blockOrder.indexOf(blockId)
		if (index >= 0) this.blockOrder.splice(index, 1)
	}'''

MERGE_ABSORB = '''	#mergeBlock({ sourceBlockId, targetBlockId }) {
		const source = this.blocks.get(sourceBlockId)
		const target = this.blocks.get(targetBlockId)
		if (!source || !target || !source.alive) return
		let holder = target.title
		while (holder.parent) holder = holder.parent
		if (holder === source.title) return
		let last = holder
		for (const node of iterateTextSliceTree(holder)) last = node
		last.appendChild(source.title)
	}'''

MERGE_SKIP = '''	#mergeBlock({ sourceBlockId, targetBlockId }) {
		const source = this.blocks.get(sourceBlockId)
		const target = this.blocks.get(targetBlockId)
		if (!source || !target || source === target) return
		if (!source.alive || !target.alive) return
		let last = target.title
		for (const node of iterateTextSliceTree(target.title)) last = node
		last.appendChild(source.title)
	}'''

MERGE_NO_SOURCE_CHECK = '''	#mergeBlock({ sourceBlockId, targetBlockId }) {
		const source = this.blocks.get(sourceBlockId)
		const target = this.blocks.get(targetBlockId)
		if (!source || !target) return
		const originalParent = source.title.parent
		source.title.detachFromParent()
		let holder = target.title
		while (holder.parent) holder = holder.parent
		if (holder === source.title) {
			if (originalParent) originalParent.appendChild(source.title)
			return
		}
		let last = holder
		for (const node of iterateTextSliceTree(holder)) last = node
		last.appendChild(source.title)
	}'''

MERGE_ORDER_SPLICE = MERGE_ABSORB.replace('''		last.appendChild(source.title)
	}''', '''		last.appendChild(source.title)
		const index = this.blockOrder.indexOf(sourceBlockId)
		if (index >= 0) this.blockOrder.splice(index, 1)
	}''')
assert MERGE_ORDER_SPLICE != MERGE_ABSORB

REMOVE_BLOCK_FLAG = '''	#removeBlock(blockId) {
		const block = this.blocks.get(blockId)
		if (!block) return
		block.removed = true
	}'''

ALL_NODES_OLD = '''		for (const block of this.blocks.values()) {
			for (const node of iterateTextSliceTree(block.title)) result.push({ block, node })
		}'''
ALL_NODES_NEW = '''		for (const block of this.blocks.values()) {
			if (block.title.parent) continue
			for (const node of iterateTextSliceTree(block.title)) result.push({ block, node })
		}'''

INVARIANT_OLD = '''		for (const block of this.blocks.values()) {
			if (block.title.parent) throw new Error("A block title root cannot have a parent")
			for (const node of iterateTextSliceTree(block.title)) {'''
INVARIANT_NEW = '''		for (const block of this.blocks.values()) {
			if (block.title.parent) continue
			for (const node of iterateTextSliceTree(block.title)) {'''

INVARIANT_TAIL_OLD = '''		for (const instance of this.instances.values()) {
			const expected = instance.rga.visibleItems()'''
INVARIANT_TAIL_NEW = '''		for (const block of this.blocks.values()) {
			if (!seenNodes.has(block.title)) throw new Error("A merged block title is not in any root tree")
		}
		for (const instance of this.instances.values()) {
			const expected = instance.rga.visibleItems()'''

# ----------------------------------------------------------------- replica.js

MERGE_REQUEST_OLD = '''		const source = blocks[sourceIndex]
		const target = blocks[sourceIndex - 1]
		const sourceRootSlice = source.title.textSlice
		let targetLastNode = target.title
		for (const node of iterateTextSliceTree(target.title)) targetLastNode = node

		this.clock.reserve(20)
		const splitId = this.clock.reserve()
		const transaction = {
			id: splitId,
			operations: [
				textOperation("splitText", source.id, {
					textInstanceId: sourceRootSlice.textInstanceId,
					searchLabel: sourceRootSlice.searchLabel,
					id: splitId,
					originId: sourceRootSlice.startItemId,
				}),
				textOperation("moveTextSlice", source.id, {
					textInstanceId: sourceRootSlice.textInstanceId,
					sourceSearchLabel: sourceRootSlice.searchLabel,
					textSliceStartItemId: splitId,
					targetBlockId: target.id,
					targetTextInstanceId: targetLastNode.textSlice.textInstanceId,
					targetSearchLabel: targetLastNode.textSlice.searchLabel,
					targetTextSliceEndItemId: targetLastNode.textSlice.endItemId,
					isMerge: true,
				}),
				{
					command: "removeBlock",
					pointer: pointer(source.id),
					path: [],
					args: { blockId: source.id },
				},
			],
		}'''

MERGE_OPERATION = '''				{
					command: "mergeBlock",
					pointer: pointer(source.id),
					path: [],
					args: { sourceBlockId: source.id, targetBlockId: target.id },
				},'''
REMOVE_OPERATION = '''
				{
					command: "removeBlock",
					pointer: pointer(source.id),
					path: [],
					args: { blockId: source.id },
				},'''

def merge_request(with_remove):
    return '''		const source = blocks[sourceIndex]
		const target = blocks[sourceIndex - 1]
		const id = this.clock.reserve()
		const transaction = {
			id,
			operations: [
''' + MERGE_OPERATION + (REMOVE_OPERATION if with_remove else '') + '''
			],
		}'''

SUMMARY_OLD = '''				case "removeBlock":
					return `remove ${blockId(operation.args.blockId)}`'''
SUMMARY_NEW = SUMMARY_OLD + '''
				case "mergeBlock":
					return `merge ${blockId(operation.args.sourceBlockId)} into ${blockId(operation.args.targetBlockId)}`'''


def hunks(variant):
    if variant == 'demo':
        return {}
    remove = variant.endswith('remove-independently')
    merge = {'skip': MERGE_SKIP, 'skip-remove-independently': MERGE_SKIP, 'no-source-check': MERGE_NO_SOURCE_CHECK,
             'design-order-splice': MERGE_ORDER_SPLICE}.get(variant, MERGE_ABSORB)
    document = [
        (BLOCK_RECORD_OLD, BLOCK_RECORD_REMOVE if remove else BLOCK_RECORD_DESIGN),
        (RECREATE_OLD, RECREATE_NEW),
        (APPLY_REMOVE_OLD, APPLY_MERGE_AND_REMOVE if remove else APPLY_MERGE),
        (REMOVE_BLOCK_OLD, merge + ('\n\n' + REMOVE_BLOCK_FLAG if remove else '')),
        (ALL_NODES_OLD, ALL_NODES_NEW),
        (INVARIANT_OLD, INVARIANT_NEW),
        (INVARIANT_TAIL_OLD, INVARIANT_TAIL_NEW),
    ]
    replica = [
        (MERGE_REQUEST_OLD, merge_request(remove)),
        (SUMMARY_OLD, SUMMARY_NEW),
    ]
    return {'document.js': document, 'replica.js': replica}


def apply(variant, sources):
    """Return a copy of `sources` (file name -> text) patched for `variant`."""
    if variant not in VARIANTS:
        raise ValueError('unknown variant ' + variant)
    out = dict(sources)
    for name, edits in hunks(variant).items():
        text = out[name]
        for old, new in edits:
            count = text.count(old)
            if count != 1:
                raise ValueError(f'{name}: patch anchor occurs {count} times, expected once:\n{old[:120]}')
            text = text.replace(old, new)
        out[name] = text
    return out


def load_pinned(cache, manifest_path):
    manifest = json.loads(Path(manifest_path).read_text())
    sources = {}
    for m in manifest['modules']:
        data = (Path(cache) / m['file']).read_bytes()
        if hashlib.sha256(data).hexdigest() != m['sha256']:
            raise ValueError('source hash mismatch: ' + m['file'])
        sources[m['file']] = data.decode('utf-8')
    return manifest, sources


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--cache', required=True, type=Path)
    p.add_argument('--emit', required=True, type=Path)
    p.add_argument('--variant', choices=VARIANTS, default='design')
    a = p.parse_args()
    here = Path(__file__).resolve().parent
    _, sources = load_pinned(a.cache, here.parent.parent / 'notion-oracle' / 'sources.json')
    a.emit.mkdir(parents=True, exist_ok=True)
    (a.emit / 'package.json').write_text('{"type":"module"}\n')
    for name, text in apply(a.variant, sources).items():
        (a.emit / name).write_text(text)
    print('Wrote', a.variant, 'modules to', a.emit)
