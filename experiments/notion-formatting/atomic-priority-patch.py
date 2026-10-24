"""Minimal shared-transaction-priority patch for temporary pinned modules."""


def replace_once(text, old, new, label):
    if text.count(old) != 1:
        raise ValueError(f'{label}: expected one match, found {text.count(old)}')
    return text.replace(old, new, 1)


def apply(sources):
    result = dict(sources)
    document = result['document.js']
    document = replace_once(document,
        'for (const operation of transaction.operations) this.#apply(operation)',
        'for (const operation of transaction.operations) this.#apply(operation, transaction.id)',
        'pass whole transaction priority')
    document = replace_once(document, '\t#apply(operation) {',
        '\t#apply(operation, transactionPriority) {', 'dispatch priority')
    document = replace_once(document, '\t\t\t\t\tid: operation.args.id,',
        '\t\t\t\t\tid: operation.args.id,\n\t\t\t\t\tpriority: transactionPriority,',
        'retain distinct ID and shared priority')
    result['document.js'] = document
    result['rich-text.js'] = replace_once(result['rich-text.js'],
        'compareOpIds(a.id, b.id)',
        'compareOpIds(a.priority ?? a.id, b.priority ?? b.id)',
        'arbitrate by shared transaction priority')
    return result
