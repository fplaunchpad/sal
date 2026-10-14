#!/usr/bin/env sh
set -eu

# Isolated research gate. Keep the historical cache/structured controls and add
# the exact compiled indexed core; no production catalogue/ledger is changed.
check_dir=$(mktemp -d "${TMPDIR:-/tmp}/notion-incremental-check.XXXXXX")
printf 'Incremental Notion check logs: %s\n' "$check_dir"

python3 - "$check_dir" <<'PY'
import pathlib, re, subprocess, sys
out = pathlib.Path(sys.argv[1])
instances = pathlib.Path('Sal/MRDTs/Instances')
paths = sorted(set(instances.glob('NotionCoreStructural*.lean')) |
               set(instances.glob('NotionCoreIncremental*.lean')) |
               set(instances.glob('NotionCoreRuntime*.lean')))
required = instances / 'NotionCoreRuntimeHonestProgress.lean'
if required not in paths:
    raise SystemExit('Missing honest native receipt/merge progress endpoint')
modules = ['.'.join(p.with_suffix('').parts) for p in paths]
# Source checks also cover optional investigations built by this gate.
for path in paths:
    source = path.read_text()
    if re.search(r'\bsorry\b|\bsorryAx\b|\bnative_decide\b|^\s*(?:private\s+)?axiom\b', source, re.M):
        raise SystemExit(f'Unproved/custom-axiom/non-kernel proof remains: {path}')
    if re.search(r'Sal\.ConditionedMRDTs|LegacyBridge', source):
        raise SystemExit(f'Historical framework dependency remains: {path}')

# Re-run every module's maintained axiom endpoint in a fresh import-only audit,
# so cached Lake output cannot conceal an unprinted custom dependency.
endpoints = []
for path in paths:
    namespaces = []
    for line in path.read_text().splitlines():
        namespace = re.fullmatch(r'namespace\s+(\S+)\s*', line.strip())
        ending = re.fullmatch(r'end(?:\s+\S+)?\s*', line.strip())
        printed = re.fullmatch(r'#print\s+axioms\s+(\S+)\s*', line.strip())
        if namespace:
            namespaces.append(namespace[1])
        elif ending and namespaces:
            namespaces.pop()
        elif printed:
            name = printed[1]
            endpoints.append(name if name.startswith('Sal.') else '.'.join(namespaces + [name]))
endpoints = sorted(set(endpoints))
required_endpoints = {
    'Sal.MRDTs.Instances.NotionCoreStructuralMRDT.' + name
    for name in ('renderer', 'fiveVCs', 'specification_ra', 'operational_reach', 'registered_query')
} | {
    'Sal.MRDTs.Instances.NotionCoreRuntimeQuery.observe_correct',
    'Sal.MRDTs.Instances.NotionCoreRuntimeAdapter.represents',
    'Sal.MRDTs.Instances.NotionCoreRuntimeAdapter.observeState_correct',
    'Sal.MRDTs.Instances.NotionCoreRuntimeTheorem.registered_query',
    'Sal.MRDTs.Instances.NotionCoreRuntimeHonestProgress.receive_honest',
    'Sal.MRDTs.Instances.NotionCoreRuntimeHonestProgress.merge_honest',
    'Sal.MRDTs.Instances.NotionCoreRuntimeHonestProgress.receiveMany_honest',
    'Sal.MRDTs.Instances.NotionCoreRuntimeEndToEnd.load_closed_version',
}
missing = required_endpoints - set(endpoints)
if missing:
    raise SystemExit(f'Missing maintained headline axiom endpoints: {sorted(missing)}')
(out / 'axioms.lean').write_text('\n'.join('import ' + m for m in modules) + '\n' +
                               '\n'.join('#print axioms ' + e for e in endpoints) + '\n')
(out / 'endpoints.txt').write_text('\n'.join(endpoints) + '\n')
with (out / 'build.log').open('w') as log:
    result = subprocess.run(['lake', 'build', *modules, 'notion_core_runtime'], stdout=log, stderr=subprocess.STDOUT)
if result.returncode:
    print('\n'.join((out / 'build.log').read_text().splitlines()[-60:]), file=sys.stderr)
    raise SystemExit(result.returncode)
print((out / 'build.log').read_text().splitlines()[-1])
with (out / 'axioms.log').open('w') as log:
    result = subprocess.run(['lake', 'env', 'lean', str(out / 'axioms.lean')], stdout=log, stderr=subprocess.STDOUT)
if result.returncode:
    print((out / 'axioms.log').read_text(), file=sys.stderr)
    raise SystemExit(result.returncode)
report = (out / 'axioms.log').read_text()
found = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", report)
if {name for name, _ in found} != set(endpoints):
    raise SystemExit('Axiom audit did not report every maintained endpoint')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in found:
    unexpected = {a.strip() for a in axioms.split(',') if a.strip()} - allowed
    if unexpected:
        raise SystemExit(f'Nonstandard axioms for {name}: {sorted(unexpected)}')
print(f'Axiom audit passed: {len(endpoints)} endpoints, standard axioms only.')
PY

# Both checks fetch unchanged hash-pinned source modules and therefore need
# network access. These are bounded regression smokes, not new performance data.
python3 experiments/notion-incremental/run.py --cases 10 --sizes 16 --repeats 1 \
  --output "$check_dir/structured-smoke.jsonl"
python3 experiments/notion-incremental/run.py --native-binary .lake/build/bin/notion_core_runtime \
  --cases 10 --sizes 16 --repeats 1 --output "$check_dir/native-smoke.jsonl"

python3 - "$check_dir" <<'PY'
import json, pathlib, sys
out = pathlib.Path(sys.argv[1])
def records(name):
    return [json.loads(line) for line in (out / name).read_text().splitlines() if line.strip()]
structured = records('structured-smoke.jsonl')
native = records('native-smoke.jsonl')
correctness = [r for r in structured if r.get('kind') == 'correctness']
if len(correctness) != 1:
    raise SystemExit('Structured smoke did not produce its correctness summary')
native_correctness = [r for r in native if r.get('kind') == 'native-correctness']
if len(native_correctness) != 1 or native_correctness[0]['cases'] != 20 or native_correctness[0]['checks'] <= 0:
    raise SystemExit('Native smoke did not complete both workload families')
metadata = [r for r in native if r.get('kind') == 'native-metadata-control']
if len(metadata) != 1 or not metadata[0]['gapNotTransmitted'] or not metadata[0]['cloneDoesNotCopyGap']:
    raise SystemExit('Native fork/merge allocator-gap regression failed')
atomic = [r for r in native if r.get('kind') == 'native-atomic-error-control']
if len(atomic) != 1 or not all(atomic[0][key] for key in
    ('receiveBatchRejected', 'mergeRejected', 'statsUnchanged', 'viewUnchanged')):
    raise SystemExit('Native atomic receive/merge rollback regression failed')
fixtures = [r for r in native if r.get('kind') == 'native-wire-fixtures']
if len(fixtures) != 1 or not all(fixtures[0]['controls'].values()):
    raise SystemExit('Native typed wire boundary fixture controls failed')
print(f"Native regression passed: {native_correctness[0]['cases']} cases, "
      f"{native_correctness[0]['checks']} query comparisons; typed fixtures, atomic rollback and fork/merge gap controls.")
print(f'Incremental Notion research gate passed. Logs: {out}')
PY
