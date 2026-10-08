#!/usr/bin/env python3
"""Rebuild the complete expanded-VC dependency graph and audit both bundles.

Run from any directory. Production dependencies must already be lake-built.
No old datatype VC, Join, or state/history invariant proof is permitted in the
transitive theorem dependency closure, even if its module is imported.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

from run_inductive import forbidden_dependency, STANDARD_AXIOMS

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = HERE / 'results'
LIB = ROOT / '.lake/build/lib/lean'
order = []
seen = set()


def visit(name):
    if name in seen:
        return
    seen.add(name)
    src = HERE / (name + '.lean')
    for dependency in re.findall(r'^import (\S+)', src.read_text(), re.M):
        if (HERE / (dependency + '.lean')).exists():
            visit(dependency)
    order.append(name)


visit('ExpandedVCs')
OUT.mkdir(exist_ok=True)
build_log = []
for name in order:
    print('Checking', name, flush=True)
    result = subprocess.run(
        ['lake', 'env', 'lean', '-o', str(LIB / (name + '.olean')),
         str(HERE / (name + '.lean'))], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    build_log.append(f'## {name}\n{result.stdout}')
    (OUT / 'expansion-build.log').write_text('\n'.join(build_log))
    if result.returncode:
        raise SystemExit(result.stdout)

theorems = ['NeemExpansion.Exact.expanded_vcs', 'NeemExpansion.Efficient.expanded_vcs']
audit = 'import ExpandedVCs\n' + (HERE / 'Audit.lean').read_text()
audit += '\n' + '\n'.join('audit_vc ' + t for t in theorems) + '\n'
with tempfile.TemporaryDirectory(prefix='sal-expansion-audit-') as tmp:
    path = Path(tmp) / 'AuditExpansion.lean'
    path.write_text(audit)
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
log = result.stdout
(OUT / 'expansion-audit.log').write_text(log)
assert result.returncode == 0, log
assert log.count('VC_AUDIT_COMPLETE') == len(theorems), log
axiom_groups = re.findall(r'VC_AXIOMS \[(.*?)\]', log)
assert len(axiom_groups) == len(theorems), log
assert all(set(a.split(', ')) <= STANDARD_AXIOMS for a in axiom_groups), axiom_groups
deps = sorted(set(re.findall(r'VC_DEP (\S+)', log)))
forbidden = [d for d in deps if forbidden_dependency(d)]
report = {
    'theorems': theorems,
    'build_order': order,
    'source_sha256': {n + '.lean': hashlib.sha256((HERE / (n + '.lean')).read_bytes()).hexdigest()
                      for n in order},
    'axioms': axiom_groups,
    'dependencies': deps,
    'forbidden_dependencies': forbidden,
}
(OUT / 'expansion-audit.json').write_text(json.dumps(report, indent=2) + '\n')
assert not forbidden, forbidden
print('Both unchanged five-VC bundles rebuilt and dependency-audited.', flush=True)
