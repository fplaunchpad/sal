#!/usr/bin/env python3
"""Rebuild the complete expanded-VC dependency graph and audit the selected five-VC bundles.

Run from any directory. Production dependencies must already be lake-built.
No old datatype VC, Join, or state/history invariant proof is permitted in the
transitive theorem dependency closure, even if its module is imported.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile

from run_inductive import forbidden_dependency, STANDARD_AXIOMS

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = HERE / 'results'
LIB = ROOT / '.lake/build/lib/lean'
order = []
seen = set()
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--transfer', action='store_true', help='Check all Track A instances')
parser.add_argument('--certified', action='store_true', help='Also check the certified RGA-family routes')
parser.add_argument('--automated', action='store_true', help='Use reusable templates for both OR-sets, MVR and RGA in the 23-case audit')
parser.add_argument('--common', action='store_true', help='Check all 23 through the common declarative verification interface')
parser.add_argument('--all', action='store_true', help='Check all 23 current named cases')
args = parser.parse_args()
if args.common:
    # The current interface is production; all other flags retain historical
    # prototype experiments and must not recompile duplicate rule registries.
    raise SystemExit(subprocess.call([sys.executable, str(ROOT / 'scripts/verify-paper1-automation.py')], cwd=ROOT))
if args.common:
    args.automated = True
if args.automated:
    args.all = True
if args.all:
    args.transfer = args.certified = True
module = 'TransferVCs' if args.transfer else 'ExpandedVCs'
prefix = 'common' if args.common else 'automated' if args.automated else 'all' if args.all else 'certified' if args.certified else 'transfer' if args.transfer else 'expansion'


def visit(name):
    if name in seen:
        return
    seen.add(name)
    src = HERE / (name + '.lean')
    for dependency in re.findall(r'^import (\S+)', src.read_text(), re.M):
        if (HERE / (dependency + '.lean')).exists():
            visit(dependency)
    order.append(name)


visit(module)
if args.certified:
    visit('CertifiedRGAExpansion')
    visit('CertifiedExpansionControls')
    visit('CertifiedCoreExpansion')
    visit('CertifiedEmbeddedExpansion')
    visit('CertifiedFugueVCExpansion')
if args.all:
    visit('TransferGuardedCommuting')
    visit('TransferAegisSheet')
    visit('CertifiedMVRExpansion')
if args.automated:
    visit('AutomatedMVR')
    visit('AutomatedRGA')
    visit('AutomatedORSet')
    visit('AutomatedEfficientORSet')
if args.common:
    visit('CommonInstances')
    visit('AutomatedCore')
    visit('AutomatedFugue')
    visit('CommonVerificationControls')
OUT.mkdir(exist_ok=True)
build_log = []
for name in order:
    print('Checking', name, flush=True)
    result = subprocess.run(
        ['lake', 'env', 'lean', '-o', str(LIB / (name + '.olean')),
         str(HERE / (name + '.lean'))], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    build_log.append(f'## {name}\n{result.stdout}')
    (OUT / (prefix + '-build.log')).write_text('\n'.join(build_log))
    if result.returncode:
        raise SystemExit(result.stdout)

theorems = ['NeemExpansion.Exact.expanded_vcs', 'NeemExpansion.Efficient.expanded_vcs']
if args.transfer:
    theorems += ['NeemExpansion.TransferSimple.' + name for name in
                 ['gset', 'addStore', 'finiteAdd', 'counter', 'ioc', 'pn', 'booleanSet', 'booleanMap']]
    theorems += ['NeemExpansion.TransferLWW.expanded_vcs']
audit = 'import ' + module + '\n' + (HERE / 'Audit.lean').read_text()
if args.certified:
    audit = 'import CertifiedRGAExpansion\nimport CertifiedCoreExpansion\nimport CertifiedEmbeddedExpansion\nimport CertifiedFugueVCExpansion\n' + audit
    theorems += ['NeemExpansion.CertifiedRGA.expanded_vcs',
                 'NeemExpansion.TransferProduct.NativeRGA.expanded_vcs',
                 'NeemExpansion.CertifiedCore.expanded_vcs',
                 'NeemExpansion.CertifiedCore.rich_expanded_vcs',
                 'NeemExpansion.CertifiedEmbedded.expanded_vcs',
                 'NeemExpansion.CertifiedEmbeddedTransfers.anchored_queue',
                 'NeemExpansion.CertifiedEmbeddedTransfers.peritext',
                 'NeemExpansion.CertifiedFugueVCExpansion.expanded_vcs']
if args.all:
    audit = 'import TransferGuardedCommuting\nimport TransferAegisSheet\nimport CertifiedMVRExpansion\n' + audit
    theorems += ['NeemExpansion.TransferGuardedCommuting.Bounded.expanded_vcs',
                 'NeemExpansion.TransferGuardedCommuting.Tree.expanded_vcs',
                 'NeemExpansion.TransferAegisSheet.expanded_vcs',
                 'NeemExpansion.CertifiedMVR.expanded_vcs']
reference_theorems = list(theorems)
if args.automated:
    audit = 'import AutomatedMVR\nimport AutomatedRGA\nimport AutomatedORSet\nimport AutomatedEfficientORSet\n' + audit
    replacements = {
        'NeemExpansion.Exact.expanded_vcs': 'NeemExpansion.AutomatedORSet.automated_vcs',
        'NeemExpansion.Efficient.expanded_vcs': 'NeemExpansion.AutomatedEfficientORSet.automated_vcs',
        'NeemExpansion.CertifiedMVR.expanded_vcs': 'NeemExpansion.AutomatedMVR.automated_vcs',
        'NeemExpansion.CertifiedRGA.expanded_vcs': 'NeemExpansion.AutomatedRGA.Sided.automated_vcs',
        'NeemExpansion.CertifiedEmbedded.expanded_vcs': 'NeemExpansion.AutomatedRGA.Embedded.automated_vcs',
        'NeemExpansion.CertifiedEmbeddedTransfers.anchored_queue': 'NeemExpansion.AutomatedRGA.anchored_queue',
        'NeemExpansion.CertifiedEmbeddedTransfers.peritext': 'NeemExpansion.AutomatedRGA.peritext',
    }
    theorems = [replacements.get(t, t) for t in theorems]
if args.common:
    audit = 'import CommonInstances\nimport AutomatedCore\nimport AutomatedFugue\n' + audit
    common_names = ['ordinaryORSet', 'efficientORSet', 'gset', 'addStore', 'finiteAdd',
                    'counter', 'ioc', 'pn', 'booleanSet', 'booleanMap', 'lww', 'sided',
                    'nativeRGA', None, None, 'embedded', 'anchored_queue', 'peritext',
                    None, 'bounded', 'tree', 'aegis', 'mvr']
    assert len(common_names) == len(theorems)
    theorems = ['NeemExpansion.CommonInstances.' + n if n is not None else t
                for n, t in zip(common_names, theorems)]
    for i, name in {13: 'NeemExpansion.AutomatedCore.automated_vcs',
                    14: 'NeemExpansion.AutomatedCore.rich_automated_vcs',
                    18: 'NeemExpansion.AutomatedFugue.automated_vcs'}.items():
        theorems[i] = name
audit += '\n' + '\n'.join('audit_vc ' + t for t in theorems) + '\n'
audit += '\n'.join(f'audit_vc_contract {t} against {r}'
                   for t, r in zip(theorems, reference_theorems)) + '\n'
with tempfile.TemporaryDirectory(prefix='sal-expansion-audit-') as tmp:
    path = Path(tmp) / 'AuditExpansion.lean'
    path.write_text(audit)
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
log = result.stdout
(OUT / (prefix + '-audit.log')).write_text(log)
assert result.returncode == 0, log
assert log.count('VC_AUDIT_COMPLETE') == len(theorems), log
assert log.count('VC_CONTRACT_MATCH') == len(theorems), log
axiom_groups = re.findall(r'VC_AXIOMS \[(.*?)\]', log)
assert len(axiom_groups) == len(theorems), log
assert all(set(a.split(', ')) <= STANDARD_AXIOMS for a in axiom_groups), axiom_groups
deps = sorted(set(re.findall(r'VC_DEP (\S+)', log)))
forbidden = [d for d in deps if forbidden_dependency(d)]
blocks = log.split('VC_AUDIT_COMPLETE')[:-1]
experiment_dependencies = {t: sorted(set(re.findall(r'VC_EXP_DEP (\S+)', block)))
                           for t, block in zip(theorems, blocks)}
old_adapters = ('NeemExpansion.Exact.', 'NeemExpansion.Efficient.',
                'EfficientReplayAdapter.', 'CausalEventClassification.',
                'NeemExpansion.CertifiedMVR.', 'NeemExpansion.CertifiedRGA.',
                'NeemExpansion.CertifiedEmbedded.', 'NeemExpansion.CertifiedEmbeddedReplay.',
                'NeemExpansion.CertifiedSidedReplay.', 'NeemExpansion.CertifiedEmbeddedTransfers.')
if args.automated:
    for t in (theorems if args.common else replacements.values()):
        forbidden += [d for d in experiment_dependencies[t] if d.startswith(old_adapters)]
if args.common:
    for t in theorems:
        forbidden += [d for d in experiment_dependencies[t]
            if d.startswith(('NeemExpansion.CertifiedCore.', 'NeemExpansion.CertifiedFugue'))
            or d in reference_theorems or d in replacements.values()
            or d.endswith(('.expanded_vcs', '.rich_expanded_vcs'))]
controls = []
if args.common:
    control = subprocess.run([sys.executable, str(HERE / 'test_contract_audit.py')],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / 'common-contract-controls.log').write_text(control.stdout)
    assert control.returncode == 0, control.stdout
    controls = ['CommonVerificationControls.lean', 'test_contract_audit.py']
report = {
    'controls': controls,
    'theorems': theorems,
    'reference_theorems': reference_theorems,
    'contract_matches': re.findall(r'VC_CONTRACT_MATCH (\S+) (\S+)', log),
    'build_order': order,
    'source_sha256': {n + '.lean': hashlib.sha256((HERE / (n + '.lean')).read_bytes()).hexdigest()
                      for n in order},
    'axioms': axiom_groups,
    'dependencies': deps,
    'forbidden_dependencies': forbidden,
    'experiment_dependencies': experiment_dependencies,
    'declaration_sources': {t: [dict(zip(['name', 'module', 'start_line', 'end_line', 'kind'], row))
        for row in re.findall(r'VC_SOURCE (\S+) (\S+) (\d+) (\d+) (\S+)', block)]
        for t, block in zip(theorems, blocks)},
}
(OUT / (prefix + '-audit.json')).write_text(json.dumps(report, indent=2) + '\n')
assert not forbidden, forbidden
print(f'{len(theorems)} unchanged five-VC instances rebuilt and dependency-audited.', flush=True)
