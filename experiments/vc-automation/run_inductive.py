#!/usr/bin/env python3
"""Bounded, audited backend trials for equation-shaped induction leaves.

Each template has one theorem named `trial` and one standalone -- SOLVER
marker. Templates own their explicit preprocessing; this runner adds no hints.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

from run import HERE, ROOT, output

STANDARD_AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}
SOLVER_AXIOMS = {'Auto.Solver.SMT.autoSMTSorry', 'autoSMTSorry'}


def forbidden_dependency(name):
    explicit = json.loads((HERE / 'premises.json').read_text())['explicitly_forbidden']
    if name in explicit:
        return True
    if any(part in name for part in (
        'mergeVCs', 'representationJoin', 'join_at_sizes', 'causal_replay_eq',
        'local_replay_eq', 'shared_replay_eq', 'ORSet.join', 'ORSet.live_join')):
        return True
    # Certified expansions must derive history evidence afresh. Raw one-step
    # collection/list algebra remains permitted; old fold invariants do not.
    if any(part in name for part in (
        '.s_fold_mem', '.s_fold_rec_sub', '.s_fold_sorted', '.s_keys_inj_events',
        '.wellformed_supported', '.e_fold_mem', '.e_fold_rec_sub', '.e_fold_sorted')):
        return True
    if '.CertifiedRGAVCAlgebra.' in name and any(part in name for part in (
        '.provenance', '.fresh_id', '.compatible', '.sorted', '.merge_toFinset',
        '.update_toFinset')):
        return True
    if any(part in name for part in (
        '.invariants_of_mint', '.event_chain_of_mint', '.delete_birth_of_mint',
        '.CertifiedFugueVCAlgebra.', '.CertifiedFugueInvariant.',
        '.CertifiedRGACoreVC.text_membership', '.CertifiedRGACoreVC.text_mono',
        '.CertifiedRGACoreVC.normalize')):
        return True
    if any(part in name for part in (
        '.noninterleaving_of_mint', '.rawFold_records', '.projected_wf',
        '.liveFold_project', '.f_fold_mem', '.f_fold_canon', '.f_fold_sorted',
        '.CertifiedRGAFugue.unique', '.CertifiedRGAFugue.laws',
        '.CertifiedFugueVCReplay.respects_lo', '.CertifiedFugueVCReplay.unique',
        '.CertifiedFugueVCReplay.peel', '.CertifiedFugueVCReplay.replaySupply')):
        return True
    # The new route forbids datatype-specific representation invariants too.
    datatype = '.ORSet.' in name or '.EfficientORSet.' in name
    return datatype and any(part in name for part in (
        '.ConcreteRep.', '.RawReplay.', 'represents_sorted_fold',
        'mem_run_iff_live', 'live_iff_fixed_add', 'representsCanonical',
        'represents_raw_canonical', 'live_merge', 'killed_covered',
        'kills_noncomm', 'raw_noncomm_kills', 'fresh_born', 'fresh_id',
        'eqExcept_fold', 'eqExcept_step', '.Guarded.agree_',
        '.Guarded.initial_agree', '.Guarded.finish_', '.Guarded.conditional'))


def failure_stage(log, status, timed_out=False, forbidden=()):
    if status in ('checked', 'solver_only'):
        return 'complete'
    if timed_out:
        return 'timeout'
    if forbidden:
        return 'dependency_audit'
    if 'Unknown identifier' in log:
        return 'elaboration'
    if 'Reason: TIMEOUT' in log:
        return 'solver_timeout'
    if any(token in log for token in ('Reason: INCOMPLETE', 'Incomplete input', 'Malformed (prefix of) input')):
        return 'solver_response'
    if any(token in log for token in ('translateExpr:', 'translateApp:', 'Auto.LamReif',
           'Auto.Monomorphization.', 'Monomorphization failed', 'Auto.Translation.', 'cannot translate ',
           'ConstInst.ofExpr', 'not a forall', 'translateNonOpaqueType:')):
        return 'translation'
    if 'reconstruct' in log.lower():
        return 'reconstruction'
    return 'search_or_preprocessing'


def trial(template, tool, seconds, out, grind_splits=None):
    base = HERE / 'lean-auto' if tool.startswith('auto-') else HERE / 'lean-smt' if tool == 'smt' else ROOT
    env = os.environ.copy()
    env['LEAN_PATH'] = output(['lake', 'env', 'printenv', 'LEAN_PATH'], base) + ':' + output(['lake', 'env', 'printenv', 'LEAN_PATH'])
    command = [output(['lake', 'env', 'which', 'lean'], base)]
    limit = min(20, seconds)
    preamble = ''
    if tool == 'grind':
        tactic = 'grind only' if grind_splits is None else f'grind (splits := {grind_splits}) only'
    elif tool == 'smt':
        preamble = (base / 'Preamble.lean').read_text()
        tactic = f'smt +mono (timeout := some {limit}) [*]'
        command += ['--plugin=' + str(base / '.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.dylib')]
    elif tool.startswith('auto-'):
        backend = {'auto-z3': 'Z3', 'auto-cvc5': 'Cvc5', 'auto-duper': 'Duper'}[tool]
        preamble = (base / f'Preamble{backend}.lean').read_text()
        preamble += f'\nset_option auto.smt.timeout {limit}\n'
        tactic = 'auto'
        config = base / 'environment.json'
        if config.exists():
            env.update(json.loads(config.read_text()))
        env['PATH'] = '/tmp/sal-vc-auto-cvc5-dist/cvc5-macOS-arm64-static/bin:' + env['PATH']
    else:
        raise ValueError(tool)
    original = template.read_text()
    lines = original.splitlines()
    namespaces = []
    theorem_name = None
    for line in lines:
        stripped = line.strip()
        match = re.fullmatch(r'namespace ([A-Za-z0-9_.]+)', stripped)
        if match:
            namespaces.append(match.group(1))
        elif re.match(r'end(?:\s|$)', stripped) and namespaces:
            namespaces.pop()
        elif re.match(r'theorem trial(?:\s|:)', stripped):
            theorem_name = '.'.join(namespaces + ['trial'])
    if theorem_name is None:
        raise ValueError(f'{template}: missing theorem trial')
    markers = [i for i, line in enumerate(lines) if line.strip() == '-- SOLVER']
    if len(markers) != 1:
        raise ValueError(f'{template}: expected exactly one standalone -- SOLVER marker')
    index = markers[0]
    indent = lines[index][:len(lines[index]) - len(lines[index].lstrip())]
    lines[index] = indent + 'all_goals (trace "INDUCTIVE_BACKEND_INVOKED"; ' + tactic + ')'
    imports, bodies = [], []
    for part in (preamble, '\n'.join(lines)):
        imports += [line for line in part.splitlines() if line.startswith('import ')]
        bodies.append('\n'.join(line for line in part.splitlines() if not line.startswith('import ')))
    source = '\n'.join(dict.fromkeys(imports)) + '\n'
    source += (HERE / 'Audit.lean').read_text() + '\nset_option maxHeartbeats 1000000\nset_option maxRecDepth 2048\n'
    source += '\n'.join(bodies) + f'\naudit_vc {theorem_name}\n'
    stem = template.stem + '-' + tool
    path, logfile = out / (stem + '.lean'), out / (stem + '.log')
    path.write_text(source)
    start, timed_out = time.monotonic(), False
    with logfile.open('w') as stream:
        process = subprocess.Popen(command + [str(path)], cwd=base, env=env, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            code = process.wait()
    log = logfile.read_text()
    values = lambda tag: [line.split(tag, 1)[1].strip() for line in log.splitlines() if tag in line]
    axioms, dependencies, direct = values('VC_AXIOMS'), values('VC_DEP'), values('VC_DIRECT')
    axiom_names = {name.strip() for group in axioms for name in group.strip('[]').split(',') if name.strip()}
    unexpected = axiom_names - STANDARD_AXIOMS
    forbidden = [name for name in dependencies if forbidden_dependency(name)]
    audited = 'VC_AUDIT_COMPLETE' in log
    # An arbitrary sorry is never accepted as a solver verdict.
    status = 'timeout' if timed_out else 'failed'
    if code == 0 and audited and not forbidden:
        if not unexpected:
            status = 'checked'
        elif unexpected & SOLVER_AXIOMS and unexpected <= SOLVER_AXIOMS | {'sorryAx'}:
            status = 'solver_only'
    stage = failure_stage(log, status, timed_out, forbidden)
    row = dict(case=template.stem, tool=tool, tier='explicit_template', status=status,
               grind_splits=grind_splits if tool == 'grind' else None,
               backend_goal_calls=log.count('INDUCTIVE_BACKEND_INVOKED'),
               failure_stage=stage, returncode=code, wall_seconds=round(time.monotonic()-start, 3),
               limit_seconds=seconds, solver_limit_seconds=limit, axioms=axioms,
               unexpected_axioms=sorted(unexpected), dependencies=dependencies,
               direct_dependencies=direct, forbidden_dependencies=forbidden,
               source_sha256=hashlib.sha256(source.encode()).hexdigest(),
               template_sha256=hashlib.sha256(original.encode()).hexdigest(),
               template=str(template), source=path.name, log=logfile.name)
    (out / (stem + '.json')).write_text(json.dumps(row, indent=2) + '\n')
    print(json.dumps({key: row[key] for key in ('case', 'tool', 'status', 'failure_stage', 'wall_seconds')}), flush=True)
    return row


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('templates', nargs='+', type=Path)
    parser.add_argument('--tools', default='grind,smt,auto-z3')
    parser.add_argument('--seconds', type=int, default=30)
    parser.add_argument('--grind-splits', type=int, default=None,
                        help='Optional explicit grind case-split search bound')
    parser.add_argument('--out', type=Path, default=HERE / 'results/inductive-pilot')
    args = parser.parse_args()
    if args.seconds <= 0:
        parser.error('--seconds must be positive')
    args.out.mkdir(parents=True, exist_ok=True)
    rows = [trial(template.resolve(), tool, args.seconds, args.out.resolve(), args.grind_splits)
            for template in args.templates for tool in args.tools.split(',')]
    (args.out / 'results.json').write_text(json.dumps(rows, indent=2) + '\n')
