"""Make backend-neutral trials without importing any preproved leaf theorem."""
from pathlib import Path
import re
root = Path(__file__).parent
s = (root / 'InductiveLeaves.lean').read_text()
prefix = s[:s.index('end Signature')] + 'end Signature\n'
out = root / 'inductive-templates'
out.mkdir(exist_ok=True)
for ns, op, step, policy in [('Exact', 'Update', 'step', 'order'), ('Efficient', 'SetOp', 'update', 'rc.order')]:
    header = prefix + f'namespace {ns}\nopen Sal.MRDTs.' + ('Paper1.ORSet' if ns == 'Exact' else 'Instances.EfficientORSet') + f'\nvariable {{α : Type}} [DecidableEq α]\ndef signature : Signature := ⟨State α, {op} α, ∅, {step}, merge, {policy}⟩\n'
    section = s.split(f'namespace {ns}\n')[1].split(f'end {ns}')[0]
    for m in re.finditer(r'theorem (\w+) : (.*?) := by\n(.*?)(?=\ntheorem |\Z)', section, re.S):
        name, goal, proof = m.groups()
        if name == 'diagonal':
            continue
        if name in ['base1', 'common1', 'comm', 'idem']:
            pol = 'order' if ns == 'Exact' else 'rc'
            proof = f'  unfold Signature.{name}\n  intros\n  dsimp [signature, Signature.Q1] at *\n  ext x\n  simp [{pol}, merge, {step}]\n'
        proof = re.sub(r' <;> grind(?: \(splits := \d+\))?', '', proof.rstrip())
        proof += '\n  all_goals\n    -- SOLVER\n'
        target = out / f'{ns}-{name}.lean'
        temp = target.with_suffix('.tmp')
        temp.write_text(header + f'theorem trial : {goal} := by\n' + proof + f'end {ns}\nend NeemExpansion\n')
        temp.replace(target)
