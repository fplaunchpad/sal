import LeanProofs1.Implementations.TreeMove.Coherence

/-!
# Tree move: the implementation and the specification

The two definitions the obligations are stated about, and nothing else.
`D_type = < Sigma, sigma0, do, merge, query, rc >` is the tuple of Section 3,
with `rc` empty; `historySpec` is the `Spec` of Section 4, a plain tree with
no undo log; `issuance` is the guard `G`.

```
  Sigma  = { s = (Q, T) | s = C(events(s)) }     the coherent states
  sigma0 = ([], T0)
  e(s)   = receive(s, e)
  merge(l, a, b) = foldl(receive, a, events(b))
  q((Q,T), ()) = visible(T)
```

`Sigma` is the **coherent** state space, exactly as the appendix defines it.
That is what makes `rc` empty a theorem here rather than a hedge: the
appendix's "complete deliveries commute on the coherent state space" is
`VCs.lean`'s `all_commute`, over the whole of `Sigma`.

No proof appears in this file. The two coherence facts `step` and
`mergeState` cite are proved in `Coherence.lean`, and every obligation is in
`VCs.lean`.
-/

namespace LeanProofs1.Implementations.TreeMove

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- `type = < O_type, Q_type, Val_type >`. The query returns the visible
tree. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := Tree

/-- `Sigma`: the coherent states, as the appendix's `Sigma` is defined. -/
abbrev St := {s : Raw // Coherent s}

/-- `do(sigma, t, r, o)`: deliver the move, suppressing a duplicate. -/
noncomputable def step (s : St) (e : Event) : St :=
  ⟨receive s.1 e.op, receive_coherent s.2 e.op⟩

/-- `merge(l, a, b)`: deliver the other branch's log. The ancestor is
ignored. -/
noncomputable def mergeState (_l a b : St) : St :=
  ⟨mergeRaw a.1 b.1, mergeRaw_coherent a.2 b.1⟩

/-- The tree the client sees, with the trash branch hidden. -/
noncomputable def view (s : St) : Tree := visible s.1.2

/-- `rc` is empty. For this row that is a claim about the coherent state
space, and `VCs.lean` proves it. -/
def rc : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`.

Reducible so that `D.Sigma` unfolds to `St` during instance search. -/
@[reducible] noncomputable def D : Impl type where
  Sigma := St
  decSigma := fun _ _ => Classical.propDecidable _
  sigma0 := ⟨([], T0), coherent_init⟩
  do_ := step
  merge := mergeState
  query s _ := view s
  rc := rc

/-! ## `Spec`

The independent state is a tree together with an update prefix used for
admission. The specification tests the resulting graph directly: it has no
undo log and does not call the implementation's ancestor test. Its states
remain acyclic from `T0`.
-/

/-- `Acyclic(T)`. -/
def Acyclic (T : Tree) : Prop := ∀ x, ¬ Path T x x

open Classical in
/-- `move_spec(T, o)`: the ordinary in-place move, kept only when the
resulting graph is acyclic. A cycle-rejected move still extends the
prefix. -/
noncomputable def moveSpec (T : Tree) (o : AppOp) : Tree :=
  let T' := Function.update T o.child (some (o.parent, o.mdata))
  if Acyclic T' then T' else T

/-- `Legal(h)`: distinct moves in nondecreasing key order, none naming the
root or the trash as its child. -/
def Legal (h : List AppOp) : Prop :=
  h.Nodup ∧ h.Pairwise (fun a b => key a ≤ key b)
    ∧ ∀ o ∈ h, o.child ≠ 0 ∧ o.child ≠ 1

/-- `Spec`: a plain tree, with no log and no ancestor test. -/
noncomputable def specMachine :
    HistoryMachine type.OType type.QType type.ValType where
  State := List AppOp × Tree
  initial := ([], T0)
  transition s label t :=
    match label with
    | .update o => Legal (s.1 ++ [o]) ∧ t = (s.1 ++ [o], moveSpec s.2 o)
    | .query _ answer => t = s ∧ answer = visible s.2

/-- `Spec` as a history language. -/
noncomputable def historySpec : Soundness.Spec type := specMachine.toSpec

/-! ## Issuance -/

/-- Issuance: the wrapper reserves root and trash as children and requires a
fresh event identifier. A destination need not exist or be visible, and a
hidden child may be moved out of trash; there is no additional visibility
guard. The first two conjuncts are the deviation `Raw.lean` documents: they
pin the operation's copy of the key to the issuing event's own, so that on
every certified execution the key is the appendix's `k(e)`. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun e s =>
    e.op.time = e.time ∧ e.op.rep = e.rep
      ∧ (∀ o ∈ ops (s : St).1, (o.time, o.rep) ≠ (e.time, e.rep))
      ∧ e.op.child ≠ 0 ∧ e.op.child ≠ 1

end LeanProofs1.Implementations.TreeMove
