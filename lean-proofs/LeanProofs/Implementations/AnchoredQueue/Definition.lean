import LeanProofs_no_spec_non_comm.Implementations.EmbeddedRGA.Coordinates

/-!
# The anchored FIFO queue: the implementation tuple

The Anchored FIFO queue row of Table 1, following Appendix
`app:dt-anchored-queue-paper-variant`. Enqueue inserts after the live tail
and dequeue removes the observed head. Coordinates retain the insertion
ancestry across merge, and descending coordinate order gives the FIFO order.

```
  Sigma = List (id, value, coordinate)      coordinate : List Bool
  sigma0 = []
  o = ins v p a        enqueue v, anchored at a with the anchor's coordinate p
  o = del x            dequeue the element with identity x
```

The state, the update and the merge are **exactly** Embedded RGA's at the
unary scheme, so the row is `EmbeddedRGA/Scheme.lean` at that scheme with
payload `Nat`, and repeats no proof. Two things are its own.

* **The query** returns the head as an optional identity and value rather
  than the payload list, which is why the core takes the query as a
  parameter.
* **Issuance is stricter.** An enqueue must anchor on the **live tail** and
  a dequeue must name the **observed head**, where the core only asks that
  the carried prefix be some live record's coordinate and the target be some
  live identity. `canIssue_core` below is the one lemma that costs anything
  here: the queue's discipline implies the core's.

`rc` is empty, as the appendix states. `Negative.lean` shows that no `rc` at
all satisfies `Laws(D_type)` for this row, and `Certificate.lean` reaches
the invariant-scoped criterion instead.

No proof appears in this file beyond `canIssue_core`, which is the bridge
the certificate needs.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.AnchoredQueue

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface
open LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

/-! ## The row's names -/

abbrev Coord := EmbeddedRGA.Coord
abbrev Record := EmbeddedRGA.Record unaryScheme Nat
abbrev AppOp := EmbeddedRGA.AppOp unaryScheme Nat
abbrev St := EmbeddedRGA.St unaryScheme Nat
abbrev gamma := EmbeddedRGA.enc
abbrev key := EmbeddedRGA.key
abbrev lexLt := EmbeddedRGA.lexLt
abbrev recKey : Record → List Nat := EmbeddedRGA.recKey
abbrev ids : St → List Nat := EmbeddedRGA.ids
abbrev insertDown : Record → St → St := EmbeddedRGA.insertDown
abbrev mergeDown : St → St → St := EmbeddedRGA.mergeDown
abbrev step : St → Op AppOp → St := EmbeddedRGA.step
abbrev mergeState : St → St → St → St := EmbeddedRGA.mergeState

/-! ## The query

The public observation is the head, not the payload list. -/

/-- `query`: the head's identity and value, if any. -/
def readHead (S : St) : Option (Nat × Nat) :=
  match S with
  | [] => none
  | z :: _ => some (z.1, z.2.1)

/-- The row's observation, as the core's query parameter. -/
def headQuery : QueryOf unaryScheme Nat where
  QType := Unit
  VType := Option (Nat × Nat)
  read := fun S _ => readHead S

/-- `type = < O_type, Q_type, Val_type >`. -/
abbrev type : MRDTType := EmbeddedRGA.type unaryScheme Nat headQuery

/-- `rc` is empty, as the appendix states. -/
abbrev rcOf : AppOp → AppOp → OrderResult := EmbeddedRGA.rcOf

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`, at an arbitrary
`rc`, because `Negative.lean` quantifies over every choice. -/
abbrev D (rc : AppOp → AppOp → OrderResult) : Impl type :=
  EmbeddedRGA.D headQuery rc

/-- The row's own tuple, with the appendix's empty `rc`. -/
abbrev Dq : Impl type := EmbeddedRGA.Dα unaryScheme Nat headQuery

/-! ## Issuance -/

/-- The live tail, as an identity and coordinate. -/
def tail? (S : St) : Option (Nat × Coord) :=
  (S.getLast?).map (fun z => (z.1, z.2.2))

/-- Issuance: an enqueue must anchor on the live tail, with a clock above
the tail identity; a dequeue must name the observed head. -/
def issuance (rc : AppOp → AppOp → OrderResult) : Issuance (D rc).toMRDTSig where
  CanIssue := fun e S =>
    match e.op with
    | .ins _ p a _ =>
        a < e.time ∧ ((S = [] ∧ a = 0 ∧ p = []) ∨ tail? S = some (a, p))
    | .del x => (readHead S).map Prod.fst = some x

/-- **The queue's discipline implies the core's.** Anchoring on the live
tail is anchoring on *a* live record, and naming the observed head is naming
*a* live identity. This is the only thing the certificate needs of the
stricter guard. -/
theorem canIssue_core (e : Op AppOp) (S : St) :
    (issuance rcOf).CanIssue e S → CoreGuard e S := by
  cases hop : e.op with
  | ins v p a g =>
    intro h
    simp only [issuance, CoreGuard, hop] at h ⊢
    refine ⟨h.1, ?_⟩
    rcases h.2 with ⟨-, ha, hp⟩ | htail
    · exact Or.inl ⟨ha, hp⟩
    · simp only [tail?, Option.map_eq_some_iff] at htail
      obtain ⟨z, hz, hzp⟩ := htail
      have hmem : z ∈ S := List.getLast?_eq_some_iff.mp hz |>.choose_spec ▸ (by
        simpa using List.mem_of_getLast?_eq_some hz)
      refine Or.inr ⟨z.2.1, ?_⟩
      have h1 : z.1 = a := congrArg Prod.fst hzp
      have h2 : z.2.2 = p := congrArg Prod.snd hzp
      rw [← h1, ← h2]
      exact hmem
  | del x =>
    intro h
    simp only [issuance, CoreGuard, hop] at h ⊢
    cases hS : S with
    | nil => rw [hS] at h; simp [readHead] at h
    | cons z Z =>
      rw [hS] at h
      simp only [readHead, Option.map_some, Option.some.injEq] at h
      simp only [EmbeddedRGA.ids, List.map_cons, List.mem_cons]
      exact Or.inl h.symm

end LeanProofs.NoSpecNonComm.Implementations.AnchoredQueue
