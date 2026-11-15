import LeanProofs.Soundness.Common

/-!
# Clause 1: `pi` is a linear extension of `(E, lo^C_E)`

The convergence side of Definition 4. A version's state must be explained by
*some* enumeration of its event set that respects the replay order, and
`Metatheory/Adequacy.lean` supplies the join lemma that makes the canonical
state such an enumeration's fold.

Nothing here mentions `Spec`. The whole clause is about the order.

`paperOrder` is the vendored form of `lo^C_E`: an edge from `a` to `b` when
`a` is visible to `b` and they do not commute, or when `rc` orders them. For
the all-commuting family both disjuncts are false, so the order constrains
nothing and **every** enumeration of the event set is a linear extension.
That is the content of this file, and it is what lets those rows hand an
arbitrary replay to clause 2.
-/

namespace LeanProofs.Soundness

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {type : MRDTType} {D : Impl type}

/-- `lo^C_E` has no edges when every pair of events commutes and `rc` is
empty: the non-commuting disjunct fails by `all_commute`, the `rc` disjunct
by `rc_either`. Clause 1 is then satisfied by any enumeration. -/
theorem paperOrder_false (h : Obligations D) (C : Configuration D.toMRDTSig)
    (E : Set D.Event) (a b : D.Event) :
    ¬ paperOrder (policy D) C.replayContext E a b := by
  rintro (⟨-, hnc⟩ | ⟨-, -, hb, -⟩)
  · exact hnc (h.all_commute a b)
  · exact OrderResult.noConfusion ((h.rc_either a.op b.op).symm.trans hb)

end LeanProofs.Soundness
