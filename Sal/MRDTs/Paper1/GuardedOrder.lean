import Sal.MRDTs.Paper1.GuardedReplay

/-! Acyclicity and finite enumeration of the semantic paper order.
Concurrent policy edges are terminal: the absorber excludes causal successors,
and guarded no-chain excludes policy successors. -/
namespace Sal.MRDTs.Paper1.GuardedReplay
open Foundation Classical

variable {D : UpdateSig} {P : OperationPolicy D.AppOp}

/-- Timestamp guards do not weaken payload no-chain: payloads can be wrapped
with three fresh timestamps. This uses no noncommutation exactness premise. -/
theorem Laws.payload_no_chain (L : Laws D P) (a b c : D.AppOp) :
    ¬ (P.before a b ∧ P.before b c) := by
  exact L.no_chain (0, 0, a) (1, 0, b) (2, 0, c) (by simp [distinctOps, Op.time]) (by simp [distinctOps, Op.time])

def supportedOrder (P : OperationPolicy D.AppOp) (C : ReplayContext D)
    (E : Set (Op D.AppOp)) (a b : Op D.AppOp) : Prop :=
  a ∈ E ∧ b ∈ E ∧ paperOrder P C E a b

private theorem concurrent_terminal (L : Laws D P)
    {C : ReplayContext D} {E : Set (Op D.AppOp)} {a b : Op D.AppOp}
    (h : ¬ C.vis a b ∧ ¬ C.vis b a ∧ P.before a.op b.op ∧
      ¬ ∃ c ∈ E, C.vis b c ∧ ¬ D.commutes b c) :
    ∀ c, ¬ supportedOrder P C E b c := by
  intro c hc
  have hcE := hc.2.1
  rcases hc.2.2 with hc | hc
  · exact h.2.2.2 ⟨c, hcE, hc⟩
  · exact L.payload_no_chain a.op b.op c.op ⟨h.2.2.1, hc.2.2.1⟩

/-- Paths have a causal prefix and at most one terminal concurrent edge. -/
private theorem path_causal_or_terminal (L : Laws D P)
    {C : ReplayContext D} {E : Set (Op D.AppOp)}
    (htrans : ∀ {a b c}, C.vis a b → C.vis b c → C.vis a c)
    {a b : Op D.AppOp} (h : Relation.TransGen (supportedOrder P C E) a b) :
    C.vis a b ∨ ∀ c, ¬ supportedOrder P C E b c := by
  induction h with
  | single h =>
    rcases h.2.2 with hv | hp
    · exact Or.inl hv.1
    · exact Or.inr (concurrent_terminal L hp)
  | @tail b c _ hbc ih =>
    rcases ih with hab | ht
    · rcases hbc.2.2 with hv | hp
      · exact Or.inl (htrans hab hv.1)
      · exact Or.inr (concurrent_terminal L hp)
    · exact False.elim (ht c hbc)

theorem paperOrder_acyclic (L : Laws D P)
    {C : ReplayContext D} {E : Set (Op D.AppOp)}
    (htrans : ∀ {a b c}, C.vis a b → C.vis b c → C.vis a c)
    (hirrefl : ∀ a, ¬ C.vis a a) (a : Op D.AppOp) :
    ¬ Relation.TransGen (supportedOrder P C E) a a := by
  intro h
  rcases path_causal_or_terminal L htrans h with hv | ht
  · exact hirrefl a hv
  · rcases Relation.TransGen.head'_iff.mp h with ⟨b, hab, _⟩
    exact ht b hab

/-- Every finite supported event set admits a linear paper-order enumeration.
The support premise records the intended context; acyclicity itself follows
from visibility and guarded no-chain alone. -/
theorem exists_paperOrder_enumeration (L : Laws D P)
    {C : ReplayContext D} {E : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (htrans : ∀ {a b c}, C.vis a b → C.vis b c → C.vis a c)
    (hirrefl : ∀ a, ¬ C.vis a a)
    (_hsupport : E ⊆ C.events) (hperm : listPermOf l E) :
    ∃ ρ, listPermOf ρ E ∧ respects ρ (paperOrder P C E) := by
  obtain ⟨ρ, hp, hr⟩ := exists_respecting_perm
    (R := Relation.TransGen (supportedOrder P C E))
    (fun hab hbc => hab.trans hbc) (paperOrder_acyclic L htrans hirrefl) l
  have hpE : listPermOf ρ E :=
    ⟨hp.nodup hperm.1, fun a => (hp.mem_iff (a := a)).symm.trans (hperm.2 a)⟩
  refine ⟨ρ, hpE, ?_⟩
  apply List.Pairwise.imp_of_mem ?_ hr
  intro a b ha hb h hba
  exact h (.single ⟨(hpE.2 b).mp hb, (hpE.2 a).mp ha, hba⟩)

end Sal.MRDTs.Paper1.GuardedReplay
