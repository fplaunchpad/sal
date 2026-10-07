import Sal.MRDTs.Paper1.CertifiedReplay

namespace Sal.MRDTs.Paper1.CertifiedPrefixScope
open Foundation
def represented (D : MRDTSig) (C : ReplayContext D.toUpdateSig)
    (H : Set (Op (D.AppOp))) (s : D.State) : Prop :=
  H ⊆ C.events ∧ (∀ a b, C.vis a b → b ∈ H → a ∈ H) ∧
  ∃ xs, listPermOf xs H ∧ respects xs C.vis ∧ applySeq D.toUpdateSig D.init xs = s

def scope (D : MRDTSig) (C : ReplayContext D.toUpdateSig) :
    CertifiedReplay.Scope D.toUpdateSig where
  context := C
  events := C.events
  represented := represented D C

theorem update_closed (D : MRDTSig) (C : ReplayContext D.toUpdateSig)
    (domain : ∀ a b, C.vis a b → a ∈ C.events)
    (H : Set (Op (D.AppOp))) (s : D.State) (e : Op (D.AppOp))
    (rep : represented D C H s) (ready : CertifiedReplay.Ready (scope D C) H e) :
    represented D C (insert e H) (D.update s e) := by
  rcases rep with ⟨supported,closed,xs,perm,ordered,fold⟩
  rcases ready with ⟨eligible,absent,past⟩
  refine ⟨?_,?_,xs ++ [e],?_,?_,?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact eligible
    · exact supported hx
  · intro a b vis hb
    rcases hb with rfl | hb
    · exact Or.inr (past a (domain a b vis) vis)
    · exact Or.inr (closed a b vis hb)
  · refine ⟨List.nodup_append.mpr ⟨perm.1,by simp,?_⟩,?_⟩
    · intro a ha b hb equal
      have be : b = e := List.mem_singleton.mp hb
      exact absent ((equal.trans be) ▸ ((perm.2 a).mp ha))
    · intro x
      simp only [List.mem_append,List.mem_singleton,Set.mem_insert_iff]
      rw [perm.2]
      tauto
  · apply List.pairwise_append.mpr ⟨ordered,by simp,?_⟩
    intro a ha b hb vis
    have be : b = e := List.mem_singleton.mp hb
    subst b
    exact absent (closed e a vis ((perm.2 a).mp ha))
  · simpa only [applySeq,List.foldl_append,List.foldl_cons,List.foldl_nil] using congrArg (fun s => D.update s e) fold

theorem laws (D : MRDTSig) (C : ReplayContext D.toUpdateSig)
    (unique : ∀ H s t, represented D C H s → represented D C H t → s = t) (domain : ∀ a b, C.vis a b → a ∈ C.events)
    (P : OperationPolicy (D.AppOp)) : CertifiedReplay.Laws (scope D C) P := by
  refine ⟨update_closed D C domain,?_⟩
  intro H s a b rep ha hb noAB _ _ _
  by_cases ne : a = b
  · subst b; rfl
  have ne : a ≠ b := ne
  have readyA : CertifiedReplay.Ready (scope D C) (insert b H) a :=
    ⟨ha.1,by simpa only [Set.mem_insert_iff,not_or] using And.intro ne ha.2.1,
      fun p hp vis => Or.inr (ha.2.2 p hp vis)⟩
  have readyB : CertifiedReplay.Ready (scope D C) (insert a H) b :=
    ⟨hb.1,by simpa only [Set.mem_insert_iff,not_or] using And.intro (Ne.symm ne) hb.2.1,
      fun p hp vis => Or.inr (hb.2.2 p hp vis)⟩
  have left := update_closed D C domain _ _ b (update_closed D C domain _ _ a rep ha) readyB
  have right := update_closed D C domain _ _ a (update_closed D C domain _ _ b rep hb) readyA
  exact unique _ _ _ left (by simpa only [Set.insert_comm] using right)


end Sal.MRDTs.Paper1.CertifiedPrefixScope
