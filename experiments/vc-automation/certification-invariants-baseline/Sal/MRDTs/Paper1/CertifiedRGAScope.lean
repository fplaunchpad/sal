import Sal.MRDTs.Paper1.CertifiedRGAReplay
import Sal.MRDTs.Paper1.CertifiedReplay

namespace Sal.MRDTs.Paper1.CertifiedRGAScope
open Foundation Sal.EmbedRGA
namespace Embedded
open Instances.EmbedRGA
variable {α : Type} [DecidableEq α] [Inhabited α]

private theorem loOn_implies_vis (Γ : OrderedPrefixCode)
    (C : ReplayContext (E Γ α).toUpdateSig) (honest : EHonestCore Γ C)
    (H : Set (Op (EOp α))) (a b : Op (EOp α))
    (ha : a ∈ C.events) (hb : b ∈ C.events) (edge : loOn C H a b) : C.vis a b := by
  rcases edge with ⟨vis,_⟩ | ⟨noVis,_,rc,_⟩
  · exact vis
  · exact False.elim (noVis (e_vis_of_rc_of_honest honest hb ha rc))

def represented (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (H : Set (Op (EOp α))) (s : EState α) : Prop :=
  H ⊆ C.events ∧ (∀ a b, C.vis a b → b ∈ H → a ∈ H) ∧
  ∃ xs, listPermOf xs H ∧ respects xs C.vis ∧ eFold Γ xs = s

def scope (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig) :
    CertifiedReplay.Scope (E Γ α).toUpdateSig where
  context := C
  events := C.events
  represented := represented Γ C

theorem wellformed (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (honest : EHonestCore Γ C) (H : Set (Op (EOp α))) (xs : List (Op (EOp α)))
    (supported : H ⊆ C.events) (closed : ∀ a b, C.vis a b → b ∈ H → a ∈ H)
    (perm : listPermOf xs H) (ordered : respects xs C.vis) : EWf Γ xs := by
  apply e_wf_of_enum honest supported (fun a b vis _ hb => closed a b vis hb) perm
  apply ordered.imp_of_mem
  intro a b ha hb hn edge
  exact hn (loOn_implies_vis Γ C honest H b a
    (supported ((perm.2 b).mp hb)) (supported ((perm.2 a).mp ha)) edge)

theorem update_closed (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (domain : ∀ a b, C.vis a b → a ∈ C.events)
    (H : Set (Op (EOp α))) (s : EState α) (e : Op (EOp α))
    (rep : represented Γ C H s) (ready : CertifiedReplay.Ready (scope Γ C) H e) :
    represented Γ C (insert e H) (eUpdate Γ s e) := by
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
  · rw [eFold_snoc,fold]

theorem unique (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (honest : EHonestCore Γ C) (H : Set (Op (EOp α))) (s t : EState α)
    (hs : represented Γ C H s) (ht : represented Γ C H t) : s = t := by
  obtain ⟨xs,px,rx,fx⟩ := hs.2.2
  obtain ⟨ys,py,ry,fy⟩ := ht.2.2
  have wfX := wellformed Γ C honest H xs hs.1 hs.2.1 px rx
  have wfY := wellformed Γ C honest H ys ht.1 ht.2.1 py ry
  exact fx.symm.trans ((e_fold_canon Γ wfX wfY (fun o => (px.2 o).trans (py.2 o).symm)).trans fy)

/-- Original issuer honesty plus causal-prefix representation supplies the
certified replay laws with concrete equality. The paper policy is untouched. -/
theorem laws (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (honest : EHonestCore Γ C) (domain : ∀ a b, C.vis a b → a ∈ C.events)
    (P : OperationPolicy (EOp α)) : CertifiedReplay.Laws (scope Γ C) P := by
  refine ⟨update_closed Γ C domain,?_⟩
  intro H s a b rep ha hb noAB _ _ _
  by_cases ne : a = b
  · subst b; rfl
  have ne : a ≠ b := ne
  have readyA : CertifiedReplay.Ready (scope Γ C) (insert b H) a :=
    ⟨ha.1,by simpa only [Set.mem_insert_iff,not_or] using And.intro ne ha.2.1,
      fun p hp vis => Or.inr (ha.2.2 p hp vis)⟩
  have readyB : CertifiedReplay.Ready (scope Γ C) (insert a H) b :=
    ⟨hb.1,by simpa only [Set.mem_insert_iff,not_or] using And.intro (Ne.symm ne) hb.2.1,
      fun p hp vis => Or.inr (hb.2.2 p hp vis)⟩
  have left := update_closed Γ C domain _ _ b (update_closed Γ C domain _ _ a rep ha) readyB
  have right := update_closed Γ C domain _ _ a (update_closed Γ C domain _ _ b rep hb) readyA
  exact unique Γ C honest _ _ _ left (by simpa only [Set.insert_comm] using right)

end Embedded
namespace Sided
open Instances.SidedEmbedRGA

private theorem loOn_implies_vis (Γ : OrderedPrefixCode)
    (C : ReplayContext (S Γ).toUpdateSig) (honest : SHonestCore Γ C)
    (H : Set (Op (SOp))) (a b : Op (SOp))
    (ha : a ∈ C.events) (hb : b ∈ C.events) (edge : loOn C H a b) : C.vis a b := by
  rcases edge with ⟨vis,_⟩ | ⟨noVis,_,rc,_⟩
  · exact vis
  · exact False.elim (noVis (s_vis_of_rc_of_honest honest hb ha rc))

def represented (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op (SOp))) (s : SState) : Prop :=
  H ⊆ C.events ∧ (∀ a b, C.vis a b → b ∈ H → a ∈ H) ∧
  ∃ xs, listPermOf xs H ∧ respects xs C.vis ∧ sFold Γ xs = s

def scope (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig) :
    CertifiedReplay.Scope (S Γ).toUpdateSig where
  context := C
  events := C.events
  represented := represented Γ C

theorem wellformed (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) (H : Set (Op (SOp))) (xs : List (Op (SOp)))
    (supported : H ⊆ C.events) (closed : ∀ a b, C.vis a b → b ∈ H → a ∈ H)
    (perm : listPermOf xs H) (ordered : respects xs C.vis) : SWf Γ xs := by
  apply s_wf_of_enum honest supported (fun a b vis _ hb => closed a b vis hb) perm
  apply ordered.imp_of_mem
  intro a b ha hb hn edge
  exact hn (loOn_implies_vis Γ C honest H b a
    (supported ((perm.2 b).mp hb)) (supported ((perm.2 a).mp ha)) edge)

theorem update_closed (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (domain : ∀ a b, C.vis a b → a ∈ C.events)
    (H : Set (Op (SOp))) (s : SState) (e : Op (SOp))
    (rep : represented Γ C H s) (ready : CertifiedReplay.Ready (scope Γ C) H e) :
    represented Γ C (insert e H) (sUpdate Γ s e) := by
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
  · rw [sFold_snoc,fold]

theorem unique (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) (H : Set (Op (SOp))) (s t : SState)
    (hs : represented Γ C H s) (ht : represented Γ C H t) : s = t := by
  obtain ⟨xs,px,rx,fx⟩ := hs.2.2
  obtain ⟨ys,py,ry,fy⟩ := ht.2.2
  have wfX := wellformed Γ C honest H xs hs.1 hs.2.1 px rx
  have wfY := wellformed Γ C honest H ys ht.1 ht.2.1 py ry
  exact fx.symm.trans ((s_fold_canon Γ wfX wfY (fun o => (px.2 o).trans (py.2 o).symm)).trans fy)

/-- Original issuer honesty plus causal-prefix representation supplies the
certified replay laws with concrete equality. The paper policy is untouched. -/
theorem laws (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) (domain : ∀ a b, C.vis a b → a ∈ C.events)
    (P : OperationPolicy (SOp)) : CertifiedReplay.Laws (scope Γ C) P := by
  refine ⟨update_closed Γ C domain,?_⟩
  intro H s a b rep ha hb noAB _ _ _
  by_cases ne : a = b
  · subst b; rfl
  have ne : a ≠ b := ne
  have readyA : CertifiedReplay.Ready (scope Γ C) (insert b H) a :=
    ⟨ha.1,by simpa only [Set.mem_insert_iff,not_or] using And.intro ne ha.2.1,
      fun p hp vis => Or.inr (ha.2.2 p hp vis)⟩
  have readyB : CertifiedReplay.Ready (scope Γ C) (insert a H) b :=
    ⟨hb.1,by simpa only [Set.mem_insert_iff,not_or] using And.intro (Ne.symm ne) hb.2.1,
      fun p hp vis => Or.inr (hb.2.2 p hp vis)⟩
  have left := update_closed Γ C domain _ _ b (update_closed Γ C domain _ _ a rep ha) readyB
  have right := update_closed Γ C domain _ _ a (update_closed Γ C domain _ _ b rep hb) readyA
  exact unique Γ C honest _ _ _ left (by simpa only [Set.insert_comm] using right)

end Sided

#print axioms Embedded.laws
#print axioms Sided.laws
end Sal.MRDTs.Paper1.CertifiedRGAScope
