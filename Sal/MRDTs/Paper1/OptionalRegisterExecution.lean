import Sal.MRDTs.Paper1.OptionalRegisterReplay
import Sal.MRDTs.Paper1.CertifiedClosedExecution

/-! An internal execution order retains same-issuer Set conflicts needed by
the generic stored/recursive-base induction. It is not the public rc policy.
On supported histories, those additional comparisons coincide with causality;
the resulting replay order is exactly the unchanged semantic paper order. -/
namespace Sal.MRDTs.Paper1.OptionalRegister
open Foundation ConcreteMRDT Instances.OptionalRegister Classical

noncomputable def executionOrder : EventOrder D.toUpdateSig where
  order a b := match a.op,b.op with
    | .unset,.set _ => .Fst_then_snd
    | .set _,.unset => .Snd_then_fst
    | .set _,.set _ => if a.rep = b.rep then
        if a.time < b.time then .Fst_then_snd
        else if b.time < a.time then .Snd_then_fst else .Either
      else .Either
    | _,_ => .Either

noncomputable local instance executionData : EventOrder D.toUpdateSig := executionOrder

@[simp] theorem execution_before (a b : Event) : D.toUpdateSig.replayBefore a b ↔
    policy.before a.op b.op ∨
      ((∃ v, a.op = .set v) ∧ (∃ v, b.op = .set v) ∧ a.rep = b.rep ∧ a.time < b.time) := by
  rcases a with ⟨ta,ra,oa⟩; rcases b with ⟨tb,rb,ob⟩
  cases oa <;> cases ob <;>
    simp [UpdateSig.replayBefore,EventOrder.Before,executionData,executionOrder,policy,Op.op,Op.rep,Op.time]
  split_ifs <;> simp_all <;> omega

theorem same_rep_sets_noncomm (ta r va tb vb : Nat) (different : ta ≠ tb) :
    ¬ D.toUpdateSig.commutes (ta,r,.set va) (tb,r,.set vb) := by
  intro comm
  have h := congrArg (fun s => (s.cells r).2.1) (comm initial)
  simp [D,update,Op.op,Op.rep,Op.time] at h
  exact different h.symm

theorem execution_noncomm_exact (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (support : Supported C E) (a b : Event) (ha : a ∈ E) (hb : b ∈ E) :
    ¬ D.toUpdateSig.commutes a b ↔
      D.toUpdateSig.replayBefore a b ∨ D.toUpdateSig.replayBefore b a := by
  simp only [execution_before]
  by_cases same : a = b
  · subst b
    have comm : D.toUpdateSig.commutes a a := fun _ => rfl
    rcases a with ⟨ta,ra,oa⟩
    cases oa <;> simp only [policy,Op.op,Op.rep,Op.time,comm,not_true_eq_false,false_or,or_false]
    all_goals simp
  · have time : a.time ≠ b.time := by
      intro eq
      exact same (timestamp_unique support ha hb eq)
    rcases a with ⟨ta,ra,oa⟩; rcases b with ⟨tb,rb,ob⟩
    simp only [Op.time] at time
    cases oa <;> cases ob
    · rename_i va vb
      by_cases own : ra = rb
      · subst rb
        have nc := same_rep_sets_noncomm ta ra va tb vb time
        simp [execution_before,policy,Op.op,Op.rep,Op.time,nc]
        omega
      · simp [execution_before,policy,Op.op,Op.rep,Op.time,own,Ne.symm own,
          sets_commute _ _ _ _ _ _ own]
    · rename_i v
      have nc := set_unset_noncomm ta ra v tb rb
      simp [policy,Op.op,Op.rep,Op.time,nc]
    · rename_i v
      have nc : ¬ D.toUpdateSig.commutes (ta,ra,.unset) (tb,rb,.set v) := by
        intro comm
        exact set_unset_noncomm tb rb v ta ra (fun s => (comm s).symm)
      simp [execution_before,policy,Op.op,Op.rep,Op.time,nc]
    · simp [execution_before,policy,Op.op,Op.rep,Op.time,
        unsets_commute (ta,ra,.unset) (tb,rb,.unset) rfl rfl]

theorem execution_concurrent_before (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (support : Supported C E) (a b : Event) (ha : a ∈ E) (hb : b ∈ E)
    (forward : ¬ C.vis a b) (backward : ¬ C.vis b a) :
    D.toUpdateSig.replayBefore a b ↔ policy.before a.op b.op := by
  rw [execution_before]
  constructor
  · rintro (edge | ⟨_,_,own,time⟩)
    · exact edge
    · have different : a ≠ b := by intro eq; subst b; exact Nat.lt_irrefl _ time
      obtain ⟨r,F,head,member⟩ := support a ha
      obtain ⟨q,G,other,mem⟩ := support b hb
      exact False.elim ((C.vis_total_same_replica head member other mem different own).elim forward backward)
  · exact Or.inl

theorem execution_order_iff (C : ReplayContext D.toUpdateSig) (E : Set Event)
    (support : Supported C E) (a b : Event) (ha : a ∈ E) (hb : b ∈ E) :
    loOn C E a b ↔ paperOrder policy C E a b := by
  have exactab := execution_noncomm_exact C E support a b ha hb
  have exactbz : ∀ z ∈ E, (D.toUpdateSig.replayBefore b z ∨ D.toUpdateSig.replayBefore z b) ↔
      ¬ D.toUpdateSig.commutes b z := fun z hz => (execution_noncomm_exact C E support b z hb hz).symm
  simp only [loOn,paperOrder,← exactab]
  constructor
  · rintro (causal | ⟨forward,backward,edge,noAbsorber⟩)
    · exact Or.inl causal
    · exact Or.inr ⟨forward,backward,(execution_concurrent_before C E support a b ha hb forward backward).mp edge,
        fun ⟨z,hz,vis,nc⟩ => noAbsorber ⟨z,hz,vis,(exactbz z hz).mpr nc⟩⟩
  · rintro (causal | ⟨forward,backward,edge,noAbsorber⟩)
    · exact Or.inl causal
    · exact Or.inr ⟨forward,backward,(execution_concurrent_before C E support a b ha hb forward backward).mpr edge,
        fun ⟨z,hz,vis,nc⟩ => noAbsorber ⟨z,hz,vis,(exactbz z hz).mp nc⟩⟩

theorem executionCanonical_to_paper (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (s : State) (sup : Supported C E) (h : IsCanonicalState C E s) :
    Canonical policy C E s := by
  obtain ⟨π,hp,ordered,fold⟩ := h
  refine ⟨π,hp,?_,fold⟩
  apply ordered.imp_of_mem
  intro a b ha hb no edge
  exact no ((execution_order_iff C E sup b a ((hp.2 b).mp hb) ((hp.2 a).mp ha)).mpr edge)

theorem paperCanonical_to_execution (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (s : State) (sup : Supported C E) (h : Canonical policy C E s) :
    IsCanonicalState C E s := by
  obtain ⟨π,hp,ordered,fold⟩ := h
  refine ⟨π,hp,?_,fold⟩
  apply ordered.imp_of_mem
  intro a b ha hb no edge
  exact no ((execution_order_iff C E sup b a ((hp.2 b).mp hb) ((hp.2 a).mp ha)).mp edge)

theorem representation_of_executionCanonical (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (s : State) (good : GoodContext C) (sup : Supported C E)
    (h : IsCanonicalState C E s) : representation C E s := by
  obtain ⟨π,hp,ordered,fold⟩ := h
  obtain ⟨t,ht⟩ := representedList C E good π hp sup
  have same : t = s := canonical_unique laws C E sup (canonical C E t ht)
    (executionCanonical_to_paper C E s sup ⟨π,hp,ordered,fold⟩)
  simpa only [same] using ht

variable (join : RepresentationJoin representation)
include join

theorem execution_closedJoin (C : Configuration D) :
    CertifiedClosedExecution.ClosedJoinAt D C.replayContext := by
  intro E₁ E₂ l a b trans irr sup₁ sup₂ closed₁ closed₂ hl ha hb
  have good : GoodContext C.replayContext := ⟨fun _ _ _ => trans,irr,fun h => C.causal_mono h⟩
  have rl := representation_of_executionCanonical C.replayContext _ l good (fun x hx => sup₁ x hx.1) hl
  have ra := representation_of_executionCanonical C.replayContext _ a good sup₁ ha
  have rb := representation_of_executionCanonical C.replayContext _ b good sup₂ hb
  have merged := join C.replayContext E₁ E₂ l a b good.trans irr sup₁ sup₂ closed₁ closed₂ rl ra rb
  exact paperCanonical_to_execution C.replayContext _ _ merged.supported
    (canonical C.replayContext _ _ merged)

theorem executionCanonicalConfig {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C) :
    @CanonicalConfig D executionOrder C :=
  CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV
    (fun C _ => execution_closedJoin join C) reach

theorem representedVersionsOfJoin {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C)
    (v : Version) (s : State) (E : Set Event) (hv : C.ver v = some (s,E)) :
    representation C.replayContext E s := by
  have good := executionCanonicalConfig join reach
  exact representation_of_executionCanonical C.replayContext E s
    ⟨fun _ _ _ => good.vis_trans,good.vis_irrefl,fun h => C.causal_mono h⟩
    (good.version_events_supported v s E hv) (good.canonical v s E hv)

#print axioms execution_order_iff
#print axioms representedVersionsOfJoin
end Sal.MRDTs.Paper1.OptionalRegister
