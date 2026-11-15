import LeanProofs.Implementations.MVRegister.SequentialSpec

namespace LeanProofs.Implementations.MVRegister
open Artifact.MRDTs
open Artifact.MRDTs.Foundation
open Classical
local instance : EventOrder D.toUpdateSig := replayOrder
set_option maxHeartbeats 1000000

theorem replayOrder_iff_overwrite_of_execution {C : Configuration D}
    (exec : CertifiedExecution D issuance C) {a b : Event} (hb : b ∈ C.events) :
    D.toUpdateSig.replayBefore a b ↔ a.1 ∈ MVR.overwrites b := by
  rw [show D.toUpdateSig.replayBefore a b ↔ a.1 < b.1 ∧ a.1 ∈ MVR.overwrites b from
    MVR.replayOrder_before_iff a b]
  exact ⟨And.right,fun h => ⟨issued_overwrite_lt exec.mintHonest hb h,h⟩⟩

noncomputable def verified : VerifiedMRDT D where
  issuance := issuance
  replayOrder := replayOrder
  replayAdequacy := replayAdequacy
  Spec := spec
  Rel := Eq
  sequentialCorrectness := sequentialCorrectness

theorem fold_present_or_overwritten (ops : List Event) {a : Event} (ha : a ∈ ops) :
    (a.1,MVR.writeValue a) ∈ ops.foldl update ∅ ∨
      ∃ b ∈ ops, a.1 ∈ MVR.overwrites b := by
  induction ops using List.reverseRecOn with
  | nil => simp at ha
  | append_singleton ops e ih =>
    rw [List.mem_append,List.mem_singleton] at ha
    rw [List.foldl_append]
    change (a.1,MVR.writeValue a) ∈ update (ops.foldl update ∅) e ∨ _
    rcases ha with ha | rfl
    · rcases ih ha with hl | ⟨b,hb,hn⟩
      · by_cases hn : a.1 ∈ MVR.overwrites e
        · exact Or.inr ⟨e,by simp,hn⟩
        · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hl,hn⟩))
      · exact Or.inr ⟨b,List.mem_append_left _ hb,hn⟩
    · exact Or.inl (Finset.mem_insert_self _ _)

theorem overwrite_iff_successor {C : Configuration D}
    (mint : MintHonest D issuance.CanIssue C) {E : Set Event}
    (sup : E ⊆ C.events) (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {a : Event} (ha : a ∈ E) :
    (∃ b ∈ E, a.1 ∈ MVR.overwrites b) ↔ ∃ b ∈ E, C.vis a b := by
  constructor
  · rintro ⟨b,hb,hn⟩
    obtain ⟨birth,hm,hv,ht⟩ := issued_overwrite mint (sup hb) hn
    have heq := C.replayContext.ts_unique hm (sup ha) ht
    exact ⟨b,hb,heq ▸ hv⟩
  · rintro ⟨b,hb,hv⟩
    obtain ⟨ops,hp,_,hg⟩ := mint b (sup hb)
    have hain : a ∈ ops := (hp.2 a).mpr ⟨sup ha,hv⟩
    rcases fold_present_or_overwritten ops hain with hl | ⟨c,hc,hn⟩
    · refine ⟨b,hb,List.mem_toFinset.mp ?_⟩
      rw [hg.2]
      exact Finset.mem_image.mpr ⟨(a.1,MVR.writeValue a),hl,rfl⟩
    · exact ⟨c,closed c b ((hp.2 c).mp hc).2 hb,hn⟩

theorem version_maximal {C : Configuration D}
    (exec : CertifiedExecution D issuance C)
    {v : Version} {s : State} {E : Set Event}
    (hver : C.ver v = some (s,E)) (p : ℕ × ℕ) :
    p ∈ s ↔ ∃ a ∈ E, a.1 = p.1 ∧ MVR.writeValue a = p.2 ∧
      ∀ b ∈ E, ¬ C.vis a b := by
  obtain ⟨hG,hR⟩ := represented_of_execution exec
  have sup := hG.version_events_supported v s E hver
  have closed := hG.version_events_causal v s E hver
  rw [hR v s E hver p]
  constructor
  · rintro ⟨⟨a,ha,hpair⟩,hn⟩
    obtain ⟨ht,hv⟩ := Prod.mk.inj hpair
    refine ⟨a,ha,ht,hv,?_⟩
    intro b hb hab
    obtain ⟨c,hc,hkill⟩ := (overwrite_iff_successor exec.mintHonest sup closed ha).mpr ⟨b,hb,hab⟩
    exact hn ⟨c,hc,ht ▸ hkill⟩
  · rintro ⟨a,ha,ht,hv,hmax⟩
    refine ⟨⟨a,ha,Prod.ext ht hv⟩,?_⟩
    rintro ⟨b,hb,hn⟩
    obtain ⟨c,hc,hvis⟩ := (overwrite_iff_successor exec.mintHonest sup closed ha).mp
      ⟨b,hb,ht.symm ▸ hn⟩
    exact hmax c hc hvis

theorem mvr_correct {C : Configuration D} (exec : CertifiedExecution D issuance C) :
    IsSpecLinearizable D replayOrder spec Eq C ∧
    (∀ v (s : State) E, C.ver v = some (s,E) → ∀ p : ℕ × ℕ,
      p ∈ s ↔ ∃ a ∈ E, a.1 = p.1 ∧ MVR.writeValue a = p.2 ∧ ∀ b ∈ E, ¬ C.vis a b) := by
  refine ⟨?_,fun _ _ _ hv p => version_maximal exec hv p⟩
  cases exec with
  | ordinary h => exact verified.correct h
  | virtual h => exact verified.correctV h

theorem linear_register {ops : List Event}
    (h : LinearMintHistory D issuance.CanIssue ops) :
    D.query (applySeq D.toUpdateSig D.init ops) () =
      {v | MVR.mvrSpecFold ops = some v} := by
  cases ops using List.reverseRecOn with
  | nil =>
    apply Set.ext
    intro v
    simp [D,applySeq,MVR.queryValues,MVR.mvrSpecFold]
  | append_singleton pre e =>
    have hg := h.guarded pre e [] (by simp)
    rw [applySeq_append_single]
    change MVR.queryValues (update (applySeq D.toUpdateSig D.init pre) e) = _
    rw [issued_write_singleton e _ hg]
    obtain ⟨t,r,⟨w,O⟩⟩ := e
    rw [MVR.mvrSpecFold_snoc]
    ext value
    simp [MVR.queryValues,MVR.writeValue]

#print axioms verified
#print axioms mvr_correct
#print axioms linear_register
end LeanProofs.Implementations.MVRegister
