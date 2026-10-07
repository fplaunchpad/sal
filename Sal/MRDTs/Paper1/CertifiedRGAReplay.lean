import Sal.MRDTs.Instances.ProductionRGA
import Sal.MRDTs.Instances.SidedPeritext
import Sal.MRDTs.Instances.FugueMaxContract

/-! Concrete replay facts for original issued embedded histories. Eligibility
uses the existing positive-chain invariant, supported events, and actual
replay provenance. It does not assume issuability at a reordered state. -/
namespace Sal.MRDTs.Paper1.CertifiedRGAReplay
open Foundation Sal.EmbedRGA

namespace Embedded
open Instances.EmbedRGA
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem insert_pair_commute {s : EState α} {a b : ERec α}
    (sorted : ESorted s)
    (freshA : ∀ x ∈ s, key x.2.2 ≠ key a.2.2)
    (freshB : ∀ x ∈ s, key x.2.2 ≠ key b.2.2)
    (different : key a.2.2 ≠ key b.2.2) :
    eInsert b (eInsert a s) = eInsert a (eInsert b s) := by
  apply esorted_ext
  · apply eInsert_sorted (eInsert_sorted sorted freshA)
    intro x mem
    rcases mem_eInsert.mp mem with old | rfl
    · exact freshB x old
    · exact different
  · apply eInsert_sorted (eInsert_sorted sorted freshB)
    intro x mem
    rcases mem_eInsert.mp mem with old | rfl
    · exact freshA x old
    · exact Ne.symm different
  · intro x
    simp only [mem_eInsert]
    tauto

/-- Exact insert commutation at an eligible represented state. Both ids are
fresh and positive-chain evidence provides strict coordinate separation. -/
theorem fresh_updates_commute (Γ : OrderedPrefixCode) (s : EState α)
    (ta ra tb rb : Nat) (xa xb : α) (pa pb : List Bool) (aa ab : Nat)
    (sorted : ESorted s) (freshA : ta ∉ eIds s) (freshB : tb ∉ eIds s)
    (distinct : ta ≠ tb)
    (keysA : ∀ x ∈ s, key x.2.2 ≠ key (pa ++ Γ.enc (ta-aa)))
    (keysB : ∀ x ∈ s, key x.2.2 ≠ key (pb ++ Γ.enc (tb-ab)))
    (different : key (pa ++ Γ.enc (ta-aa)) ≠ key (pb ++ Γ.enc (tb-ab))) :
    eUpdate Γ (eUpdate Γ s (ta,ra,.ins xa pa aa)) (tb,rb,.ins xb pb ab) =
      eUpdate Γ (eUpdate Γ s (tb,rb,.ins xb pb ab)) (ta,ra,.ins xa pa aa) := by
  have secondA : ta ∉ eIds (eInsert (tb,xb,pb ++ Γ.enc (tb-ab)) s) := by
    simpa only [mem_eIds_eInsert,not_or] using And.intro freshA distinct
  have secondB : tb ∉ eIds (eInsert (ta,xa,pa ++ Γ.enc (ta-aa)) s) := by
    simpa only [mem_eIds_eInsert,not_or] using And.intro freshB (Ne.symm distinct)
  simp only [eUpdate,if_neg freshA,if_neg freshB,if_neg secondA,if_neg secondB]
  exact insert_pair_commute sorted keysA keysB different

/-- A supported replay that omits a certified insertion contains neither
its identifier nor its key. This evidence survives arbitrary reordering of
that replay because the argument uses record provenance alone. -/
theorem fold_fresh_metadata (Γ : OrderedPrefixCode)
    (C : ReplayContext (E Γ α).toUpdateSig) (honest : EHonestCore Γ C)
    (xs : List (Op (EOp α))) (supported : ∀ o ∈ xs, o ∈ C.events)
    (a : Op (EOp α)) (eligible : a ∈ C.events) (insertion : eIsIns a = true)
    (absent : a ∉ xs) :
    a.1 ∉ eIds (eFold Γ xs) ∧
      (∀ x ∈ eFold Γ xs, key x.2.2 ≠ key (eCoord Γ a)) := by
  have distinct : ∀ o ∈ xs, o.1 ≠ a.1 := by
    intro o mem equal
    exact absent ((C.ts_unique (supported o mem) eligible equal) ▸ mem)
  constructor
  · intro mem
    obtain ⟨x,hx,id⟩ := List.mem_map.mp mem
    obtain ⟨o,ho,_,record⟩ := e_fold_rec_sub Γ xs x hx
    have born : x.1 = o.1 := by rw [record]; rfl
    exact distinct o ho (born.symm.trans id)
  · intro x mem
    obtain ⟨o,ho,ins,record⟩ := e_fold_rec_sub Γ xs x mem
    have different := e_keys_inj_events honest o (supported o ho) a eligible ins insertion (distinct o ho)
    simpa only [record,eRecOf] using different

/-- Two distinct certified inserts commute on a well-formed supported
replay omitting them. The invariant premises come from the original issuer;
no global commutation claim over malformed lists is needed. -/
theorem eligible_inserts_commute (Γ : OrderedPrefixCode)
    (C : ReplayContext (E Γ α).toUpdateSig) (honest : EHonestCore Γ C)
    (xs : List (Op (EOp α))) (supported : ∀ o ∈ xs, o ∈ C.events) (wf : EWf Γ xs)
    (ta ra tb rb : Nat) (xa xb : α) (pa pb : List Bool) (aa ab : Nat)
    (ha : (ta,ra,EOp.ins xa pa aa) ∈ C.events)
    (hb : (tb,rb,EOp.ins xb pb ab) ∈ C.events)
    (absentA : (ta,ra,EOp.ins xa pa aa) ∉ xs)
    (absentB : (tb,rb,EOp.ins xb pb ab) ∉ xs) (distinct : ta ≠ tb) :
    eUpdate Γ (eUpdate Γ (eFold Γ xs) (ta,ra,.ins xa pa aa)) (tb,rb,.ins xb pb ab) =
      eUpdate Γ (eUpdate Γ (eFold Γ xs) (tb,rb,.ins xb pb ab)) (ta,ra,.ins xa pa aa) := by
  obtain ⟨idA,keyA⟩ := fold_fresh_metadata Γ C honest xs supported
    (ta,ra,.ins xa pa aa) ha rfl absentA
  obtain ⟨idB,keyB⟩ := fold_fresh_metadata Γ C honest xs supported
    (tb,rb,.ins xb pb ab) hb rfl absentB
  have different := e_keys_inj_events honest _ ha _ hb rfl rfl distinct
  exact fresh_updates_commute Γ _ ta ra tb rb xa xb pa pb aa ab (e_fold_sorted Γ wf)
    idA idB distinct keyA keyB different

/-- Original honesty evidence establishes well-formedness separately for
both reordered replays, then equality follows from records and sortedness. -/
theorem replay_equal (Γ : OrderedPrefixCode)
    (C : ReplayContext (E Γ α).toUpdateSig) (honest : EHonestCore Γ C)
    (events : Set (Op (EOp α))) (supported : events ⊆ C.events)
    (closed : ∀ a b, C.vis a b → ¬ (E Γ α).toUpdateSig.commutes a b → b ∈ events → a ∈ events)
    (xs ys : List (Op (EOp α))) (px : listPermOf xs events) (py : listPermOf ys events)
    (rx : respects xs (loOn C events)) (ry : respects ys (loOn C events)) :
    eFold Γ xs = eFold Γ ys :=
  e_fold_canon Γ (e_wf_of_enum honest supported closed px rx)
    (e_wf_of_enum honest supported closed py ry) (fun o => (px.2 o).trans (py.2 o).symm)

/-- All operation shapes admit the exact prefix diamond whenever both
extensions satisfy the original history well-formedness conditions. -/
theorem prefix_diamond_of_wf (Γ : OrderedPrefixCode) (xs : List (Op (EOp α)))
    (a b : Op (EOp α)) (forward : EWf Γ (xs ++ [a,b]))
    (backward : EWf Γ (xs ++ [b,a])) :
    eUpdate Γ (eUpdate Γ (eFold Γ xs) a) b =
      eUpdate Γ (eUpdate Γ (eFold Γ xs) b) a := by
  have eq := e_fold_canon Γ forward backward (by intro o; simp; tauto)
  simpa only [eFold,applySeq,List.foldl_append,List.foldl_cons,List.foldl_nil,E] using eq

end Embedded
namespace Sided
open Instances.SidedEmbedRGA

theorem insert_pair_commute {s : SState} {a b : SRec}
    (sorted : SSorted s)
    (freshA : ∀ x ∈ s, sKey x.2.2 ≠ sKey a.2.2)
    (freshB : ∀ x ∈ s, sKey x.2.2 ≠ sKey b.2.2)
    (different : sKey a.2.2 ≠ sKey b.2.2) :
    sInsert b (sInsert a s) = sInsert a (sInsert b s) := by
  apply ssorted_ext
  · apply sInsert_sorted (sInsert_sorted sorted freshA)
    intro x mem
    rcases mem_sInsert.mp mem with old | rfl
    · exact freshB x old
    · exact different
  · apply sInsert_sorted (sInsert_sorted sorted freshB)
    intro x mem
    rcases mem_sInsert.mp mem with old | rfl
    · exact freshA x old
    · exact Ne.symm different
  · intro x
    simp only [mem_sInsert]
    tauto

/-- Exact insert commutation at an eligible represented state. Both ids are
fresh and positive-chain evidence provides strict coordinate separation. -/
theorem fresh_updates_commute (Γ : OrderedPrefixCode) (s : SState)
    (ta ra tb rb : Nat) (xa xb : Nat) (pa pb : List Nat) (aa ab : Nat) (sdA sdB : Side)
    (sorted : SSorted s) (freshA : ta ∉ sIds s) (freshB : tb ∉ sIds s)
    (distinct : ta ≠ tb)
    (keysA : ∀ x ∈ s, sKey x.2.2 ≠ sKey (pa ++ sBlock Γ (sdA,ta-aa)))
    (keysB : ∀ x ∈ s, sKey x.2.2 ≠ sKey (pb ++ sBlock Γ (sdB,tb-ab)))
    (different : sKey (pa ++ sBlock Γ (sdA,ta-aa)) ≠ sKey (pb ++ sBlock Γ (sdB,tb-ab))) :
    sUpdate Γ (sUpdate Γ s (ta,ra,.ins xa pa aa sdA)) (tb,rb,.ins xb pb ab sdB) =
      sUpdate Γ (sUpdate Γ s (tb,rb,.ins xb pb ab sdB)) (ta,ra,.ins xa pa aa sdA) := by
  have secondA : ta ∉ sIds (sInsert (tb,xb,pb ++ sBlock Γ (sdB,tb-ab)) s) := by
    simpa only [mem_sIds_sInsert,not_or] using And.intro freshA distinct
  have secondB : tb ∉ sIds (sInsert (ta,xa,pa ++ sBlock Γ (sdA,ta-aa)) s) := by
    simpa only [mem_sIds_sInsert,not_or] using And.intro freshB (Ne.symm distinct)
  simp only [sUpdate,if_neg freshA,if_neg freshB,if_neg secondA,if_neg secondB]
  exact insert_pair_commute sorted keysA keysB different

/-- A supported replay that omits a certified insertion contains neither
its identifier nor its key. This evidence survives arbitrary reordering of
that replay because the argument uses record provenance alone. -/
theorem fold_fresh_metadata (Γ : OrderedPrefixCode)
    (C : ReplayContext (S Γ).toUpdateSig) (honest : SHonestCore Γ C)
    (xs : List (Op (SOp))) (supported : ∀ o ∈ xs, o ∈ C.events)
    (a : Op (SOp)) (eligible : a ∈ C.events) (insertion : sIsIns a = true)
    (absent : a ∉ xs) :
    a.1 ∉ sIds (sFold Γ xs) ∧
      (∀ x ∈ sFold Γ xs, sKey x.2.2 ≠ sKey (sCoord Γ a)) := by
  have distinct : ∀ o ∈ xs, o.1 ≠ a.1 := by
    intro o mem equal
    exact absent ((C.ts_unique (supported o mem) eligible equal) ▸ mem)
  constructor
  · intro mem
    obtain ⟨x,hx,id⟩ := List.mem_map.mp mem
    obtain ⟨o,ho,_,record⟩ := s_fold_rec_sub Γ xs x hx
    have born : x.1 = o.1 := by rw [record]; rfl
    exact distinct o ho (born.symm.trans id)
  · intro x mem
    obtain ⟨o,ho,ins,record⟩ := s_fold_rec_sub Γ xs x mem
    have different := s_keys_inj_events honest o (supported o ho) a eligible ins insertion (distinct o ho)
    simpa only [record,sRecOf] using different

/-- Two distinct certified inserts commute on a well-formed supported
replay omitting them. The invariant premises come from the original issuer;
no global commutation claim over malformed lists is needed. -/
theorem eligible_inserts_commute (Γ : OrderedPrefixCode)
    (C : ReplayContext (S Γ).toUpdateSig) (honest : SHonestCore Γ C)
    (xs : List (Op (SOp))) (supported : ∀ o ∈ xs, o ∈ C.events) (wf : SWf Γ xs)
    (ta ra tb rb : Nat) (xa xb : Nat) (pa pb : List Nat) (aa ab : Nat) (sdA sdB : Side)
    (ha : (ta,ra,SOp.ins xa pa aa sdA) ∈ C.events)
    (hb : (tb,rb,SOp.ins xb pb ab sdB) ∈ C.events)
    (absentA : (ta,ra,SOp.ins xa pa aa sdA) ∉ xs)
    (absentB : (tb,rb,SOp.ins xb pb ab sdB) ∉ xs) (distinct : ta ≠ tb) :
    sUpdate Γ (sUpdate Γ (sFold Γ xs) (ta,ra,.ins xa pa aa sdA)) (tb,rb,.ins xb pb ab sdB) =
      sUpdate Γ (sUpdate Γ (sFold Γ xs) (tb,rb,.ins xb pb ab sdB)) (ta,ra,.ins xa pa aa sdA) := by
  obtain ⟨idA,keyA⟩ := fold_fresh_metadata Γ C honest xs supported
    (ta,ra,.ins xa pa aa sdA) ha rfl absentA
  obtain ⟨idB,keyB⟩ := fold_fresh_metadata Γ C honest xs supported
    (tb,rb,.ins xb pb ab sdB) hb rfl absentB
  have different := s_keys_inj_events honest _ ha _ hb rfl rfl distinct
  exact fresh_updates_commute Γ _ ta ra tb rb xa xb pa pb aa ab sdA sdB (s_fold_sorted Γ wf)
    idA idB distinct keyA keyB different

/-- Original honesty evidence establishes well-formedness separately for
both reordered replays, then equality follows from records and sortedness. -/
theorem replay_equal (Γ : OrderedPrefixCode)
    (C : ReplayContext (S Γ).toUpdateSig) (honest : SHonestCore Γ C)
    (events : Set (Op (SOp))) (supported : events ⊆ C.events)
    (closed : ∀ a b, C.vis a b → ¬ (S Γ).toUpdateSig.commutes a b → b ∈ events → a ∈ events)
    (xs ys : List (Op (SOp))) (px : listPermOf xs events) (py : listPermOf ys events)
    (rx : respects xs (loOn C events)) (ry : respects ys (loOn C events)) :
    sFold Γ xs = sFold Γ ys :=
  s_fold_canon Γ (s_wf_of_enum honest supported closed px rx)
    (s_wf_of_enum honest supported closed py ry) (fun o => (px.2 o).trans (py.2 o).symm)

/-- All operation shapes admit the exact prefix diamond whenever both
extensions satisfy the original history well-formedness conditions. -/
theorem prefix_diamond_of_wf (Γ : OrderedPrefixCode) (xs : List (Op (SOp)))
    (a b : Op (SOp)) (forward : SWf Γ (xs ++ [a,b]))
    (backward : SWf Γ (xs ++ [b,a])) :
    sUpdate Γ (sUpdate Γ (sFold Γ xs) a) b =
      sUpdate Γ (sUpdate Γ (sFold Γ xs) b) a := by
  have eq := s_fold_canon Γ forward backward (by intro o; simp; tauto)
  simpa only [sFold,applySeq,List.foldl_append,List.foldl_cons,List.foldl_nil,S] using eq

end Sided

#print axioms Embedded.eligible_inserts_commute
#print axioms Embedded.replay_equal
#print axioms Sided.eligible_inserts_commute
#print axioms Sided.replay_equal
end Sal.MRDTs.Paper1.CertifiedRGAReplay
