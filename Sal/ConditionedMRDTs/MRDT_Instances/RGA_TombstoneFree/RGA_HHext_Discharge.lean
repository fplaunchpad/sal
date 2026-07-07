import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Skeleton3

/-!
# hHext DISCHARGED — the discipline extends at applicable applies

*Additive; modifies no existing file; 0 `sorry`.*

Skeleton 3's `hHext` leaf: at an apply step, the H-witness `ρ` for the head version's events
extends by the new op — `rgaH (ρ ++ [(t, r, o)])` — given only that the op is `applicable`
(accurate + fresh) at the witness fold.  The two ingredients beyond `applicable`:

* **the step's own stored-freshness side-condition** (`h_fresh_store`, extracted by inverting the
  `Step3.apply` constructor): no event stored at ANY version of `C₀` — in particular none in
  `evh` — carries time `t`.  This is what makes the *no-id-reuse* clauses of `CanonStepOK`
  (never-deleted, absent from prior chains) provable: `HonestPayloads` turns any recorded
  occurrence of `t` into an INSERT of `t` in `ρ ⊆ evh`, whose time is `t` — contradiction.
* **payload honesty of the extension**: the new op's own payload is honest at the fold —
  `accurate` makes a delete's nonzero target and an insert's chain entries LIVE, and ids enter a
  fold only by their own `Ins` (`insertedIn_of_contains_fold`).

The fold-step obligations themselves are the two accuracy cruxes (`chainOK_of_accurate`,
`delOK_of_accurate`) plus `canonFoldOK_append`.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGASkeleton3

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonInv CanonStepOK CanonFoldOK insertedIn)
open Sal.ConditionedMRDTs.RGACanonFoldOK (canonFoldOK_append insertedIn_of_contains_fold)

/-- **hHext, discharged.**  The witness discipline `rgaH` extends at an applicable apply. -/
theorem rga_hHext_discharged
    {C₀ C₁ : Sal.ConditionedMRDTs.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)}
    {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : app_op_t}
    {v : Sal.ConditionedMRDTs.Version}
    {sh : QState RGACondSig' rgaEqEquiv'} {evh : Set (Op app_op_t)} :
    (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
      (Sal.ConditionedMRDTs.initConfig
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C₀ →
    Sal.ConditionedMRDTs.Step3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
      C₀ (Sal.ConditionedMRDTs.Label3.apply t r o) C₁ →
    C₀.head r = some v → C₀.ver v = some (sh, evh) →
    ∀ ρ : List op_t, listPermOf ρ evh → rgaH ρ →
      RGACondSig'.applicable (t, r, o) (applySeq RGACondSig'.toCRDTSig RGACondSig'.init ρ) →
      rgaH (ρ ++ [(t, r, o)]) := by
  intro _hreach hstep hhead hver ρ hρp hH happ
  obtain ⟨hOK, hHP⟩ := hH
  -- freshness of t against evh, from the step's stored-freshness side-condition
  have hfresh : ∀ x : op_t, x ∈ evh → x.1 ≠ t := by
    cases hstep with
    | apply h_head' h_ver' hft hfs hvn hrk C' hN hL hvis hver2 hhead2 hparents =>
      intro x hx
      exact hfs v sh evh hver x hx
  -- the applicable premise at the raw fold
  have hstate : applySeq RGACondSig'.toCRDTSig RGACondSig'.init ρ = applySeqR init_st ρ :=
    Sal.ConditionedMRDTs.RGAInstanceFinal.applySeq_eq_applySeqR RGACondSig'.init ρ
  rw [hstate] at happ
  have hacc : accurate (t, r, o) (applySeqR init_st ρ) := happ.1
  have hfr : fresh_ts (t, r, o) (applySeqR init_st ρ) := happ.2
  have hinv : CanonInv ρ (applySeqR init_st ρ) := by
    have h := RGACanonConvergence.canon_fold ρ [] init_st
      RGACanonConvergence.canonInv_init hOK
    rwa [List.nil_append] at h
  have h0 : contains (applySeqR init_st ρ) 0 = false := hinv.1
  have hlift : ∀ x : ℕ, insertedIn ρ x → insertedIn (ρ ++ [(t, r, o)]) x := by
    rintro x ⟨r', e', p', a', hm'⟩
    exact ⟨r', e', p', a', List.mem_append_left _ hm'⟩
  cases o with
  | Ins e p a =>
    have hstepOK : CanonStepOK ρ (applySeqR init_st ρ) (t, r, app_op_t.Ins e p a) := by
      refine ⟨hfr.1, hfr.2, ?_, ?_, ?_,
        RGACanonConvergence.chainOK_of_accurate _ t r e a p h0 hacc⟩
      · -- no id reuse: a recorded delete of t names an inserted id — freshness contra
        rintro ⟨t', r', p', hm'⟩
        rcases hHP.1 t' r' t p' hm' with h0' | hins
        · exact hfr.1 h0'
        · obtain ⟨r'', e'', p'', a'', hm''⟩ := hins
          exact hfresh _ ((hρp.2 _).mp hm'') rfl
      · -- t not in its own chain: accurate entries are live, t is fresh
        intro htmem
        have hacc' := hacc
        simp only [accurate, opLeaf, opPath] at hacc'
        rcases hacc' with ⟨ha0, hp0⟩ | ⟨hal, hpath⟩
        · subst ha0; subst hp0
          rcases List.mem_cons.mp htmem with h | h
          · exact hfr.1 h
          · simp at h
        · have hlive : contains (applySeqR init_st ρ) t = true := by
            rcases List.mem_cons.mp htmem with h | h
            · exact h ▸ hal
            · exact isAncPath_mem _ a p hpath t h
          rw [hfr.2] at hlive
          exact Bool.noConfusion hlive
      · -- t not in prior chains: honest payloads make entries inserted — freshness contra
        intro t' r' e' p' a' hm' htmem
        rcases hHP.2 t' r' e' a' p' hm' t htmem with h0' | hins
        · exact hfr.1 h0'
        · obtain ⟨r'', e'', p'', a'', hm''⟩ := hins
          exact hfresh _ ((hρp.2 _).mp hm'') rfl
    refine ⟨canonFoldOK_append ρ [] init_st _ hOK hstepOK, ?_, ?_⟩
    · -- delete payloads: only old members (the appended op is an Ins)
      intro t' r' x' p' hm'
      rcases List.mem_append.mp hm' with h | h
      · rcases hHP.1 t' r' x' p' h with h0' | hins
        · exact Or.inl h0'
        · exact Or.inr (hlift x' hins)
      · exfalso
        have hEq := List.mem_singleton.mp h
        exact app_op_t.noConfusion (congrArg (fun z : op_t => z.2.2) hEq)
    · -- insert payloads: old members lift; the new op's chain is accurate-live
      intro t' r' e' a' p' hm' c hc
      rcases List.mem_append.mp hm' with h | h
      · rcases hHP.2 t' r' e' a' p' h c hc with h0' | hins
        · exact Or.inl h0'
        · exact Or.inr (hlift c hins)
      · have hEq := List.mem_singleton.mp h
        have h3 := congrArg (fun z : op_t => z.2.2) hEq
        injection h3 with h3e h3p h3a
        have hchain : (a' : ℕ) :: p' = a :: p := by rw [h3a, h3p]
        rw [hchain] at hc
        have hacc' := hacc
        simp only [accurate, opLeaf, opPath] at hacc'
        rcases hacc' with ⟨ha0, hp0⟩ | ⟨hal, hpath⟩
        · subst ha0; subst hp0
          rcases List.mem_cons.mp hc with h' | h'
          · exact Or.inl h'
          · simp at h'
        · have hlive : contains (applySeqR init_st ρ) c = true := by
            rcases List.mem_cons.mp hc with h' | h'
            · exact h' ▸ hal
            · exact isAncPath_mem _ a p hpath c h'
          exact Or.inr (hlift c (insertedIn_of_contains_fold ρ c hlive))
  | Del p x =>
    have hstepOK : CanonStepOK ρ (applySeqR init_st ρ) (t, r, app_op_t.Del p x) :=
      RGACanonConvergence.delOK_of_accurate _ t r x p h0 hacc
    refine ⟨canonFoldOK_append ρ [] init_st _ hOK hstepOK, ?_, ?_⟩
    · -- delete payloads: old members lift; the new del's nonzero target is accurate-live
      intro t' r' x' p' hm'
      rcases List.mem_append.mp hm' with h | h
      · rcases hHP.1 t' r' x' p' h with h0' | hins
        · exact Or.inl h0'
        · exact Or.inr (hlift x' hins)
      · have hEq := List.mem_singleton.mp h
        have h3 := congrArg (fun z : op_t => z.2.2) hEq
        injection h3 with h3p h3x
        have hacc' := hacc
        simp only [accurate, opLeaf, opPath] at hacc'
        rcases hacc' with ⟨hx0, _⟩ | ⟨hxl, _⟩
        · exact Or.inl (h3x.trans hx0)
        · exact Or.inr (hlift x'
            (h3x ▸ insertedIn_of_contains_fold ρ x hxl))
    · -- insert payloads: only old members (the appended op is a Del)
      intro t' r' e' a' p' hm' c hc
      rcases List.mem_append.mp hm' with h | h
      · rcases hHP.2 t' r' e' a' p' h c hc with h0' | hins
        · exact Or.inl h0'
        · exact Or.inr (hlift c hins)
      · exfalso
        have hEq := List.mem_singleton.mp h
        exact app_op_t.noConfusion (congrArg (fun z : op_t => z.2.2) hEq)

/-! ## Axiom audit -/

#print axioms rga_hHext_discharged

end Sal.ConditionedMRDTs.RGASkeleton3
