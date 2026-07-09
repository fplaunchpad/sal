import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_GenDisc_Peel

/-!
# GenDisc2C DISCHARGED — the strong induction from born accuracy

*Additive; modifies no existing file; 0 `sorry`.*

The centerpiece of task #32, assembling the bricks of `RGA_GenDisc_Peel`:

**`genDisc2C_of_born`** — the generation discipline `GenDisc2C Cfg E` (each event accurate at the
fold of any enumeration of its transitive dependencies) follows from **born accuracy**
(`hborn`: each event accurate at the fold of SOME `loOnA`-respecting enumeration of its full
causal past — the honest content of born-applicability) plus the execution-model facts
(id-uniqueness, nonzero ids, strict `vis`).

Strong induction on `|pastE o|` (well-founded: `pastE z ⊊ pastE o` for `z ∈ pastE o`, measured by
filtering the finite listing of `E`).  The step, for `o` with dependency prefix `d`:

1. IH + `isDepPreC_of_restrict` give `GenDisc2C Cfg (pastE o)` — the whole engine applies at the
   restricted set with NO relativization cost (`loOnA` is ev-free; the past is `loOnA`-closed).
2. `canonFoldOK_of_gen` at `pastE o` disciplines BOTH the born enumeration `π₀` and the deps-first
   enumeration `d ++ N` (`N` = the non-dependencies, freely sorted; a cross edge `N → d` would make
   its source a dependency).
3. `RGA_update_convergence_canon`: the two folds are observationally equal.
4. `accurate_eq_iff`/`fresh_ts_eq_iff` transport `o`'s applicability across.
5. `applicable_peel_suffix` peels the pointwise-invisible `N` off the end: `o` is applicable —
   in particular accurate — at `applySeqR (init_st (α := α)) d`.  ∎
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open Classical

namespace Sal.ConditionedMRDTs.RGAK1Delta

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA appliesDependsOn)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonFoldOK RGA_update_convergence_canon insertedIn)
open Sal.ConditionedMRDTs.RGACanonFoldOK

/-! ## §1  The measure -/

/-- The size of `o`'s causal past, measured through the finite listing of `E`. -/
noncomputable def msr (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (lE : List (op_t α)) (o : op_t α) : ℕ :=
  (lE.filter (fun z => decide (z ∈ pastE Cfg E o))).length

/-- **The measure strictly decreases into the past**: for `z ∈ pastE o`, `pastE z ⊆ pastE o`
(transitivity) while `z` itself is in the difference (irreflexivity). -/
theorem msr_lt_of_mem (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (lE : List (op_t α)) (hlE : listPermOf lE E)
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (o z : op_t α) (hz : z ∈ pastE Cfg E o) :
    msr Cfg E lE z < msr Cfg E lE o := by
  have hsub : (z :: lE.filter (fun x => decide (x ∈ pastE Cfg E z)))
      ⊆ lE.filter (fun x => decide (x ∈ pastE Cfg E o)) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_filter.mpr ⟨(hlE.2 x).mpr hz.1, decide_eq_true hz⟩
    · obtain ⟨hxl, hxp⟩ := List.mem_filter.mp hx
      have hxpast : x ∈ pastE Cfg E z := of_decide_eq_true hxp
      exact List.mem_filter.mpr ⟨hxl, decide_eq_true ⟨hxpast.1, htr hxpast.2 hz.2⟩⟩
  have hnd : (z :: lE.filter (fun x => decide (x ∈ pastE Cfg E z))).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, hlE.1.filter _⟩
    intro hmem
    obtain ⟨_, hp⟩ := List.mem_filter.mp hmem
    exact hirr z (of_decide_eq_true hp).2
  have hle := (List.subperm_of_subset hnd hsub).length_le
  simp only [List.length_cons] at hle
  exact Nat.lt_of_succ_le hle

/-! ## §2  Freshness at a past fold -/

/-- `o`'s own id is fresh at the fold of any enumeration of its causal past: the past cannot
contain an insert with `o`'s id (id-uniqueness, and `o` is not in its own past). -/
theorem fresh_at_past_fold (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α))
    (hdts : ∀ a b : op_t α, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ x ∈ E, x.1 ≠ 0)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (o : op_t α) (hoE : o ∈ E) (π : List (op_t α))
    (hπp : listPermOf π (pastE Cfg E o)) :
    fresh_ts o (applySeqR (init_st (α := α)) π) := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Del p x => trivial
  | Ins e p a =>
    refine ⟨hids0 (t, r, app_op_t.Ins e p a) hoE, ?_⟩
    cases hb : contains (applySeqR (init_st (α := α)) π) t with
    | false => rfl
    | true =>
      obtain ⟨r', e', p', a', hm⟩ := insertedIn_of_contains_fold π t hb
      have hmem : (t, r', app_op_t.Ins e' p' a') ∈ pastE Cfg E (t, r, app_op_t.Ins e p a) :=
        (hπp.2 _).mp hm
      have hne : (t, r', app_op_t.Ins e' p' a') ≠ (t, r, app_op_t.Ins e p a) := by
        intro heq
        exact hirr (t, r, app_op_t.Ins e p a) (heq ▸ hmem).2
      exact absurd rfl
        (hdts (t, r', app_op_t.Ins e' p' a') (t, r, app_op_t.Ins e p a) hmem.1 hoE hne)

/-! ## §3  The strong induction -/

/-- The workhorse: dependency-fold accuracy for every event whose past is smaller than `n`. -/
theorem genDisc2C_of_born_aux (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (lE : List (op_t α)) (hlE : listPermOf lE E)
    (hdts : ∀ a b : op_t α, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ x ∈ E, x.1 ≠ 0)
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (hborn : ∀ o ∈ E, ∃ π, listPermOf π (pastE Cfg E o) ∧
        respects π (loOnA (RGACondSig α) Cfg E) ∧ accurate o (applySeqR (init_st (α := α)) π)) :
    ∀ (n : ℕ) (o : op_t α), o ∈ E → msr Cfg E lE o < n →
      ∀ d, IsDepPreC Cfg E o d → accurate o (applySeqR (init_st (α := α)) d) := by
  intro n
  induction n with
  | zero => intro o _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro o hoE hlt d hd
    obtain ⟨π₀, hπp, hπr, hacc⟩ := hborn o hoE
    -- GenDisc2C at the past, from the IH + relativization transport
    have hGenP : GenDisc2C Cfg (pastE Cfg E o) := by
      intro o' ho' d' hd'
      have hd'E : IsDepPreC Cfg E o' d' :=
        isDepPreC_of_restrict Cfg E (pastE Cfg E o) (fun x hx => hx.1)
          (fun x hx z hz hlo => pastE_loOnA_closed Cfg E o htr x hx z hz hlo) o' ho' d' hd'
      exact ih o' ho'.1
        (lt_of_lt_of_le (msr_lt_of_mem Cfg E lE hlE htr hirr o o' ho')
          (Nat.lt_succ_iff.mp hlt)) d' hd'E
    -- restricted execution facts
    have hdtsP : ∀ a b : op_t α, a ∈ pastE Cfg E o → b ∈ pastE Cfg E o → a ≠ b → a.1 ≠ b.1 :=
      fun a b ha hb => hdts a b ha.1 hb.1
    have hids0P : ∀ x ∈ pastE Cfg E o, x.1 ≠ 0 := fun x hx => hids0 x hx.1
    -- the dependency prefix sits inside the past
    obtain ⟨hdmem, hdnd, hdresp, hdcomp, hdsound⟩ := hd
    have hdP : ∀ x ∈ d, x ∈ pastE Cfg E o := fun x hx =>
      depC_mem_pastE Cfg E o htr x (hdsound x hx).2
    -- the non-dependencies, freely sorted
    have hlNnd : (lE.filter (fun z => decide (z ∈ pastE Cfg E o ∧ z ∉ d))).Nodup :=
      hlE.1.filter _
    have hlNmem : ∀ x, x ∈ lE.filter (fun z => decide (z ∈ pastE Cfg E o ∧ z ∉ d))
        ↔ x ∈ {z | z ∈ pastE Cfg E o ∧ z ∉ d} := by
      intro x
      rw [List.mem_filter]
      constructor
      · rintro ⟨_, hx⟩; exact of_decide_eq_true hx
      · intro hx; exact ⟨(hlE.2 x).mpr hx.1.1, decide_eq_true hx⟩
    obtain ⟨N, hNp, hNr⟩ := exists_loOnA_perm Cfg {z | z ∈ pastE Cfg E o ∧ z ∉ d}
      _ hlNnd hlNmem htr hirr
    have hNmem : ∀ x, x ∈ N ↔ x ∈ pastE Cfg E o ∧ x ∉ d := fun x => hNp.2 x
    -- W := d ++ N enumerates the past
    have hWp : listPermOf (d ++ N) (pastE Cfg E o) := by
      refine ⟨?_, ?_⟩
      · refine List.nodup_append.mpr ⟨hdnd, hNp.1, ?_⟩
        intro a ha b hb heq
        exact ((hNmem b).mp hb).2 (heq ▸ ha)
      · intro x
        rw [List.mem_append]
        constructor
        · rintro (h | h)
          · exact hdP x h
          · exact ((hNmem x).mp h).1
        · intro hx
          by_cases hxd : x ∈ d
          · exact Or.inl hxd
          · exact Or.inr ((hNmem x).mpr ⟨hx, hxd⟩)
    -- W respects loOnA at E: cross edges N → d would make the source a dependency
    have hNrE : respects N (loOnA (RGACondSig α) Cfg E) :=
      List.Pairwise.imp (fun hn hl => hn ((loOnA_ev_free Cfg E _ _ _).mp hl)) hNr
    have hWr : respects (d ++ N) (loOnA (RGACondSig α) Cfg E) := by
      refine List.pairwise_append.mpr ⟨hdresp, hNrE, ?_⟩
      intro a ha b hb hlo
      have hbP : b ∈ pastE Cfg E o := ((hNmem b).mp hb).1
      have hdep : DepC Cfg E b o :=
        Relation.TransGen.head ⟨hbP.1, hlo⟩ (hdsound a ha).2
      have hbo : b ≠ o := fun heq => hirr o (heq ▸ hbP.2)
      exact ((hNmem b).mp hb).2 (hdcomp b hbP.1 hbo hdep)
    -- respects transported to the past set (ev-free), GoodEnums, discipline
    have hπrP : respects π₀ (loOnA (RGACondSig α) Cfg (pastE Cfg E o)) :=
      List.Pairwise.imp (fun hn hl => hn ((loOnA_ev_free Cfg (pastE Cfg E o) E _ _).mp hl)) hπr
    have hWrP : respects (d ++ N) (loOnA (RGACondSig α) Cfg (pastE Cfg E o)) :=
      List.Pairwise.imp (fun hn hl => hn ((loOnA_ev_free Cfg (pastE Cfg E o) E _ _).mp hl)) hWr
    have hOKπ : CanonFoldOK [] (init_st (α := α)) π₀ :=
      canonFoldOK_of_gen Cfg (pastE Cfg E o) hdtsP hids0P hGenP π₀.length π₀ le_rfl
        (goodEnum_of_perm Cfg (pastE Cfg E o) π₀ hπp hπrP)
    have hOKW : CanonFoldOK [] (init_st (α := α)) (d ++ N) :=
      canonFoldOK_of_gen Cfg (pastE Cfg E o) hdtsP hids0P hGenP (d ++ N).length _ le_rfl
        (goodEnum_of_perm Cfg (pastE Cfg E o) (d ++ N) hWp hWrP)
    -- the two past folds converge
    have heqf : eq (applySeqR (init_st (α := α)) π₀) (applySeqR (init_st (α := α)) (d ++ N)) :=
      RGA_update_convergence_canon π₀ (d ++ N)
        (fun x => (hπp.2 x).trans (hWp.2 x).symm) hOKπ hOKW
    -- o applicable at the born fold; transport; peel
    have happπ : (RGACondSig α).applicable o (applySeqR (init_st (α := α)) π₀) :=
      ⟨hacc, fresh_at_past_fold Cfg E hdts hids0 hirr o hoE π₀ hπp⟩
    have happW : (RGACondSig α).applicable o (applySeqR (init_st (α := α)) (d ++ N)) :=
      ⟨(Sal.ConditionedMRDTs.RGAEqQuotient.accurate_eq_iff o heqf).mp happπ.1,
       (Sal.ConditionedMRDTs.RGAEqQuotient.fresh_ts_eq_iff o heqf).mp happπ.2⟩
    have hinv : ∀ z ∈ N, ¬ appliesDependsOn (RGACondSig α) o z := by
      intro z hz
      have hzP : z ∈ pastE Cfg E o := ((hNmem z).mp hz).1
      refine nondep_not_appliesDependsOn Cfg E o z hzP.2 ?_
      intro hlo
      have hzo : z ≠ o := fun heq => hirr o (heq ▸ hzP.2)
      exact ((hNmem z).mp hz).2
        (hdcomp z hzP.1 hzo (Relation.TransGen.single ⟨hzP.1, hlo⟩))
    have hsplit : applySeqR (init_st (α := α)) (d ++ N) = applySeqR (applySeqR (init_st (α := α)) d) N := by
      simp only [applySeqR, List.foldl_append]
    have hpeel := applicable_peel_suffix o N hinv (applySeqR (init_st (α := α)) d)
    rw [hsplit, hpeel] at happW
    exact happW.1

/-- **GenDisc2C from born accuracy** — task #32's discharge.  Each event accurate at the fold of
SOME causally-ordered enumeration of its full past (the honest generation content) ⟹ accurate at
the fold of EVERY enumeration of its transitive dependencies. -/
theorem genDisc2C_of_born (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (lE : List (op_t α)) (hlE : listPermOf lE E)
    (hdts : ∀ a b : op_t α, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ x ∈ E, x.1 ≠ 0)
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (hborn : ∀ o ∈ E, ∃ π, listPermOf π (pastE Cfg E o) ∧
        respects π (loOnA (RGACondSig α) Cfg E) ∧ accurate o (applySeqR (init_st (α := α)) π)) :
    GenDisc2C Cfg E :=
  fun o hoE d hd =>
    genDisc2C_of_born_aux Cfg E lE hlE hdts hids0 htr hirr hborn
      (msr Cfg E lE o + 1) o hoE (Nat.lt_succ_self _) d hd

/-! ## Axiom audit -/

#print axioms msr_lt_of_mem
#print axioms fresh_at_past_fold
#print axioms genDisc2C_of_born

end Sal.ConditionedMRDTs.RGAK1Delta
