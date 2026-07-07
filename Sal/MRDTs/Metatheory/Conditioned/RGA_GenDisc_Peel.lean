import Sal.MRDTs.Metatheory.Conditioned.RGA_K1_Wiring

/-!
# GenDisc2C discharge, part 1 — the pointwise peel and its bricks

*Additive; modifies no existing file; 0 `sorry`.*

The critical-path leaf after K1 is `GenDisc2C Cfg E` (task #32): each event accurate at the fold
of its dependency prefix.  Discharge design (recorded in `AgentNotes.md`): born-applicability gives
accuracy at the fold of the FULL causal past; a past-op `z` that is NOT a dependency satisfies
`¬ appliesDependsOn o z` — *by definition* its application never flips `o`'s applicability at ANY
state — so non-dependencies **peel pointwise off the end** of a deps-first past enumeration, with
no state reasoning whatsoever.  The reorder to deps-first is engine convergence on the strictly
smaller past set (well-founded: `past z ⊊ past o`).

This file proves the bounded bricks of that design:

* `not_appliesDependsOn_iff` — the classical unfolding: `¬ appliesDependsOn o z` IS pointwise
  applicability-invariance.
* `nondep_not_appliesDependsOn` — a past-op with no `loOnA`-edge into `o` is pointwise-invisible
  to `o`'s applicability (the semantic content of "not a dependency").
* `applicable_peel_suffix` — the peel: appending any list of pointwise-invisible ops to a fold
  leaves `o`'s applicability unchanged.
* `loOnA_ev_free` — for the RGA, `loOnA` does not depend on the ambient event set (`rc = Either`
  kills the only set-dependent clause), so relativizing the discharge to `past o` is free.
* `pastE_loOnA_closed` — the causal past (within `E`) is closed under `loOnA`-predecessors, so
  past enumerations are `GoodEnum`s at `E` verbatim.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.Metatheory.RGAK1Delta

open Sal.Emulation
open Sal.Metatheory.G2Probe (RGACondSig loOnC rc_is_Either)
open Sal.Metatheory.ConditionedConvergence (loOnA appliesDependsOn)
open RGAMergeLinearization (applySeqR applySeqR_cons)
open Sal.Metatheory.RGACanonFoldOK

/-! ## §1  Pointwise invisibility -/

/-- `¬ appliesDependsOn o z` unfolded: `z`'s application never changes `o`'s applicability, at
any state. -/
theorem not_appliesDependsOn_iff (D : ConditionedMRDTSig) (o z : Op D.AppOp) :
    ¬ appliesDependsOn D o z ↔
      ∀ s, D.applicable o s = D.applicable o (D.update s z) := by
  constructor
  · intro h s
    by_contra hne
    exact h ⟨s, hne⟩
  · rintro h ⟨s, hne⟩
    exact hne (h s)

/-- **A non-dependency past-op is pointwise invisible to `o`'s applicability.**  If `z` is
causally below `o` but carries no `loOnA` edge into `o`, then `¬ appliesDependsOn o z` — the
`vis ∧ appliesDependsOn` arm of `loOnA` is exactly what would catch it. -/
theorem nondep_not_appliesDependsOn (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev : Set op_t) (o z : op_t)
    (hvis : Cfg.vis z o)
    (hnlo : ¬ loOnA RGACondSig Cfg ev z o) :
    ¬ appliesDependsOn RGACondSig o z :=
  fun hdep => hnlo (Or.inr ⟨hvis, hdep⟩)

/-! ## §2  The peel -/

/-- **The pointwise peel.**  Appending ops that are pointwise invisible to `o`'s applicability
leaves it unchanged — peeled one at a time from the right, each step an instance of the pointwise
fact at the current fold state; NO other property of the state is used. -/
theorem applicable_peel_suffix (o : op_t) (Z : List op_t)
    (hinv : ∀ z ∈ Z, ¬ appliesDependsOn RGACondSig o z) :
    ∀ s : concrete_st,
      RGACondSig.applicable o (applySeqR s Z) = RGACondSig.applicable o s := by
  induction Z with
  | nil => intro s; rfl
  | cons z rest ih =>
    intro s
    have hz : RGACondSig.applicable o (RGACondSig.update s z) = RGACondSig.applicable o s :=
      ((not_appliesDependsOn_iff RGACondSig o z).mp (hinv z (by simp)) s).symm
    have hrest := ih (fun z' hz' => hinv z' (by simp [hz'])) (do_ s z)
    calc RGACondSig.applicable o (applySeqR s (z :: rest))
        = RGACondSig.applicable o (applySeqR (do_ s z) rest) := by rw [applySeqR_cons]
      _ = RGACondSig.applicable o (do_ s z) := hrest
      _ = RGACondSig.applicable o s := hz

/-! ## §3  `loOnA` is ambient-set-free for the RGA -/

/-- For the RGA, `loOnC` does not depend on the ambient event set: the only set-dependent clause
(the concurrent-arm absorber) sits under `rc = Fst_then_snd`, which `rc = Either` refutes. -/
theorem loOnC_ev_free (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev ev' : Set op_t) (e₁ e₂ : op_t) :
    loOnC RGACondSig Cfg ev e₁ e₂ ↔ loOnC RGACondSig Cfg ev' e₁ e₂ := by
  constructor <;>
  · rintro (h | ⟨_, _, hrc, _⟩)
    · exact Or.inl h
    · rw [rc_is_Either] at hrc
      exact absurd hrc (fun h => Sal.Emulation.RcRes.noConfusion h)

/-- For the RGA, `loOnA` does not depend on the ambient event set. -/
theorem loOnA_ev_free (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev ev' : Set op_t) (e₁ e₂ : op_t) :
    loOnA RGACondSig Cfg ev e₁ e₂ ↔ loOnA RGACondSig Cfg ev' e₁ e₂ := by
  constructor <;>
  · rintro (h | h)
    · exact Or.inl ((loOnC_ev_free Cfg _ _ e₁ e₂).mp h)
    · exact Or.inr h

/-! ## §4  The causal past is a `GoodEnum` domain -/

/-- The causal past of `o` within `E`. -/
def pastE (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (o : op_t) : Set op_t :=
  {z | z ∈ E ∧ Cfg.vis z o}

/-- **The causal past is `loOnA`-predecessor-closed in `E`**: an `loOnA`-predecessor is a `vis`
predecessor, and `vis` is transitive.  Hence any `loOnA`-respecting enumeration of `pastE` is a
`GoodEnum` at `E` verbatim — the engine applies to past enumerations with no relativization. -/
theorem pastE_loOnA_closed (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (o : op_t)
    (htr : ∀ {a b c : op_t}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (x : op_t) (hx : x ∈ pastE Cfg E o) (z : op_t) (hz : z ∈ E)
    (hlo : loOnA RGACondSig Cfg E z x) : z ∈ pastE Cfg E o :=
  ⟨hz, htr (loOnA_imp_vis Cfg E z x hlo) hx.2⟩

/-- A `loOnA`-respecting enumeration of the causal past is a `GoodEnum` at `E`. -/
theorem goodEnum_of_past_perm (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (o : op_t)
    (htr : ∀ {a b c : op_t}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (π : List op_t) (hπp : listPermOf π (pastE Cfg E o))
    (hπr : respects π (loOnA RGACondSig Cfg E)) :
    GoodEnum Cfg E π := by
  refine ⟨fun x hx => ((hπp.2 x).mp hx).1, hπp.1, hπr, ?_⟩
  intro x hx z hz _hzx hlo
  exact (hπp.2 z).mpr (pastE_loOnA_closed Cfg E o htr x ((hπp.2 x).mp hx) z hz hlo)

/-- The dependency set sits inside the causal past: a transitive dependency of `o` is a causal
predecessor of `o` lying in `E`. -/
theorem depC_mem_pastE (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (o : op_t)
    (htr : ∀ {a b c : op_t}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (z : op_t) (h : DepC Cfg E z o) : z ∈ pastE Cfg E o :=
  ⟨depC_src_mem Cfg E z o h, depC_imp_vis Cfg E htr z o h⟩

/-! ## §5  Relativization — dependency structure restricts to a closed subset

The strong-induction step works at `E' := pastE Cfg E o` and calls the EXISTING engine
(`canonFoldOK_of_gen`) there verbatim.  What makes this free: a `DepC`-chain into a member of a
`vis`-closed subset never leaves the subset, so `DepC` (and hence `IsDepPreC`) agree between `E`
and `E'` on `E'`-targets. -/

/-- A dependency chain into a member of an `loOnA`-pred-closed subset stays in the subset:
`DepC` at `E` into `w ∈ E'` implies `DepC` at `E'`. -/
theorem depC_restrict (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E E' : Set op_t) (hsub : ∀ x ∈ E', x ∈ E)
    (hcl : ∀ x ∈ E', ∀ z ∈ E, loOnA RGACondSig Cfg E z x → z ∈ E')
    (z w : op_t) (hw : w ∈ E') (h : DepC Cfg E z w) : DepC Cfg E' z w := by
  induction h using Relation.TransGen.head_induction_on with
  | single hzw =>
    rename_i z'
    exact Relation.TransGen.single
      ⟨hcl w hw z' hzw.1 hzw.2, ((loOnA_ev_free Cfg E E' _ _).mp hzw.2)⟩
  | head h' hc ihc =>
    rename_i z' c
    -- the intermediate c is in E' (it is DepC-below w at E', by IH's chain)
    have hcE' : c ∈ E' := by
      have := ihc
      -- source of the E'-chain c →* w is in E'
      exact depC_src_mem Cfg E' c w this
    exact Relation.TransGen.head
      ⟨hcl c hcE' z' h'.1 h'.2, ((loOnA_ev_free Cfg E E' _ _).mp h'.2)⟩
      ihc

/-- `DepC` at a subset is `DepC` at the ambient set (membership weakening). -/
theorem depC_mono_ev (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E E' : Set op_t) (hsub : ∀ x ∈ E', x ∈ E)
    (z w : op_t) (h : DepC Cfg E' z w) : DepC Cfg E z w := by
  induction h with
  | single hzw => exact Relation.TransGen.single ⟨hsub _ hzw.1, (loOnA_ev_free Cfg E' E _ _).mp hzw.2⟩
  | tail _ hbc ih =>
    exact Relation.TransGen.tail ih ⟨hsub _ hbc.1, (loOnA_ev_free Cfg E' E _ _).mp hbc.2⟩

/-- **`IsDepPreC` transports from a closed subset to the ambient set**: an `E'`-dependency prefix
of `o ∈ E'` is an `E`-dependency prefix — completeness holds because an `E`-dependency chain into
`o` stays inside `E'` (`depC_restrict`). -/
theorem isDepPreC_of_restrict (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E E' : Set op_t) (hsub : ∀ x ∈ E', x ∈ E)
    (hcl : ∀ x ∈ E', ∀ z ∈ E, loOnA RGACondSig Cfg E z x → z ∈ E')
    (o : op_t) (ho : o ∈ E') (d : List op_t)
    (h : IsDepPreC Cfg E' o d) : IsDepPreC Cfg E o d := by
  obtain ⟨hmem, hnd, hresp, hcomp, hsound⟩ := h
  refine ⟨fun x hx => hsub x (hmem x hx), hnd,
    List.Pairwise.imp (fun hn hl => hn ((loOnA_ev_free Cfg E E' _ _).mp hl)) hresp,
    ?_, ?_⟩
  · intro z _hz hzo hdep
    have hdep' : DepC Cfg E' z o := depC_restrict Cfg E E' hsub hcl z o ho hdep
    exact hcomp z (depC_src_mem Cfg E' z o hdep') hzo hdep'
  · intro x hx
    obtain ⟨hxo, hdep⟩ := hsound x hx
    exact ⟨hxo, depC_mono_ev Cfg E E' hsub x o hdep⟩

/-! ## Axiom audit -/

#print axioms not_appliesDependsOn_iff
#print axioms nondep_not_appliesDependsOn
#print axioms applicable_peel_suffix
#print axioms loOnA_ev_free
#print axioms goodEnum_of_past_perm
#print axioms depC_mem_pastE
#print axioms depC_restrict
#print axioms isDepPreC_of_restrict

end Sal.Metatheory.RGAK1Delta
