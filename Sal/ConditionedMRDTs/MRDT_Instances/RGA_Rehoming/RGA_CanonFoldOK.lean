import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_CanonConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_SubchainResolve
import Sal.ConditionedMRDTs.Framework.ConditionedConvergence
import Sal.MRDTs.RGA_Rehoming.RGA_Tombstone_Free_MRDT
import Sal.MRDTs.RGA_Rehoming.RGA_Reachability_Invariant
import Sal.ConditionedMRDTs.Refutations.G2_Transport_Probe
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.Framework.ConditionedExecutionModel

/-!
# Discharging `CanonFoldOK` from the per-event generation discipline

*0 `sorry`.*

`RGA_CanonConvergence.RGA_update_convergence_canon` proves update convergence
conditional on `CanonFoldOK [] (init_st (α := α)) π`, the per-event discipline at each
event's OWN application point along the enumeration.  This file derives that
discipline from an honest per-event GENERATION hypothesis (`GenDisc2C`, §1:
`accurate` at the event's dependency prefix, the transitive-closure form of
`RGA_GenDischarge2`'s `GenDisc2`) plus the execution-model allocation facts
(`ConditionedConfiguration.distinctTs`, nonzero ids), for any `loOnA`-respecting
enumeration of the delivered set.  Headline: `RGA_update_convergence_final`
(§6), two `loOnA`-respecting enumerations of `E` fold from `(init_st (α := α))` to
observationally equal states, with NO `CanonFoldOK` residual, NO swap oracle,
NO per-prefix `Faithful`, NO `DepComp`, NO `EligibleThread`, and (notably) NO
`ReachInv`: the canonical-state engine self-supplies the reachable-state facts.

## `GenDisc2C` vs `GenDisc2`: the one honest delta

`RGA_GenDischarge2.GenDisc2` pins `accurate o` at enumerations of exactly `o`'s
DIRECT `loOnA`-predecessors (`IsDepPre`).  That set is not backward-closed
(`loOnA` is not transitive), so its fold is not in general a state any replica
ever holds, and it is too weak to seat the cross-chain coherence this
derivation needs.  `GenDisc2C` (§1) replaces "direct predecessor" with the
`E`-internal TRANSITIVE closure `DepC` (`IsDepPreC`): the dependency prefix is
the closure of `o`'s `loOnA`-past, which IS backward-closed, i.e. itself a
genuine execution prefix.  For the RGA every `loOnA`-edge is a `vis`-edge
(`rc = Either` empties the rc-arm), so `DepC ⊆ vis` and the closure prefix is a
sub-past of `o`'s causal past: a concurrent `Del` of `o`'s target is still
excluded, and the satisfiability story of `GenDisc2` carries over verbatim.
This is still strictly a GENERATION discipline: per event, at that event's own
dependency prefix, never at reordered application prefixes.

## Shape of the derivation

Strong induction on enumeration length (§5).  For the last event `o` of a good
enumeration `F ++ [o]`, `CanonStepOK F (fold F) o` (§4) is assembled from:
* freshness/no-reuse/absent-from-chains, `distinctTs` + the fold-domain lemma
  (`insertedIn_of_contains_fold`, §2: only an `Ins t` ever adds `t`) + each
  event's `accurate` at its dependency prefix (chain entries are 0-or-inserted
  there, §2);
* `ChainOK`/`DelOK`, the transport §3: `o`'s accurate chain at its dependency
  fold `s_d`, the induction hypothesis's `CanonInv` at BOTH `s_d` and the
  application fold `s_F` (the dependency prefix is a strictly shorter good
  enumeration, this is where the transitive closure is load-bearing), and
  `IsAncPath`-uniqueness pin each surviving entry's stored anchor at `s_F` to
  the next `F`-surviving entry of `o`'s recorded chain.  This is exactly the
  regime where `accurate o` FAILS at `s_F` (a concurrent `Del` of `o`'s anchor
  may sit in `F`): `ChainOK` is derived directly, not via `accurate`-at-`F`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open Classical

namespace Sal.ConditionedMRDTs.RGACanonFoldOK

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation (respects listPermOf)
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA)
open Sal.ConditionedMRDTs.ConditionedExecutionModel (ConditionedConfiguration)
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open RGAMergeLinearization (applySeqR applySeqR_nil applySeqR_cons)
open RGACanonConvergence

/-! ## §1  The per-event generation discipline via transitive closure -/

/-- An `E`-internal dependency edge: an `loOnA`-edge whose source is delivered. -/
def DepE (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (z x : op_t α) : Prop :=
  z ∈ E ∧ loOnA (RGACondSig α) Cfg E z x

/-- Transitive dependency: the `E`-internal transitive closure of `loOnA`.
For the RGA every `loOnA`-edge is a `vis`-edge (`rc = Either` empties the
rc-arm of `loOnC`), so `DepC z o → Cfg.vis z o`: transitive dependencies stay
inside the causal past, and a concurrent op is never a `DepC`-predecessor. -/
def DepC (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) : op_t α → op_t α → Prop :=
  Relation.TransGen (DepE Cfg E)

/-- **`IsDepPreC Cfg E o d`**, `d` is a `loOnA`-respecting `Nodup` enumeration
of exactly `o`'s strict TRANSITIVE dependencies in `E`.  The transitive-closure
form of `RGA_GenDischarge2.IsDepPre`: membership is pinned both ways, so the prefix set
is unique; unlike the direct-predecessor set it is backward-closed under
`loOnA`, the dependency prefix is itself a genuine execution prefix. -/
def IsDepPreC (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (o : op_t α) (d : List (op_t α)) : Prop :=
  (∀ x ∈ d, x ∈ E) ∧ d.Nodup ∧ respects d (loOnA (RGACondSig α) Cfg E) ∧
  (∀ z ∈ E, z ≠ o → DepC Cfg E z o → z ∈ d) ∧
  (∀ x ∈ d, x ≠ o ∧ DepC Cfg E x o)

/-- **`GenDisc2C`, the per-event generation discipline.**  Each delivered
event's recorded path is its target's TRUE live ancestor chain at the fold of
the event's (transitively closed) dependency prefix.  A per-event, single-
prefix assertion about each event's generation, never about reordered
application prefixes.  Satisfiable exactly as `GenDisc2` (see the header): the
ops that could falsify `accurate o` at the prefix are concurrent with `o`,
hence not `DepC`-below it, hence excluded. -/
def GenDisc2C (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) : Prop :=
  ∀ o ∈ E, ∀ d : List (op_t α), IsDepPreC Cfg E o d →
    accurate o (applySeqR (init_st (α := α)) d)

/-- A good enumeration (of a backward-closed portion of the delivery): members
delivered, no duplicates, `loOnA`-respecting, and closed under `E`-internal
`loOnA`-predecessors.  Every full `loOnA`-respecting enumeration of `E` is
good (closure is vacuous), and (the engine of §5) so is every prefix and
every dependency sub-prefix of a good enumeration. -/
def GoodEnum (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (σ : List (op_t α)) : Prop :=
  (∀ x ∈ σ, x ∈ E) ∧ σ.Nodup ∧ respects σ (loOnA (RGACondSig α) Cfg E) ∧
  (∀ x ∈ σ, ∀ z ∈ E, z ≠ x → loOnA (RGACondSig α) Cfg E z x → z ∈ σ)

/-! ## §2  Fold-domain groundwork: ids enter only by their own `Ins` -/

/-- A single step adds no id but an `Ins`'s own. -/
theorem contains_do_cases (s : concrete_st α) (o : op_t α) (c : ℕ)
    (h : contains (do_ s o) c = true) :
    contains s c = true ∨ (∃ r e p a, o = (c, r, .Ins e p a)) := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e p a =>
    rw [show do_ s (t, r, .Ins e p a) = upd s t (e, resolve s (a :: p)) from by
          simp only [do_], lemma_InDomUpd1] at h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | h
    · exact Or.inr ⟨r, e, p, a, rfl⟩
    · exact Or.inl h
  | Del p x =>
    rw [contains_doDel, Bool.and_eq_true] at h
    exact Or.inl h.1

/-- Fold-domain: an id live after a fold was live before or inserted in it. -/
theorem contains_fold_cases :
    ∀ (L : List (op_t α)) (s : concrete_st α) (c : ℕ),
      contains (applySeqR s L) c = true → contains s c = true ∨ insertedIn L c := by
  intro L
  induction L with
  | nil => intro s c h; exact Or.inl h
  | cons o rest ih =>
    intro s c h
    rw [applySeqR_cons] at h
    rcases ih (do_ s o) c h with h' | ⟨r, e, p, a, hm⟩
    · rcases contains_do_cases s o c h' with h'' | ⟨r, e, p, a, rfl⟩
      · exact Or.inl h''
      · exact Or.inr ⟨r, e, p, a, List.mem_cons_self ..⟩
    · exact Or.inr ⟨r, e, p, a, List.mem_cons_of_mem o hm⟩

theorem contains_init (c : ℕ) : contains (init_st (α := α)) c = false := by
  simp [init_st]

/-- An id live at a fold from `(init_st (α := α))` was inserted in the fold. -/
theorem insertedIn_of_contains_fold (L : List (op_t α)) (c : ℕ)
    (h : contains (applySeqR (init_st (α := α)) L) c = true) : insertedIn L c := by
  rcases contains_fold_cases L (init_st (α := α)) c h with h' | h'
  · rw [contains_init] at h'; exact Bool.noConfusion h'
  · exact h'

/-- A live id not deleted along a fold stays live. -/
theorem contains_fold_pres :
    ∀ (L : List (op_t α)) (s : concrete_st α) (c : ℕ),
      contains s c = true → ¬ deletedIn L c →
      contains (applySeqR s L) c = true := by
  intro L
  induction L with
  | nil => intro s c h _; exact h
  | cons o rest ih =>
    intro s c h hnd
    rw [applySeqR_cons]
    refine ih (do_ s o) c ?_ (fun ⟨t, r, p, hm⟩ => hnd ⟨t, r, p, List.mem_cons_of_mem o hm⟩)
    obtain ⟨t, r, op⟩ := o
    cases op with
    | Ins e p a =>
      rw [show do_ s (t, r, .Ins e p a) = upd s t (e, resolve s (a :: p)) from by
            simp only [do_], lemma_InDomUpd1, h, Bool.or_true]
    | Del p x =>
      have hcx : c ≠ x := fun hEq =>
        hnd ⟨t, r, p, by rw [hEq]; exact List.mem_cons_self ..⟩
      rw [contains_doDel, h, Bool.true_and, bne_iff_ne]
      exact hcx

/-- A survivor of the applied list is live at its fold from `(init_st (α := α))`. -/
theorem contains_fold_of_surv :
    ∀ (L : List (op_t α)) (s : concrete_st α) (c : ℕ),
      insertedIn L c → ¬ deletedIn L c → contains (applySeqR s L) c = true := by
  intro L
  induction L with
  | nil => intro s c ⟨r, e, p, a, hm⟩ _; exact absurd hm (by simp)
  | cons o rest ih =>
    intro s c ⟨r, e, p, a, hm⟩ hnd
    have hnd' : ¬ deletedIn rest c :=
      fun ⟨t', r', p', hm'⟩ => hnd ⟨t', r', p', List.mem_cons_of_mem o hm'⟩
    rw [applySeqR_cons]
    rcases List.mem_cons.mp hm with rfl | hm'
    · refine contains_fold_pres rest _ c ?_ hnd'
      rw [show do_ s (c, r, .Ins e p a) = upd s c (e, resolve s (a :: p)) from by
            simp only [do_], lemma_InDomUpd1]
      simp
    · exact ih (do_ s o) c ⟨r, e, p, a, hm'⟩ hnd'

/-- `insertedIn` is monotone under list inclusion. -/
theorem insertedIn_mono {L₁ L₂ : List (op_t α)} (h : ∀ x ∈ L₁, x ∈ L₂) {c : ℕ}
    (hi : insertedIn L₁ c) : insertedIn L₂ c := by
  obtain ⟨r, e, p, a, hm⟩ := hi
  exact ⟨r, e, p, a, h _ hm⟩

/-- `deletedIn` is monotone under list inclusion. -/
theorem deletedIn_mono {L₁ L₂ : List (op_t α)} (h : ∀ x ∈ L₁, x ∈ L₂) {c : ℕ}
    (hd : deletedIn L₁ c) : deletedIn L₂ c := by
  obtain ⟨t, r, p, hm⟩ := hd
  exact ⟨t, r, p, h _ hm⟩

/-- The stored-anchor chain of a node is unique (root `0` unstored). -/
theorem isAncPath_unique (s : concrete_st α) (h0 : contains s 0 = false) :
    ∀ (L₁ L₂ : List ℕ) (z : ℕ), IsAncPath s z L₁ → IsAncPath s z L₂ → L₁ = L₂ := by
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ z h1 h2
    cases L₂ with
    | nil => rfl
    | cons c cs =>
      simp only [IsAncPath] at h1 h2
      rw [h1] at h2
      rw [← h2.1, h0] at h2
      exact absurd h2.2.1 (by simp)
  | cons c cs ih =>
    intro L₂ z h1 h2
    cases L₂ with
    | nil =>
      simp only [IsAncPath] at h1 h2
      rw [h2] at h1
      rw [← h1.1, h0] at h1
      exact absurd h1.2.1 (by simp)
    | cons c' cs' =>
      simp only [IsAncPath] at h1 h2
      have hcc : c = c' := by rw [← h1.1, ← h2.1]
      subst hcc
      rw [ih cs' c h1.2.2 h2.2.2]

/-- Entries of an accurate `Ins`'s recorded chain are root-or-live there. -/
theorem accurate_ins_entries (t r : ℕ) (e : α) (a : ℕ) (p : List ℕ) (s : concrete_st α)
    (hacc : accurate (t, r, .Ins e p a) s) :
    ∀ c ∈ a :: p, c = 0 ∨ contains s c = true := by
  simp only [accurate, opLeaf, opPath] at hacc
  intro c hc
  rcases hacc with ⟨ha0, hp0⟩ | ⟨hal, hpath⟩
  · subst ha0; subst hp0
    exact Or.inl (by simpa using hc)
  · rcases List.mem_cons.mp hc with rfl | hc'
    · exact Or.inr hal
    · exact Or.inr (isAncPath_mem s a p hpath c hc')

/-! ## §3  The dependency layer: good enumerations and dependency sub-prefixes -/

/-- Peeling the last event of a good enumeration: the prefix is good, the last
event is delivered, fresh in the prefix, and `loOnA`-above nothing in it. -/
theorem goodEnum_append (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (F : List (op_t α)) (o : op_t α)
    (h : GoodEnum Cfg E (F ++ [o])) :
    GoodEnum Cfg E F ∧ o ∈ E ∧ o ∉ F ∧
      (∀ x ∈ F, ¬ loOnA (RGACondSig α) Cfg E o x) := by
  obtain ⟨hmem, hnd, hresp, hclose⟩ := h
  have hndF : F.Nodup ∧ ([o] : List (op_t α)).Nodup ∧ ∀ a ∈ F, ∀ b ∈ [o], a ≠ b :=
    List.nodup_append.mp hnd
  have honF : o ∉ F :=
    fun hoF => hndF.2.2 o hoF o (List.mem_singleton_self o) rfl
  have hcross : ∀ a ∈ F, ∀ b ∈ [o], ¬ loOnA (RGACondSig α) Cfg E b a :=
    (List.pairwise_append.mp hresp).2.2
  have hlast : ∀ x ∈ F, ¬ loOnA (RGACondSig α) Cfg E o x :=
    fun x hx => hcross x hx o (List.mem_singleton_self o)
  refine ⟨⟨fun x hx => hmem x (List.mem_append_left _ hx),
           hndF.1,
           List.Pairwise.sublist (List.sublist_append_left F [o]) hresp,
           ?_⟩,
          hmem o (List.mem_append_right _ (List.mem_singleton_self o)), honF, hlast⟩
  intro x hx z hz hzx hlo
  rcases List.mem_append.mp (hclose x (List.mem_append_left _ hx) z hz hzx hlo) with h' | h'
  · exact h'
  · exact absurd hlo (List.mem_singleton.mp h' ▸ hlast x hx)

/-- Transitive dependencies of a member of a good enumeration are members. -/
theorem mem_of_depC (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (σ : List (op_t α)) (hg : GoodEnum Cfg E σ) :
    ∀ (x z : op_t α), DepC Cfg E z x → x ∈ σ → z ∈ σ := by
  intro x z h
  induction h with
  | @single b h' =>
    intro hb
    by_cases hzb : z = b
    · rwa [hzb]
    · exact hg.2.2.2 b hb z h'.1 hzb h'.2
  | @tail b c _ hbc ih =>
    intro hc
    refine ih ?_
    by_cases hbc' : b = c
    · rwa [hbc']
    · exact hg.2.2.2 c hc b hbc.1 hbc' hbc.2

/-- The dependency sub-prefix of `w` carved out of an enumeration `F`:
`F` filtered to `w`'s strict transitive dependencies, in `F`'s order. -/
noncomputable def depList (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (F : List (op_t α)) (w : op_t α) : List (op_t α) :=
  F.filter (fun z => decide (z ≠ w ∧ DepC Cfg E z w))

theorem mem_depList {Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig}
    {E : Set (op_t α)} {F : List (op_t α)} {w x : op_t α} :
    x ∈ depList Cfg E F w ↔ x ∈ F ∧ x ≠ w ∧ DepC Cfg E x w := by
  simp only [depList, List.mem_filter, decide_eq_true_eq]

/-- The carved sub-prefix IS a dependency prefix (`IsDepPreC`), provided `F`
contains all of `w`'s strict transitive dependencies. -/
theorem isDepPreC_depList (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (F : List (op_t α)) (w : op_t α)
    (hmemE : ∀ x ∈ F, x ∈ E) (hnd : F.Nodup)
    (hresp : respects F (loOnA (RGACondSig α) Cfg E))
    (hcomp : ∀ z ∈ E, z ≠ w → DepC Cfg E z w → z ∈ F) :
    IsDepPreC Cfg E w (depList Cfg E F w) := by
  refine ⟨fun x hx => hmemE x (mem_depList.mp hx).1,
          hnd.filter _,
          List.Pairwise.sublist (List.filter_sublist) hresp,
          fun z hz hzw hdep => mem_depList.mpr ⟨hcomp z hz hzw hdep, hzw, hdep⟩,
          fun x hx => (mem_depList.mp hx).2⟩

/-- For the LAST event of a good enumeration, its dependency sub-prefix of the
strict prefix is itself GOOD, the backward closure that fails for the
direct-predecessor set (`IsDepPre`) holds for the transitive one. -/
theorem goodEnum_depList_last (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (F : List (op_t α)) (o : op_t α)
    (hg : GoodEnum Cfg E (F ++ [o])) :
    GoodEnum Cfg E (depList Cfg E F o) := by
  obtain ⟨hgF, _hoE, _honF, hlast⟩ := goodEnum_append Cfg E F o hg
  refine ⟨fun x hx => hgF.1 x (mem_depList.mp hx).1,
          hgF.2.1.filter _,
          List.Pairwise.sublist (List.filter_sublist) hgF.2.2.1,
          ?_⟩
  intro x hx z hz hzx hlo
  obtain ⟨hxF, _hxo, hxdep⟩ := mem_depList.mp hx
  have hzF : z ∈ F := hgF.2.2.2 x hxF z hz hzx hlo
  have hzo : z ≠ o := by
    rintro rfl
    exact hlast x hxF hlo
  exact mem_depList.mpr ⟨hzF, hzo, Relation.TransGen.head ⟨hz, hlo⟩ hxdep⟩

/-- `IsDepPreC` for the last event, from goodness of the whole enumeration. -/
theorem isDepPreC_depList_last (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (F : List (op_t α)) (o : op_t α)
    (hg : GoodEnum Cfg E (F ++ [o])) :
    IsDepPreC Cfg E o (depList Cfg E F o) := by
  obtain ⟨hgF, _hoE, honF, _hlast⟩ := goodEnum_append Cfg E F o hg
  refine isDepPreC_depList Cfg E F o hgF.1 hgF.2.1 hgF.2.2.1 ?_
  intro z hz hzo hdep
  have hzρ : z ∈ F ++ [o] :=
    mem_of_depC Cfg E (F ++ [o]) hg o z hdep
      (List.mem_append_right _ (List.mem_singleton_self o))
  rcases List.mem_append.mp hzρ with h' | h'
  · exact h'
  · exact absurd (List.mem_singleton.mp h') hzo

/-- `IsDepPreC` for a MEMBER of a good enumeration. -/
theorem isDepPreC_depList_mem (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (F : List (op_t α)) (w : op_t α)
    (hgF : GoodEnum Cfg E F) (hw : w ∈ F) :
    IsDepPreC Cfg E w (depList Cfg E F w) :=
  isDepPreC_depList Cfg E F w hgF.1 hgF.2.1 hgF.2.2.1
    (fun z _hz _hzw hdep => mem_of_depC Cfg E F hgF w z hdep hw)

/-! ## §4  Transport: dependency-fold chains pin application-fold anchors

Throughout, `sF` is the fold of the application prefix `F` and `sD` the fold of
the dependency sub-prefix `d ⊆ F` (as lists: every `d`-member is an `F`-member).
`CanonInv` at both states is supplied by the §5 induction. -/

/-- **Chain restriction.**  For a chain `L` whose entries are root-or-inserted
in `d`, resolving `L` at `sF` equals resolving its `sD`-live sublist at `sF`:
an entry dead at `sD` (deleted among the dependencies) is dead at `sF` too
(deletes persist), and an entry live at `sF` was already live at `sD` (its
insert is in `d`; no delete of it is in `F` at all). -/
theorem resolve_restrict (F d : List (op_t α))
    (hdsubF : ∀ x ∈ d, x ∈ F)
    (h0F : contains (applySeqR (init_st (α := α)) F) 0 = false)
    (hdomF : ∀ c, contains (applySeqR (init_st (α := α)) F) c = true ↔ survP F c)
    (hdomD : ∀ c, contains (applySeqR (init_st (α := α)) d) c = true ↔ survP d c) :
    ∀ L : List ℕ, (∀ c ∈ L, c = 0 ∨ insertedIn d c) →
      resolve (applySeqR (init_st (α := α)) F) L
        = resolve (applySeqR (init_st (α := α)) F) (liveSub (applySeqR (init_st (α := α)) d) L) := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro hL
    have hcs := fun c' hc' => hL c' (List.mem_cons_of_mem c hc')
    set sF := applySeqR (init_st (α := α)) F
    set sD := applySeqR (init_st (α := α)) d
    show resolve sF (c :: cs) = resolve sF (liveSub sD (c :: cs))
    have hfilter : liveSub sD (c :: cs)
        = if contains sD c then c :: liveSub sD cs else liveSub sD cs := by
      simp only [liveSub, List.filter_cons]
    cases hcF : contains sF c with
    | false =>
      rw [resolve_dead_head sF c cs hcF, hfilter]
      cases hcD : contains sD c with
      | false => rw [if_neg (by simp)]; exact ih hcs
      | true =>
        rw [if_pos rfl, resolve_dead_head sF c _ hcF]
        exact ih hcs
    | true =>
      have hc0 : c ≠ 0 := fun hEq => by rw [hEq, h0F] at hcF; exact Bool.noConfusion hcF
      have hins : insertedIn d c := by
        rcases hL c (List.mem_cons_self ..) with h | h
        · exact absurd h hc0
        · exact h
      have hsurvF : survP F c := (hdomF c).mp hcF
      have hcD : contains sD c = true :=
        (hdomD c).mpr ⟨hins, fun hd => hsurvF.2 (deletedIn_mono hdsubF hd)⟩
      rw [hfilter, if_pos hcD, resolve_live_head sF c cs hcF,
          resolve_live_head sF c _ hcF]

/-- **Anchor transport (the workhorse).**  A node `z` live at both folds, whose
`sD`-ancestor chain is `W`, has `sF`-anchor `resolve sF W`, i.e. the first
`F`-survivor of the remainder of the chain.  Proof: `z` is a `d`-surviving
insert; `CanonInv d` gives its `LiveChain` at `sD`, whose path component equals
`W` by uniqueness of stored-anchor chains; `CanonInv F` pins `anc sF z` to
`canonAnc F` of `z`'s recorded chain = `resolve sF` of it (`resolve_eq_canonAnc`),
and `resolve_restrict` collapses the recorded chain to its `sD`-live sublist `W`. -/
theorem anc_transport (F d : List (op_t α))
    (hdsubF : ∀ x ∈ d, x ∈ F)
    (hinvF : CanonInv F (applySeqR (init_st (α := α)) F))
    (hinvD : CanonInv d (applySeqR (init_st (α := α)) d))
    (hchains : ∀ z rz ez az (pz : List ℕ), (z, rz, .Ins ez pz az) ∈ d →
        ∀ c ∈ az :: pz, c = 0 ∨ insertedIn d c)
    (z : ℕ) (hzD : contains (applySeqR (init_st (α := α)) d) z = true)
    (hzF : contains (applySeqR (init_st (α := α)) F) z = true)
    (W : List ℕ) (hW : IsAncPath (applySeqR (init_st (α := α)) d) z W) :
    anc (applySeqR (init_st (α := α)) F) z = resolve (applySeqR (init_st (α := α)) F) W := by
  obtain ⟨h0F, _hwfF, hdomF, hinsF⟩ := hinvF
  obtain ⟨h0D, _hwfD, hdomD, hinsD⟩ := hinvD
  set sF := applySeqR (init_st (α := α)) F
  set sD := applySeqR (init_st (α := α)) d
  have hsurvD : survP d z := (hdomD z).mp hzD
  obtain ⟨⟨rz, ez, pz, az, hmz⟩, _⟩ := id hsurvD
  obtain ⟨_, hlcz⟩ := hinsD z rz ez pz az hmz hsurvD
  obtain ⟨_, _, hpathz⟩ := hlcz
  have huniq : liveSub sD (az :: pz) = W :=
    isAncPath_unique sD h0D _ _ z hpathz hW
  have hsurvF : survP F z := (hdomF z).mp hzF
  obtain ⟨_, hancF⟩ :=
    (canonMatch_of_canonInv F sF ⟨h0F, _hwfF, hdomF, hinsF⟩).2
      z rz ez pz az (hdsubF _ hmz) hsurvF
  rw [hancF, ← resolve_eq_canonAnc F sF hdomF (az :: pz),
      resolve_restrict F d hdsubF h0F hdomF hdomD (az :: pz)
        (hchains z rz ez az pz hmz),
      huniq]

/-- **`ChainOK` transport**: any chain that is genuine at the dependency fold
satisfies `ChainOK` at the application fold, its `sF`-live sublist is a
genuine `sF`-ancestor path.  Induction along the chain; `anc_transport` pins
each surviving entry's stored anchor to the next `sF`-survivor.  This covers
exactly the concurrent-anchor-delete case where `accurate`-at-`sF` fails. -/
theorem chainOK_transport (F d : List (op_t α))
    (hdsubF : ∀ x ∈ d, x ∈ F)
    (hinvF : CanonInv F (applySeqR (init_st (α := α)) F))
    (hinvD : CanonInv d (applySeqR (init_st (α := α)) d))
    (hchains : ∀ z rz ez az (pz : List ℕ), (z, rz, .Ins ez pz az) ∈ d →
        ∀ c ∈ az :: pz, c = 0 ∨ insertedIn d c) :
    ∀ (W : List ℕ) (z : ℕ),
      contains (applySeqR (init_st (α := α)) d) z = true →
      IsAncPath (applySeqR (init_st (α := α)) d) z W →
      ∀ c cs, liveSub (applySeqR (init_st (α := α)) F) (z :: W) = c :: cs →
        IsAncPath (applySeqR (init_st (α := α)) F) c cs := by
  intro W
  induction W with
  | nil =>
    intro z hzD hW c cs heq
    set sF := applySeqR (init_st (α := α)) F
    have hfilter : liveSub sF [z]
        = if contains sF z then [z] else [] := by
      simp only [liveSub, List.filter_cons, List.filter_nil]
    cases hzF : contains sF z with
    | false =>
      rw [hfilter, if_neg (by rw [hzF]; exact Bool.false_ne_true)] at heq
      exact absurd heq (by simp)
    | true =>
      rw [hfilter, if_pos hzF] at heq
      obtain ⟨rfl, rfl⟩ : z = c ∧ ([] : List ℕ) = cs := by
        constructor <;> [exact (List.cons.injEq .. ▸ heq).1; exact (List.cons.injEq .. ▸ heq).2]
      show IsAncPath sF z []
      simp only [IsAncPath]
      have := anc_transport F d hdsubF hinvF hinvD hchains z hzD hzF [] hW
      simpa using this
  | cons w W' ih =>
    intro z hzD hW c cs heq
    set sF := applySeqR (init_st (α := α)) F
    set sD := applySeqR (init_st (α := α)) d
    have hW1 : anc sD z = w := hW.1
    have hW2 : contains sD w = true := hW.2.1
    have hW3 : IsAncPath sD w W' := hW.2.2
    have hfilter : liveSub sF (z :: w :: W')
        = if contains sF z then z :: liveSub sF (w :: W') else liveSub sF (w :: W') := by
      simp only [liveSub, List.filter_cons]
    cases hzF : contains sF z with
    | false =>
      rw [hfilter, if_neg (by rw [hzF]; exact Bool.false_ne_true)] at heq
      exact ih w hW2 hW3 c cs heq
    | true =>
      rw [hfilter, if_pos hzF] at heq
      have hcz : z = c := (List.cons.injEq .. ▸ heq).1
      have hcs : liveSub sF (w :: W') = cs := (List.cons.injEq .. ▸ heq).2
      subst hcz
      rw [← hcs]
      have hanc : anc sF z = resolve sF (w :: W') :=
        anc_transport F d hdsubF hinvF hinvD hchains z hzD hzF (w :: W') hW
      cases hls : liveSub sF (w :: W') with
      | nil =>
        show IsAncPath sF z []
        simp only [IsAncPath]
        rw [hanc]
        exact resolve_of_liveSub_nil sF (w :: W') hls
      | cons c' cs' =>
        show IsAncPath sF z (c' :: cs')
        simp only [IsAncPath]
        refine ⟨hanc.trans (resolve_of_liveSub_cons sF _ c' cs' hls), ?_, ?_⟩
        · exact liveSub_live sF (w :: W') c' (by rw [hls]; simp)
        · exact ih w hW2 hW3 c' cs' hls

/-! ## §5  The per-step discharge -/

/-- `CanonFoldOK` extends on the right by one disciplined step. -/
theorem canonFoldOK_append :
    ∀ (π F : List (op_t α)) (s : concrete_st α) (o : op_t α),
      CanonFoldOK F s π → CanonStepOK (F ++ π) (applySeqR s π) o →
      CanonFoldOK F s (π ++ [o]) := by
  intro π
  induction π with
  | nil =>
    intro F s o _ hstep
    exact ⟨by simpa using hstep, trivial⟩
  | cons x xs ih =>
    intro F s o hfold hstep
    obtain ⟨hx, hrest⟩ := hfold
    refine ⟨hx, ih (F ++ [x]) (do_ s x) o hrest ?_⟩
    rw [show (F ++ [x]) ++ xs = F ++ (x :: xs) from by simp]
    exact hstep

/-- Recorded-chain entries of a member of a good enumeration are root-or-
inserted in that member's dependency sub-prefix (its `accurate` chain at its
dependency fold is live there, and ids enter a fold only by their own `Ins`). -/
theorem chain_entries_mem (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (hGen : GenDisc2C Cfg E) (F : List (op_t α))
    (hgF : GoodEnum Cfg E F) (t' r' : ℕ) (e' : α) (a' : ℕ) (p' : List ℕ)
    (hm : (t', r', .Ins e' p' a') ∈ F) :
    ∀ c ∈ a' :: p',
      c = 0 ∨ insertedIn (depList Cfg E F (t', r', .Ins e' p' a')) c := by
  intro c hc
  have hacc := hGen _ (hgF.1 _ hm) _ (isDepPreC_depList_mem Cfg E F _ hgF hm)
  rcases accurate_ins_entries t' r' e' a' p' _ hacc c hc with h | h
  · exact Or.inl h
  · exact Or.inr (insertedIn_of_contains_fold _ c h)

/-- The dependency-fold package for the LAST event of a good enumeration:
its dependency sub-prefix (a strictly shorter good enumeration, so the strong
induction supplies `CanonInv` at its fold), its `accurate` fact there, and the
closedness of all recorded chains of the sub-prefix within the sub-prefix. -/
theorem depPack_last (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (hGen : GenDisc2C Cfg E)
    (F : List (op_t α)) (o : op_t α) (hg : GoodEnum Cfg E (F ++ [o]))
    (hIH : ∀ σ : List (op_t α), σ.length ≤ F.length → GoodEnum Cfg E σ →
      CanonFoldOK [] (init_st (α := α)) σ) :
    ∃ d : List (op_t α), (∀ x ∈ d, x ∈ F) ∧
      CanonInv d (applySeqR (init_st (α := α)) d) ∧
      accurate o (applySeqR (init_st (α := α)) d) ∧
      (∀ z rz ez az (pz : List ℕ), (z, rz, .Ins ez pz az) ∈ d →
        ∀ c ∈ az :: pz, c = 0 ∨ insertedIn d c) := by
  obtain ⟨hgF, hoE, honF, _hlast⟩ := goodEnum_append Cfg E F o hg
  refine ⟨depList Cfg E F o, fun x hx => (mem_depList.mp hx).1, ?_, ?_, ?_⟩
  · exact canon_fold _ [] (init_st (α := α)) canonInv_init
      (hIH _ (List.length_filter_le _ _) (goodEnum_depList_last Cfg E F o hg))
  · exact hGen o hoE _ (isDepPreC_depList_last Cfg E F o hg)
  · intro z rz ez az pz hm c hc
    have hmF : (z, rz, .Ins ez pz az) ∈ F := (mem_depList.mp hm).1
    rcases chain_entries_mem Cfg E hGen F hgF z rz ez az pz hmF c hc with h | h
    · exact Or.inl h
    · refine Or.inr (insertedIn_mono ?_ h)
      intro x hx
      obtain ⟨hxF, _hxne, hxdep⟩ := mem_depList.mp hx
      refine mem_depList.mpr ⟨hxF, ?_, ?_⟩
      · rintro rfl; exact honF hxF
      · exact Relation.TransGen.trans hxdep (mem_depList.mp hm).2.2

/-- **`canonStepOK_of_gen`**, the application discipline at the event's OWN
application point, from the generation discipline.  The heart of the file. -/
theorem canonStepOK_of_gen (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α))
    (hdts : ∀ a b : op_t α, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2C Cfg E)
    (F : List (op_t α)) (o : op_t α)
    (hg : GoodEnum Cfg E (F ++ [o]))
    (hIH : ∀ σ : List (op_t α), σ.length ≤ F.length → GoodEnum Cfg E σ →
      CanonFoldOK [] (init_st (α := α)) σ) :
    CanonStepOK F (applySeqR (init_st (α := α)) F) o := by
  obtain ⟨hgF, hoE, honF, _hlast⟩ := goodEnum_append Cfg E F o hg
  have hinvF : CanonInv F (applySeqR (init_st (α := α)) F) :=
    canon_fold F [] (init_st (α := α)) canonInv_init (hIH F le_rfl hgF)
  -- o's id was never allocated by any insert seen from F (id uniqueness)
  have hfresh : ∀ L : List (op_t α), (∀ x ∈ L, x ∈ F) → ¬ insertedIn L o.1 := by
    rintro L hL ⟨r', e', p', a', hm⟩
    have hmF : (o.1, r', .Ins e' p' a') ∈ F := hL _ hm
    have hne : (o.1, r', .Ins e' p' a') ≠ o := fun hEq => honF (hEq ▸ hmF)
    exact hdts _ o (hgF.1 _ hmF) hoE hne rfl
  obtain ⟨d, hdsubF, hinvD, hacc, hchains⟩ := depPack_last Cfg E hGen F o hg hIH
  obtain ⟨t, r, op⟩ := o
  have ht0 : t ≠ 0 := hids0 (t, r, op) hoE
  cases op with
  | Ins e p a =>
    refine ⟨ht0, ?_, ?_, ?_, ?_, ?_⟩
    · -- t is absent from the application fold
      cases hb : contains (applySeqR (init_st (α := α)) F) t with
      | false => rfl
      | true =>
        exact absurd (insertedIn_of_contains_fold F t hb)
          (hfresh F (fun _ hx => hx))
    · -- t was never deleted in F: a Del of t is accurate at ITS dependency
      -- prefix, so t is inserted there, impossible for a fresh id
      rintro ⟨t', r', p', hm⟩
      have haccδ := hGen _ (hgF.1 _ hm) _ (isDepPreC_depList_mem Cfg E F _ hgF hm)
      simp only [accurate, opLeaf, opPath] at haccδ
      rcases haccδ with ⟨hx0, _⟩ | ⟨hxl, _⟩
      · exact ht0 hx0
      · exact hfresh (depList Cfg E F (t', r', .Del p' t))
          (fun x hx => (mem_depList.mp hx).1)
          (insertedIn_of_contains_fold _ t hxl)
    · -- t is not on its own recorded chain
      intro hmem
      rcases accurate_ins_entries t r e a p _ hacc t hmem with h | h
      · exact ht0 h
      · exact hfresh d hdsubF (insertedIn_of_contains_fold d t h)
    · -- t is not on any recorded chain in F
      intro t' r' e' p' a' hm hmem
      rcases chain_entries_mem Cfg E hGen F hgF t' r' e' a' p' hm t hmem with h | h
      · exact ht0 h
      · exact hfresh (depList Cfg E F (t', r', .Ins e' p' a'))
          (fun x hx => (mem_depList.mp hx).1) h
    · -- ChainOK at the application fold, via the §4 transport
      simp only [accurate, opLeaf, opPath] at hacc
      rcases hacc with ⟨ha0, hp0⟩ | ⟨hal, hpath⟩
      · subst ha0; subst hp0
        intro c cs heq
        have hnil : liveSub (applySeqR (init_st (α := α)) F) [0] = [] := by
          unfold liveSub
          rw [List.filter_cons, List.filter_nil, hinvF.1]
          simp
        rw [hnil] at heq
        exact absurd heq (by simp)
      · exact fun c cs heq =>
          chainOK_transport F d hdsubF hinvF hinvD hchains p a hal hpath c cs heq
  | Del p x =>
    simp only [accurate, opLeaf, opPath] at hacc
    rcases hacc with ⟨hx0, hp0⟩ | ⟨hxl, hpath⟩
    · subst hx0; subst hp0
      refine ⟨fun _ => rfl, fun hcx => ?_⟩
      rw [hinvF.1] at hcx
      exact Bool.noConfusion hcx
    · refine ⟨fun hx0 => ?_, fun hcx => ?_⟩
      · rw [hx0, hinvD.1] at hxl
        exact Bool.noConfusion hxl
      · exact (anc_transport F d hdsubF hinvF hinvD hchains x hxl hcx p hpath).symm

/-! ## §6  The induction and the headline -/

/-- **`canonFoldOK_of_gen`**, every good enumeration is `CanonFoldOK`-
disciplined.  Strong induction on length: both the strict prefix and the last
event's dependency sub-prefix are strictly shorter good enumerations (the
latter is where `IsDepPreC`'s backward closure is load-bearing). -/
theorem canonFoldOK_of_gen (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α))
    (hdts : ∀ a b : op_t α, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2C Cfg E) :
    ∀ (n : ℕ) (σ : List (op_t α)), σ.length ≤ n → GoodEnum Cfg E σ →
      CanonFoldOK [] (init_st (α := α)) σ := by
  intro n
  induction n with
  | zero =>
    intro σ hlen _
    have hσ : σ = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hσ
    trivial
  | succ n ih =>
    intro σ hlen hg
    rcases List.eq_nil_or_concat σ with rfl | ⟨F, o, hEq⟩
    · trivial
    · rw [List.concat_eq_append] at hEq
      subst hEq
      have hlenF : F.length ≤ n := by
        rw [List.length_append] at hlen
        simp only [List.length_singleton] at hlen
        omega
      have hgF := (goodEnum_append Cfg E F o hg).1
      exact canonFoldOK_append F [] (init_st (α := α)) o (ih F hlenF hgF)
        (canonStepOK_of_gen Cfg E hdts hids0 hGen F o hg
          (fun τ hτ hgτ => ih τ (hτ.trans hlenF) hgτ))

/-- Every `loOnA`-respecting enumeration of the delivered set is disciplined:
`CanonFoldOK` holds with NO residual beyond the generation discipline and the
execution model's id-uniqueness. -/
theorem canonFoldOK_of_genDisc
    (C : ConditionedConfiguration (RGACondSig α))
    (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2C Cfg E)
    (π : List (op_t α)) (hπp : listPermOf π E)
    (hπr : respects π (loOnA (RGACondSig α) Cfg E)) :
    CanonFoldOK [] (init_st (α := α)) π :=
  canonFoldOK_of_gen Cfg E
    (fun _ _ ha hb hne => C.distinctTs E hE ha hb hne)
    hids0 hGen π.length π le_rfl
    ⟨fun x hx => (hπp.2 x).mp hx, hπp.1, hπr,
     fun _x _hx z hz _ _ => (hπp.2 z).mpr hz⟩

/-- **HEADLINE, RGA update convergence from the generation discipline.**
Two `loOnA`-respecting enumerations of the same backward-closed delivered set
`E` fold from `(init_st (α := α))` to observationally equal states.

Premises, in full: the execution model (`C`, with `hE : C.BackClosed E`,
supplying only global id-uniqueness `distinct_ts`, and nonzero ids `hids0`),
the enumeration hypotheses (`listPermOf`/`respects`), and the per-event
generation discipline `GenDisc2C` (each event `accurate` at its own dependency
prefix).  NOTHING else: no `CanonFoldOK` residual (it is DERIVED, §5–§6), no
`EligibleThread`, no per-prefix `Faithful`, no `DepComp`, no swap oracle, and
no `ReachInv`, the canonical-state engine of `RGA_CanonConvergence` supplies
the reachable-state facts itself. -/
theorem RGA_update_convergence_final
    (C : ConditionedConfiguration (RGACondSig α))
    (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (π₁ π₂ : List (op_t α))
    (h₁p : listPermOf π₁ E) (h₂p : listPermOf π₂ E)
    (h₁r : respects π₁ (loOnA (RGACondSig α) Cfg E))
    (h₂r : respects π₂ (loOnA (RGACondSig α) Cfg E))
    (hGen : GenDisc2C Cfg E) :
    eq (applySeqR (init_st (α := α)) π₁) (applySeqR (init_st (α := α)) π₂) :=
  RGA_update_convergence_canon π₁ π₂
    (fun o => (h₁p.2 o).trans (h₂p.2 o).symm)
    (canonFoldOK_of_genDisc C Cfg E hE hids0 hGen π₁ h₁p h₁r)
    (canonFoldOK_of_genDisc C Cfg E hE hids0 hGen π₂ h₂p h₂r)

/-! ## §7  Axiom audit -/

#print axioms canonStepOK_of_gen
#print axioms canonFoldOK_of_gen
#print axioms RGA_update_convergence_final

end Sal.ConditionedMRDTs.RGACanonFoldOK
