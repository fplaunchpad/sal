import Sal.ConditionedMRDTs.Development.RGA_ConvergenceEq
import Sal.ConditionedMRDTs.MRDT_Instances.RGA.RGA_MergeLinearization_TwoSided

/-!
# General-start canonical-state convergence, and the swap-oracle-free merge bridge

*Additive; modifies no existing file; 0 `sorry`.*

`RGA_ConvergenceEq.RGA_update_convergence_eq` proves canonical-state convergence
of two `loOnEq`-respecting enumerations from `init_st` / empty history.  The
merge bridge (`RGA_MergeLinearization_TwoSided.merge_fold_indep`) instead needs
convergence from the LCA state `l` (with history `F₀`) and, as written, imports
it through `eq_convergence` — which drags in the swap oracle `hSwap`/`hMSR`.

This file re-threads the WHOLE canonical-state pipeline from `init_st`/`[]` to a
general start `l`/`F₀`, and assembles the merge bridge WITHOUT any swap /
`Faithful` / `hMSR` hypothesis.

The engine (`canon_fold`, `CanonInv`, `CanonStepOK`, `CanonFoldOK`,
`eq_of_canonMatch2`) is already start/history-generic.  The only init-anchored
pieces are the transport lemmas `resolve_restrict` / `anc_transport` /
`chainOK_transport` (stated over `applySeqR init_st`, though their proofs use
ONLY the `CanonInv` projections) and the discharge `canonStepOK_of_genR` /
`canonFoldOK_of_genR`.  §1 restates the transport over abstract states; §2–§3
re-thread the discharge over `l`/`F₀`; §4 is the two deliverables.

## The honest extra premises for a general start

Starting from `l` (history `F₀`) instead of `init_st` (history `[]`) needs three
canon-side well-formedness facts about the LCA — none of them swap/`Faithful`:

* `FoldChainClosed F₀` — `F₀`'s inserts reference only anchors inserted in `F₀`
  (no dangling recorded chains); the transport recurses through `l`-nodes on a
  new event's anchor chain, so their own chains must stay inside `F₀`.
* `EFreshFrom E F₀` — every new event's id is fresh w.r.t. the LCA history: not
  inserted in `F₀`, not deleted in `F₀`, and not on any `F₀` recorded chain.
  ("New events after the LCA carry new ids.")
* `CanonInv F₀ l` — `l` IS the canonical state of `F₀`.

These replace the `init_st`-specific facts (`contains_init`, `canonInv_init`)
that the template used for free.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGAMergeConvergenceCanon

open Sal.Emulation (respects listPermOf)
open Sal.ConditionedMRDTs.ConditionedExecutionModel (ConditionedConfiguration)
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.GenericEqQuotient (loOnEq)
open Sal.ConditionedMRDTs.RGAInstance (rgaEqEquiv')
open Sal.ConditionedMRDTs.RGAInvUpdateQ (WfOpQ)
open Sal.ConditionedMRDTs.RGACanonFoldOK
open Sal.ConditionedMRDTs.RGAConvergenceEq
open Sal.ConditionedMRDTs.RGAConditionedConvergence (eq_trans)
open RGAMergeLinearization (applySeqR applySeqR_nil applySeqR_cons)
open RGACanonConvergence

/-! ## §0  The general-start premises and small membership algebra -/

/-- The generation discipline over an abstract order `R`, folded onto a general
start `l` (history `F₀`): each `E`-event is `accurate` at the fold of its
`E`-internal transitive `R`-dependency prefix ONTO `l`.  The `l`-anchored mirror
of `RGA_ConvergenceEq.GenDiscR` (which folds onto `init_st`). -/
def GenDiscR' (E : Set op_t) (R : op_t → op_t → Prop)
    (l : concrete_st) (_F₀ : List op_t) : Prop :=
  ∀ o ∈ E, ∀ d : List op_t, IsDepPreR E R o d → accurate o (applySeqR l d)

/-- The LCA history is internally chain-closed: every insert of `F₀` records
only anchors that are the root or are themselves inserted in `F₀`. -/
def FoldChainClosed (F₀ : List op_t) : Prop :=
  ∀ z rz ez az (pz : List ℕ), (z, rz, .Ins ez pz az) ∈ F₀ →
    ∀ c ∈ az :: pz, c = 0 ∨ insertedIn F₀ c

/-- Every delivered new event's id is fresh w.r.t. the LCA history `F₀`: not
inserted in `F₀`, not deleted in `F₀`, and absent from every `F₀` recorded
chain. -/
def EFreshFrom (E : Set op_t) (F₀ : List op_t) : Prop :=
  ∀ o ∈ E, ¬ insertedIn F₀ o.1 ∧ ¬ deletedIn F₀ o.1 ∧
    (∀ z rz ez az (pz : List ℕ), (z, rz, .Ins ez pz az) ∈ F₀ → o.1 ∉ az :: pz)

/-- Split `insertedIn` across a list append. -/
theorem insertedIn_append_or (L₁ L₂ : List op_t) (c : ℕ)
    (h : insertedIn (L₁ ++ L₂) c) : insertedIn L₁ c ∨ insertedIn L₂ c := by
  obtain ⟨r, e, p, a, hm⟩ := h
  rcases List.mem_append.mp hm with h' | h'
  · exact Or.inl ⟨r, e, p, a, h'⟩
  · exact Or.inr ⟨r, e, p, a, h'⟩

/-! ## §1  The transport lemmas, restated over abstract states

`RGA_CanonFoldOK.resolve_restrict` / `anc_transport` / `chainOK_transport` are
stated over `applySeqR init_st _`, but their proofs consult only the `CanonInv`
projections.  These are the same proofs with the fold states abstracted to
`sF`/`sD` and the applied lists to `AF`/`AD`. -/

/-- Chain restriction (state-generic `resolve_restrict`). -/
theorem resolve_restrict' (AF AD : List op_t) (sF sD : concrete_st)
    (hdsubF : ∀ x ∈ AD, x ∈ AF)
    (h0F : contains sF 0 = false)
    (hdomF : ∀ c, contains sF c = true ↔ survP AF c)
    (hdomD : ∀ c, contains sD c = true ↔ survP AD c) :
    ∀ L : List ℕ, (∀ c ∈ L, c = 0 ∨ insertedIn AD c) →
      resolve sF L = resolve sF (liveSub sD L) := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro hL
    have hcs := fun c' hc' => hL c' (List.mem_cons_of_mem c hc')
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
      have hins : insertedIn AD c := by
        rcases hL c (List.mem_cons_self ..) with h | h
        · exact absurd h hc0
        · exact h
      have hsurvF : survP AF c := (hdomF c).mp hcF
      have hcD : contains sD c = true :=
        (hdomD c).mpr ⟨hins, fun hd => hsurvF.2 (deletedIn_mono hdsubF hd)⟩
      rw [hfilter, if_pos hcD, resolve_live_head sF c cs hcF,
          resolve_live_head sF c _ hcF]

/-- Anchor transport (state-generic `anc_transport`). -/
theorem anc_transport' (AF AD : List op_t) (sF sD : concrete_st)
    (hdsubF : ∀ x ∈ AD, x ∈ AF)
    (hinvF : CanonInv AF sF)
    (hinvD : CanonInv AD sD)
    (hchains : ∀ z rz ez az (pz : List ℕ), (z, rz, .Ins ez pz az) ∈ AD →
        ∀ c ∈ az :: pz, c = 0 ∨ insertedIn AD c)
    (z : ℕ) (hzD : contains sD z = true) (hzF : contains sF z = true)
    (W : List ℕ) (hW : IsAncPath sD z W) :
    anc sF z = resolve sF W := by
  obtain ⟨h0F, _hwfF, hdomF, hinsF⟩ := hinvF
  obtain ⟨h0D, _hwfD, hdomD, hinsD⟩ := hinvD
  have hsurvD : survP AD z := (hdomD z).mp hzD
  obtain ⟨⟨rz, ez, pz, az, hmz⟩, _⟩ := id hsurvD
  obtain ⟨_, hlcz⟩ := hinsD z rz ez pz az hmz hsurvD
  obtain ⟨_, _, hpathz⟩ := hlcz
  have huniq : liveSub sD (az :: pz) = W :=
    isAncPath_unique sD h0D _ _ z hpathz hW
  have hsurvF : survP AF z := (hdomF z).mp hzF
  obtain ⟨_, hancF⟩ :=
    (canonMatch_of_canonInv AF sF ⟨h0F, _hwfF, hdomF, hinsF⟩).2
      z rz ez pz az (hdsubF _ hmz) hsurvF
  rw [hancF, ← resolve_eq_canonAnc AF sF hdomF (az :: pz),
      resolve_restrict' AF AD sF sD hdsubF h0F hdomF hdomD (az :: pz)
        (hchains z rz ez az pz hmz),
      huniq]

/-- `ChainOK` transport (state-generic `chainOK_transport`). -/
theorem chainOK_transport' (AF AD : List op_t) (sF sD : concrete_st)
    (hdsubF : ∀ x ∈ AD, x ∈ AF)
    (hinvF : CanonInv AF sF)
    (hinvD : CanonInv AD sD)
    (hchains : ∀ z rz ez az (pz : List ℕ), (z, rz, .Ins ez pz az) ∈ AD →
        ∀ c ∈ az :: pz, c = 0 ∨ insertedIn AD c) :
    ∀ (W : List ℕ) (z : ℕ),
      contains sD z = true →
      IsAncPath sD z W →
      ∀ c cs, liveSub sF (z :: W) = c :: cs →
        IsAncPath sF c cs := by
  intro W
  induction W with
  | nil =>
    intro z hzD hW c cs heq
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
      have := anc_transport' AF AD sF sD hdsubF hinvF hinvD hchains z hzD hzF [] hW
      simpa using this
  | cons w W' ih =>
    intro z hzD hW c cs heq
    have _hW1 : anc sD z = w := hW.1
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
        anc_transport' AF AD sF sD hdsubF hinvF hinvD hchains z hzD hzF (w :: W') hW
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

/-! ## §2  The per-event discharge over a general start `l` / history `F₀` -/

/-- Recorded-chain entries of a member of a good enumeration are root-or-inserted
in `F₀` together with that member's dependency sub-prefix (general-start
`RGA_ConvergenceEq.chain_entries_memR`).  An id live at the `l`-fold of the
dependency prefix is either live in `l` — hence a survivor, hence inserted in
`F₀` — or inserted along the prefix (`contains_fold_cases` + `CanonInv F₀ l`). -/
theorem chain_entries_memR' (E : Set op_t) (R : op_t → op_t → Prop)
    (l : concrete_st) (F₀ : List op_t) (hCanonL : CanonInv F₀ l)
    (hGen' : GenDiscR' E R l F₀) (F : List op_t)
    (hgF : GoodEnumR E R F) (t' r' e' a' : ℕ) (p' : List ℕ)
    (hm : (t', r', .Ins e' p' a') ∈ F) :
    ∀ c ∈ a' :: p',
      c = 0 ∨ insertedIn (F₀ ++ depListR E R F (t', r', .Ins e' p' a')) c := by
  intro c hc
  have hacc := hGen' _ (hgF.1 _ hm) _ (isDepPreR_depList_mem E R F _ hgF hm)
  rcases accurate_ins_entries t' r' e' a' p' _ hacc c hc with h | h
  · exact Or.inl h
  · rcases contains_fold_cases (depListR E R F (t', r', .Ins e' p' a')) l c h with hl | hd
    · exact Or.inr (insertedIn_mono (fun x hx => List.mem_append_left _ hx)
        ((hCanonL.2.2.1 c).mp hl).1)
    · exact Or.inr (insertedIn_mono (fun x hx => List.mem_append_right _ hx) hd)

/-- The dependency-fold package for the LAST event of a good enumeration, over a
general start (general-start `RGA_ConvergenceEq.depPack_lastR`).  The recorded
chains are closed within `F₀ ++ d` — for `F₀`-inserts by `FoldChainClosed`, for
`d`-inserts by `chain_entries_memR'` plus dependency-transitivity. -/
theorem depPack_lastR' (E : Set op_t) (R : op_t → op_t → Prop)
    (l : concrete_st) (F₀ : List op_t) (hCanonL : CanonInv F₀ l)
    (hGen' : GenDiscR' E R l F₀) (hF₀chains : FoldChainClosed F₀)
    (F : List op_t) (o : op_t) (hg : GoodEnumR E R (F ++ [o]))
    (hIH : ∀ σ : List op_t, σ.length ≤ F.length → GoodEnumR E R σ →
      CanonFoldOK F₀ l σ) :
    ∃ d : List op_t, (∀ x ∈ d, x ∈ F) ∧
      CanonInv (F₀ ++ d) (applySeqR l d) ∧
      accurate o (applySeqR l d) ∧
      (∀ z rz ez az (pz : List ℕ), (z, rz, .Ins ez pz az) ∈ F₀ ++ d →
        ∀ c ∈ az :: pz, c = 0 ∨ insertedIn (F₀ ++ d) c) := by
  obtain ⟨hgF, hoE, honF, _hlast⟩ := goodEnumR_append E R F o hg
  refine ⟨depListR E R F o, fun x hx => (mem_depListR.mp hx).1, ?_, ?_, ?_⟩
  · exact canon_fold (depListR E R F o) F₀ l hCanonL
      (hIH _ (List.length_filter_le _ _) (goodEnumR_depList_last E R F o hg))
  · exact hGen' o hoE _ (isDepPreR_depList_last E R F o hg)
  · intro z rz ez az pz hm c hc
    rcases List.mem_append.mp hm with hmF₀ | hmd
    · rcases hF₀chains z rz ez az pz hmF₀ c hc with h | h
      · exact Or.inl h
      · exact Or.inr (insertedIn_mono (fun x hx => List.mem_append_left _ hx) h)
    · have hmF : (z, rz, .Ins ez pz az) ∈ F := (mem_depListR.mp hmd).1
      rcases chain_entries_memR' E R l F₀ hCanonL hGen' F hgF z rz ez az pz hmF c hc with h | h
      · exact Or.inl h
      · refine Or.inr (insertedIn_mono ?_ h)
        intro x hx
        rcases List.mem_append.mp hx with hxF₀ | hxd
        · exact List.mem_append_left _ hxF₀
        · obtain ⟨hxF, _hxne, hxdep⟩ := mem_depListR.mp hxd
          refine List.mem_append_right _ (mem_depListR.mpr ⟨hxF, ?_, ?_⟩)
          · rintro rfl; exact honF hxF
          · exact Relation.TransGen.trans hxdep (mem_depListR.mp hmd).2.2

/-- **`canonStepOK_of_genR'`** — the per-event application discipline at the
event's OWN application point, over a general start `l` / history `F₀`.  The
general-start `RGA_ConvergenceEq.canonStepOK_of_genR`: `init_st` becomes `l`, `[]`
becomes `F₀`, `insertedIn_of_contains_fold` becomes `contains_fold_cases` +
`CanonInv F₀ l`, and freshness w.r.t. the LCA history is supplied by
`EFreshFrom`. -/
theorem canonStepOK_of_genR' (E : Set op_t) (R : op_t → op_t → Prop)
    (l : concrete_st) (F₀ : List op_t) (hCanonL : CanonInv F₀ l)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen' : GenDiscR' E R l F₀) (hF₀chains : FoldChainClosed F₀)
    (hEFresh : EFreshFrom E F₀)
    (F : List op_t) (o : op_t)
    (hg : GoodEnumR E R (F ++ [o]))
    (hIH : ∀ σ : List op_t, σ.length ≤ F.length → GoodEnumR E R σ →
      CanonFoldOK F₀ l σ) :
    CanonStepOK (F₀ ++ F) (applySeqR l F) o := by
  obtain ⟨hgF, hoE, honF, _hlast⟩ := goodEnumR_append E R F o hg
  have hinvF : CanonInv (F₀ ++ F) (applySeqR l F) :=
    canon_fold F F₀ l hCanonL (hIH F le_rfl hgF)
  have hfresh : ∀ L : List op_t, (∀ x ∈ L, x ∈ F) → ¬ insertedIn L o.1 := by
    rintro L hL ⟨r', e', p', a', hm⟩
    have hmF : (o.1, r', .Ins e' p' a') ∈ F := hL _ hm
    have hne : (o.1, r', .Ins e' p' a') ≠ o := fun hEq => honF (hEq ▸ hmF)
    exact hdts _ o (hgF.1 _ hmF) hoE hne rfl
  have hEF := hEFresh o hoE
  have depfold_absurd : ∀ (d' : List op_t), (∀ x ∈ d', x ∈ F) →
      contains (applySeqR l d') o.1 = true → False := by
    intro d' hd'F hcd'
    rcases contains_fold_cases d' l o.1 hcd' with hl | hd
    · exact hEF.1 ((hCanonL.2.2.1 o.1).mp hl).1
    · exact hfresh d' hd'F hd
  obtain ⟨d, hdsubF, hinvD, hacc, hchains⟩ :=
    depPack_lastR' E R l F₀ hCanonL hGen' hF₀chains F o hg hIH
  have hADsubAF : ∀ x ∈ F₀ ++ d, x ∈ F₀ ++ F := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (hdsubF x h)
  obtain ⟨t, r, op⟩ := o
  have ht0 : t ≠ 0 := hids0 (t, r, op) hoE
  cases op with
  | Ins e p a =>
    refine ⟨ht0, ?_, ?_, ?_, ?_, ?_⟩
    · cases hb : contains (applySeqR l F) t with
      | false => rfl
      | true =>
        rcases insertedIn_append_or F₀ F t ((hinvF.2.2.1 t).mp hb).1 with hi | hi
        · exact absurd hi hEF.1
        · exact absurd hi (hfresh F (fun _ h => h))
    · rintro ⟨t', r', p', hm⟩
      rcases List.mem_append.mp hm with hmF₀ | hmF
      · exact hEF.2.1 ⟨t', r', p', hmF₀⟩
      · have haccδ := hGen' _ (hgF.1 _ hmF) _ (isDepPreR_depList_mem E R F _ hgF hmF)
        simp only [accurate, opLeaf, opPath] at haccδ
        rcases haccδ with ⟨hx0, _⟩ | ⟨hxl, _⟩
        · exact ht0 hx0
        · exact depfold_absurd (depListR E R F (t', r', .Del p' t))
            (fun x hx => (mem_depListR.mp hx).1) hxl
    · intro hmem
      rcases accurate_ins_entries t r e a p _ hacc t hmem with h | h
      · exact ht0 h
      · exact depfold_absurd d hdsubF h
    · intro t' r' e' p' a' hm hmem
      rcases List.mem_append.mp hm with hmF₀ | hmF
      · exact hEF.2.2 t' r' e' a' p' hmF₀ hmem
      · rcases chain_entries_memR' E R l F₀ hCanonL hGen' F hgF t' r' e' a' p' hmF t hmem
          with h | h
        · exact ht0 h
        · rcases insertedIn_append_or F₀ (depListR E R F (t', r', .Ins e' p' a')) t h
            with hi | hi
          · exact absurd hi hEF.1
          · exact hfresh (depListR E R F (t', r', .Ins e' p' a'))
              (fun x hx => (mem_depListR.mp hx).1) hi
    · simp only [accurate, opLeaf, opPath] at hacc
      rcases hacc with ⟨ha0, hp0⟩ | ⟨hal, hpath⟩
      · subst ha0; subst hp0
        intro c cs heq
        have hnil : liveSub (applySeqR l F) [0] = [] := by
          unfold liveSub
          rw [List.filter_cons, List.filter_nil, hinvF.1]
          simp
        rw [hnil] at heq
        exact absurd heq (by simp)
      · exact fun c cs heq =>
          chainOK_transport' (F₀ ++ F) (F₀ ++ d) (applySeqR l F) (applySeqR l d)
            hADsubAF hinvF hinvD hchains p a hal hpath c cs heq
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
      · exact (anc_transport' (F₀ ++ F) (F₀ ++ d) (applySeqR l F) (applySeqR l d)
          hADsubAF hinvF hinvD hchains x hxl hcx p hpath).symm

/-- **`canonFoldOK_of_genR'`** — every good enumeration over `R` is
`CanonFoldOK`-disciplined FROM the general start `l` / history `F₀` (general-start
`RGA_ConvergenceEq.canonFoldOK_of_genR`).  Strong induction on length. -/
theorem canonFoldOK_of_genR' (E : Set op_t) (R : op_t → op_t → Prop)
    (l : concrete_st) (F₀ : List op_t) (hCanonL : CanonInv F₀ l)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen' : GenDiscR' E R l F₀) (hF₀chains : FoldChainClosed F₀)
    (hEFresh : EFreshFrom E F₀) :
    ∀ (n : ℕ) (σ : List op_t), σ.length ≤ n → GoodEnumR E R σ →
      CanonFoldOK F₀ l σ := by
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
      have hgF := (goodEnumR_append E R F o hg).1
      exact canonFoldOK_append F F₀ l o (ih F hlenF hgF)
        (canonStepOK_of_genR' E R l F₀ hCanonL hdts hids0 hGen' hF₀chains hEFresh F o hg
          (fun τ hτ hgτ => ih τ (hτ.trans hlenF) hgτ))

/-! ## §3  Instantiation at the framework order `loOnEq rgaEqEquiv' WfOpQ` -/

/-- **`canonFoldOK_of_loOnEq'`** — every `loOnEq`-respecting enumeration of the
backward-closed delivered set is `CanonFoldOK`-disciplined FROM the LCA state `l`
(general-start `RGA_ConvergenceEq.canonFoldOK_of_loOnEq`).  Id-uniqueness from
the execution model; LCA-history well-formedness from `FoldChainClosed`/
`EFreshFrom`. -/
theorem canonFoldOK_of_loOnEq'
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (l : concrete_st) (F₀ : List op_t) (hCanonL : CanonInv F₀ l)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen' : GenDiscR' E (loEqRGA Cfg E) l F₀)
    (hF₀chains : FoldChainClosed F₀) (hEFresh : EFreshFrom E F₀)
    (π : List op_t) (hπp : listPermOf π E)
    (hπr : respects π (loOnEq rgaEqEquiv' WfOpQ Cfg.vis E)) :
    CanonFoldOK F₀ l π :=
  canonFoldOK_of_genR' E (loEqRGA Cfg E) l F₀ hCanonL
    (fun _ _ ha hb hne => C.distinctTs E hE ha hb hne)
    hids0 hGen' hF₀chains hEFresh π.length π le_rfl
    ⟨fun x hx => (hπp.2 x).mp hx, hπp.1, hπr,
     fun _x _hx z hz _ _ => (hπp.2 z).mpr hz⟩

/-! ## §4  DELIVERABLE 1 — the linchpin -/

/-- **`merge_fold_convergence_eq` — RGA merge-side convergence over the framework
order, FROM the LCA state `l`.**  Two `loOnEq`-respecting enumerations of the same
backward-closed set `E` fold from `l` to observationally equal states.  This is
the exact fact the merge bridge needs to drop the swap oracle: it is proved
purely by `canon_fold` + `eq_of_canonMatch2` (both folds are `CanonMatch (F₀ ++ E)`),
with NO swap, NO `Faithful`, NO `hMSR`.  The premises are canon-side: the LCA is
canonical (`hCanonL`), its history is chain-closed (`hF₀chains`) and disjoint from
the new ids (`hEFresh`); the enumeration hypotheses; and the (conditional)
generation discipline `hGen'`. -/
theorem merge_fold_convergence_eq
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (l : concrete_st) (F₀ : List op_t) (hCanonL : CanonInv F₀ l)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hF₀chains : FoldChainClosed F₀) (hEFresh : EFreshFrom E F₀)
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ E) (h₂p : listPermOf π₂ E)
    (h₁r : respects π₁ (loOnEq rgaEqEquiv' WfOpQ Cfg.vis E))
    (h₂r : respects π₂ (loOnEq rgaEqEquiv' WfOpQ Cfg.vis E))
    (hGen' : GenDiscR' E (loEqRGA Cfg E) l F₀) :
    eq (applySeqR l π₁) (applySeqR l π₂) := by
  have c₁ := canon_fold π₁ F₀ l hCanonL
    (canonFoldOK_of_loOnEq' C Cfg l F₀ hCanonL E hE hids0 hGen' hF₀chains hEFresh π₁ h₁p h₁r)
  have c₂ := canon_fold π₂ F₀ l hCanonL
    (canonFoldOK_of_loOnEq' C Cfg l F₀ hCanonL E hE hids0 hGen' hF₀chains hEFresh π₂ h₂p h₂r)
  refine eq_of_canonMatch2 (F₀ ++ π₁) (F₀ ++ π₂) _ _ ?_
    (canonMatch_of_canonInv _ _ c₁) (canonMatch_of_canonInv _ _ c₂)
  intro o
  constructor
  · intro h
    rcases List.mem_append.mp h with hF | hp
    · exact List.mem_append_left _ hF
    · exact List.mem_append_right _ ((Iff.trans (h₁p.2 o) (h₂p.2 o).symm).mp hp)
  · intro h
    rcases List.mem_append.mp h with hF | hp
    · exact List.mem_append_left _ hF
    · exact List.mem_append_right _ ((Iff.trans (h₁p.2 o) (h₂p.2 o).symm).mpr hp)

/-! ## §5  DELIVERABLE 2 — the merge bridge with NO swap oracle -/

/-- **`merge_fold_indep_canon` — interleave independence with NO swap oracle.**
Given the bridge for one reference interleave `π₀` (`href`), any other
`loOnEq`-respecting interleave `π` of the same set `E` also satisfies it — by
`merge_fold_convergence_eq` (canonical-state convergence from `l`) and
`eq`-transitivity.  Unlike `RGA_MergeLinearization_TwoSided.merge_fold_indep`
there is NO `hSwap`, NO `hMSR`, NO `Faithful` premise: the ONLY hypotheses are
`href` and the canon-convergence premises (LCA canonical/chain-closed/fresh,
back-closed, distinct-ids, enum hyps, conditional generation discipline). -/
theorem merge_fold_indep_canon
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (l a b : concrete_st) (F₀ : List op_t) (hCanonL : CanonInv F₀ l)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hF₀chains : FoldChainClosed F₀) (hEFresh : EFreshFrom E F₀)
    (π₀ π : List op_t)
    (href : eq (merge l a b) (applySeqR l π₀))
    (h₀p : listPermOf π₀ E) (hπp : listPermOf π E)
    (h₀r : respects π₀ (loOnEq rgaEqEquiv' WfOpQ Cfg.vis E))
    (hπr : respects π (loOnEq rgaEqEquiv' WfOpQ Cfg.vis E))
    (hGen' : GenDiscR' E (loEqRGA Cfg E) l F₀) :
    eq (merge l a b) (applySeqR l π) :=
  eq_trans _ _ _ href
    (merge_fold_convergence_eq C Cfg l F₀ hCanonL E hE hids0 hF₀chains hEFresh
      π₀ π h₀p hπp h₀r hπr hGen')

/-! ## §6  Axiom audit -/

#print axioms merge_fold_convergence_eq
#print axioms merge_fold_indep_canon

end Sal.ConditionedMRDTs.RGAMergeConvergenceCanon
