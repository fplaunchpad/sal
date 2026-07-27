import Sal.ConditionedMRDTs.Metatheory.VC_Minimal_Core

/-!
# The restricted converse of adequacy — the completeness direction (task #114, phase 3)

Adequacy (`Adequacy.lean`) is `{VC1..VC8} ⟹ RA-linearizable`. This file mechanizes
the **converse** validated pen-and-paper + Python in phase 2
(`whiteboard/converse-note.md`, harness `whiteboard/litmus/converse_check.py`):

> A **canonical RA-linearizable** flat MRDT satisfies the four *core* verification
> conditions {VC5-at-empty, VC6, VC7, VC8} on its reachable, weakly-closed event sets.

The full converse (RA-lin ⟹ all eight VCs) is refuted — the four *shell* VCs
(VC1..VC4) quantify over the whole op/state universe and have RA-linearizable
violators off the reachable-canonical domain. Only the four config-driven core
laws, on reachable weakly-closed sets, admit the converse. This is the mirror of
the phase-1 shrink: adequacy shrank its contract to the four-law core
(`VC_Minimal_Core.lean`), and the converse recovers exactly that core from RA-lin.

## The hypothesis (`CanonicalRALin3`), stated faithfully

The Lean `IsRALinearizable3` (`Adequacy.lean:35`) is **existence-only** and
**per-configuration**: it says each version's state is *some* `lo`-respecting fold
of its event set. It does **not** supply the two ingredients the note's
"canonical RA-linearizable" needs — the *Join* (a merge lands on the canonical
state of the union) and *convergence* (folds are unique, so `sig` is a function).
So `IsRALinearizable3` alone is too weak to be the converse hypothesis. Following
the note's definitional setup ("existence + convergence" plus "the merge is that
fold"), the faithful hypothesis is the pair

* **`join`** : `JoinLemma3 D` — the operational half, `mergeL(σ(E₁∩E₂), σ(E₁),
  σ(E₂)) = σ(E₁∪E₂)` on backward-closed sides (existing framework definition);
* **`converges`** : canonical states are **unique** on every reachable
  weakly-closed set (`sig` is a well-defined function) — the convergence half,
  taken as an explicit hypothesis because the framework only *derives* it from the
  update layer (`isCanonicalState_unique_u`), which the converse does not assume.

This is exactly the "add the convergence/canonical hypothesis" the phase-3 brief
mandates, not a silent strengthening: convergence is guarded by the note's own
domain (reachable, weakly-closed), and only its uniqueness half is used (existence
of every canonical state below is supplied by the concrete `IsCanonicalState`
witnesses each VC already carries and by the Join).

## What is forced by what (matches the note's table)

| core VC | forced by | Join instances | convergence |
|---------|-----------|----------------|-------------|
| VC5-empty / VC5⁺ | the Join | 1 | uniqueness on the set |
| VC6 | the Join | 4 | uniqueness on `E₁∪E₂` |
| VC7 | the Join | 6 (note: "5 distinct") | uniqueness on `E₁∪E₂` |
| VC8 | the Join **and** convergence | 1 | via `sig_peel_maximal` |

VC5-empty, VC6, VC7 are pure Join reductions: every merge node rewrites to "the
merge produces the canonical state of the union," and the two sides collapse to
`σ(union)`; convergence closes each as the *uniqueness* of that canonical state.
VC8 additionally invokes the fold-peel `sig(U) = e(sig(U∖e))`
(`sig_peel_maximal`), the one genuinely new lemma, whose content is convergence
used as an equation. So the converse reduces to `JoinLemma3` (all four) plus
`sig_peel_maximal` (only VC8).

## Note-derivation audit

Every step of the note's "The derivation" section went through in Lean unchanged.
The structural facts L1 (`wc_union`/`wc_inter`), L2 (`closure_diff_of_max`), L3
(`downset_subset`/`downset_max`), L4 (`loOn_mono`, inside `isCanonicalState_snoc`)
and L5/L6 (`sig_peel_maximal` = `isCanonicalState_snoc` + convergence) were all
either present in the framework or one-liners. No note step failed.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1. Structural set lemmas (the note's L1, plus the diff/inter rewrites) -/

/-- Removing a point from `E` and intersecting with a subset `S ⊆ E` is the same
as puncturing `S`. (The `s₀`-slot rewrite of every Join instance below: a merge's
LCA set `(E∖e) ∩ S` is `S∖e`.) -/
theorem diff_inter_of_subset {α : Type} {E S : Set α} {e : α} (h : S ⊆ E) :
    (E \ {e}) ∩ S = S \ {e} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨_, hne⟩, hs⟩; exact ⟨hs, hne⟩
  · rintro ⟨hs, hne⟩; exact ⟨⟨h hs, hne⟩, hs⟩

/-- Re-adding a subset `S ⊆ E` that contains the removed point recovers `E`.
(The union-slot rewrite of every Join instance below: `(E∖e) ∪ S = E`.) -/
theorem diff_union_of_subset {α : Type} {E S : Set α} {e : α}
    (h : S ⊆ E) (he : e ∈ S) : (E \ {e}) ∪ S = E := by
  ext x
  simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨hx, _⟩ | hs)
    · exact hx
    · exact h hs
  · intro hx
    by_cases hxe : x = e
    · exact Or.inr (hxe ▸ he)
    · exact Or.inl ⟨hx, hxe⟩

/-- **(L1) union of weakly-closed sets is weakly closed.** -/
theorem wc_union {D : ConditionedMRDTSig}
    {C : Sal.Emulation.Configuration D.toCRDTSig} {E₁ E₂ : Set (Op D.AppOp)}
    (h₁ : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ E₁ → a ∈ E₁)
    (h₂ : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ E₂ → a ∈ E₂) :
    ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ E₁ ∪ E₂ → a ∈ E₁ ∪ E₂ := by
  intro a b hv hnc hb
  rcases hb with hb | hb
  · exact Or.inl (h₁ a b hv hnc hb)
  · exact Or.inr (h₂ a b hv hnc hb)

/-- **(L1) intersection of weakly-closed sets is weakly closed.** -/
theorem wc_inter {D : ConditionedMRDTSig}
    {C : Sal.Emulation.Configuration D.toCRDTSig} {E₁ E₂ : Set (Op D.AppOp)}
    (h₁ : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ E₁ → a ∈ E₁)
    (h₂ : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ E₂ → a ∈ E₂) :
    ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ E₁ ∩ E₂ → a ∈ E₁ ∩ E₂ := by
  intro a b hv hnc ⟨hb₁, hb₂⟩
  exact ⟨h₁ a b hv hnc hb₁, h₂ a b hv hnc hb₂⟩

/-! ## §2. The converse hypothesis and the reachable-core bundle -/

variable {D : ConditionedMRDTSig}

/-- **Convergence on `ev`** — the note's "`sig(ev)` is a well-defined function":
all `loOn C ev`-respecting folds agree, i.e. the canonical state of `ev` is
unique. (Existence, the other half of the note's convergence, is supplied at every
use site by the concrete `IsCanonicalState` witnesses and by the Join, so only
uniqueness is packaged here.) -/
def Converges (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev : Set (Op D.AppOp)) : Prop :=
  ∀ s s' : D.State, IsCanonicalState C ev s → IsCanonicalState C ev s' → s = s'

/-- **Canonical RA-linearizability** (the faithful converse hypothesis; see the
file header). The note's "canonical RA-linearizable" = *existence + convergence*
(here `converges`, the uniqueness of the fold on reachable weakly-closed sets)
plus *the merge is that fold* (here `join`, `JoinLemma3`). The framework's
`IsRALinearizable3` is the strictly weaker existence-only, per-config notion and
does **not** imply either field. -/
structure CanonicalRALin3 (D : ConditionedMRDTSig) : Prop where
  /-- The Join everywhere: a merge on backward-closed sides lands on the canonical
  state of the union (the existence / merge-is-the-fold half). -/
  join : JoinLemma3 D
  /-- Convergence everywhere on the reachable weakly-closed domain: the canonical
  state (`sig`) is unique. -/
  converges : ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev : Set (Op D.AppOp)),
    (∀ a ∈ ev, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev → a ∈ ev) →
    Converges C ev

/-- **The four core laws on the reachable-canonical domain** — the converse's
conclusion. `vc5` is `FeasibleInitConsumed` (VC5 on **weakly-closed** `ev`, the
note's domain restriction; `feasible_init`'s surplus over non-weakly-closed `ev`
is off-domain and not a converse target). `vc6`/`vc7` are the feasible
redistribute laws verbatim; `vc8` is the causal-delta equation `CDVC3`. -/
structure ReachableCoreVCs (D : ConditionedMRDTSig) : Prop where
  /-- VC5 on weakly-closed `ev` (the reachable-canonical domain of the unit law). -/
  vc5 : FeasibleInitConsumed D
  /-- VC6, feasible local-redistribute. -/
  vc6 : FeasibleLocalRedistributeVC D
  /-- VC7, feasible redistribute. -/
  vc7 : FeasibleRedistributeVC D
  /-- VC8, the causal-delta equation. -/
  vc8 : CDVC3 D

/-! ## §3. The fold-peel lemma (the note's L5, the one genuinely new lemma) -/

/-- **`sig_peel_maximal` (L5): `sig(U) = e(sig(U∖e))` for a `loOn(U)`-maximal `e`.**
Take the `loOn(U∖e)`-respecting enumeration underlying `sUe`; by antitonicity of
`loOn` (`loOn_mono`, inside `isCanonicalState_snoc`) it is `loOn(U)`-respecting on
`U∖e`, and `e` being `loOn(U)`-maximal, appending `e` yields a `loOn(U)`-respecting
enumeration of `U` whose fold is `do sUe e`; convergence on `U` (uniqueness) makes
that the canonical state `sU`. Convergence is used here as an **equation**, and no
merge is consumed. -/
theorem sig_peel_maximal {C : Sal.Emulation.Configuration D.toCRDTSig}
    {U : Set (Op D.AppOp)} {e : Op D.AppOp} {sU sUe : D.State}
    (hconv : Converges C U)
    (h_e_in : e ∈ U)
    (h_max : ∀ x ∈ U, x ≠ e → ¬ loOn C U e x)
    (hU : IsCanonicalState C U sU)
    (hUe : IsCanonicalState C (U \ {e}) sUe) :
    sU = D.update sUe e :=
  hconv sU (D.update sUe e) hU (isCanonicalState_snoc h_e_in h_max hUe)

/-! ## §4. The four core laws, each a Join reduction closed by convergence -/

/-- **VC5 on weakly-closed `ev`** (`FeasibleInitConsumed`): `mergeL init init s = s`
for `s = σ(ev)`. The Join at `(∅, ev)` makes `mergeL init init s` a canonical state
of `∅ ∪ ev = ev`; convergence on `ev` equates it with `s`. **Forced by the Join.** -/
theorem converse_VC5 (h : CanonicalRALin3 D) : FeasibleInitConsumed D := by
  intro C ev s h_tr h_ir h_in h_cl hcs
  have h0 : IsCanonicalState C (∅ : Set (Op D.AppOp)) D.init :=
    isCanonicalState_empty_init C
  have h_in0 : ∀ a ∈ (∅ : Set (Op D.AppOp)), a ∈ C.events :=
    fun a ha => absurd ha (Set.notMem_empty a)
  have h_cl0 : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b →
      b ∈ (∅ : Set (Op D.AppOp)) → a ∈ (∅ : Set (Op D.AppOp)) :=
    fun a b _ _ hb => absurd hb (Set.notMem_empty b)
  have hJoin := h.join C ∅ ev D.init D.init s h_tr h_ir h_in0 h_in h_cl0 h_cl
    (by rw [Set.empty_inter]; exact h0) h0 hcs
  rw [Set.empty_union] at hJoin
  exact (h.converges C ev h_in h_cl) _ _ hJoin hcs

/-- **VC5-empty** (`FeasibleInitAtEmpty`, the nullary unit `mergeL init init init =
init`). Instantiate weakly-closed VC5 at the empty configuration and event set. -/
theorem converse_VC5_empty (h : CanonicalRALin3 D) : FeasibleInitAtEmpty D :=
  converse_VC5 h (Sal.Emulation.initConfig D.toCRDTSig) ∅ D.init
    (fun hab _ => hab.elim)
    (fun _ haa => haa.elim)
    (fun a ha => absurd ha (Set.notMem_empty a))
    (fun _ b _ _ hb => absurd hb (Set.notMem_empty b))
    (isCanonicalState_empty_init _)

/-- **VC6** (feasible local-redistribute). Four Join instances rewrite each merge
node to a canonical state: the inner branches become `σ(E₁)` and `σ((E₁∪E₂)∖e)`,
and both whole sides land on `σ(E₁∪E₂)`; convergence on `E₁∪E₂` equates them.
**Forced by the Join.** -/
theorem converse_VC6 (h : CanonicalRALin3 D) : FeasibleLocalRedistributeVC D := by
  intro C ev₁ ev₂ s₀ B t₁ s₂ e h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ h_e₁ h_e₂
    h_max hs₀ hB ht₁ hs₂
  -- Structural facts.
  have h_dsub₁ : downset C e ⊆ ev₁ := downset_subset h_cl₁ h_e₁
  have h_dsubU : downset C e ⊆ ev₁ ∪ ev₂ := fun x hx => Or.inl (h_dsub₁ hx)
  have h_clU := wc_union h_cl₁ h_cl₂
  have h_inU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events :=
    fun a ha => ha.elim (h_in₁ a) (h_in₂ a)
  have h_in_e₁ : ∀ a ∈ ev₁ \ {e}, a ∈ C.events := fun a ha => h_in₁ a ha.1
  have h_in_Um : ∀ a ∈ (ev₁ ∪ ev₂) \ {e}, a ∈ C.events := fun a ha => h_inU a ha.1
  have h_in_de : ∀ a ∈ downset C e, a ∈ C.events := fun a ha => h_in₁ a (h_dsub₁ ha)
  have h_sub₁ : ev₁ ⊆ ev₁ ∪ ev₂ := Set.subset_union_left
  have h_subU : ev₁ ∪ ev₂ ⊆ ev₁ ∪ ev₂ := Set.Subset.rfl
  have h_cl_e₁ := closure_diff_of_max h_sub₁ h_cl₁ h_max
  have h_cl_Um := closure_diff_of_max h_subU h_clU h_max
  have hBde : IsCanonicalState C (downset C e) (D.update B e) :=
    isCanonicalState_snoc self_mem_downset (downset_max h_tr h_ir) hB
  -- The two special set-node rewrites (`e ∉ ev₂`).
  have set_c : (ev₁ \ {e}) ∩ ev₂ = ev₁ ∩ ev₂ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx₁, _⟩, hx₂⟩; exact ⟨hx₁, hx₂⟩
    · rintro ⟨hx₁, hx₂⟩
      exact ⟨⟨hx₁, by rintro rfl; exact h_e₂ hx₂⟩, hx₂⟩
  have set_d : (ev₁ \ {e}) ∪ ev₂ = (ev₁ ∪ ev₂) \ {e} := by
    ext x
    simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro (⟨hx₁, hne⟩ | hx₂)
      · exact ⟨Or.inl hx₁, hne⟩
      · exact ⟨Or.inr hx₂, by rintro rfl; exact h_e₂ hx₂⟩
    · rintro ⟨hx₁ | hx₂, hne⟩
      · exact Or.inl ⟨hx₁, hne⟩
      · exact Or.inr hx₂
  -- inner-left `mergeL B t₁ (update B e) = σ(E₁)` — Join at `(E₁∖e, ↓e)`.
  have hP := h.join C (ev₁ \ {e}) (downset C e) B t₁ (D.update B e)
    h_tr h_ir h_in_e₁ h_in_de h_cl_e₁ downset_closed
    (by rw [diff_inter_of_subset h_dsub₁]; exact hB) ht₁ hBde
  rw [diff_union_of_subset h_dsub₁ self_mem_downset] at hP
  -- LHS `= σ(E₁∪E₂)` — Join at `(E₁, E₂)`.
  have hLHS := h.join C ev₁ ev₂ s₀ (D.mergeL B t₁ (D.update B e)) s₂
    h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ hs₀ hP hs₂
  -- inner-right `mergeL s₀ t₁ s₂ = σ((E₁∪E₂)∖e)` — Join at `(E₁∖e, E₂)`.
  have hQ := h.join C (ev₁ \ {e}) ev₂ s₀ t₁ s₂
    h_tr h_ir h_in_e₁ h_in₂ h_cl_e₁ h_cl₂
    (by rw [set_c]; exact hs₀) ht₁ hs₂
  rw [set_d] at hQ
  -- RHS `= σ(E₁∪E₂)` — Join at `((E₁∪E₂)∖e, ↓e)`.
  have hRHS := h.join C ((ev₁ ∪ ev₂) \ {e}) (downset C e) B (D.mergeL s₀ t₁ s₂)
    (D.update B e) h_tr h_ir h_in_Um h_in_de h_cl_Um downset_closed
    (by rw [diff_inter_of_subset h_dsubU]; exact hB) hQ hBde
  rw [diff_union_of_subset h_dsubU self_mem_downset] at hRHS
  exact (h.converges C (ev₁ ∪ ev₂) h_inU h_clU) _ _ hLHS hRHS

/-- **VC7** (feasible redistribute). Six Join instances: the three shared-peel
branches become `σ(E₁∩E₂)`, `σ(E₁)`, `σ(E₂)` so the LHS is `σ(E₁∪E₂)`; the inner
`mergeL t₀ t₁ t₂` is `σ((E₁∪E₂)∖e)` so the RHS is `σ(E₁∪E₂)`; convergence on
`E₁∪E₂` equates them. **Forced by the Join.** -/
theorem converse_VC7 (h : CanonicalRALin3 D) : FeasibleRedistributeVC D := by
  intro C ev₁ ev₂ t₀ t₁ t₂ B e h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ h_e₁ h_e₂
    h_max ht₀ hB ht₁ ht₂
  -- Structural facts.
  have h_dsub₁ : downset C e ⊆ ev₁ := downset_subset h_cl₁ h_e₁
  have h_dsub₂ : downset C e ⊆ ev₂ := downset_subset h_cl₂ h_e₂
  have h_dsubI : downset C e ⊆ ev₁ ∩ ev₂ := fun x hx => ⟨h_dsub₁ hx, h_dsub₂ hx⟩
  have h_dsubU : downset C e ⊆ ev₁ ∪ ev₂ := fun x hx => Or.inl (h_dsub₁ hx)
  have h_clU := wc_union h_cl₁ h_cl₂
  have h_clI := wc_inter h_cl₁ h_cl₂
  have h_inU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events :=
    fun a ha => ha.elim (h_in₁ a) (h_in₂ a)
  have h_in_i₀ : ∀ a ∈ (ev₁ ∩ ev₂) \ {e}, a ∈ C.events :=
    fun a ha => h_in₁ a ha.1.1
  have h_in_e₁ : ∀ a ∈ ev₁ \ {e}, a ∈ C.events := fun a ha => h_in₁ a ha.1
  have h_in_e₂ : ∀ a ∈ ev₂ \ {e}, a ∈ C.events := fun a ha => h_in₂ a ha.1
  have h_in_Um : ∀ a ∈ (ev₁ ∪ ev₂) \ {e}, a ∈ C.events := fun a ha => h_inU a ha.1
  have h_in_de : ∀ a ∈ downset C e, a ∈ C.events := fun a ha => h_in₁ a (h_dsub₁ ha)
  have h_subI : ev₁ ∩ ev₂ ⊆ ev₁ ∪ ev₂ := fun x hx => Or.inl hx.1
  have h_sub₁ : ev₁ ⊆ ev₁ ∪ ev₂ := Set.subset_union_left
  have h_sub₂ : ev₂ ⊆ ev₁ ∪ ev₂ := Set.subset_union_right
  have h_subU : ev₁ ∪ ev₂ ⊆ ev₁ ∪ ev₂ := Set.Subset.rfl
  have h_cl_i₀ := closure_diff_of_max h_subI h_clI h_max
  have h_cl_e₁ := closure_diff_of_max h_sub₁ h_cl₁ h_max
  have h_cl_e₂ := closure_diff_of_max h_sub₂ h_cl₂ h_max
  have h_cl_Um := closure_diff_of_max h_subU h_clU h_max
  have hBde : IsCanonicalState C (downset C e) (D.update B e) :=
    isCanonicalState_snoc self_mem_downset (downset_max h_tr h_ir) hB
  -- The two special set-node rewrites (both sides punctured).
  have set_c : (ev₁ \ {e}) ∩ (ev₂ \ {e}) = (ev₁ ∩ ev₂) \ {e} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff]; tauto
  have set_d : (ev₁ \ {e}) ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
    ext x
    simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]; tauto
  -- `mergeL B t₀ (update B e) = σ(E₁∩E₂)` — Join at `((E₁∩E₂)∖e, ↓e)`.
  have hP₀ := h.join C ((ev₁ ∩ ev₂) \ {e}) (downset C e) B t₀ (D.update B e)
    h_tr h_ir h_in_i₀ h_in_de h_cl_i₀ downset_closed
    (by rw [diff_inter_of_subset h_dsubI]; exact hB) ht₀ hBde
  rw [diff_union_of_subset h_dsubI self_mem_downset] at hP₀
  -- `mergeL B t₁ (update B e) = σ(E₁)` — Join at `(E₁∖e, ↓e)`.
  have hP₁ := h.join C (ev₁ \ {e}) (downset C e) B t₁ (D.update B e)
    h_tr h_ir h_in_e₁ h_in_de h_cl_e₁ downset_closed
    (by rw [diff_inter_of_subset h_dsub₁]; exact hB) ht₁ hBde
  rw [diff_union_of_subset h_dsub₁ self_mem_downset] at hP₁
  -- `mergeL B t₂ (update B e) = σ(E₂)` — Join at `(E₂∖e, ↓e)`.
  have hP₂ := h.join C (ev₂ \ {e}) (downset C e) B t₂ (D.update B e)
    h_tr h_ir h_in_e₂ h_in_de h_cl_e₂ downset_closed
    (by rw [diff_inter_of_subset h_dsub₂]; exact hB) ht₂ hBde
  rw [diff_union_of_subset h_dsub₂ self_mem_downset] at hP₂
  -- LHS `= σ(E₁∪E₂)` — Join at `(E₁, E₂)`.
  have hLHS := h.join C ev₁ ev₂ (D.mergeL B t₀ (D.update B e))
    (D.mergeL B t₁ (D.update B e)) (D.mergeL B t₂ (D.update B e))
    h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ hP₀ hP₁ hP₂
  -- inner `mergeL t₀ t₁ t₂ = σ((E₁∪E₂)∖e)` — Join at `(E₁∖e, E₂∖e)`.
  have hQ := h.join C (ev₁ \ {e}) (ev₂ \ {e}) t₀ t₁ t₂
    h_tr h_ir h_in_e₁ h_in_e₂ h_cl_e₁ h_cl_e₂
    (by rw [set_c]; exact ht₀) ht₁ ht₂
  rw [set_d] at hQ
  -- RHS `= σ(E₁∪E₂)` — Join at `((E₁∪E₂)∖e, ↓e)`.
  have hRHS := h.join C ((ev₁ ∪ ev₂) \ {e}) (downset C e) B (D.mergeL t₀ t₁ t₂)
    (D.update B e) h_tr h_ir h_in_Um h_in_de h_cl_Um downset_closed
    (by rw [diff_inter_of_subset h_dsubU]; exact hB) hQ hBde
  rw [diff_union_of_subset h_dsubU self_mem_downset] at hRHS
  exact (h.converges C (ev₁ ∪ ev₂) h_inU h_clU) _ _ hLHS hRHS

/-- **VC8** (`CDVC3`, the causal-delta equation `mergeL B A (update B e) =
update A e`). The LHS is the Join at `(U∖e, ↓e)`, a canonical state of
`(U∖e) ∪ ↓e = U`; the RHS is `sig_peel_maximal` (`σ(U) = e(σ(U∖e))`). **Forced by
the Join and convergence.** -/
theorem converse_VC8 (h : CanonicalRALin3 D) : CDVC3 D := by
  intro C U A B e h_tr h_ir h_in h_cl h_e_in h_max hA hB
  have h_dsub : downset C e ⊆ U := downset_subset h_cl h_e_in
  have h_in_Ue : ∀ a ∈ U \ {e}, a ∈ C.events := fun a ha => h_in a ha.1
  have h_in_de : ∀ a ∈ downset C e, a ∈ C.events := fun a ha => h_in a (h_dsub ha)
  have h_subU : U ⊆ U := Set.Subset.rfl
  have h_cl_Ue := closure_diff_of_max h_subU h_cl h_max
  have hBde : IsCanonicalState C (downset C e) (D.update B e) :=
    isCanonicalState_snoc self_mem_downset (downset_max h_tr h_ir) hB
  -- LHS `= σ(U)` — Join at `(U∖e, ↓e)`.
  have hJoin := h.join C (U \ {e}) (downset C e) B A (D.update B e)
    h_tr h_ir h_in_Ue h_in_de h_cl_Ue downset_closed
    (by rw [diff_inter_of_subset h_dsub]; exact hB) hA hBde
  rw [diff_union_of_subset h_dsub self_mem_downset] at hJoin
  -- RHS `= σ(U)` too, via the fold-peel.
  exact sig_peel_maximal (h.converges C U h_in h_cl) h_e_in h_max hJoin hA

/-! ## §5. The converse, packaged -/

/-- **`converse_core`** — the restricted converse of adequacy. A canonical
RA-linearizable flat MRDT satisfies the four core VCs on its reachable,
weakly-closed event sets. Two ingredients only: `JoinLemma3` (all four laws) and
`sig_peel_maximal` (VC8's convergence half). -/
theorem converse_core (h : CanonicalRALin3 D) : ReachableCoreVCs D where
  vc5 := converse_VC5 h
  vc6 := converse_VC6 h
  vc7 := converse_VC7 h
  vc8 := converse_VC8 h

/-! ## §6. The completeness corollary

The two task-#114 directions meet at the four-law core / the Join. Adequacy
(`join_lemma3_of_cd_feasible`, then `ra_linearizable3_of_join`) runs
`{VC1..VC8} ⟹ JoinLemma3 ⟹ RA-lin`; this file's `converse_core` runs
`canonical-RA-lin ⟹ {VC5°, VC6, VC7, VC8}` on reachable states. Both pivot on
`JoinLemma3`. -/

/-- Re-export of adequacy's Join production (the backward pivot), stated over the
raw eight-VC bundle. -/
theorem adequacy_join (hVC : CoreVCs3CD D) (hFΔ : FeasibleDeltaVCs3 D)
    (hCD : CDVC3 D) : JoinLemma3 D :=
  join_lemma3_of_cd_feasible hVC hFΔ hCD

/-- **Flat completeness (both directions).** The converse (`converse_core`):
canonical-RA-lin forces the four reachable-core laws. Adequacy (`adequacy_join`,
then `ra_linearizable3_of_join`): the raw eight-VC bundle forces `JoinLemma3` and
hence per-config RA-lin. They meet at the four-law core / `JoinLemma3` pivot.

**The biconditional gap (#119, not done).** A *tight* biconditional at the
four-reachable-core level — `ReachableCoreVCs D ∧ (convergence) ↔ CanonicalRALin3 D`
— needs the backward implication `ReachableCoreVCs + convergence + weakened update
layer ⟹ JoinLemma3`. That is exactly the phase-2 "weakened-adequacy re-thread"
named as the residue in `VC_Minimal_Core.lean` (re-hosting `convergence_on_u`,
`loOnNe_acyclic_u`, `isCanonicalState_unique_u`/`_exists_u` on `WeakUpdateVCs` +
`ReachState`, and re-threading `join_lemma3_of_cd_feasible` to consume the
`FeasibleInitConsumed` / canonical-tuple forms). Mechanical (~500 lines), no
mathematical obstruction, but a re-derivation rather than a composition — so the
tight `↔` is deferred to #119, and what is proved now is the pair below. -/
theorem flat_completeness :
    (CanonicalRALin3 D → ReachableCoreVCs D) ∧
      (CoreVCs3CD D → FeasibleDeltaVCs3 D → CDVC3 D → JoinLemma3 D) :=
  ⟨converse_core, adequacy_join⟩

#print axioms sig_peel_maximal
#print axioms converse_VC8
#print axioms converse_core
#print axioms flat_completeness

end Sal.ConditionedMRDTs
