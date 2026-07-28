import Sal.ConditionedMRDTs.Metatheory.Adequacy

/-!
# Kill-test: the ternary causal-delta bound `CDVC3` is an INDEPENDENT rule

This file settles Open Question `oq:cd` in the **ternary** (three-way merge)
direction: is `CDVC3` derivable from `CoreVCs3 + DeltaVCs3` (the unconditional
core + delta laws), or is it an independent verification condition of the
bundle?

**Verdict: independent.** `CDVC3` is NOT derivable — there is a concrete
`ConditionedMRDTSig` satisfying every `CoreVCs3` and `DeltaVCs3` clause yet
falsifying `CDVC3` on a specific reachable configuration. The VC bundle is
therefore *minimal at `CDVC3`*: it cannot be reduced by dropping `CDVC3`
(unless `CoreVCs3 + DeltaVCs3` already implied the Join Lemma, which the same
countermodel refutes).

## The two results

1. **Ternary exactness** (`cdVC3_of_joinLemma3`, `joinLemma3_iff_cdVC3`,
   `cdVC3_weakest`).  The lift of the binary result
   (`Sal/CRDTs/Metatheory/CD_Exact.lean`): under `CoreVCs3`, the Join Lemma
   *implies* `CDVC3` — so given `DeltaVCs3` the two are equivalent, and no
   strictly weaker bridge VC exists.  Notably the ternary backward direction
   needs **no idempotence** (the binary `cdVC_of_joinLemma` had to convert an
   `⊑`-inequality with `merge_idem`; ternary `CDVC3` is already an equation, so
   uniqueness of canonical states closes it directly).  Hence "`CDVC3`
   derivable from `CoreVCs3 + DeltaVCs3`" is *equivalent* to "`CoreVCs3 +
   DeltaVCs3 ⇒ JoinLemma3`".

2. **The countermodel** (`AWSetF3`, `cdvc3_not_derivable_from_core_delta`).
   `AWSetF3` is the LCA-blind ternary lift of the binary separator
   `AWSetF` (`Sal/CRDTs/Metatheory/Assoc_CounterModel.lean`): state is an
   add-wins set together with a Boolean flag written by every op (`add ↦ true`,
   `rem ↦ false`), the ternary merge is the pairwise join `mergeL l a b = a ⊔ b`
   dropping the LCA slot `l`.  The join is a bounded semilattice (ACI), so
   `DeltaVCs3` holds unconditionally; `AWSetF`'s binary core lemmas give
   `CoreVCs3` verbatim (the ternary `merge_peel_comm3` is the binary
   `merge_peel_comm` at the branch slot).  **But** `AWSetF`'s update is
   *deflationary* (a `rem` decreases the flag), and `DeltaVCs3` carries NO
   inflation axiom — so at a `loOn`-maximal `rem` event `e` with
   `A = σ(U∖e)`, `B = σ(↓e∖e)`:

      mergeL B A (update B e)   has flag  A.flag ∨ (update B e).flag = true ∨ false = true
      update A e                has flag  false

   `CDVC3`'s equation `mergeL B A (update B e) = update A e` fails.  The
   ternary `CDVC3`-equation silently packs the *inflation half* that the
   binary lattice contract (`LatticeVCsPlus`) supplies as a separate axiom;
   `DeltaVCs3` does not, and `AWSetF3` exhibits the gap.

Self-contained kill-test: the concrete signature, the two
positive VC bundles, the refuted target, and `#print axioms` at the end.
-/

namespace Sal.ConditionedMRDTs.CDNotDerivableTernary

open Sal.Emulation
open Sal.ConditionedMRDTs
open Classical

/-! ## §1. The ternary lift `AWSetF3` -/

/-- The LCA-blind ternary lift of `AWSetF`: same state / update / rc / init as
the binary A10 separator, ternary merge `mergeL l a b := awfMerge a b` dropping
the LCA slot, conditioning trivial. -/
noncomputable def AWSetF3 : ConditionedMRDTSig where
  toMRDTSig :=
    { toCRDTSig := AWSetF
      mergeL := fun _l a b => awfMerge a b
      merge_init_slice := fun _ _ => rfl }
  Inv := fun _ => True
  applicable := fun _ _ => True

@[simp] theorem AWSetF3_toCRDTSig : AWSetF3.toCRDTSig = AWSetF := rfl
@[simp] theorem AWSetF3_mergeL (l a b : AWFState) :
    AWSetF3.mergeL l a b = awfMerge a b := rfl
@[simp] theorem AWSetF3_update (s : AWFState) (e : Op AWOp) :
    AWSetF3.update s e = awfUpdate s e := rfl
@[simp] theorem AWSetF3_init : AWSetF3.init = AWSetF.init := rfl

/-! ## §2. `CoreVCs3 AWSetF3` — the binary core lemmas, verbatim

Every field reduces to an `AWSetF` core lemma: the update-layer fields are the
binary `CoreVCs` slimmed by `UpdateVCs.of_core`; `mergeL_comm/init` and
`lem_0op3` drop the LCA slot to the binary `merge_comm/init`/`lem_0op`; and the
ternary `merge_peel_comm3` at the branch slot IS the binary `merge_peel_comm`
(the LCA-slot fold `π₀` is dropped, so its commuting hypothesis is unused). -/

theorem AWSetF3_coreVCs3 : CoreVCs3 AWSetF3 where
  update_core := UpdateVCs.of_core AWSetF_coreVCs
  mergeL_comm := fun _l a b => AWSetF_merge_comm a b
  mergeL_init := fun s => AWSetF_merge_init s
  lem_0op3 := fun _l a b e => AWSetF_lem_0op a b e
  merge_peel_comm3 := fun a e _π₀ π₂ _h₀ h₂ => AWSetF_merge_peel_comm a e π₂ h₂

/-! ## §3. `DeltaVCs3 AWSetF3` — from the ACI semilattice laws

`awfMerge` is associative, commutative, idempotent (`AWSetF_merge_*`). Both
delta laws are pure semilattice rearrangements of the LCA-blind merge. -/

private theorem awfMerge_comm (a b : AWFState) : awfMerge a b = awfMerge b a :=
  AWSetF_merge_comm a b
private theorem awfMerge_assoc (a b c : AWFState) :
    awfMerge (awfMerge a b) c = awfMerge a (awfMerge b c) :=
  AWSetF_merge_assoc a b c
private theorem awfMerge_idem (a : AWFState) : awfMerge a a = a :=
  AWSetF_merge_idem a

/-- `(x₁ ⊔ c) ⊔ (x₂ ⊔ c) = (x₁ ⊔ x₂) ⊔ c` — the redistribution identity
(idempotence collapses the duplicated LCA-slot `c`). -/
private theorem awf_redistribute (x₁ x₂ c : AWFState) :
    awfMerge (awfMerge x₁ c) (awfMerge x₂ c) = awfMerge (awfMerge x₁ x₂) c := by
  rw [awfMerge_assoc, ← awfMerge_assoc c x₂ c, awfMerge_comm c x₂,
    awfMerge_assoc x₂ c c, awfMerge_idem, ← awfMerge_assoc]

/-- `(x ⊔ c) ⊔ y = (x ⊔ y) ⊔ c` — right-commutativity. -/
private theorem awf_local_redistribute (x c y : AWFState) :
    awfMerge (awfMerge x c) y = awfMerge (awfMerge x y) c := by
  rw [awfMerge_assoc, awfMerge_comm c y, ← awfMerge_assoc]

theorem AWSetF3_deltaVCs3 : DeltaVCs3 AWSetF3 where
  redistribute := fun _m _x₀ x₁ x₂ c => awf_redistribute x₁ x₂ c
  local_redistribute := fun _l _m x c y => awf_local_redistribute x c y

/-! ## §4. Ternary exactness: `JoinLemma3 ⇒ CDVC3` under `CoreVCs3`

The lift of the binary `cdVC_of_joinLemma`. The principal Join-Lemma instance
`(ev₁, ev₂) = (U∖e, ↓e)` produces the canonical state of the union `U` as
`mergeL B A (update B e)`; `update A e` is canonical for `U` too; uniqueness
of canonical states (`isCanonicalState_unique_u`, needing only `UpdateVCs`)
gives the `CDVC3` equation. No idempotence, no delta law. -/

theorem cdVC3_of_joinLemma3 {D : ConditionedMRDTSig}
    (hVC : CoreVCs3 D) (hJoin : JoinLemma3 D) : CDVC3 D := by
  intro C U A B e h_tr h_ir h_in h_cl h_e h_max hA hB
  have hU := hVC.update_core
  -- σ(↓e) = update B e (free peel; e is loOn(↓e)-maximal, no VC).
  have hT : IsCanonicalState C (downset C e) (D.update B e) :=
    isCanonicalState_snoc self_mem_downset (downset_max h_tr h_ir) hB
  have h_dsub : downset C e ⊆ U := downset_subset h_cl h_e
  -- honest LCA set (U∖e) ∩ ↓e = ↓e∖{e}, canonical state B.
  have hInt : (U \ {e}) ∩ downset C e = downset C e \ {e} := by
    ext x
    constructor
    · rintro ⟨⟨_, hne⟩, hd⟩; exact ⟨hd, hne⟩
    · rintro ⟨hd, hne⟩; exact ⟨⟨h_dsub hd, hne⟩, hd⟩
  have hB' : IsCanonicalState C ((U \ {e}) ∩ downset C e) B := by
    rw [hInt]; exact hB
  -- The Join Lemma on the pair (U∖e, ↓e).
  have h_join := hJoin C (U \ {e}) (downset C e) B A (D.update B e)
    h_tr h_ir (fun a ha => h_in a ha.1) (fun a ha => h_in a (h_dsub ha))
    (closure_diff_of_max Set.Subset.rfl h_cl h_max) downset_closed hB' hA hT
  have hUnion : (U \ {e}) ∪ downset C e = U := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact h_dsub hx
    · intro hx
      by_cases hxe : x = e
      · exact hxe ▸ Or.inr self_mem_downset
      · exact Or.inl ⟨hx, hxe⟩
  have h_can : IsCanonicalState C U (D.mergeL B A (D.update B e)) := by
    rw [← hUnion]; exact h_join
  have h_can' : IsCanonicalState C U (D.update A e) :=
    isCanonicalState_snoc h_e h_max hA
  exact isCanonicalState_unique_u hU h_in h_can h_can'

/-- **Ternary exactness**: under `CoreVCs3 + DeltaVCs3`, the ternary Join Lemma
and `CDVC3` are equivalent. So "`CDVC3` derivable from `CoreVCs3 + DeltaVCs3`"
IS the metatheorem question "`CoreVCs3 + DeltaVCs3 ⇒ JoinLemma3`". -/
theorem joinLemma3_iff_cdVC3 {D : ConditionedMRDTSig}
    (hVC : CoreVCs3 D) (hΔ : DeltaVCs3 D) : JoinLemma3 D ↔ CDVC3 D :=
  ⟨cdVC3_of_joinLemma3 hVC, join_lemma3_of_cd hVC hΔ⟩

/-- **Minimality**: any hypothesis `X` sufficient to close the metatheorem
already implies `CDVC3`. No strictly weaker bridge VC exists. -/
theorem cdVC3_weakest {D : ConditionedMRDTSig} {X : Prop}
    (hVC : CoreVCs3 D) (hX : X → JoinLemma3 D) : X → CDVC3 D :=
  fun hx => cdVC3_of_joinLemma3 hVC (hX hx)

/-! ## §5. The `CDVC3` refutation for `AWSetF3`

Reuses the binary refuting configuration `flagConfig`: replica 0 holds
`{aF (add), eF (rem)}` with `vis aF eF`, replica 1 holds `{aF}`. Take
`U = {aF, eF}`, `e = eF`, `A = B = σ({aF}) = sF₂` (both `U∖e` and `↓e∖e`
equal `{aF}` here). All `CDVC3` contextual hypotheses hold; the equation fails
on the flag. -/

/-- `aF ≠ eF` (distinct timestamps). -/
private theorem aF_ne_eF : aF ≠ eF := by decide

/-- `flagConfig`'s only `vis`-edge is `aF → eF`. -/
private theorem hvis_trans :
    ∀ {x y z : Op AWSetF.AppOp},
      flagConfig.vis x y → flagConfig.vis y z → flagConfig.vis x z := by
  rintro x y z ⟨rfl, rfl⟩ ⟨h1, _⟩
  exact absurd h1 (by decide)

private theorem hvis_irrefl : ∀ x : Op AWSetF.AppOp, ¬ flagConfig.vis x x := by
  rintro x ⟨rfl, h⟩
  exact absurd h (by decide)

private theorem hin : ∀ a ∈ evF₁ ∪ evF₂, a ∈ flagConfig.events := by
  rintro x (hx | hx)
  · exact ⟨0, {aF, eF}, by simp [flagConfig], hx⟩
  · exact ⟨1, {aF}, by simp [flagConfig], hx⟩

private theorem hcl :
    ∀ a b, flagConfig.vis a b → ¬ AWSetF.commutes a b →
      b ∈ evF₁ ∪ evF₂ → a ∈ evF₁ ∪ evF₂ := by
  rintro a b ⟨rfl, rfl⟩ _ _
  exact Or.inl (Or.inl rfl)

private theorem he_mem : eF ∈ evF₁ ∪ evF₂ := Or.inl (Or.inr rfl)

/-- `eF` is `loOn(U)`-maximal: its only candidate target `aF` is `vis`-before
it, so neither `loOn` disjunct fires. -/
private theorem hmax :
    ∀ x ∈ evF₁ ∪ evF₂, x ≠ eF →
      ¬ loOn flagConfig (evF₁ ∪ evF₂) eF x := by
  intro x hx hne
  rintro (⟨hv, _⟩ | ⟨_, hnv, _, _⟩)
  · obtain ⟨h1, _⟩ := hv
    exact absurd h1 (by decide)
  · have hxa : x = aF := by
      rcases hx with hx | hx
      · rcases hx with h | h
        · exact h
        · exact absurd h hne
      · exact hx
    subst hxa
    exact hnv ⟨rfl, rfl⟩

/-- `σ(U∖e) = sF₂`: `U∖{eF} = {aF}`. -/
private theorem hA_can :
    IsCanonicalState flagConfig ((evF₁ ∪ evF₂) \ {eF}) sF₂ := by
  refine ⟨[aF], ⟨List.nodup_singleton _, fun x => ?_⟩,
    List.pairwise_singleton _ _, rfl⟩
  rw [List.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨Or.inl (Or.inl rfl), by simp [aF, eF]⟩
  · rintro ⟨hmem, hne⟩
    simp only [Set.mem_singleton_iff] at hne
    rcases hmem with (h | h) | h
    · exact h
    · exact absurd h hne
    · exact h

/-- `↓eF = {aF, eF}`, so `↓eF∖{eF} = {aF}` and `σ(↓eF∖eF) = sF₂`. The forward
membership uses `downset_vis` (everything below `eF` other than `eF` is
`vis`-before `eF`, hence `= aF`); the reverse plants `aF` via the single
`vis∧¬commutes` edge `aF → eF`. -/
private theorem hB_can :
    IsCanonicalState flagConfig (downset flagConfig eF \ {eF}) sF₂ := by
  refine ⟨[aF], ⟨List.nodup_singleton _, fun x => ?_⟩,
    List.pairwise_singleton _ _, rfl⟩
  rw [List.mem_singleton]
  constructor
  · rintro rfl
    refine ⟨Or.inr (Relation.TransGen.single ⟨⟨rfl, rfl⟩, ?_⟩), ?_⟩
    · exact AWSetF_not_comm_add_rem (by decide) (by decide)
    · simp [aF, eF]
  · rintro ⟨hx, hne⟩
    simp only [Set.mem_singleton_iff] at hne
    have hvis : flagConfig.vis x eF := downset_vis (D := AWSetF) hvis_trans hx hne
    exact hvis.1

/-- **`CDVC3` fails for `AWSetF3`.** At the maximal `rem` event `eF`, the merge
`mergeL B A (update B eF)` carries flag `true` (the branch `A = sF₂` was set by
an `add`), but `update A eF` carries flag `false` (`rem` writes `false`). -/
theorem AWSetF3_not_cdVC3 : ¬ CDVC3 AWSetF3 := by
  intro h
  have key := h flagConfig (evF₁ ∪ evF₂) sF₂ sF₂ eF
    hvis_trans hvis_irrefl hin hcl he_mem hmax hA_can hB_can
  -- key : AWSetF3.mergeL sF₂ sF₂ (AWSetF3.update sF₂ eF) = AWSetF3.update sF₂ eF
  have hsnd := congrArg Prod.snd key
  simp only [AWSetF3_mergeL, AWSetF3_update, awfMerge, awfUpdate] at hsnd
  -- hsnd : sF₂.2 || awFlag eF = awFlag eF, i.e. true || false = false
  revert hsnd
  decide

/-! ## §6. The independence result -/

/-- **`CDVC3` is an independent VC of the ternary bundle.** There is a
`ConditionedMRDTSig` satisfying every `CoreVCs3` and `DeltaVCs3` clause yet
falsifying `CDVC3`. Hence the VC set `CoreVCs3 + DeltaVCs3 + CDVC3` is minimal
at `CDVC3`: the causal-delta bound cannot be dropped or derived from the core
and delta laws. Equivalently (by `joinLemma3_iff_cdVC3`), `CoreVCs3 +
DeltaVCs3` do not imply the ternary Join Lemma. -/
theorem cdvc3_not_derivable_from_core_delta :
    ∃ D : ConditionedMRDTSig, CoreVCs3 D ∧ DeltaVCs3 D ∧ ¬ CDVC3 D :=
  ⟨AWSetF3, AWSetF3_coreVCs3, AWSetF3_deltaVCs3, AWSetF3_not_cdVC3⟩

/-- Corollary: `CoreVCs3 + DeltaVCs3` do NOT imply `JoinLemma3`. -/
theorem coreDelta3_not_joinLemma3 :
    ∃ D : ConditionedMRDTSig, CoreVCs3 D ∧ DeltaVCs3 D ∧ ¬ JoinLemma3 D :=
  ⟨AWSetF3, AWSetF3_coreVCs3, AWSetF3_deltaVCs3,
   fun hJ => AWSetF3_not_cdVC3 (cdVC3_of_joinLemma3 AWSetF3_coreVCs3 hJ)⟩

#print axioms cdvc3_not_derivable_from_core_delta
#print axioms cdVC3_of_joinLemma3

end Sal.ConditionedMRDTs.CDNotDerivableTernary
