import Sal.CRDTs.Metatheory.JoinLemma_Of_CD

/-!
# (CD) is the *exact* residual: `CDVC ↔ JoinLemma` under the lattice
# contract

`JoinLemma_Of_CD.lean` proved `CoreVCs + LatticeVCsPlus + CDVC ⇒
JoinLemma`. This file proves the **converse**: given
`CoreVCs + LatticeVCsPlus`, the Join Lemma implies (CD) — the
principal-case instance `(U∖e, ↓e)` of the Join Lemma *is* (CD), up
to the free half supplied by the lattice laws. Hence

    joinLemma_iff_cdVC :  JoinLemma D ↔ CDVC D
      (given CoreVCs D and LatticeVCsPlus D)

with two consequences:

1. **(CD) is the weakest sufficient residual** (`cdVC_weakest`): any
   hypothesis `X` that closes the metatheorem
   (`X → JoinLemma D`) already implies `CDVC D`. There is no weaker
   bridge VC to look for: the question ("is (CD) derivable from
   `CoreVCs + LatticeVCsPlus` alone?") is *equivalent* to
   "does `CoreVCs + LatticeVCsPlus` imply the Join Lemma /
   RA-linearizability?". (CD) is its exact Skolemization.
2. The per-CRDT `JoinPeelVCs` bundle strictly subsumes `CDVC`:
   `cdVC_of_joinPeelVCs`, every `JoinPeelVCs` discharge yields a
   (CD) discharge for free (given the lattice contract).

## The derivability question

Both attack directions on the derivability question hit
characterizable walls:

* **Mutual induction (positive attack).** Absorbing (CD) into
  `join_lemma_of_cd`'s strong induction reduces the size-`n` (CD)
  instance, via the downset decomposition `σ(U∖e) = ⊔ₓ σ(↓x)` and
  `lem_0op`, to per-event peel steps. The steps discharge from the
  axioms when the peeled `loOn`-maximal `x` commutes with all of
  `↓e ∪ {e}` (`merge_peel_comm`), and when `¬commutes(e,x)` with
  `x vis e` or an absorber (maximality + `M(<n)` absorption). The two
  surviving shapes (`x ∥ e` with `rc x e = Fst`, and
  `commutes(e,x)` with `x` rc/vis-entangled in `↓e`) are *provably
  circular*: unwinding them with `lem_0op`/commutation reproduces the
  size-`n` (CD) goal verbatim. No axiom mentions the pair
  `(x-then-e, rc x e = Fst)` when `e` has no absorber, so the
  induction cannot cross it.
* **Countermodels (negative attack).** Four further families died on
  a sharp forcing dichotomy: a delta of `e` that reads state
  written by `y ∥ e` either makes `(y,e)` non-commuting, forcing (via
  `rc`-directionality + `cond_comm_lift` + update-inflationarity)
  every writer to *pre-push* the read's image (tagged or not)
  into the state, creating exactly the accumulation invariant that
  validates (CD); or leaves them commuting, and `merge_peel_comm`
  directly forbids the delta from growing under merged-in commuting
  context. `no_rc_chain` blocks all three-op-kind escapes (the
  `rc`-Fst digraph on kinds must be 2-path-free). All these forcing
  arguments are *powerset-specific* (they decompose deltas over
  atoms); non-atomic lattice states are the one remaining
  countermodel habitat.
-/

namespace Sal.Emulation

open Classical

section
variable {D : CRDTSig}

/-- **The Join Lemma implies (CD)** under the lattice contract: the
principal instance `(U∖e, ↓e)` of the Join Lemma delivers
`σ(U∖e) ⊔ update σ(↓e∖e) e = update σ(U∖e) e` (via the free peel of
`↓e` and uniqueness of canonical states), and idempotence turns the
equation into the (CD) inequality. -/
theorem cdVC_of_joinLemma (hVC : CoreVCs D) (hL : LatticeVCsPlus D)
    (hJoin : JoinLemma D) : CDVC D := by
  intro C U A B e h_tr h_ir h_in h_cl h_e h_max hA hB
  -- update B e is canonical for the downset (free peel).
  have hT : IsCanonicalState C (downset C e) (D.update B e) :=
    isCanonicalState_snoc self_mem_downset (downset_max h_tr h_ir) hB
  have h_dsub : downset C e ⊆ U := downset_subset h_cl h_e
  -- The Join Lemma on the pair (U∖e, ↓e).
  have h_join := hJoin C (U \ {e}) (downset C e) A (D.update B e)
    h_tr h_ir (fun a ha => h_in a ha.1) (fun a ha => h_in a (h_dsub ha))
    (closure_diff_of_max Set.Subset.rfl h_cl h_max) downset_closed
    hA hT
  have hset : (U \ {e}) ∪ downset C e = U := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact h_dsub hx
    · intro hx
      by_cases hxe : x = e
      · subst hxe
        exact Or.inr self_mem_downset
      · exact Or.inl ⟨hx, hxe⟩
  have h_can : IsCanonicalState C U (D.merge A (D.update B e)) := by
    rw [← hset]
    exact h_join
  -- Both sides are canonical for U, hence equal; idempotence closes.
  have h_eq : D.merge A (D.update B e) = D.update A e :=
    isCanonicalState_unique hVC h_in h_can
      (isCanonicalState_snoc h_e h_max hA)
  rw [h_eq]
  exact hL.merge_idem _

/-- **Exactness**: under `CoreVCs + LatticeVCsPlus`, the causal-delta
bound and the Join Lemma are equivalent. (CD) is not one workable
residual among many, it is *the* residual: the derivability question
is equivalent to the unconditional metatheorem question. -/
theorem joinLemma_iff_cdVC (hVC : CoreVCs D) (hL : LatticeVCsPlus D) :
    JoinLemma D ↔ CDVC D :=
  ⟨cdVC_of_joinLemma hVC hL, join_lemma_of_cd hVC hL⟩

/-- **Minimality**: any hypothesis `X` sufficient to close the
metatheorem already implies (CD). No strictly weaker bridge VC
exists. -/
theorem cdVC_weakest {X : Prop} (hVC : CoreVCs D)
    (hL : LatticeVCsPlus D) (hX : X → JoinLemma D) :
    X → CDVC D :=
  fun hx => cdVC_of_joinLemma hVC hL (hX hx)

/-- The `JoinPeelVCs` per-CRDT bundle subsumes the CD one: a `JoinPeelVCs`
discharge yields a (CD) discharge for free (given the lattice
contract). -/
theorem cdVC_of_joinPeelVCs (hVC : CoreVCs D) (hL : LatticeVCsPlus D)
    (hPeel : JoinPeelVCs D) : CDVC D :=
  cdVC_of_joinLemma hVC hL (join_lemma_of_peel hVC hPeel)

end

end Sal.Emulation
