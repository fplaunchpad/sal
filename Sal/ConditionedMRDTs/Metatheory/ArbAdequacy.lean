import Sal.ConditionedMRDTs.Metatheory.Arbitration_Refactor

/-!
# Arbitration-generic adequacy (task #119, half B; enabler for #123)

The falsifiable next step of the arbitration refactor
(`Metatheory/Arbitration_Refactor.lean`, `whiteboard/ra-lin-definition-note.md`
§4): re-derive RA-linearizability against the **abstract** acyclic arbitration
rather than the concrete `loOn`, so that `loOn` becomes *one* instance and LWW's
timestamp total order *another*, both certified through the same generic engine.

## What lands here (all kernel-clean, axioms ⊆ {propext, Classical.choice,
Quot.sound}); each theorem's `#print axioms` is checked below.

* **§1 The arbitration topological sort** (`exists_maximal_of_acyclic`,
  `exists_respecting_perm_fixed`): from *acyclicity alone*, i.e. the
  `AcyclicArbitration.acyclic` field, a respecting enumeration of any event set
  exists. This is the **existence** obligation, re-derived over the abstract
  `arb` with **no** `loOn` structure and, crucially, with the relation held fixed
  while the carrier shrinks, so it consumes no monotonicity. (The published
  `exists_loOn_respecting_perm_u` re-indexes `loOn C T` by the carrier `T`, and so
  leans on `loOn`'s antitonicity `loOn_mono`; the fixed-relation topological sort
  here does not.)

* **§2 The generic canonical state** (`IsCanonicalStateArb`) and its two pillars:
  `isCanonicalStateArb_exists` (from acyclicity, §1) and
  `isCanonicalStateArb_unique` (from `ArbConvergence`). Plus
  `isCanonicalStateArb_snoc`, re-attaching an `arb`-maximal event, which is the
  one piece that consumes a **third** arbitration property (see the FINDING).

* **§3 The generic adequacy theorem** `isRALinearizable3Arb_of_acyclicArb_refines_loOn`:
  any acyclic arbitration that **refines** `loOn` (every `loOn`-edge is an
  `arb`-edge) is one against which every good configuration is RA-linearizable.
  Both target instances route through it: `loOn` refines itself
  (`loOn_isRALinearizable3Arb_via_generic`), and LWW's `lwwArb` refines the empty
  `loOn` (`lww_loOn_empty`), so both are certified by the same theorem.

## FINDING: the arbitration thesis needs a THIRD clause beyond acyclicity and
convergence (a refinement of the phase-3b diagnostic).

Phase-3b (`Arbitration_Refactor.lean` §4) split the adequacy chain's consumption
of `loOn` into two independent obligations: **existence** ("acyclicity-only") and
**convergence** (`ArbConvergence`, the B-site). Mechanizing the re-thread here
shows that split is incomplete. The Join Lemma / apply layer additionally
consumes `isCanonicalState_snoc` (re-attaching an order-maximal event to the
canonical state of the set-minus-it), and that lemma consumes, via
`respects_loOn_mono` / `loOn_mono`, a **third** structural property:

> **antitonicity under carrier restriction**: `E' ⊆ E'' → arb E'' a b → arb E' a b`
> (growing the event set only *removes* order edges; equivalently, removing an
> element never *flips* an existing order).

This is NOT implied by acyclicity, extends-`vis`, and convergence. A set-indexed
`arb` that flips an edge when an element is removed can still be acyclic and
convergent on every fixed set, yet `isCanonicalStateArb_snoc` fails for it: the
canonical state of `E∖{e}` no longer respects `arb E`. It is the set-relative
absorber scope (the reason `loOn` is indexed by the event set at all, Strike 4 of
the definition note) that forces the clause. Both target instances discharge it:
`loOn` by `loOn_mono`, and `lwwArb` because it is set-*independent*
(`lwwArb _E = (· < ·) on lwwWrite`, antitone vacuously). So the clause does not
bound the thesis toward `rc`; it is a monotonicity artifact satisfied by every
arbitration of interest. But it *is* a genuine third requirement that the
phase-3b existence/convergence dichotomy omitted, and it is mechanized here as
the explicit hypothesis of `isCanonicalStateArb_snoc`.

Consequence for the *fully*-generic form (arb-canonical states throughout, folds
pinned by `ArbConvergence`, with `loOn` absent from the statement): it goes
through as a re-thread, with **no** mathematical obstruction (confirming
phase-3b's "no obstruction" claim), once given (i) the third clause above and
(ii) a re-threading of the ~340-line ternary Join Lemma and ~450-line
`GoodConfig3` transition induction over `IsCanonicalStateArb` in place of
`IsCanonicalState`. The theorem delivered here (§3) instead **reuses** the
published `loOn` convergence (`convergence_on_u`) as the fold oracle, and asks the
abstract `arb` only to be acyclic and to *refine* `loOn`. It is short,
kernel-clean, and certifies both instances, at the cost of still routing the
fold-pinning through `loOn`. The fully-generic engine (`IsRALinearizable3Arb`
from `{VC5-empty,VC6,VC7,VC8} + AcyclicArbitration + antitone + ArbConvergence`)
is named as the remaining #119(B-full) tail; `GoodConfig3Arb` (§4) is its target
invariant, and its `→ IsRALinearizable3Arb` lifting is discharged here.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

variable {D : ConditionedMRDTSig}

/-! ## §1. The arbitration topological sort (existence, from acyclicity alone) -/

/-- The distinct-restricted step of a **fixed** relation `R` on a carrier `S`.
Unlike `arbNe`, `R` is not re-indexed by `S`, so the carrier can shrink in a
topological sort while the relation stays put, which is what lets §1 avoid any
monotonicity of `arb`. Note `arbNe E arb = stepNe E (arb E)` definitionally. -/
def stepNe (S : Set (Op D.AppOp)) (R : Op D.AppOp → Op D.AppOp → Prop)
    (a b : Op D.AppOp) : Prop :=
  a ≠ b ∧ a ∈ S ∧ b ∈ S ∧ R a b

/-- `arbNe` is the `stepNe` of the set-indexed relation at its own index. -/
theorem arbNe_eq_stepNe (E : Set (Op D.AppOp))
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop) :
    arbNe E arb = stepNe E (arb E) := rfl

/-- **A maximal element from acyclicity** (abstract `exists_loOn_maximal_u`).
A finite (`listPermOf`-enumerable) nonempty carrier `S` under a relation `R`
whose `stepNe S R` is acyclic contains an `R`-maximal element: nothing in `S`
sits `R`-after it. The walk is verbatim the published proof, with
`loOnNe_acyclic_u` replaced by the *given* acyclicity, which is the sole place
acyclicity is consumed. -/
theorem exists_maximal_of_acyclic {R : Op D.AppOp → Op D.AppOp → Prop}
    {S : Set (Op D.AppOp)}
    (h_acyc : ∀ a, ¬ Relation.TransGen (stepNe S R) a a)
    {l : List (Op D.AppOp)} (h_l : listPermOf l S) (h_ne : S.Nonempty) :
    ∃ e ∈ S, ∀ x ∈ S, x ≠ e → ¬ R e x := by
  suffices walk : ∀ n (rem : List (Op D.AppOp)), rem.length = n → rem.Nodup →
      ∀ cur ∈ S,
      (∀ x ∈ S, x ∉ rem → x ≠ cur →
        Relation.TransGen (stepNe S R) x cur) →
      ∃ e ∈ S, ∀ x ∈ S, x ≠ e → ¬ R e x by
    obtain ⟨t₀, ht₀⟩ := h_ne
    exact walk l.length l rfl h_l.1 t₀ ht₀
      (fun x hx hx_not_l _ => absurd ((h_l.2 x).mpr hx) hx_not_l)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro rem h_len h_nodup cur h_cur h_reach
    by_cases h_max : ∃ x ∈ S, x ≠ cur ∧ R cur x
    · obtain ⟨x, hx_S, hx_ne, h_edge⟩ := h_max
      have h_edge_ne : stepNe S R cur x :=
        ⟨fun h => hx_ne h.symm, h_cur, hx_S, h_edge⟩
      by_cases hx_rem : x ∈ rem
      · have h_len' : (rem.erase x).length < n := by
          have h_pos : 0 < rem.length := List.length_pos_of_mem hx_rem
          rw [List.length_erase_of_mem hx_rem]
          omega
        refine ih _ h_len' (rem.erase x) rfl (h_nodup.erase x) x hx_S ?_
        intro y hy_S hy_not hy_ne
        by_cases hy_cur : y = cur
        · subst hy_cur
          exact Relation.TransGen.single h_edge_ne
        · have hy_not_rem : y ∉ rem := fun h_in =>
            hy_not (h_nodup.mem_erase_iff.mpr ⟨hy_ne, h_in⟩)
          exact (h_reach y hy_S hy_not_rem hy_cur).tail h_edge_ne
      · exfalso
        have h_x_reaches_cur : Relation.TransGen (stepNe S R) x cur :=
          h_reach x hx_S hx_rem hx_ne
        exact h_acyc x (h_x_reaches_cur.tail h_edge_ne)
    · push_neg at h_max
      exact ⟨cur, h_cur, fun x hx hx_ne h_lo => (h_max x hx hx_ne) h_lo⟩

/-- **A respecting enumeration from acyclicity** (abstract, fixed-relation
`exists_loOn_respecting_perm_u`). Topological sort of a finite acyclic relation:
the carrier shrinks by peeling a maximal element while the relation `R` stays
fixed, so (unlike the `loOn` proof) **no antitonicity is used**. -/
theorem exists_respecting_perm_fixed {R : Op D.AppOp → Op D.AppOp → Prop}
    {S : Set (Op D.AppOp)}
    (h_acyc : ∀ a, ¬ Relation.TransGen (stepNe S R) a a)
    {l : List (Op D.AppOp)} (h_l : listPermOf l S) :
    ∃ ρ : List (Op D.AppOp), listPermOf ρ S ∧ respects ρ R := by
  suffices gen : ∀ n (S' : Set (Op D.AppOp)) (l : List (Op D.AppOp)),
      l.length = n → S' ⊆ S → listPermOf l S' →
      ∃ ρ, listPermOf ρ S' ∧ respects ρ R by
    exact gen _ S l rfl Set.Subset.rfl h_l
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S' l h_len h_sub h_perm
    rcases Set.eq_empty_or_nonempty S' with rfl | h_ne
    · exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil⟩
    · have h_acyc' : ∀ a, ¬ Relation.TransGen (stepNe S' R) a a := by
        intro a hcyc
        refine h_acyc a (Relation.TransGen.mono (fun x y hxy => ?_) hcyc)
        obtain ⟨hne, ha, hb, hR⟩ := hxy
        exact ⟨hne, h_sub ha, h_sub hb, hR⟩
      obtain ⟨m, hm, h_max⟩ := exists_maximal_of_acyclic h_acyc' h_perm h_ne
      have hm_in_l : m ∈ l := (h_perm.2 m).mpr hm
      have h_perm' : listPermOf (l.erase m) (S' \ {m}) := by
        refine ⟨h_perm.1.erase m, fun a => ?_⟩
        rw [h_perm.1.mem_erase_iff]
        constructor
        · rintro ⟨hne, ha⟩
          exact ⟨(h_perm.2 a).mp ha, hne⟩
        · rintro ⟨ha, hne⟩
          exact ⟨hne, (h_perm.2 a).mpr ha⟩
      have h_len' : (l.erase m).length < n := by
        have h_pos : 0 < l.length := List.length_pos_of_mem hm_in_l
        rw [List.length_erase_of_mem hm_in_l]
        omega
      obtain ⟨ρ', hρ'_perm, hρ'_resp⟩ :=
        ih _ h_len' (S' \ {m}) (l.erase m) rfl
          (fun x hx => h_sub hx.1) h_perm'
      have hm_not_ρ' : m ∉ ρ' := fun h => ((hρ'_perm.2 m).mp h).2 rfl
      refine ⟨ρ' ++ [m], ⟨?_, fun a => ?_⟩, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hρ'_perm.1, List.nodup_singleton _, ?_⟩
        intro x hx y hy
        rw [List.mem_singleton] at hy; subst hy
        intro heq; subst heq
        exact hm_not_ρ' hx
      · rw [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h' | rfl)
          · exact ((hρ'_perm.2 a).mp h').1
          · exact hm
        · intro ha
          by_cases hae : a = m
          · exact Or.inr hae
          · exact Or.inl ((hρ'_perm.2 a).mpr ⟨ha, hae⟩)
      · unfold respects
        rw [List.pairwise_append]
        refine ⟨hρ'_resp, List.pairwise_singleton _ _, ?_⟩
        intro y hy b hb
        rw [List.mem_singleton] at hb; subst hb
        obtain ⟨hy_S, hy_ne⟩ := (hρ'_perm.2 y).mp hy
        exact h_max y hy_S hy_ne

/-! ## §2. The generic canonical state -/

/-- **The canonical state against an abstract arbitration**: the fold of some
`arb E`-respecting enumeration of `E`. With `arb := loOn (core C)` this is
`IsCanonicalState (core C) E`; the difference is that the arbitration is now a
parameter. `IsRALinearizable3Arb C arb` says every stored version's state is such
a canonical state (definitionally, this predicate at each version). -/
def IsCanonicalStateArb (_C : Configuration D)
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop)
    (E : Set (Op D.AppOp)) (s : D.State) : Prop :=
  ∃ ρ : List (Op D.AppOp),
    listPermOf ρ E ∧ respects ρ (arb E) ∧
    applySeq D.toCRDTSig D.init ρ = s

/-- **Existence** of the canonical state: from the arbitration's acyclicity on
`E` (the `AcyclicArbitration.acyclic` field). Pure §1 topological sort. -/
theorem isCanonicalStateArb_exists {C : Configuration D}
    (arb : AcyclicArbitration C) {E : Set (Op D.AppOp)}
    (hE : ∀ a ∈ E, a ∈ C.events)
    {l : List (Op D.AppOp)} (hl : listPermOf l E) :
    ∃ s, IsCanonicalStateArb C arb.arb E s := by
  obtain ⟨ρ, hp, hr⟩ :=
    exists_respecting_perm_fixed (R := arb.arb E)
      (fun a => arb.acyclic E hE a) hl
  exact ⟨applySeq D.toCRDTSig D.init ρ, ρ, hp, hr, rfl⟩

/-- **Uniqueness** of the canonical state: exactly the `ArbConvergence`
obligation (the phase-3b B-site, abstracted). Two `arb E`-respecting folds of the
same `E` agree. -/
theorem isCanonicalStateArb_unique {C : Configuration D}
    {arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop}
    {E : Set (Op D.AppOp)} {s s' : D.State}
    (hConv : ArbConvergence C arb)
    (hE : ∀ a ∈ E, a ∈ C.events)
    (h : IsCanonicalStateArb C arb E s)
    (h' : IsCanonicalStateArb C arb E s') : s = s' := by
  obtain ⟨ρ, hp, hr, hs⟩ := h
  obtain ⟨ρ', hp', hr', hs'⟩ := h'
  rw [← hs, ← hs']
  exact hConv E D.init ρ ρ' hE hp hp' hr hr'

/-- **Re-attaching an `arb`-maximal event** (abstract `isCanonicalState_snoc`).
This is the piece that consumes the THIRD arbitration clause, **antitonicity**
`h_anti : E' ⊆ E'' → arb E'' a b → arb E' a b`, via the step
`respects ρ (arb (E∖{e})) → respects ρ (arb E)`. See the file-header FINDING:
`loOn` supplies `h_anti` by `loOn_mono`; a set-indexed arbitration that flips
an edge on element removal would break this lemma while remaining acyclic and
convergent, so `h_anti` is independent of the other clauses. -/
theorem isCanonicalStateArb_snoc {C : Configuration D}
    {arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop}
    {E : Set (Op D.AppOp)} {t : D.State} {e : Op D.AppOp}
    (h_anti : ∀ {E' E'' : Set (Op D.AppOp)} {a b : Op D.AppOp},
       E' ⊆ E'' → arb E'' a b → arb E' a b)
    (h_e_in : e ∈ E)
    (h_max : ∀ x ∈ E, x ≠ e → ¬ arb E e x)
    (h : IsCanonicalStateArb C arb (E \ {e}) t) :
    IsCanonicalStateArb C arb E (D.update t e) := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  have h_e_notin : e ∉ ρ := fun hmem => ((hp.2 e).mp hmem).2 rfl
  refine ⟨ρ ++ [e], ⟨?_, fun a => ?_⟩, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hp.1, List.nodup_singleton _, ?_⟩
    intro x hx y hy heq
    rw [List.mem_singleton] at hy; subst hy; subst heq
    exact h_e_notin hx
  · rw [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h' | rfl)
      · exact ((hp.2 a).mp h').1
      · exact h_e_in
    · intro ha
      by_cases hae : a = e
      · exact Or.inr hae
      · exact Or.inl ((hp.2 a).mpr ⟨ha, hae⟩)
  · unfold respects
    rw [List.pairwise_append]
    refine ⟨hr.imp (fun hn h' => hn (h_anti Set.diff_subset h')),
      List.pairwise_singleton _ _, ?_⟩
    intro y hy b hb
    rw [List.mem_singleton] at hb; subst hb
    obtain ⟨hy_ev, hy_ne⟩ := (hp.2 y).mp hy
    exact h_max y hy_ev hy_ne
  · rw [applySeq_append_single, hf]

/-! ## §3. The generic adequacy theorem (loOn-refining form)

Any acyclic arbitration that **refines** `loOn` (every `loOn`-edge is an
`arb`-edge) certifies RA-linearizability of every good configuration against
`arb`. The proof: from `arb`'s acyclicity a respecting enumeration `ρ` of the
version's event set exists (§1); refinement makes `ρ` also `loOn`-respecting; and
the published `loOn` convergence (`convergence_on_u`) pins `ρ`'s fold to the
version's (already `loOn`-canonical) state. So the *order* is the abstract `arb`;
the *fold uniqueness* is still `loOn`'s. Both target instances refine `loOn`. -/

theorem isRALinearizable3Arb_of_acyclicArb_refines_loOn {C : Configuration D}
    (hU : UpdateVCs D.toCRDTSig)
    (arb : AcyclicArbitration C)
    (h_ref : ∀ (E : Set (Op D.AppOp)) {a b : Op D.AppOp},
       loOn (Configuration.core C) E a b → arb.arb E a b)
    (h : GoodConfig3 C) :
    IsRALinearizable3Arb C arb.arb := by
  intro v s E hv
  obtain ⟨ρlo, hplo, hrlo, hflo⟩ := h.canonical v s E hv
  have hE_evC : ∀ a ∈ E, a ∈ C.events := h.ver_events_sub v s E hv
  obtain ⟨ρ, hp, hr⟩ :=
    exists_respecting_perm_fixed (R := arb.arb E)
      (fun a => arb.acyclic E hE_evC a) hplo
  have hr_lo : respects ρ (loOn (Configuration.core C) E) :=
    hr.imp (fun hn h' => hn (h_ref E h'))
  refine ⟨ρ, hp, hr, ?_⟩
  have hconv := convergence_on_u hU D.init hE_evC hp hplo hr_lo hrlo
  rw [hconv, hflo]

/-- **loOn as an instance of the generic theorem.** `loOn` refines itself, so
the published `loOn`-form RA-linearizability is now the `arb := loOn` corollary
of `isRALinearizable3Arb_of_acyclicArb_refines_loOn` (compare the direct
`isRALinearizable3Arb_loOn_of_goodConfig3`). -/
theorem loOn_isRALinearizable3Arb_via_generic {C : Configuration D}
    (hU : UpdateVCs D.toCRDTSig) (h : GoodConfig3 C) :
    IsRALinearizable3Arb C (fun E => loOn (Configuration.core C) E) :=
  isRALinearizable3Arb_of_acyclicArb_refines_loOn hU
    (loOnArbitration C hU h.vis_trans h.vis_irrefl)
    (by intro _E _a _b h'; exact h') h

/-! ## §4. `GoodConfig3Arb`, the target invariant of the fully-generic engine

The fully-generic engine (arb-canonical states throughout, folds pinned by
`ArbConvergence`, `loOn` absent from the statement) establishes this invariant by
re-threading the transition induction; its `→ IsRALinearizable3Arb` lifting is
the trivial unfold discharged here. The induction itself (Join Lemma + apply/
merge cases over `IsCanonicalStateArb`, consuming §1/§2 in place of the `loOn`
machinery and the antitone clause of `isCanonicalStateArb_snoc`) is the named
#119(B-full) residue; see the file-header FINDING. -/

/-- Every stored version holds the `arb`-canonical state of its event set. -/
def GoodConfig3Arb (C : Configuration D)
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop) : Prop :=
  ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) → IsCanonicalStateArb C arb E s

/-- The invariant delivers arb-RA-linearizability (definitional unfold). -/
theorem isRALinearizable3Arb_of_goodConfig3Arb {C : Configuration D}
    {arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop}
    (h : GoodConfig3Arb C arb) : IsRALinearizable3Arb C arb :=
  fun v s E hv => h v s E hv

#print axioms exists_maximal_of_acyclic
#print axioms exists_respecting_perm_fixed
#print axioms isCanonicalStateArb_exists
#print axioms isCanonicalStateArb_unique
#print axioms isCanonicalStateArb_snoc
#print axioms isRALinearizable3Arb_of_acyclicArb_refines_loOn
#print axioms loOn_isRALinearizable3Arb_via_generic
#print axioms isRALinearizable3Arb_of_goodConfig3Arb

end Sal.ConditionedMRDTs
