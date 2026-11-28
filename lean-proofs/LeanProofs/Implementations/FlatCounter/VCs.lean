import LeanProofs_no_spec_non_comm.Implementations.FlatCounter.Definition
import LeanProofs_no_spec_non_comm.Interface.VCRoute
import LeanProofs_no_spec_non_comm.Soundness.RALinearizability

/-!
**A duplicate, plus one section.** Everything up to the last section is
`Implementations/FlatCounter/VCs.lean` with the namespace changed. The last
section is what this folder adds: the chosen history respects
**specification visibility** as well, reached without SPEC-NON-COMM
although this row proves that law.

# The counter: every verification condition

All of them, in one file:

* Section 4's `Laws(D_type, Spec)`: RC-NON-COMM, NO-RC-CHAIN, COND-COMM and
  SPEC-NON-COMM.
* Section 5's VC1 to VC5.
* the sequential premise, `AnyOrderSound`.

`obligations` bundles what the metatheory consumes; `spec_non_comm` and
`anyOrderSound` are passed beside it. `Certificate.lean` uses all three, so no
condition here is stated without being consumed.

Each obligation is an integer identity closed by `omega`.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.FlatCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.NoSpecNonComm.Interface

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.NoSpecNonComm.Interface

/-- Every pair of events commutes, so by RC-NON-COMM `rc` is empty. -/
theorem all_commute (e₁ e₂ : D.Event) : D.Commutes e₁ e₂ := by
  intro z
  change Int at z
  change (z + delta e₁.op) + delta e₂.op = (z + delta e₂.op) + delta e₁.op
  omega

/-! ## `Laws(D_type)`, the three conditions that constrain `rc`

Proved here, not derived in the metatheory, and under the same names every
other row uses.

`rc` is `Either` at every pair for this datatype, so `no_rc_edge` is
immediate from the tuple and needs no lemma of its own. `all_commute` above
supplies the other half of each proof. The fourth law, SPEC-NON-COMM, needs
`Spec` and is in `SequentialSpec.lean`. -/

/-- `rc` orders no pair of events: the tuple's `rc` is `Either`. -/
theorem no_rc_edge (e₁ e₂ : D.Event) : ¬ D.EventRcBefore e₁ e₂ :=
  fun hb => OrderResult.noConfusion hb

/-- **NO-RC-CHAIN**: there is no `rc` edge at all, so there is none to
chain. -/
theorem no_rc_chain (o₁ o₂ o₃ : type.OType) :
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃) :=
  fun hc => OrderResult.noConfusion hc.1

/-- **`rc` relates exactly the non-commuting pairs.** Not one of the laws
and not part of this row's interface, which is why it is `private`. For the
counter both sides are false at every pair: nothing fails to commute, and
`rc` is `Either` everywhere. RC-NON-COMM is read off this one. -/
private theorem noncomm_iff_rc (e₁ e₂ : D.Event) :
    ¬ D.Commutes e₁ e₂ ↔ D.EventRcBefore e₁ e₂ ∨ D.EventRcBefore e₂ e₁ :=
  ⟨fun hn => (hn (all_commute e₁ e₂)).elim,
   fun hb => (hb.elim (no_rc_edge _ _) (no_rc_edge _ _)).elim⟩

/-- **The COND-COMM equation**, under the hypotheses its proof uses. The
absorber clause is reached only behind an `rc` edge, and there is none. -/
private theorem cond_comm_eq (S : D.Sigma) (e e' e'' : D.Event)
    (pi : List D.Event)
    (hrc : D.EventRcBefore e e') (_hnc : ¬ D.Commutes e' e'') :
    D.do_ (D.applyList (D.do_ (D.do_ S e') e) pi) e''
      = D.do_ (D.applyList (D.do_ (D.do_ S e) e') pi) e'' :=
  (no_rc_edge e e' hrc).elim

/-- **RC-NON-COMM**, exactly as Section 4 states it: at concurrent events,
with `o1 /= o2` on the left. NO-RC-CHAIN produces that conjunct read right
to left, which is what `rcNonComm_of_exact` does. -/
theorem rc_non_comm (e₁ e₂ : D.Event)
    (ht : D.time e₁ ≠ D.time e₂) (hr : D.rep e₁ ≠ D.rep e₂) :
    ((¬ D.Commutes e₁ e₂ ∧ e₁.op ≠ e₂.op) ↔
      D.EventRcBefore e₁ e₂ ∨ D.EventRcBefore e₂ e₁) :=
  rcNonComm_of_exact no_rc_chain (fun a b _ _ => noncomm_iff_rc a b) e₁ e₂ ht hr

/-- **COND-COMM**, exactly as Section 4 states it: at concurrent `e` and
`e'`. The guards are not used; there is no `rc` edge to transpose. -/
theorem cond_comm (S : D.Sigma) (e e' e'' : D.Event) (pi : List D.Event)
    (_ht : D.time e ≠ D.time e') (_hr : D.rep e ≠ D.rep e')
    (hrc : D.EventRcBefore e e') (hnc : ¬ D.Commutes e' e'') :
    D.do_ (D.applyList (D.do_ (D.do_ S e') e) pi) e''
      = D.do_ (D.applyList (D.do_ (D.do_ S e) e') pi) e'' :=
  cond_comm_eq S e e' e'' pi hrc hnc

/-- **`Laws(D_type)`.** Each field is the row's theorem of the same name,
unweakened. -/
theorem laws : Laws D := ⟨rc_non_comm, no_rc_chain, cond_comm⟩

/-! ## VC1 to VC5

Stated as Section 5 states them and proved here, premises and all. A
`merge` that never inspects its delta lets each proof abstract `e(m)` in one
step and close by arithmetic, but the theorem proved is the condition, not a
stronger equation that the condition is read off from.

All five are proved in place, VC4 included. This row needs no context
reasoning for it at all: `merge` subtracts its base, so the `B` of
CAUSAL-DELTA cancels and the condition holds at arbitrary states, like the
other four. -/

/-- **VC1** MERGE-COMM, over arbitrary states as the paper has it. -/
theorem vc1_merge_comm (l a b : D.Sigma) :
    D.merge l a b = D.merge l b a := by
  change Int at l a b
  change a + b - l = b + a - l
  omega

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init :
    ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
      SupportedOn D C E → IsCanOn D C E s →
      D.merge D.sigma0 D.sigma0 s = s := by
  intro _ _ s _ _
  change Int at s
  change (0 : Int) + s - 0 = s
  omega

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (l m x y : D.Sigma)
      (e : D.Event),
      VisStrict D C →
      SupportedOn D C E₁ → SupportedOn D C E₂ →
      WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
      e ∈ E₁ → e ∉ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
      IsCanOn D C (E₁ ∩ E₂) l →
      IsCanOn D C (downset C e \ {e}) m →
      IsCanOn D C (E₁ \ {e}) x →
      IsCanOn D C E₂ y →
      D.merge l (D.merge m x (D.do_ m e)) y
        = D.merge m (D.merge l x y) (D.do_ m e) := by
  intro _ _ _ l m x y e _ _ _ _ _ _ _ _ _ _ _ _
  generalize D.do_ m e = c
  change Int at l m x c y
  change (x + c - m) + y - l = x + y - l + c - m
  omega

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (x₀ x₁ x₂ m : D.Sigma)
      (e : D.Event),
      VisStrict D C →
      SupportedOn D C E₁ → SupportedOn D C E₂ →
      WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
      e ∈ E₁ → e ∈ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
      IsCanOn D C ((E₁ ∩ E₂) \ {e}) x₀ →
      IsCanOn D C (downset C e \ {e}) m →
      IsCanOn D C (E₁ \ {e}) x₁ →
      IsCanOn D C (E₂ \ {e}) x₂ →
      D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
          (D.merge m x₂ (D.do_ m e))
        = D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e) := by
  intro _ _ _ x₀ x₁ x₂ m e _ _ _ _ _ _ _ _ _ _ _ _
  generalize D.do_ m e = c
  change Int at m x₀ x₁ x₂ c
  change (x₁ + c - m) + (x₂ + c - m) - (x₀ + c - m) = x₁ + x₂ - x₀ + c - m
  omega

/-- **VC4** CAUSAL-DELTA.

`merge` subtracts its base, and `do` adds the delta to whatever state it is
handed. So `merge B A (e(B))` returns `A + (B + delta) - B`, which is
`A + delta`, which is `e(A)`. The base `B` cancels, and the condition holds
at arbitrary states for the same reason the other four do. -/
theorem vc4_causal_delta :
    ∀ (C : Ctx D) (U : Set D.Event) (A B : D.Sigma) (e : D.Event),
      VisStrict D C →
      SupportedOn D C U → WeaklyClosed D C U →
      e ∈ U → MaximalOn D C U e →
      IsCanOn D C (U \ {e}) A →
      IsCanOn D C (downset C e \ {e}) B →
      D.merge B A (D.do_ B e) = D.do_ A e := by
  intro _ _ A B e _ _ _ _ _ _ _
  change Int at A B
  change A + (B + delta e.op) - B = A + delta e.op
  omega

/-- **VC1 to VC5** of Section 5. -/
theorem joinLaws : CanonicalJoinLawsOn D (fun _ => True) where
  vc1_merge_comm := vc1_merge_comm
  vc2_merge_init := fun C E s _ => vc2_merge_init C E s
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ =>
    vc3_local_redistribute C E₁ E₂ l m x y e
  vc4_causal_delta := fun C U A B e _ => vc4_causal_delta C U A B e
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ =>
    vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e

/-! ## The sequential premise, and SPEC-NON-COMM -/

/-- The abstraction function of Section 6. The counter's state is already
the specification's state, so `alpha` is the identity and conditions (i),
(ii) and (iii) all hold definitionally. -/
def abstraction : Soundness.Abstraction D specMachine where
  alpha := id
  init := rfl
  step := fun _ _ => rfl
  observes := fun _ _ => rfl

/-- The sequential premise: `ops(pi) . (q => b)` is admitted by `Spec`, with
`b` the implementation's own answer. It follows from the three conditions. -/
theorem anyOrderSound : Soundness.AnyOrderSound D historySpec :=
  abstraction.anyOrderSound

/-! ## `Laws(D_type, Spec)`: the fourth law

SPEC-NON-COMM is the one law of Section 4 that mentions `Spec`, so it is
proved here rather than in `Laws.lean`. The specification adds a delta, so its two updates commute for the same
reason the implementation's do. -/

/-- Every pair of operations commutes in `Spec`. -/
theorem spec_commutes (o₁ o₂ : type.OType) :
    Interface.spec_commutes historySpec o₁ o₂ :=
  specMachine.language_commutes o₁ o₂ (fun s => by
    change Int at s
    show s + delta o₁ + delta o₂ = s + delta o₂ + delta o₁
    omega)

/-- **SPEC-NON-COMM**: no implementation commutation erases a specification
conflict, because `Spec` has no conflict to erase. -/
theorem spec_non_comm : Interface.spec_non_comm D historySpec :=
  Interface.spec_non_comm_of_spec_commutes spec_commutes

/-- **The bundle the specification route consumes**: the obligations of
Section 5 together with SPEC-NON-COMM, the one law of Section 4 that
mentions `Spec`. -/
theorem obligations : SpecObligations D historySpec :=
  SpecObligations.ofUniform laws noncomm_iff_rc cond_comm_eq joinLaws
    spec_non_comm

/-! # Specification visibility, without SPEC-NON-COMM

This row proves SPEC-NON-COMM, so it does not **need** the route below. What
the section shows is that the route is available anyway, on its own terms.

`Soundness.certifiedSpecRA_any` asks a row for one thing, that
`Soundness.joint` has no loop. Here that is immediate: every event of this
row commutes with every other, so `rc` is empty by RC-NON-COMM and `lo^C_E`
has no edges at all, which leaves `joint` a subrelation of `vis`.
-/

open Artifact.MRDTs.Paper1

/-- **Every edge is causal.** `lo^C_E` is empty here, and a
specification-visibility arrow runs along `vis`. -/
theorem edge_vis  {C : Configuration D.toMRDTSig} {E : Set D.Event} {a b : D.Event}
    (h : Soundness.joint D historySpec C.replayContext E a b) : C.replayContext.vis a b := by
  rcases h.2.2 with hs | hp
  · exact hs.1
  · exact absurd hp (Soundness.paperOrder_false noncomm_iff_rc all_commute _ _ _ _)

/-- So every path composes into one `vis` edge. -/
theorem vis_of_joint_path  {C : Configuration D.toMRDTSig} {E : Set D.Event}
    (hvs : VisStrict D C.replayContext) :
    ∀ {a b : D.Event}, Relation.TransGen (Soundness.joint D historySpec C.replayContext E) a b →
      C.replayContext.vis a b := by
  intro a b h
  induction h with
  | single hedge => exact edge_vis hedge
  | tail _ hedge ih => exact hvs.1 ih (edge_vis hedge)

/-- **No loop**, since a loop would make an event see itself. -/
theorem joint_acyclic  : Soundness.JointAcyclic D historySpec :=
  fun _ _ hvs a h => hvs.2 a (vis_of_joint_path hvs h)

end LeanProofs.NoSpecNonComm.Implementations.FlatCounter
