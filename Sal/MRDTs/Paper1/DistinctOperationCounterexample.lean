import Sal.MRDTs.Paper1.InvariantReplay

/-! A countermodel to deriving replay diamonds from distinct-payload exactness.
The two events have one application payload, distinct timestamps and replicas,
and no visibility edge. Updating overwrites the state with the event timestamp.
Both complete admissible enumerations exist, but their concrete results differ.
This refutes the proposed policy-only sufficient conditions; it does not refute
`InvariantReplay.convergence_on`, which separately requires a replay diamond.
-/
namespace Sal.MRDTs.Paper1.DistinctOperationCounterexample
open Foundation

abbrev D : UpdateSig where
  State := Nat
  dec_state := inferInstance
  init := 0
  AppOp := Unit
  dec_op := inferInstance
  update := fun _ e => e.time

def a : Op Unit := (1, 0, ())
def b : Op Unit := (2, 1, ())
def E : Set (Op Unit) := fun x => x = a ∨ x = b
def P : OperationPolicy Unit := ⟨fun _ _ => False⟩

def C : ReplayContext D where
  L := fun _ => some E
  vis := fun _ _ => False
  timestamps_distinct := by
    intro x y r s r' s' hs hx ht hy ne
    simp only [Option.some.injEq] at hs ht
    subst s; subst s'
    change x = a ∨ x = b at hx
    change y = a ∨ y = b at hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [a, b] at ne ⊢
  vis_total_same_replica := by
    intro x y r s r' s' hs hx ht hy ne same
    simp only [Option.some.injEq] at hs ht
    subst s; subst s'
    change x = a ∨ x = b at hx
    change y = a ∨ y = b at hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [a, b] at ne same

def scope : InvariantReplay.Scope D := ⟨C, E, fun _ _ => True⟩
abbrev Inv : D.State → Prop := fun _ => True

/-- The revised exactness law holds, solely because distinct payloads cannot
occur. Equal payload does not imply equal effectors. -/
theorem revised_exact : ∀ x y : Op D.AppOp, x.op ≠ y.op →
    (¬ D.commutes x y ↔ P.before x.op y.op ∨ P.before y.op x.op) := by
  intro x y h
  exact False.elim (h (Subsingleton.elim _ _))

theorem revised_other_laws :
    (∀ x y z : Op D.AppOp, ¬ (P.before x.op y.op ∧ P.before y.op z.op)) ∧
    (∀ (s : D.State) (x y z : Op D.AppOp) (between : List (Op D.AppOp)),
      P.before x.op y.op → ¬ D.commutes y z →
      D.update (applySeq D (D.update (D.update s y) x) between) z =
      D.update (applySeq D (D.update (D.update s x) y) between) z) := by
  constructor
  · intro x y z; simp [P]
  · intro s x y z between impossible; exact impossible.elim

/-- PASS+FAIL: actual distinct eligible events have equal payloads and unequal
concrete order results. The invariant contains the initial and replay states. -/
theorem concrete_pair : a ∈ C.events ∧ b ∈ C.events ∧
    a.time ≠ b.time ∧ a.rep ≠ b.rep ∧ a.op = b.op ∧
    Inv 0 ∧ Inv 1 ∧ Inv 2 ∧
    applySeq D 0 [a,b] = 2 ∧ applySeq D 0 [b,a] = 1 ∧
    applySeq D 0 [a,b] ≠ applySeq D 0 [b,a] := by
  refine ⟨⟨0,E,rfl,by simp [E]⟩,⟨0,E,rfl,by simp [E]⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    decide

theorem noncommuting : ¬ InvariantOrder.Commutes D Inv a b := by
  intro h
  have bad := h 0 trivial
  have : (2 : Nat) = 1 := bad
  omega

private theorem empty_order (x y : Op D.AppOp) :
    ¬ InvariantOrder.order Inv P C E x y := by
  simp [InvariantOrder.order, C, P]

private theorem enumeration_ab : listPermOf [a,b] E := by
  constructor
  · decide
  · intro x; change x ∈ [a,b] ↔ x = a ∨ x = b; simp

private theorem enumeration_ba : listPermOf [b,a] E := by
  constructor
  · decide
  · intro x; change x ∈ [b,a] ↔ x = a ∨ x = b; simp [or_comm]

private theorem causal (xs : List (Op D.AppOp)) : respects xs C.vis := by
  exact List.pairwise_of_forall (fun _ _ => by simp [C])

private theorem ordered (xs : List (Op D.AppOp)) :
    respects xs (InvariantOrder.order Inv P C E) := by
  exact List.pairwise_of_forall (fun _ _ => empty_order _ _)

/-- Both canonical witnesses satisfy the existing readiness, visibility,
completeness and order definitions. Their concrete final states differ. -/
theorem two_canonical_states :
    InvariantReplay.Canonical scope Inv P 0 2 ∧
    InvariantReplay.Canonical scope Inv P 0 1 ∧ (2 : Nat) ≠ 1 := by
  constructor
  · exact ⟨[a,b],enumeration_ab,
      InvariantReplay.legal_of_causal_enumeration (fun _ h => h)
        enumeration_ab (causal _),causal _,ordered _,rfl⟩
  constructor
  · exact ⟨[b,a],enumeration_ba,
      InvariantReplay.legal_of_causal_enumeration (fun _ h => h)
        enumeration_ba (causal _),causal _,ordered _,rfl⟩
  · decide

/-- The separate replay diamond rejects the countermodel. Exempting equal
payloads requires a concrete equal-payload concurrent-pair condition,
or retaining this independently certified diamond. -/
theorem no_replay_certificate : ¬ InvariantReplay.Laws scope Inv P := by
  intro laws
  obtain ⟨h2,h1,ne⟩ := two_canonical_states
  exact ne (InvariantReplay.canonical_unique laws trivial h2 h1)

#print axioms revised_exact
#print axioms concrete_pair
#print axioms two_canonical_states
#print axioms no_replay_certificate
end Sal.MRDTs.Paper1.DistinctOperationCounterexample
