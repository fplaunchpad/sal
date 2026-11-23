import LeanProofs1.Implementations.TreeMove.Definition
import LeanProofs1.Interface.VCRoute
import LeanProofs1.Interface.VCRoute

/-!
# Tree move: every verification condition

All of them, in one file:

* Section 4's `Laws(D_type, Spec)`: RC-NON-COMM, NO-RC-CHAIN, COND-COMM and
  SPEC-NON-COMM.
* Section 5's VC1 to VC5.
* the sequential premise, in its execution-scoped form `HistorySound`.

`obligations` bundles what the metatheory consumes; `historySound` is passed
beside it. `Certificate.lean` uses both.

The appendix's claim for this row is that **complete deliveries commute on
the coherent state space, including their undo metadata**. That is
`all_commute` below, and unlike the embedded RGA family it is a theorem
rather than a hedge, because `Sigma` **is** the coherent state space.

`Coherence.lean` did the work: on a coherent state every delivery returns
the `build` of a key-descending list, and a coherent state is determined by
its move set. So each condition of Section 5 reduces to a membership
identity, closed by `tauto` after `ext_of_ops` turns state equality into
move-set equality. This row therefore discharges the conditions the way a
grow-only row does, even though its `merge` is an undo/insert/redo fold
rather than a union.

The sequential premise cannot be `SpecSound`: `Legal` admits only key-sorted
histories, so the row has to choose the explaining order itself. It chooses
the key-ascending enumeration, and the agreement rests on
`candidate_safe_iff`, which says that on an acyclic tree the implementation's
ancestor test and the specification's acyclicity test are complements.
-/

namespace LeanProofs1.Implementations.TreeMove

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-! ## States are their move sets -/

/-- Two states with the same moves are the same state. -/
theorem ext_of_ops {s t : St} (h : ∀ x, x ∈ ops s.1 ↔ x ∈ ops t.1) : s = t :=
  Subtype.ext (coh_ext s.2 t.2 h)

/-- The moves of a delivery. -/
@[simp] theorem ops_step (s : St) (e : Event) (x : AppOp) :
    x ∈ ops (step s e).1 ↔ x = e.op ∨ x ∈ ops s.1 := by
  show x ∈ ops (receive s.1 e.op) ↔ _
  rw [ops_receive s.2, mem_ins]

/-- The moves of a merge. The ancestor contributes nothing. -/
@[simp] theorem ops_mergeState (l a b : St) (x : AppOp) :
    x ∈ ops (mergeState l a b).1 ↔ x ∈ ops b.1 ∨ x ∈ ops a.1 :=
  ops_mergeRaw a.2 b.1 x

/-- The initial state has no moves. -/
@[simp] theorem ops_init (x : AppOp) : x ∈ ops (D.sigma0 : St).1 ↔ False := by
  simp [ops]

/-! ## `Laws(D_type)`, the three conditions that constrain `rc`

**Complete deliveries commute on the coherent state space.** Each side
delivers the same two moves, the resulting state is the `build` of the
descending list of all of them, and that list does not depend on the order
they arrived in. The undo metadata is part of that state, so it agrees too.

`rc` is `Either` at every pair, so `no_rc_edge` is immediate from the tuple.
-/

/-- The appendix's commutation claim, over the whole of `Sigma`. -/
theorem all_commute (e₁ e₂ : D.Event) : D.Commutes e₁ e₂ := by
  intro s
  apply ext_of_ops
  intro x
  simp only [Impl.do_, ops_step]
  tauto

/-- `rc` orders no pair of events: the tuple's `rc` is `Either`. -/
theorem no_rc_edge (e₁ e₂ : D.Event) : ¬ D.EventRcBefore e₁ e₂ :=
  fun hb => OrderResult.noConfusion hb

/-- **NO-RC-CHAIN**: there is no `rc` edge at all, so there is none to
chain. -/
theorem no_rc_chain (o₁ o₂ o₃ : type.OType) :
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃) :=
  fun hc => OrderResult.noConfusion hc.1

/-- **RC-NON-COMM**, without the concurrency guard. Both sides are false:
the left by `all_commute`, the right because `rc` is empty. -/
theorem rc_non_comm : UniformRcNonComm D := fun e₁ e₂ =>
  ⟨fun hn => (hn (all_commute e₁ e₂)).elim,
   fun hb => (hb.elim (no_rc_edge _ _) (no_rc_edge _ _)).elim⟩

/-- **COND-COMM**, without the concurrency guard. The absorber clause is
reached only behind an `rc` edge, and there is none. -/
theorem cond_comm : UniformCondComm D := fun _ e e' _ _ hb _ =>
  (no_rc_edge e e' hb).elim

/-- **`Laws(D_type)`.** RC-NON-COMM carries the paper's `o1 /= o2` conjunct,
which NO-RC-CHAIN supplies through `rcNonComm_of_exact`. -/
theorem laws : Laws D :=
  ⟨rcNonComm_of_exact no_rc_chain (fun e₁ e₂ _ _ => rc_non_comm e₁ e₂),
   no_rc_chain,
   fun _ e e' _ _ _ _ hb _ => (no_rc_edge e e' hb).elim⟩

/-! ## VC1 and VC2 -/

/-- **VC1** MERGE-COMM, over arbitrary states as the paper has it. -/
theorem vc1_merge_comm (l a b : D.Sigma) : D.merge l a b = D.merge l b a := by
  apply ext_of_ops; intro x; simp only [Impl.merge, ops_mergeState]; tauto

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init : ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
    SupportedOn D C E → IsCanOn D C E s →
    D.merge D.sigma0 D.sigma0 s = s := by
  intro _ _ s _ _
  apply ext_of_ops; intro x
  simp only [Impl.merge, ops_mergeState, ops_init]; tauto

/-! ## The three canonical conditions -/

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (l m x y : D.Sigma) (e : D.Event),
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
  apply ext_of_ops; intro z
  simp only [Impl.merge, Impl.do_, ops_mergeState, ops_step]; tauto

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (x₀ x₁ x₂ m : D.Sigma) (e : D.Event),
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
  apply ext_of_ops; intro z
  simp only [Impl.merge, Impl.do_, ops_mergeState, ops_step]; tauto

/-- **VC4** CAUSAL-DELTA.

Every pair of events commutes, so `lo^C_E` has no edges, `down(e) \ {e}` is
empty and `B` is forced to `sigma0`. The condition is then the row's own
merge identity at the initial state. -/
theorem vc4_causal_delta :
    ∀ (C : Ctx D) (U : Set D.Event) (A B : D.Sigma) (e : D.Event),
      VisStrict D C →
      SupportedOn D C U → WeaklyClosed D C U →
      e ∈ U → MaximalOn D C U e →
      IsCanOn D C (U \ {e}) A →
      IsCanOn D C (downset C e \ {e}) B →
      D.merge B A (D.do_ B e) = D.do_ A e := by
  letI : EventOrder D.toMRDTSig.toUpdateSig := Interface.rcOrder D
  intro C U A B e _ _ _ _ _ _ hB
  rw [isCanonicalState_empty (downset_diff_self_of_commuting all_commute C e) hB]
  show D.merge D.sigma0 A (D.do_ D.sigma0 e) = D.do_ A e
  apply ext_of_ops; intro x
  simp only [Impl.merge, Impl.do_, ops_mergeState, ops_step, ops_init]; tauto
/-- **VC1 to VC5** of Section 5. -/
theorem joinLaws : CanonicalJoinLawsOn D (fun _ => True) where
  vc1_merge_comm := vc1_merge_comm
  vc2_merge_init := fun C E s _ => vc2_merge_init C E s
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ =>
    vc3_local_redistribute C E₁ E₂ l m x y e
  vc4_causal_delta := fun C U A B e _ => vc4_causal_delta C U A B e
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ =>
    vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e

/-- **Everything the metatheory consumes.** The same bundle a commuting row
supplies: `Laws(D_type)`, the two unguarded readings it leaves open, VC1 to
VC5, and an execution order. -/
theorem obligations : Obligations D :=
  Obligations.ofCommuting laws all_commute joinLaws

/-! ## The two rejection tests agree

The implementation refuses a move when the child is its own parent or the
parent already reaches the child; the specification refuses one when the
candidate graph has a cycle. `candidate_safe_iff` is the appendix's claim
that on an acyclic tree these are complements, so the two agree on every
state the specification can be in.

Everything rests on one observation: the candidate tree differs from the
original only at the moved child, so any path that does not start at that
child takes the same first step in both.
-/

section Acyclicity

variable (T : Tree) (c p m : Nat)

/-- Off the moved child, the candidate tree has the original's edges. -/
theorem edge_update_of_ne {x z : Nat} (hx : x ≠ c) :
    Edge (Function.update T c (some (p, m))) x z ↔ Edge T x z := by
  simp only [Edge, Function.update_of_ne hx]

/-- At the moved child, the only edge goes to the new parent. -/
theorem edge_update_self (z : Nat) :
    Edge (Function.update T c (some (p, m))) c z ↔ z = p := by
  simp only [Edge, Function.update_self]
  constructor
  · rintro ⟨m', h⟩; exact (Prod.mk.injEq .. ▸ (Option.some.inj h)).1.symm
  · rintro rfl; exact ⟨m, rfl⟩

/-- **The path dichotomy.** A candidate path out of a node other than the
moved child either avoids that child entirely, in which case it is an
original path, or it reaches it, in which case the original reaches it
too. -/
theorem path_update_split {x y : Nat}
    (h : Path (Function.update T c (some (p, m))) x y) :
    x ≠ c → Path T x y
      ∨ (Path T x c ∧ Path (Function.update T c (some (p, m))) c y) := by
  refine Relation.TransGen.head_induction_on h ?_ ?_
  · intro a ha hx
    exact Or.inl (Relation.TransGen.single ((edge_update_of_ne T c p m hx).mp ha))
  · intro a z h' hrest IH hx
    have hae : Edge T a z := (edge_update_of_ne T c p m hx).mp h'
    by_cases hzc : z = c
    · subst hzc
      exact Or.inr ⟨Relation.TransGen.single hae, hrest⟩
    · rcases IH hzc with hl | ⟨h1, h2⟩
      · exact Or.inl (hl.head hae)
      · exact Or.inr ⟨h1.head hae, h2⟩

/-- An original path into the moved child survives into the candidate: every
edge it takes starts somewhere other than the child. -/
theorem path_update_to_self {x : Nat} (h : Path T x c) :
    x ≠ c → Path (Function.update T c (some (p, m))) x c := by
  refine Relation.TransGen.head_induction_on h ?_ ?_
  · intro a ha hx
    exact Relation.TransGen.single ((edge_update_of_ne T c p m hx).mpr ha)
  · intro a z h' hrest IH hx
    have hae : Edge (Function.update T c (some (p, m))) a z :=
      (edge_update_of_ne T c p m hx).mpr h'
    by_cases hzc : z = c
    · subst hzc; exact Relation.TransGen.single hae
    · exact (IH hzc).head hae

/-- When the rejection test passes, the moved child is on no candidate
cycle. -/
theorem no_cycle_at_child (hne : c ≠ p) (hnp : ¬ Path T p c) :
    ¬ Path (Function.update T c (some (p, m))) c c := by
  intro hcyc
  obtain ⟨z, hz, hrest⟩ := Relation.TransGen.head'_iff.mp hcyc
  have hzp : z = p := (edge_update_self T c p m z).mp hz
  rw [hzp] at hrest
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hrest with heq | htr
  · exact hne heq
  · rcases path_update_split T c p m htr (Ne.symm hne) with hl | ⟨h1, -⟩
    · exact hnp hl
    · exact hnp h1

/-- **`candidate_safe_iff`.** On an acyclic tree, the implementation's
ancestor test and the specification's acyclicity test are complements. -/
theorem candidate_safe_iff (hT : Acyclic T) :
    Acyclic (Function.update T c (some (p, m))) ↔ ¬ (c = p ∨ Path T p c) := by
  constructor
  · intro hac hbad
    rcases hbad with hcp | hpath
    · exact hac c (Relation.TransGen.single
        ((edge_update_self T c p m c).mpr hcp))
    · by_cases hpc : p = c
      · exact hac c (Relation.TransGen.single
          ((edge_update_self T c p m c).mpr hpc.symm))
      · exact hac c (Relation.TransGen.head
          ((edge_update_self T c p m p).mpr rfl)
          (path_update_to_self T c p m hpath hpc))
  · intro hgood x hcyc
    rw [not_or] at hgood
    obtain ⟨hne, hnp⟩ := hgood
    by_cases hxc : x = c
    · subst hxc; exact no_cycle_at_child T x p m hne hnp hcyc
    · rcases path_update_split T c p m hcyc hxc with hl | ⟨h1, h2⟩
      · exact hT x hl
      · exact no_cycle_at_child T c p m hne hnp
          (h2.trans (path_update_to_self T c p m h1 hxc))

end Acyclicity

/-- **The update agrees with the specification's move** on every acyclic
tree. -/
theorem f_eq_moveSpec {T : Tree} (hT : Acyclic T) (o : AppOp) :
    f T o = moveSpec T o := by
  by_cases h : o.child = o.parent ∨ Path T o.parent o.child
  · have hbad : ¬ Acyclic (Function.update T o.child (some (o.parent, o.mdata))) :=
      fun hac => ((candidate_safe_iff T o.child o.parent o.mdata hT).mp hac) h
    simp only [f, moveSpec, if_pos h, if_neg hbad]
  · have hok : Acyclic (Function.update T o.child (some (o.parent, o.mdata))) :=
      (candidate_safe_iff T o.child o.parent o.mdata hT).mpr h
    simp only [f, moveSpec, if_neg h, if_pos hok]

/-- The update preserves acyclicity. -/
theorem acyclic_f {T : Tree} (hT : Acyclic T) (o : AppOp) : Acyclic (f T o) := by
  by_cases h : o.child = o.parent ∨ Path T o.parent o.child
  · simpa only [f, if_pos h] using hT
  · simpa only [f, if_neg h] using
      (candidate_safe_iff T o.child o.parent o.mdata hT).mpr h

/-- The empty tree has no edges. -/
theorem acyclic_init : Acyclic T0 := by
  have h : ∀ a b : Nat, ¬ Path T0 a b := by
    intro a b hp
    induction hp with
    | single h => exact absurd h (by simp [Edge, T0])
    | tail _ h _ => exact absurd h (by simp [Edge, T0])
  exact fun x => h x x

/-- So the implementation's fold and the specification's fold agree. -/
theorem foldl_f_eq : ∀ (A : List AppOp) {T : Tree}, Acyclic T →
    A.foldl f T = A.foldl moveSpec T
  | [], _, _ => rfl
  | o :: A, T, hT => by
      simp only [List.foldl_cons, f_eq_moveSpec hT o]
      exact foldl_f_eq A (f_eq_moveSpec hT o ▸ acyclic_f hT o)

/-! ## The implementation state is the key-descending build

`Coherence.lean` showed that a coherent state is its move set. So the state
after delivering a list of events is read off from its moves alone, and the
tree it maintains is the oldest-first fold of the update.
-/

/-- `build` applies the updates oldest first. -/
theorem tree_build : ∀ L : List AppOp, (build L).2 = L.reverse.foldl f T0
  | [] => rfl
  | o :: E => by
      show f (build E).2 o = _
      rw [tree_build E, List.reverse_cons, List.foldl_append]
      rfl

/-- The moves of a delivery sequence. -/
theorem ops_applyList : ∀ (pi : List Event) (s : St) (x : AppOp),
    x ∈ ops (D.applyList s pi).1 ↔ x ∈ pi.map Op.op ∨ x ∈ ops s.1
  | [], s, x => by simp [Impl.applyList]
  | e :: pi, s, x => by
      show x ∈ ops (D.applyList (D.do_ s e) pi).1 ↔ _
      rw [ops_applyList pi (D.do_ s e) x]
      simp only [Impl.do_, ops_step, List.map_cons, List.mem_cons]
      tauto

/-- **The state after a key-ascending delivery is the build of its
reverse.** Both are coherent and carry the same moves. -/
theorem applyList_eq (pi : List Event) (hd : Desc (pi.map Op.op).reverse) :
    (D.applyList D.sigma0 pi).1 = build (pi.map Op.op).reverse := by
  refine coh_ext (D.applyList D.sigma0 pi).2 (coherent_build hd) ?_
  intro x
  rw [ops_build, ops_applyList pi D.sigma0 x, List.mem_reverse]
  simp [ops]

/-! ## Context facts -/

variable {C : Configuration D.toMRDTSig}

/-- Distinct events of a context carry distinct timestamps. -/
theorem time_ne {K : Ctx D} {a b : D.Event} (ha : a ∈ K.events)
    (hb : b ∈ K.events) (hne : a ≠ b) : a.time ≠ b.time := by
  obtain ⟨p, t, hL, ht⟩ := ha
  obtain ⟨p', t', hL', ht'⟩ := hb
  exact K.timestamps_distinct hL ht hL' ht' hne

/-- What honest issuance supplies: the operation's copy of the key is the
event's own, and the child is neither the root nor the trash. -/
theorem issued (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {e : D.Event} (he : e ∈ C.events) :
    e.op.time = e.time ∧ e.op.rep = e.rep ∧ e.op.child ≠ 0 ∧ e.op.child ≠ 1 := by
  obtain ⟨pi, -, -, hg⟩ := hmint e he
  rw [show issuance.CanIssue e (applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init pi)
        = issuance.CanIssue e (D.applyList D.sigma0 pi) from rfl] at hg
  exact ⟨hg.1, hg.2.1, hg.2.2.2.1, hg.2.2.2.2⟩

/-- Honest events carry distinct moves, since their keys carry distinct
timestamps. -/
theorem op_inj (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {a b : D.Event} (ha : a ∈ C.events) (hb : b ∈ C.events)
    (h : a.op = b.op) : a = b := by
  by_contra hne
  refine time_ne (K := C.replayContext)
    (by rw [Configuration.replayContext_events]; exact ha)
    (by rw [Configuration.replayContext_events]; exact hb) hne ?_
  rw [← (issued hmint ha).1, ← (issued hmint hb).1, h]

/-! ## The arrangement

The row chooses the key-ascending enumeration, which is the one the
specification's `Legal` admits.
-/

/-- Compare two events on the key their moves carry. -/
def byKey (a b : Event) : Bool := decide (key a.op ≤ key b.op)

/-- The explaining order. -/
noncomputable def arrange (pi : List Event) : List Event := pi.mergeSort byKey

theorem arrange_perm (pi : List Event) : (arrange pi).Perm pi :=
  List.mergeSort_perm _ _

theorem arrange_sorted (pi : List Event) :
    (arrange pi).Pairwise (fun a b => key a.op ≤ key b.op) := by
  have := List.pairwise_mergeSort (le := byKey)
    (by intro a b c hab hbc
        simp only [byKey, decide_eq_true_eq] at hab hbc ⊢
        exact le_trans hab hbc)
    (by intro a b
        simp only [byKey, Bool.or_eq_true, decide_eq_true_eq]
        exact le_total _ _) pi
  exact this.imp (by intro a b h; simpa only [byKey, decide_eq_true_eq] using h)

/-! ## The arranged history is legal -/

/-- `Legal` is inherited by sublists, so it holds at every prefix. -/
theorem legal_sublist {h h' : List AppOp} (hs : List.Sublist h' h) (hl : Legal h) :
    Legal h' :=
  ⟨hl.1.sublist hs, hl.2.1.sublist hs, fun o ho => hl.2.2 o (hs.mem ho)⟩

/-- The arranged move list is nondecreasing in the key, has no repeats, and
names neither reserved node as a child. -/
theorem legal_arrange (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {E : Set D.Event} {pi : List D.Event}
    (hpi : listPermOf pi E) (hsub : ∀ e ∈ E, e ∈ C.events) :
    Legal ((arrange pi).map Op.op) := by
  have hmemC : ∀ e ∈ arrange pi, e ∈ C.events := fun e he =>
    hsub e ((hpi.2 e).mp ((arrange_perm pi).mem_iff.mp he))
  refine ⟨?_, ?_, ?_⟩
  · refine List.Nodup.map_on ?_ ((arrange_perm pi).nodup_iff.mpr hpi.1)
    intro x hx y hy hk
    exact op_inj hmint (hmemC x hx) (hmemC y hy) hk
  · exact List.pairwise_map.mpr (arrange_sorted pi)
  · intro o ho
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    exact ⟨(issued hmint (hmemC e he)).2.2.1, (issued hmint (hmemC e he)).2.2.2⟩

/-- The arranged move list is strictly ascending, so its reverse is a
descending log. -/
theorem desc_arrange (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {E : Set D.Event} {pi : List D.Event}
    (hpi : listPermOf pi E) (hsub : ∀ e ∈ E, e ∈ C.events) :
    Desc ((arrange pi).map Op.op).reverse := by
  have hl := legal_arrange hmint hpi hsub
  rw [Desc, List.pairwise_reverse]
  exact (hl.2.1.and hl.1).imp (fun h => lt_of_le_of_ne h.1 (key_ne h.2))

/-! ## The sequential premise

`SpecSound` is out of reach: `Legal` admits only key-sorted histories, so
the row has to choose the explaining order itself. That is the `E = Y`
column of Table 1, and `HistorySound` is its form.
-/

/-- The specification runs along any legal move list, keeping the prefix
beside the tree. -/
theorem spec_run : ∀ (A pre : List AppOp) (T : Tree), Legal (pre ++ A) →
    Runs specMachine.transition (pre, T)
      (A.map (SeqLabel.update (Query := type.QType) (Value := type.ValType)))
      (pre ++ A, A.foldl moveSpec T)
  | [], pre, T, _ => by simpa using Runs.nil (step := specMachine.transition) (pre, T)
  | o :: A, pre, T, hl => by
      have hsub : List.Sublist (pre ++ [o]) (pre ++ o :: A) :=
        List.Sublist.append_left (List.cons_sublist_cons.mpr (List.nil_sublist A)) pre
      refine Runs.cons (m := (pre ++ [o], moveSpec T o)) ⟨legal_sublist hsub hl, rfl⟩ ?_
      have hnext : Legal ((pre ++ [o]) ++ A) := by simpa using hl
      have hrun := spec_run A (pre ++ [o]) (moveSpec T o) hnext
      simpa [List.append_assoc] using hrun

/-- **Clause 2, execution-scoped.** The key-ascending enumeration is
admitted by `Spec`, and the tree it ends at is the one the implementation's
query reads. -/
theorem historySound : Soundness.HistorySound D historySpec issuance := by
  rintro C hmint E hsub hclosed ⟨pi, hpi⟩ q
  have hlegal := legal_arrange hmint hpi hsub
  have hdesc := desc_arrange hmint hpi hsub
  refine ⟨arrange pi, ?_, ?_, ?_⟩
  · exact ⟨(arrange_perm pi).nodup_iff.mpr hpi.1,
      fun a => ((arrange_perm pi).mem_iff).trans (hpi.2 a)⟩
  · exact ((arrange_perm pi).nodup_iff.mpr hpi.1).imp
      (fun {_ _} _ => Soundness.paperOrder_false rc_non_comm all_commute _ _ _ _)
  · have hlabels : projectedUpdates (D := D.toMRDTSig) (arrange pi)
        = ((arrange pi).map Op.op).map SeqLabel.update := by
      simp [projectedUpdates, List.map_map, Function.comp]
    have hstate : D.toMRDTSig.query (D.applyList D.sigma0 (arrange pi)) q
        = visible (((arrange pi).map Op.op).foldl moveSpec T0) := by
      show visible (D.applyList D.sigma0 (arrange pi)).1.2 = _
      rw [applyList_eq (arrange pi) hdesc, tree_build, List.reverse_reverse,
        foldl_f_eq _ acyclic_init]
    rw [hlabels, show applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init (arrange pi)
          = D.applyList D.sigma0 (arrange pi) from rfl, hstate]
    exact ⟨_, Runs.append
      (spec_run ((arrange pi).map Op.op) [] T0 (by simpa using hlegal))
      (Runs.cons (m := ([] ++ ((arrange pi).map Op.op),
        (((arrange pi).map Op.op)).foldl moveSpec T0)) ⟨rfl, rfl⟩ (Runs.nil _))⟩

end LeanProofs1.Implementations.TreeMove
