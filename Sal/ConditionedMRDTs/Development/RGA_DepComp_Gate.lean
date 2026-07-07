import Sal.ConditionedMRDTs.Development.RGA_SimulInduction

/-!
# `DepComp` gate for the RGA's concrete `loOnA` — prove or refute

QUESTION (`RGA_SimulInduction.lean` §2, `DepComp`): is `loOnA RGACondSig Cfg E`
transitive on a backward-closed event set of a real execution?

UNFOLDING for the RGA: `loOnA = loOnC ∨ (vis ∧ appliesDependsOn)` where
`appliesDependsOn D e₂ e₁ := ∃ s, D.applicable e₂ s ≠ D.applicable e₂ (D.update s e₁)`
(the SEMANTIC dependency of `ConditionedConvergence.lean:121`), and `loOnC`'s
rc-disjunct is dead (`rc ≡ Either`).  The 2×2 mixed cases of the composition
`b→a→o` collapse: the `loOnC` (vis-noncommuting) disjunct is unavailable as a
*conclusion* whenever the pair commutes, so the crux case is DEP∘DEP:

    vis b a ∧ dep(a,b)  →  vis a o ∧ dep(o,a)  →  vis b o ∧ dep(o,b)?

VERDICT: **REFUTED.**  The conjectured reason it holds — "path-ancestor chains
are rootward-closed, so applicability-relevance composes" — is defeated by the
tombstone-free RGA's REHOMING: `Del` re-parents the target's children to its
nearest live ancestor, so a later op's accurate path NO LONGER names the deleted
ancestor.  Concretely, in the single-replica execution

    b = (1,0, Ins 10 [] 0)   -- insert node 1 at root
    a = (2,0, Ins 20 [] 1)   -- insert node 2 anchored at node 1
    d = (3,0, Del [] 1)      -- delete node 1; node 2 is rehomed to root
    o = (4,0, Del [] 2)      -- delete node 2 (its true chain is now [])

we have `loOnA b a` (b creates the node a anchors at) and `loOnA a o` (a creates
o's target), but `¬ loOnA b o`: `o` reads only key 2 while `b` writes only key 1
(`¬ dep(o,b)`), and `b,o` commute on ALL states (`¬` the loOnC disjunct).  The
event set `E = {b,a,d,o}` is the full (hence backward-closed) event set, `vis`
is the transitive program order, ids are nonzero and distinct, and every op is
`applicable` at its generation state (`gen_b/gen_a/gen_d/gen_o`) — so no
dischargeable hypothesis on `E`/`Cfg` (backward-closure, vis strict order,
GenDisc-style generation accuracy) can rescue `DepComp`.

Without `d` the composite edge returns (`o` would carry path `[1]`), so
deletion-with-rehoming is exactly the defeater.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGADepCompGate

open Sal.Emulation
open Sal.ConditionedMRDTs.RGASig (RGACondSig rc_is_Either)
open Sal.ConditionedMRDTs (loOnC)
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA appliesDependsOn)
open Classical

/-! ## §1  The four events and the execution states -/

def bOp : op_t := (1, 0, .Ins 10 [] 0)
def aOp : op_t := (2, 0, .Ins 20 [] 1)
def dOp : op_t := (3, 0, .Del [] 1)
def oOp : op_t := (4, 0, .Del [] 2)

def st1 : concrete_st := do_ init_st bOp
def st2 : concrete_st := do_ st1 aOp
def st3 : concrete_st := do_ st2 dOp
def st4 : concrete_st := do_ st3 oOp

def evGate : Set op_t := {bOp, aOp, dOp, oOp}

theorem mem_b : bOp ∈ evGate := Or.inl rfl
theorem mem_a : aOp ∈ evGate := Or.inr (Or.inl rfl)
theorem mem_d : dOp ∈ evGate := Or.inr (Or.inr (Or.inl rfl))
theorem mem_o : oOp ∈ evGate := Or.inr (Or.inr (Or.inr rfl))

/-- Program order on the four events: membership plus strictly increasing
timestamp.  Transitive by construction — the refutation does NOT exploit a
non-transitive `vis`. -/
def visGate (x y : op_t) : Prop := x ∈ evGate ∧ y ∈ evGate ∧ x.1 < y.1

theorem visGate_trans {x y z : op_t} (h1 : visGate x y) (h2 : visGate y z) :
    visGate x z := ⟨h1.1, h2.2.1, lt_trans h1.2.2 h2.2.2⟩

theorem visGate_irrefl (x : op_t) : ¬ visGate x x :=
  fun h => lt_irrefl _ h.2.2

/-- `evGate` is trivially backward-closed under `visGate`. -/
theorem evGate_backClosed : ∀ y ∈ evGate, ∀ z, visGate z y → z ∈ evGate :=
  fun _ _ _z hz => hz.1

theorem ids_nonzero : ∀ x ∈ evGate, x.1 ≠ 0 := by
  intro x hx
  have hx' : x = bOp ∨ x = aOp ∨ x = dOp ∨ x = oOp := hx
  rcases hx' with rfl | rfl | rfl | rfl <;> decide

/-! ## §2  Generation honesty: each op is applicable at its generation state.

This certifies the four events as a genuine single-replica history
`init —b→ st1 —a→ st2 —d→ st3 —o→ st4` (GenDisc-conformant), so the
counterexample lives inside a real execution, not an adversarial `Cfg`. -/

theorem gen_b : RGACondSig.applicable bOp init_st :=
  ⟨Or.inl ⟨rfl, rfl⟩, by decide, by decide⟩

theorem gen_a : RGACondSig.applicable aOp st1 :=
  ⟨Or.inr ⟨by decide, show anc st1 1 = 0 by decide⟩, by decide, by decide⟩

theorem gen_d : RGACondSig.applicable dOp st2 :=
  ⟨Or.inr ⟨by decide, show anc st2 1 = 0 by decide⟩, trivial⟩

theorem gen_o : RGACondSig.applicable oOp st3 :=
  ⟨Or.inr ⟨by decide, show anc st3 2 = 0 by decide⟩, trivial⟩

/-! ## §3  The two positive dependency edges

`dep(a,b)`: at `init_st`, `a` (Ins anchored at node 1) is inapplicable (its
anchor is absent) but applicable after `b` creates node 1.
`dep(o,a)`: at `init_st`, `o` (Del of node 2) is inapplicable (target absent)
but applicable after `a` creates node 2 (whose anchor resolves to root there). -/

theorem dep_a_b : appliesDependsOn RGACondSig aOp bOp := by
  refine ⟨init_st, fun h => ?_⟩
  have hyes : RGACondSig.applicable aOp (do_ init_st bOp) :=
    ⟨Or.inr ⟨by decide, show anc (do_ init_st bOp) 1 = 0 by decide⟩,
     by decide, by decide⟩
  have hno : ¬ RGACondSig.applicable aOp init_st := by
    intro hApp
    rcases hApp.1 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
  rw [h] at hno
  exact hno hyes

theorem dep_o_a : appliesDependsOn RGACondSig oOp aOp := by
  refine ⟨init_st, fun h => ?_⟩
  have hyes : RGACondSig.applicable oOp (do_ init_st aOp) :=
    ⟨Or.inr ⟨by decide, show anc (do_ init_st aOp) 2 = 0 by decide⟩, trivial⟩
  have hno : ¬ RGACondSig.applicable oOp init_st := by
    intro hApp
    rcases hApp.1 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
  rw [h] at hno
  exact hno hyes

/-! ## §4  The severed composite: `¬ dep(o,b)` and `commutesOn b o`

`b` writes only key 1 (`upd s 1 _`); `o`'s applicability reads only key 2
(`contains s 2`, `anc s 2`) — after `d`'s rehoming, `o`'s accurate path `[]`
no longer names node 1.  So `b` can never change `o`'s applicability, at ANY
state.  And the pair commutes at every state, killing the `loOnC` disjunct. -/

/-- `b` leaves `o`'s applicability literally invariant on every state. -/
theorem app_o_do_b (s : concrete_st) :
    RGACondSig.applicable oOp (do_ s bOp) = RGACondSig.applicable oOp s := by
  have hc : contains (do_ s bOp) 2 = contains s 2 := by simp [bOp]
  have ha : anc (do_ s bOp) 2 = anc s 2 := by simp [bOp]
  show (accurate oOp (do_ s bOp) ∧ fresh_ts oOp (do_ s bOp))
     = (accurate oOp s ∧ fresh_ts oOp s)
  simp only [accurate, fresh_ts, oOp, opLeaf, opPath, IsAncPath, hc, ha]

theorem not_dep_o_b : ¬ appliesDependsOn RGACondSig oOp bOp := by
  rintro ⟨s, hne⟩
  exact hne (app_o_do_b s).symm

/-- `b` and `o` commute at EVERY state (not merely vacuously): they touch
disjoint keys, and both `resolve` calls are root-bound. -/
theorem comm_b_o (s : concrete_st) :
    do_ (do_ s bOp) oOp = do_ (do_ s oOp) bOp := by
  simp only [bOp, oOp, do_, resolve, ite_self, upd, del, iter_upd, domain]
  congr 1
  · funext x
    by_cases hx : x = 1 <;> simp [hx]
  · funext k
    by_cases hk1 : k = 1 <;> by_cases hk2 : k = 2 <;> simp [hk1, hk2]

theorem commutesOn_b_o : RGACondSig.commutesOn bOp oOp :=
  fun s _ _ _ => comm_b_o s

/-- The `loOnC` disjunct is dead for `(b, o)` in ANY configuration and event
set: the vis-flavor dies on `commutesOn_b_o`, the rc-flavor on `rc ≡ Either`. -/
theorem not_loOnC_b_o (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev : Set op_t) : ¬ loOnC RGACondSig C ev bOp oOp := by
  rintro (⟨-, hnc⟩ | ⟨-, -, hrc, -⟩)
  · exact hnc commutesOn_b_o
  · rw [rc_is_Either] at hrc
    exact RcRes.noConfusion hrc

/-! ## §5  The concrete configuration

The reachable shape a single replica produces via
`createReplica 0; apply b; apply a; apply d; apply o` — same construction
pattern as `G2_Transport_Probe.Ccex`, with `vis` the (transitive, irreflexive,
same-replica-total) program order. -/

private theorem optL_inv {α : Type} {x y : α} {r : ℕ}
    (h : (if r = 0 then some x else none) = some y) : x = y := by
  by_cases hr : r = 0
  · rw [if_pos hr] at h
    exact Option.some.inj h
  · rw [if_neg hr] at h
    exact absurd h (by simp)

noncomputable def Cgate : Sal.Emulation.Configuration RGACondSig.toCRDTSig where
  N := fun r => if r = 0 then some st4 else none
  L := fun r => if r = 0 then some evGate else none
  vis := visGate
  dom_eq := by
    intro r
    by_cases h : r = 0 <;> simp [h]
  vis_src := fun {x y} hv => ⟨0, evGate, rfl, hv.1⟩
  vis_tgt := fun {x y} hv => ⟨0, evGate, rfl, hv.2.1⟩
  vis_causal := by
    intro x y r s hv hL _hy
    obtain rfl := optL_inv hL
    exact hv.1
  timestamps_distinct := by
    intro x y r s r' s' hL hx hL' hy hne
    obtain rfl := optL_inv hL
    obtain rfl := optL_inv hL'
    have hx' : x = bOp ∨ x = aOp ∨ x = dOp ∨ x = oOp := hx
    have hy' : y = bOp ∨ y = aOp ∨ y = dOp ∨ y = oOp := hy
    rcases hx' with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | decide
  vis_total_same_replica := by
    intro x y r s r' s' hL hx hL' hy hne _hrep
    obtain rfl := optL_inv hL
    obtain rfl := optL_inv hL'
    have hx' : x = bOp ∨ x = aOp ∨ x = dOp ∨ x = oOp := hx
    have hy' : y = bOp ∨ y = aOp ∨ y = dOp ∨ y = oOp := hy
    rcases hx' with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact Or.inl ⟨hx, hy, by decide⟩
        | exact Or.inr ⟨hy, hx, by decide⟩

/-- `Cgate.vis` is the program order — definitionally. -/
theorem Cgate_vis : Cgate.vis = visGate := rfl

/-! ## §6  The refutation: `loOnA b a`, `loOnA a o`, `¬ loOnA b o`

Both positive edges are the DEP disjunct (`vis ∧ appliesDependsOn`) — the
`loOnC` disjunct never fires for the RGA — so the crux composition case
DEP∘DEP is the one that fails. -/

theorem loOnA_b_a : loOnA RGACondSig Cgate evGate bOp aOp :=
  Or.inr ⟨⟨mem_b, mem_a, by decide⟩, dep_a_b⟩

theorem loOnA_a_o : loOnA RGACondSig Cgate evGate aOp oOp :=
  Or.inr ⟨⟨mem_a, mem_o, by decide⟩, dep_o_a⟩

/-- The composite edge is severed — even though `vis b o` HOLDS (program
order is transitive; the refutation does not hide behind a missing vis edge). -/
theorem vis_b_o : Cgate.vis bOp oOp := ⟨mem_b, mem_o, by decide⟩

theorem not_loOnA_b_o : ¬ loOnA RGACondSig Cgate evGate bOp oOp := by
  rintro (hC | ⟨-, hdep⟩)
  · exact not_loOnC_b_o Cgate evGate hC
  · exact not_dep_o_b hdep

/-- **THE GATE VERDICT: `DepComp` is FALSE for the RGA's concrete `loOnA`.**

`DepComp Cgate evGate` (the exact residual of `RGA_SimulInduction.lean` §2)
fails on the triple `(b, a, o)` inside a genuine, GenDisc-conformant,
single-replica, backward-closed, transitive-`vis` execution.  The deps-first
reorder step of the simultaneous induction is therefore not available as
stated: `loOnA`-reachability (deps of deps) is strictly wider than `loOnA`. -/
theorem depComp_rga_refuted :
    ¬ Sal.ConditionedMRDTs.RGASimulInduction.DepComp Cgate evGate := fun h =>
  not_loOnA_b_o (h bOp aOp oOp mem_b mem_a mem_o loOnA_b_a loOnA_a_o)

/-! ## §7  Axiom audit -/

#print axioms depComp_rga_refuted

end Sal.ConditionedMRDTs.RGADepCompGate
