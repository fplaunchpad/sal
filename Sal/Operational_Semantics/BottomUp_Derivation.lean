import Sal.Operational_Semantics.Defeater_Store_Execution

/-!
# The published merge-case induction, as an operational semantics

`Store_TS.lean` encodes the paper's *store* (Fig. `sem`): how a configuration
evolves. This file encodes the paper's *proof*: how a merge-linearization
obligation evolves under the induction of Theorem 1's appendix proof
(arXiv:2502.19967 `appendix.tex:221-375`, and verbatim again for Theorem 2 at
`:380-531`).

The statement whose proof is encoded:

> **Theorem 1.** If an MRDT `D` satisfies `BottomUp-2-OP`, `BottomUp-1-OP`,
> `BottomUp-0-OP`, `MergeIdempotence` and `MergeCommutativity`, then `D` is
> linearizable.

Its proof runs an induction on `|τ|` with four cases — `CreateBranch`, `Apply`,
`Merge`, `Query`. Three are one-liners. The `Merge` case is the whole content,
and it is itself a nest of three inductions. Read as a rewriting system, each
step takes a merge obligation to a strictly smaller one, committing one event to
the tail of the witness; a derivation succeeds when it bottoms out at
`MergeIdempotence`.

## The appendix's case tree, and what each case becomes here

| appendix (`appendix.tex`) | guard | law used | here |
|---|---|---|---|
| **Base Case 1** `:296` | `\|L₁ᵃ∪L₂ᵃ\|=0`, `\|L_⊤ᵃ\|=0` | `MergeIdempotence` | `Discharged` |
| **Inductive Case 1** `:300` | `\|L₁ᵃ∪L₂ᵃ\|=0`, `\|L_⊤ᵃ\|>0` | `BottomUp-0-OP` (eq:0op) | `Derive.zeroOP` |
| **Base Case 1.1** `:313` | `\|M₁ᵃ∪M₂ᵃ\|=0` | — (IH) | `Discharged` |
| **Case 1.1.1** `:322` | one `Mᵢᵃ` empty | `BottomUp-1-OP` (eq:1op9) | `Derive.oneOP{L,R}` |
| **Case 1.1.2** `:342` | both `Mᵢᵃ` nonempty | `BottomUp-2-OP` (eq:2op9) | `Derive.twoOP{L,R}` |
| **Case 2** `:367` | `\|L₁ᵃ∪L₂ᵃ\|>0` | "identical to Inductive Case 1.1, substituting `L₁ᵃ` and `L₂ᵃ` for `M₁ᵃ` and `M₂ᵃ`" | same two constructors |

Because Case 2 *is* Case 1.1 under a renaming, the `Goal` carries one pair of
pending local sets, `P1`/`P2`: they are `L₁ᵃ`/`L₂ᵃ` in Case 2 and
`M₁ᵃ = L₁ᵇ(e_m^⊤)` / `M₂ᵃ = L₂ᵇ(e_m^⊤)` inside Inductive Case 1. One pair of
rules serves both, exactly as the appendix says.

`MergeCommutativity` is *not* a step. The paper introduces it "in order to avoid
mirrored versions of `BottomUp-2-OP` and `BottomUp-1-OP` where the second and
third arguments are swapped" (`lemmas.tex:135`) — that is, to make each peel
available in both orientations. Encoding it as a rewrite would add a step that
makes no progress and could fire forever; encoding it as the paper *uses* it
gives the `L`/`R` constructor pairs below. An exhaustive check must cover both,
and the stuck theorem does.

## Where the invalid inference sits

Every peel rule is a *pattern*: to apply it to a concrete merge one must exhibit
the side as a `do`-image with the peeled event outermost. The appendix derives
that factorization from `lo_m`-maximality, in one sentence repeated verbatim in
both proofs (`:343`, `:515`):

> "Since `lo` ordering between events remains the same in all versions, and
> since versions `v₁` and `v₂` (which are being merged) were already
> linearizable, there would exist sequences leading to the states `a''` and
> `b''` such that `e₁` and `e₂` would appear at the end resp. Hence, there
> exists `a'''` and `b'''` such that `a'' = e₁(a''')` and `b'' = e₁(b''')`."

(The second is a typo for `e₂(b''')`.) Here maximality and factorization are
kept as *separate premises*, which is what the rules actually require. The
defeater satisfies the first and refutes the second, so the encoding lets the
two come apart and shows which one fails.

## The result

`defeater_stuck`: the defeater's obligation is neither `Discharged` nor able to
take a single `Derive` step, in either orientation of either peel. The
derivation the published proof must run cannot begin.

`no_rem_peel_any` states the robust core separately, with the schedule guards
dropped: no orientation of any peel can remove a `rem` from either head,
whatever case the schedule claims to be in.

## Scope

Stuckness here is relative to the appendix's own rule set and schedule. The
off-schedule readings (peeling an `add`, which *does* factor but is not
`lo_m`-maximal and folds wrong) and the peel-shaped repairs are exhausted in
`Sal/ConditionedMRDTs/defeater-walkthrough.pdf` §4-§5, anchored to
`reunification_peel_obstruction`, `no_proper_back_block` and
`killTest_no_common_U`.
-/

namespace Sal.Operational_Semantics.BottomUp

open Sal.Emulation
open Sal.ConditionedMRDTs
open Sal.ConditionedMRDTs.Store
open Sal.ConditionedMRDTs.Store.Defeater
open Classical

/-! ## §1. The obligation

The state of the appendix's merge-case derivation: the three merge arguments,
the events still to be linearized, the linearization order they must respect,
and the witness suffix built so far. -/

/-- A merge-linearization obligation — the appendix's proof state.

`π` is built **back to front**: the appendix's peels each commit one event to
the *last* free slot of the witness (`π = π'.e₁`), so a step conses onto `π`. -/
structure Goal (D : MRDTSig) where
  /-- The LCA state, `merge`'s first argument. -/
  l : D.State
  /-- The a-side state, `merge`'s second argument. -/
  a : D.State
  /-- The b-side state, `merge`'s third argument. -/
  b : D.State
  /-- Pending local events on the a-side: `L₁ᵃ` in Case 2, `M₁ᵃ = L₁ᵇ(e_m^⊤)`
  inside Inductive Case 1. -/
  P1 : Set (Op D.AppOp)
  /-- Pending local events on the b-side: `L₂ᵃ`, resp. `M₂ᵃ`. -/
  P2 : Set (Op D.AppOp)
  /-- `L_⊤ᵃ`: LCA events with a local `lo_m`-predecessor, still to be placed. -/
  Ltop_a : Set (Op D.AppOp)
  /-- `lo_m`: the linearization relation restricted to the merged version's
  event set. Peels may only commit `lo_m`-maximal events. -/
  lo : Op D.AppOp → Op D.AppOp → Prop
  /-- The witness suffix committed so far. -/
  π : List (Op D.AppOp)

variable {D : MRDTSig}

/-- `e` is `lo_m`-maximal in `S`: nothing left in `S` must come after it. This
is the appendix's "there does not exist `e ∈ Mᵢᵃ` and `eᵢ →lo_m e`". -/
def Maximal (g : Goal D) (S : Set (Op D.AppOp)) (e : Op D.AppOp) : Prop :=
  ∀ e' ∈ S, e' ≠ e → ¬ g.lo e e'

/-- **Base Case 1** (`appendix.tex:296`) and **Base Case 1.1** (`:313`): the
obligation is closed. Nothing local is pending, no LCA event is left to place,
so all three arguments coincide and `MergeIdempotence` gives
`merge(l,l,l) = l`, already linearized by the induction hypothesis. -/
def Discharged (g : Goal D) : Prop :=
  g.P1 = ∅ ∧ g.P2 = ∅ ∧ g.Ltop_a = ∅ ∧ g.l = g.a ∧ g.a = g.b

/-! ## §2. The steps

One constructor per peeling case of the appendix, each carrying that case's
guard, its `lo_m`-maximality condition, its factorization requirement, and (for
`2-OP`) its `rc` side condition. The conclusion names the smaller obligation the
appendix recurses on. -/

/-- **The merge case's induction, as a step relation.**

Each constructor is one case of `appendix.tex:250-375`. A step commits exactly
one event to `π` and strictly shrinks the pending events, so a derivation either
reaches `Discharged` or gets stuck; there is no way to loop. -/
inductive Derive (D : MRDTSig) : Goal D → Goal D → Prop where
  /-- **Inductive Case 1** (`appendix.tex:300`), by `BottomUp-0-OP`:

  `merge(e⊤(l'), e⊤(a''), e⊤(b'')) = e⊤(merge(l', a'', b''))`  (eq:0op)

  Reached only in Case 1 — with `S₃ = L₁ᵃ ∪ L₂ᵃ` exhausted — and requires the
  shared LCA event outermost on **all three** arguments. -/
  | zeroOP {g : Goal D} (etop : Op D.AppOp) (l' a' b' : D.State)
      (hP1 : g.P1 = ∅) (hP2 : g.P2 = ∅)
      (hmem : etop ∈ g.Ltop_a)
      (hfl : g.l = D.update l' etop)
      (hfa : g.a = D.update a' etop)
      (hfb : g.b = D.update b' etop)
      (hmax : Maximal g g.Ltop_a etop) :
      Derive D g
        { l := l', a := a', b := b', P1 := ∅, P2 := ∅,
          Ltop_a := g.Ltop_a \ {etop}, lo := g.lo, π := etop :: g.π }
  /-- **Case 1.1.1 / Case 2 with the b-side exhausted** (`appendix.tex:322`),
  by `BottomUp-1-OP`:

  `merge(e⊤(l''), e₁(a'''), e⊤(b''')) = e₁(merge(e⊤(l''), a''', e⊤(b''')))`  (eq:1op9)

  The a-side must factor by the peeled local event; `l` and `b` must share a
  trailing LCA event, or else be equal (the rule's `e⊤ = ε ∧ l = b` clause). -/
  | oneOPL {g : Goal D} (e₁ : Op D.AppOp) (a''' : D.State)
      (hne : g.P1.Nonempty) (hP2 : g.P2 = ∅)
      (hmem : e₁ ∈ g.P1)
      (hmax : Maximal g g.P1 e₁)
      (hfa : g.a = D.update a''' e₁)
      (hshared : (∃ (etop : Op D.AppOp) (l'' b''' : D.State),
                    g.l = D.update l'' etop ∧ g.b = D.update b''' etop ∧
                    e₁ ≠ etop) ∨ g.l = g.b) :
      Derive D g
        { l := g.l, a := a''', b := g.b, P1 := g.P1 \ {e₁}, P2 := ∅,
          Ltop_a := g.Ltop_a, lo := g.lo, π := e₁ :: g.π }
  /-- `BottomUp-1-OP` in the mirrored orientation, available via
  `MergeCommutativity` (`lemmas.tex:135`): the a-side is exhausted and the peel
  comes off the b-side. -/
  | oneOPR {g : Goal D} (e₂ : Op D.AppOp) (b''' : D.State)
      (hne : g.P2.Nonempty) (hP1 : g.P1 = ∅)
      (hmem : e₂ ∈ g.P2)
      (hmax : Maximal g g.P2 e₂)
      (hfb : g.b = D.update b''' e₂)
      (hshared : (∃ (etop : Op D.AppOp) (l'' a''' : D.State),
                    g.l = D.update l'' etop ∧ g.a = D.update a''' etop ∧
                    e₂ ≠ etop) ∨ g.l = g.a) :
      Derive D g
        { l := g.l, a := g.a, b := b''', P1 := ∅, P2 := g.P2 \ {e₂},
          Ltop_a := g.Ltop_a, lo := g.lo, π := e₂ :: g.π }
  /-- **Case 1.1.2 / Case 2 with both sides pending** (`appendix.tex:342`), by
  `BottomUp-2-OP`:

  `merge(l', e₁(a'''), e₂(b''')) = e₁(merge(l', a''', e₂(b''')))`  (eq:2op9)

  This is the appendix's own first move on the defeater: both `L₁ᵃ` and `L₂ᵃ`
  are nonempty, so the schedule (`lemmas.tex` Table 1) prescribes `2-OP`. Both
  sides must factor by their maximal pending event, and the peeled `e₁` must be
  the `rc`-winner or commute with `e₂`. -/
  | twoOPL {g : Goal D} (e₁ e₂ : Op D.AppOp) (a''' b''' : D.State)
      (hne1 : g.P1.Nonempty) (hne2 : g.P2.Nonempty)
      (hm1 : e₁ ∈ g.P1) (hm2 : e₂ ∈ g.P2)
      (hne : e₁ ≠ e₂)
      (hmax1 : Maximal g g.P1 e₁) (hmax2 : Maximal g g.P2 e₂)
      (hrc : D.rc e₂ e₁ = RcRes.Fst_then_snd ∨ D.commutes e₁ e₂)
      (hfa : g.a = D.update a''' e₁)
      (hfb : g.b = D.update b''' e₂) :
      Derive D g
        { l := g.l, a := a''', b := g.b, P1 := g.P1 \ {e₁}, P2 := g.P2,
          Ltop_a := g.Ltop_a, lo := g.lo, π := e₁ :: g.π }
  /-- `BottomUp-2-OP` in the mirrored orientation, via `MergeCommutativity`:
  the peel comes off the b-side instead. -/
  | twoOPR {g : Goal D} (e₁ e₂ : Op D.AppOp) (a''' b''' : D.State)
      (hne1 : g.P1.Nonempty) (hne2 : g.P2.Nonempty)
      (hm1 : e₁ ∈ g.P1) (hm2 : e₂ ∈ g.P2)
      (hne : e₁ ≠ e₂)
      (hmax1 : Maximal g g.P1 e₁) (hmax2 : Maximal g g.P2 e₂)
      (hrc : D.rc e₁ e₂ = RcRes.Fst_then_snd ∨ D.commutes e₁ e₂)
      (hfa : g.a = D.update a''' e₁)
      (hfb : g.b = D.update b''' e₂) :
      Derive D g
        { l := g.l, a := g.a, b := b''', P1 := g.P1, P2 := g.P2 \ {e₂},
          Ltop_a := g.Ltop_a, lo := g.lo, π := e₂ :: g.π }

/-- A goal is **stuck** when the derivation can neither close it nor advance it:
the published proof, at such a goal, produces no witness. -/
def Stuck (D : MRDTSig) (g : Goal D) : Prop :=
  ¬ Discharged g ∧ ¬ ∃ g', Derive D g g'

/-! ## §3. The defeater's obligation

At the critical merge of the reachable configuration built in
`Defeater_Store_Execution.lean` (`defeater_obtainable`), the induction holds
witnesses for both heads and owes a witness for the merged version. The
six-set partition of that merge (walkthrough §4.2):

* `L₁' = {R_p}`, `L₂' = {R_q}`;
* neither remove is `lo_m`-before an LCA event, so `L₁ᵇ = L₂ᵇ = ∅` and
  hence `L_⊤ᵃ = ∅`;
* `L₁ᵃ = {R_p}`, `L₂ᵃ = {R_q}`, `L_⊤ᵇ = {A_p, A_q}`.

Both `L₁ᵃ` and `L₂ᵃ` are nonempty, so this is the appendix's **Case 2**, which
delegates to Case 1.1.2 and `BottomUp-2-OP`. -/

/-- `lo_m` on the defeater's four events. On the union `U` both `rc` edges are
absorbed — `A_q vis R_q` with `¬(A_q ⇄ R_q)` kills `R_p → A_q`, and `R_p`
symmetrically kills `R_q → A_p` — so `lo_m` is exactly the two visibility
edges, and its maximal events are `R_p` and `R_q`. -/
inductive defeaterLo : Op AWOp → Op AWOp → Prop where
  /-- `A_p vis R_p`, a non-commuting pair. -/
  | ap_rp : defeaterLo A_p R_p
  /-- `A_q vis R_q`, a non-commuting pair. -/
  | aq_rq : defeaterLo A_q R_q

/-- The obligation the published proof owes at the defeater's critical merge. -/
noncomputable def defeaterGoal : Goal AWSetT where
  l := Sal.Emulation.LCA
  a := head_p
  b := head_q
  P1 := {R_p}
  P2 := {R_q}
  Ltop_a := ∅
  lo := defeaterLo
  π := []

/-! ### The order side is satisfied

Worth recording before the stuck theorem, because it locates the failure: the
guard fires, the maximality conditions hold, and the `rc` side condition holds.
Nothing about the *order* blocks `BottomUp-2-OP` here. -/

theorem defeater_P1_nonempty : defeaterGoal.P1.Nonempty := ⟨R_p, rfl⟩
theorem defeater_P2_nonempty : defeaterGoal.P2.Nonempty := ⟨R_q, rfl⟩

/-- `R_p` is `lo_m`-maximal in `L₁ᵃ` — trivially, it is the only element. -/
theorem defeater_max_P1 : Maximal defeaterGoal defeaterGoal.P1 R_p := by
  intro e' he' hne
  exact absurd he' hne

/-- `R_q` is `lo_m`-maximal in `L₂ᵃ`. -/
theorem defeater_max_P2 : Maximal defeaterGoal defeaterGoal.P2 R_q := by
  intro e' he' hne
  exact absurd he' hne

/-- The `2-OP` `rc` side condition holds: the two removes commute. -/
theorem defeater_rc : AWSetT.commutes R_p R_q :=
  AWSet_comm_rem_rem hRp hRq

/-! ## §4. The stuck theorem -/

/-- **The robust core**, with the schedule guards dropped: no orientation of any
peel can take a `rem` off either head, whichever case the schedule claims to be
in. Both heads have a nonempty live set and every `rem`-image is all-dead
(`awset_rem_output_empty`). -/
theorem no_rem_peel_any (s : AWState) (e : Op AWOp) (he : e.2.2 = AWOp.rem) :
    head_p ≠ AWSetT.update s e ∧ head_q ≠ AWSetT.update s e :=
  ⟨no_rem_peelable_from_defeater_heads.1 s e he,
   no_rem_peelable_from_defeater_heads.2 s e he⟩

/-- **The defeater is stuck in the published proof's own semantics.**

At the defeater's critical merge the obligation is not closed, and no step of
the appendix's induction applies — not `BottomUp-0-OP`, not `BottomUp-1-OP` or
`BottomUp-2-OP` in either orientation. So the derivation that must produce the
merged version's witness cannot take its first move.

The failure is located: for `2-OP`, the case the appendix's own schedule
prescribes here, the guard fires and both maximality conditions and the `rc`
side condition hold (`defeater_max_P1`, `defeater_max_P2`, `defeater_rc`). What
fails is the factorization the appendix infers from maximality — `head_p` is not
`do a''' R_p` for any state, because every `rem`-image is all-dead while
`live(head_p) = {2}`. -/
theorem defeater_stuck : Stuck AWSetT defeaterGoal := by
  refine ⟨?_, ?_⟩
  · -- Not `Discharged`: `L₁ᵃ = {R_p}` is nonempty, so Base Case 1 does not apply.
    rintro ⟨hP1, -, -, -, -⟩
    have : R_p ∈ defeaterGoal.P1 := rfl
    rw [hP1] at this
    exact this
  · -- No step applies.
    rintro ⟨g', hstep⟩
    cases hstep with
    | zeroOP etop l' a' b' hP1 hP2 hmem hfl hfa hfb hmax =>
        -- Case 1's guard fails: `L₁ᵃ ≠ ∅`.
        have : R_p ∈ defeaterGoal.P1 := rfl
        rw [hP1] at this
        exact this
    | oneOPL e₁ a''' hne hP2 hmem hmax hfa hshared =>
        -- Case 1.1.1's guard fails: `L₂ᵃ ≠ ∅`.
        have : R_q ∈ defeaterGoal.P2 := rfl
        rw [hP2] at this
        exact this
    | oneOPR e₂ b''' hne hP1 hmem hmax hfb hshared =>
        -- Mirrored guard fails: `L₁ᵃ ≠ ∅`.
        have : R_p ∈ defeaterGoal.P1 := rfl
        rw [hP1] at this
        exact this
    | twoOPL e₁ e₂ a''' b''' hne1 hne2 hm1 hm2 hne hmax1 hmax2 hrc hfa hfb =>
        -- The guard fires. The peeled `e₁` must be `R_p`, and `head_p` is not
        -- a `rem`-image of any state.
        have he₁ : e₁ = R_p := hm1
        subst he₁
        exact (no_rem_peel_any a''' R_p hRp).1 hfa
    | twoOPR e₁ e₂ a''' b''' hne1 hne2 hm1 hm2 hne hmax1 hmax2 hrc hfa hfb =>
        -- Mirrored: the peeled `e₂` must be `R_q`, and `head_q` is not a
        -- `rem`-image either.
        have he₂ : e₂ = R_q := hm2
        subst he₂
        exact (no_rem_peel_any b''' R_q hRq).2 hfb

/-- The separation, in one statement: the obligation is stuck, yet a witness for
the merged version exists — `w = [A_p, R_p, A_q, R_q]` folds to it
(`crack1_witness`). The published *proof* fails on this execution; the published
*theorem* is not contradicted by it. -/
theorem stuck_but_witnessed :
    Stuck AWSetT defeaterGoal ∧
    applySeq AWSet AWSet.init w = mergedState :=
  ⟨defeater_stuck, crack1_witness.2.1⟩

/-! ## §5. Positive controls: the semantics is not vacuous

`defeater_stuck` would be worthless if `Derive` were uninhabited — then *every*
goal would be stuck and the theorem would say nothing about the defeater. So each
peel is fired here on an obligation that does factor, and `Discharged` is
witnessed too. These are the `¬`-companions the stuck theorem needs to mean
something. -/

/-- A goal where **`BottomUp-2-OP` does fire**: two concurrent adds, each side a
`do`-image of the peeled event. Same shape as the defeater's Case 2 — both
pending sets nonempty — and the only difference is that an `add`-image exists
where a `rem`-image does not. -/
noncomputable def addAddGoal : Goal AWSetT where
  l := AWSet.init
  a := awUpdate AWSet.init A_p
  b := awUpdate AWSet.init A_q
  P1 := {A_p}
  P2 := {A_q}
  Ltop_a := ∅
  lo := fun _ _ => False
  π := []

/-- `BottomUp-2-OP` fires on `addAddGoal`, peeling `A_p` off the a-side.

Every premise the defeater satisfies is satisfied here too — the guard, both
maximality conditions, the `rc` side condition. The single difference is the
factorization: `do init A_p` *is* an `add`-image, where `head_p` is no
`rem`-image. -/
theorem addAdd_steps : ∃ g', Derive AWSetT addAddGoal g' := by
  refine ⟨_, Derive.twoOPL A_p A_q AWSet.init AWSet.init
    ⟨A_p, rfl⟩ ⟨A_q, rfl⟩ rfl rfl ?_ ?_ ?_ ?_ rfl rfl⟩
  · decide
  · intro e' _ _; exact not_false
  · intro e' _ _; exact not_false
  · exact Or.inr (AWSet_comm_add_add hAp hAq)

/-- And the mirrored orientation fires too, peeling `A_q` off the b-side — so
both orientations of `2-OP` are live in this encoding, which is what makes the
defeater's refutation of *both* meaningful. -/
theorem addAdd_steps_mirrored : ∃ g', Derive AWSetT addAddGoal g' := by
  refine ⟨_, Derive.twoOPR A_p A_q AWSet.init AWSet.init
    ⟨A_p, rfl⟩ ⟨A_q, rfl⟩ rfl rfl ?_ ?_ ?_ ?_ rfl rfl⟩
  · decide
  · intro e' _ _; exact not_false
  · intro e' _ _; exact not_false
  · exact Or.inr (AWSet_comm_add_add hAp hAq)

/-- A goal where **`BottomUp-0-OP` does fire**: one shared LCA event outermost
on all three arguments, nothing local pending. -/
noncomputable def sharedGoal : Goal AWSetT where
  l := awUpdate AWSet.init A_p
  a := awUpdate AWSet.init A_p
  b := awUpdate AWSet.init A_p
  P1 := ∅
  P2 := ∅
  Ltop_a := {A_p}
  lo := fun _ _ => False
  π := []

theorem shared_steps : ∃ g', Derive AWSetT sharedGoal g' := by
  refine ⟨_, Derive.zeroOP A_p AWSet.init AWSet.init AWSet.init
    rfl rfl rfl rfl rfl rfl ?_⟩
  intro e' _ _; exact not_false

/-- A goal where **`BottomUp-1-OP` does fire**: the b-side is exhausted, the
a-side factors, and `l = b` supplies the rule's `e⊤ = ε` clause. -/
noncomputable def oneSidedGoal : Goal AWSetT where
  l := AWSet.init
  a := awUpdate AWSet.init A_p
  b := AWSet.init
  P1 := {A_p}
  P2 := ∅
  Ltop_a := ∅
  lo := fun _ _ => False
  π := []

theorem oneSided_steps : ∃ g', Derive AWSetT oneSidedGoal g' := by
  refine ⟨_, Derive.oneOPL A_p AWSet.init ⟨A_p, rfl⟩ rfl rfl ?_ rfl (Or.inr rfl)⟩
  intro e' _ _; exact not_false

/-- `Discharged` is satisfiable: **Base Case 1** really does close goals. -/
theorem discharged_witness :
    Discharged
      ({ l := AWSet.init, a := AWSet.init, b := AWSet.init, P1 := ∅, P2 := ∅,
         Ltop_a := ∅, lo := fun _ _ => False, π := [] } : Goal AWSetT) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The contrast, in one statement.** All three of the appendix's peels fire on
obligations that factor, and `Discharged` closes goals — yet at the defeater's
merge nothing fires and nothing closes. Stuckness is a property of the defeater,
not an artifact of an empty rule set. -/
theorem stuck_is_not_vacuous :
    (∃ g', Derive AWSetT addAddGoal g') ∧
    (∃ g', Derive AWSetT sharedGoal g') ∧
    (∃ g', Derive AWSetT oneSidedGoal g') ∧
    Stuck AWSetT defeaterGoal :=
  ⟨addAdd_steps, shared_steps, oneSided_steps, defeater_stuck⟩

end Sal.Operational_Semantics.BottomUp
