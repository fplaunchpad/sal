import Sal.Operational_Semantics.Store_TS
import Sal.ConditionedMRDTs.Refutations.InterLca2op_Defeater_Arbiter

/-!
# The defeater as an execution of the store semantics

`Sal/Operational_Semantics/Store_TS.lean` encodes the paper's Fig. `sem`
(arXiv:2502.19967 `lin.tex` §3.1) as an inductive step relation. This file
states and proves **one lemma** in that setting:

> `defeater_obtainable` — the defeater is obtainable by a sequence of store
> operations. Some configuration reachable from `C₀` carries the LCA `v_s`, the
> two heads `head_p` and `head_q`, and the all-dead merged version.

Everything else here is machinery for that statement's premises: the
configurations, their lookups, the version graph and its ancestor table, the
four `LCA` side conditions, and timestamp freshness.

## Why the lemma is worth proving

`InterLca2op_Defeater_Arbiter.lean` proves the *algebraic* obstruction: neither
head is in the image of `rem`, so no bottom-up rule can peel a remove. But that
file works with bare states — it takes on faith that the three states
`(LCA, head_p, head_q)` arise together at one legal merge of a real store
execution. That is exactly what the published proof's merge case gets to assume,
and exactly what a reader should not have to take on faith: if no execution put
those three states into the LCA/left/right slots simultaneously, the obstruction
would be vacuous. This lemma closes that gap.

The execution is drawn in
`Sal/Operational_Semantics/Defeater_Store_Viz.lean`.

## The execution, ten transitions

Replicas `p = 0`, `q = 1`, `s = 2` (the staging replica); versions `0`–`10`.

| # | label | new version | state | `L` |
|---|---|---|---|---|
| 1 | `createBranch q p` | `1` | `σ₀` | `∅` |
| 2 | `apply 1 p add` | `2` = `p₁` | `({1},∅)` | `{A_p}` |
| 3 | `apply 2 q add` | `3` = `q₁` | `({2},∅)` | `{A_q}` |
| 4 | `createBranch s p` | `4` | `({1},∅)` | `{A_p}` |
| 5 | `merge s q` | `5` = `v_s` | `({1,2},∅)` | `{A_p,A_q}` |
| 6 | `apply 3 p rem` | `6` = `p₂` | `({1},{1})` | `{A_p,R_p}` |
| 7 | `apply 4 q rem` | `7` = `q₂` | `({2},{2})` | `{A_q,R_q}` |
| 8 | `merge p s` | `8` = `head_p` | `({1,2},{1})` | `{A_p,R_p,A_q}` |
| 9 | `merge q s` | `9` = `head_q` | `({1,2},{2})` | `{A_q,R_q,A_p}` |
| 10 | `merge p q` | `10` | `({1,2},{1,2})` | all four |

Steps 6 and 7 are the crux of the shape: `p` and `q` remove from *their own*
heads (versions `2` and `3`), never having seen `v_s`. That is what leaves each
head alive on the tag it did not add.

The version graph's 14 edges, all pointing from lower to higher id:
`0→1, 0→2, 1→3, 2→4, 4→5, 3→5, 2→6, 3→7, 6→8, 5→8, 7→9, 5→9, 8→10, 9→10`.

## Method notes

*States are shared, not duplicated.* The states threaded through the trace are
the same terms as `InterLca2op_Defeater_Arbiter.lean`'s (`LCA`, `sp`, `sq`,
`head_p`, `head_q`, `mergedState`), so every lookup — `C₁₀.N 10 = some
mergedState` and friends — holds by `rfl`. The store execution and the
state-level refutation are talking about one object, not two that happen to
agree.

*Ancestry is decided by a table.* `ancOf` lists each version's ancestors and
`anc_sound` proves it sound against the final graph (one case per edge). Since
the edge relation only grows along an execution, a *negative* ancestry fact in
the final graph transports back to every earlier configuration
(`Config.Anc.mono`), which is what makes the four LCA maximality clauses cheap:
each candidate common ancestor is either given an explicit chain or refuted by
`decide` on the table.
-/

namespace Sal.ConditionedMRDTs.Store.Defeater

open Sal.Emulation
open Sal.ConditionedMRDTs
open Sal.ConditionedMRDTs.Store
open Classical

/-! ## §1. The ternary lift of the AWSet skeleton

The LCA-blind ternary lift: `mergeL l a b := awMerge a b`, dropping the LCA
slot exactly as the add-wins set does. Same pattern as `AWSetF3` in
`CD_Not_Derivable_Ternary.lean`. -/

/-- `AWSet` as an `MRDTSig`: the ternary merge ignores its LCA argument. -/
noncomputable def AWSetT : MRDTSig where
  toCRDTSig := AWSet
  mergeL := fun _l a b => awMerge a b
  merge_init_slice := fun _ _ => rfl

@[simp] theorem AWSetT_mergeL (l a b : AWState) :
    AWSetT.mergeL l a b = awMerge a b := rfl
@[simp] theorem AWSetT_update (s : AWState) (e : Op AWOp) :
    AWSetT.update s e = awUpdate s e := rfl

/-! ## §2. Event sets, in the exact accumulated shape the rules build -/

/-- `L` of versions 2 and 4: `{A_p}`. -/
def evAp : Set (Op AWOp) := (∅ : Set (Op AWOp)) ∪ {A_p}
/-- `L` of version 3: `{A_q}`. -/
def evAq : Set (Op AWOp) := (∅ : Set (Op AWOp)) ∪ {A_q}
/-- `L` of version 5 (`v_s`): `{A_p, A_q}`. -/
def evS : Set (Op AWOp) := evAp ∪ evAq
/-- `L` of version 6 (`p₂`): `{A_p, R_p}`. -/
def evP2 : Set (Op AWOp) := evAp ∪ {R_p}
/-- `L` of version 7 (`q₂`): `{A_q, R_q}`. -/
def evQ2 : Set (Op AWOp) := evAq ∪ {R_q}
/-- `L` of version 8 (`head_p`): `{A_p, R_p, A_q}` — the arbiter file's `E₁`. -/
def evH1 : Set (Op AWOp) := evP2 ∪ evS
/-- `L` of version 9 (`head_q`): `{A_q, R_q, A_p}` — the arbiter file's `E₂`. -/
def evH2 : Set (Op AWOp) := evQ2 ∪ evS

/-! ## §3. The two one-tag states, reusing the arbiter's own terms -/

/-- Version 2's state, `p₁ = ({1},∅)`. Definitionally the arbiter's `vp`. -/
noncomputable def st2 : AWState := awUpdate AWSet.init A_p
/-- Version 3's state, `q₁ = ({2},∅)`. Definitionally the arbiter's `vq`. -/
noncomputable def st3 : AWState := awUpdate AWSet.init A_q

/-! ## §4. The eleven configurations -/

/-- `C₀`: one replica `p = 0` at version `0`, state `σ₀`, nothing seen. -/
noncomputable def C0 : Config AWSetT := Store.initConfig AWSetT 0 0
/-- After `createBranch q p`. -/
noncomputable def C1 : Config AWSetT := stepCB C0 1 1 0 AWSetT.init ∅
/-- After `apply 1 p add` (`A_p`). -/
noncomputable def C2 : Config AWSetT := stepApply C1 1 0 AWOp.add 2 0 AWSetT.init ∅
/-- After `apply 2 q add` (`A_q`). -/
noncomputable def C3 : Config AWSetT := stepApply C2 2 1 AWOp.add 3 1 AWSetT.init ∅
/-- After `createBranch s p`: the staging replica forks *after* `A_p`. -/
noncomputable def C4 : Config AWSetT := stepCB C3 2 4 2 st2 evAp
/-- After `merge s q`: version `5` is `v_s`, the honest LCA-to-be. -/
noncomputable def C5 : Config AWSetT := stepMerge C4 2 5 4 3 AWSetT.init st2 st3 evAp evAq
/-- After `apply 3 p rem` (`R_p`), from `p`'s own head `2` — `v_s` unseen. -/
noncomputable def C6 : Config AWSetT := stepApply C5 3 0 AWOp.rem 6 2 st2 evAp
/-- After `apply 4 q rem` (`R_q`), from `q`'s own head `3`. -/
noncomputable def C7 : Config AWSetT := stepApply C6 4 1 AWOp.rem 7 3 st3 evAq
/-- After `merge p s`: version `8` is `head_p`, over LCA `2`. -/
noncomputable def C8 : Config AWSetT :=
  stepMerge C7 0 8 6 5 st2 sp Sal.Emulation.LCA evP2 evS
/-- After `merge q s`: version `9` is `head_q`, over LCA `3`. -/
noncomputable def C9 : Config AWSetT :=
  stepMerge C8 1 9 7 5 st3 Sal.Emulation.sq Sal.Emulation.LCA evQ2 evS
/-- After the **critical merge** `merge p q`: version `10`, over LCA `5 = v_s`. -/
noncomputable def C10 : Config AWSetT :=
  stepMerge C9 0 10 8 9 Sal.Emulation.LCA head_p head_q evH1 evH2

/-- The label sequence of the defeater. -/
noncomputable def defeaterTrace : List (Label AWSetT) :=
  [ .createBranch 1 0,
    .apply 1 0 AWOp.add,
    .apply 2 1 AWOp.add,
    .createBranch 2 0,
    .merge 2 1,
    .apply 3 0 AWOp.rem,
    .apply 4 1 AWOp.rem,
    .merge 0 2,
    .merge 1 2,
    .merge 0 1 ]

/-! ## §5. Lookups

Every one holds by `rfl`: the trace threads the arbiter file's own terms, so
`N`/`H`/`L` reduce to them definitionally. -/

theorem H1_p : C1.H 0 = some 0 := rfl
theorem N1_0 : C1.N 0 = some AWSetT.init := rfl
theorem L1_0 : C1.L 0 = some (∅ : Set (Op AWOp)) := rfl
theorem N1_2 : C1.N 2 = none := rfl

theorem H2_q : C2.H 1 = some 1 := rfl
theorem N2_1 : C2.N 1 = some AWSetT.init := rfl
theorem L2_1 : C2.L 1 = some (∅ : Set (Op AWOp)) := rfl
theorem N2_3 : C2.N 3 = none := rfl

theorem H3_p : C3.H 0 = some 2 := rfl
theorem H3_s : C3.H 2 = none := rfl
theorem N3_2 : C3.N 2 = some st2 := rfl
theorem L3_2 : C3.L 2 = some evAp := rfl
theorem N3_4 : C3.N 4 = none := rfl

theorem H4_s : C4.H 2 = some 4 := rfl
theorem H4_q : C4.H 1 = some 3 := rfl
theorem N4_0 : C4.N 0 = some AWSetT.init := rfl
theorem N4_4 : C4.N 4 = some st2 := rfl
theorem N4_3 : C4.N 3 = some st3 := rfl
theorem L4_4 : C4.L 4 = some evAp := rfl
theorem L4_3 : C4.L 3 = some evAq := rfl
theorem N4_5 : C4.N 5 = none := rfl

theorem H5_p : C5.H 0 = some 2 := rfl
theorem N5_2 : C5.N 2 = some st2 := rfl
theorem L5_2 : C5.L 2 = some evAp := rfl
theorem N5_6 : C5.N 6 = none := rfl

theorem H6_q : C6.H 1 = some 3 := rfl
theorem N6_3 : C6.N 3 = some st3 := rfl
theorem L6_3 : C6.L 3 = some evAq := rfl
theorem N6_7 : C6.N 7 = none := rfl

theorem H7_p : C7.H 0 = some 6 := rfl
theorem H7_s : C7.H 2 = some 5 := rfl
theorem N7_2 : C7.N 2 = some st2 := rfl
/-- Version 6 carries the arbiter's `sp = state[A_p, R_p]`. -/
theorem N7_6 : C7.N 6 = some sp := rfl
/-- Version 5 carries the arbiter's `LCA = merge({A_p},{A_q})`. -/
theorem N7_5 : C7.N 5 = some Sal.Emulation.LCA := rfl
theorem L7_6 : C7.L 6 = some evP2 := rfl
theorem L7_5 : C7.L 5 = some evS := rfl
theorem N7_8 : C7.N 8 = none := rfl

theorem H8_q : C8.H 1 = some 7 := rfl
theorem H8_s : C8.H 2 = some 5 := rfl
theorem N8_3 : C8.N 3 = some st3 := rfl
/-- Version 7 carries the arbiter's `sq = state[A_q, R_q]`. -/
theorem N8_7 : C8.N 7 = some Sal.Emulation.sq := rfl
theorem N8_5 : C8.N 5 = some Sal.Emulation.LCA := rfl
theorem L8_7 : C8.L 7 = some evQ2 := rfl
theorem L8_5 : C8.L 5 = some evS := rfl
theorem N8_9 : C8.N 9 = none := rfl

theorem H9_p : C9.H 0 = some 8 := rfl
theorem H9_q : C9.H 1 = some 9 := rfl
theorem N9_5 : C9.N 5 = some Sal.Emulation.LCA := rfl
/-- **Version 8 is the arbiter's `head_p`**, on the nose. -/
theorem N9_8 : C9.N 8 = some head_p := rfl
/-- **Version 9 is the arbiter's `head_q`**, on the nose. -/
theorem N9_9 : C9.N 9 = some head_q := rfl
theorem L9_8 : C9.L 8 = some evH1 := rfl
theorem L9_9 : C9.L 9 = some evH2 := rfl
theorem N9_10 : C9.N 10 = none := rfl

/-- **The critical merge's output is the arbiter's `mergedState`**: all-dead. -/
theorem N10_10 : C10.N 10 = some mergedState := rfl
theorem N10_8 : C10.N 8 = some head_p := rfl
theorem N10_9 : C10.N 9 = some head_q := rfl
theorem N10_5 : C10.N 5 = some Sal.Emulation.LCA := rfl

/-! ## §6. The version graph

Each rule's edge field is literally `fun x y => C.E x y ∨ (new edges)`, so the
graph is unfolded one transition at a time (unfolding all eleven
configurations at once times out). -/

theorem C1_E (x y : Version) : C1.E x y ↔ (x = 0 ∧ y = 1) := by
  simp [C1, C0, stepCB, Store.initConfig]

theorem C2_E (x y : Version) :
    C2.E x y ↔ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) := by
  rw [show C2.E x y ↔ C1.E x y ∨ (x = 0 ∧ y = 2) from Iff.rfl, C1_E]

theorem C3_E (x y : Version) :
    C3.E x y ↔ ((x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)) ∨ (x = 1 ∧ y = 3) := by
  rw [show C3.E x y ↔ C2.E x y ∨ (x = 1 ∧ y = 3) from Iff.rfl, C2_E]

theorem C4_E (x y : Version) :
    C4.E x y ↔ (((x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)) ∨ (x = 1 ∧ y = 3)) ∨
      (x = 2 ∧ y = 4) := by
  rw [show C4.E x y ↔ C3.E x y ∨ (x = 2 ∧ y = 4) from Iff.rfl, C3_E]

theorem C5_E (x y : Version) :
    C5.E x y ↔ C4.E x y ∨ ((x = 4 ∨ x = 3) ∧ y = 5) := Iff.rfl
theorem C6_E (x y : Version) : C6.E x y ↔ C5.E x y ∨ (x = 2 ∧ y = 6) := Iff.rfl
theorem C7_E (x y : Version) : C7.E x y ↔ C6.E x y ∨ (x = 3 ∧ y = 7) := Iff.rfl
theorem C8_E (x y : Version) :
    C8.E x y ↔ C7.E x y ∨ ((x = 6 ∨ x = 5) ∧ y = 8) := Iff.rfl
theorem C9_E (x y : Version) :
    C9.E x y ↔ C8.E x y ∨ ((x = 7 ∨ x = 5) ∧ y = 9) := Iff.rfl
theorem C10_E (x y : Version) :
    C10.E x y ↔ C9.E x y ∨ ((x = 8 ∨ x = 9) ∧ y = 10) := Iff.rfl

/-- The 14 edges of the final version graph, and nothing else. -/
theorem C10_E_iff (x y : Version) :
    C10.E x y ↔
      ((((((((((x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)) ∨ (x = 1 ∧ y = 3)) ∨
        (x = 2 ∧ y = 4)) ∨ ((x = 4 ∨ x = 3) ∧ y = 5)) ∨ (x = 2 ∧ y = 6)) ∨
        (x = 3 ∧ y = 7)) ∨ ((x = 6 ∨ x = 5) ∧ y = 8)) ∨
        ((x = 7 ∨ x = 5) ∧ y = 9)) ∨ ((x = 8 ∨ x = 9) ∧ y = 10)) := by
  rw [C10_E, C9_E, C8_E, C7_E, C6_E, C5_E, C4_E]

/-! ### The ancestor table -/

/-- The causal ancestors of each version in the final graph. Versions above
`10` are their own only ancestor (no edge touches them), which keeps the
reflexive case of `anc_sound` total. -/
def ancOf : Version → List Version
  | 0 => [0]
  | 1 => [0, 1]
  | 2 => [0, 2]
  | 3 => [0, 1, 3]
  | 4 => [0, 2, 4]
  | 5 => [0, 1, 2, 3, 4, 5]
  | 6 => [0, 2, 6]
  | 7 => [0, 1, 3, 7]
  | 8 => [0, 1, 2, 3, 4, 5, 6, 8]
  | 9 => [0, 1, 2, 3, 4, 5, 7, 9]
  | 10 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  | n + 11 => [n + 11]

/-- Ancestry, as a decidable proposition. -/
def AncTable (v w : Version) : Prop := v ∈ ancOf w

instance (v w : Version) : Decidable (AncTable v w) := by
  unfold AncTable; infer_instance

/-- **Soundness of the ancestor table** against the final graph: one case per
edge, each a containment between two concrete ancestor lists. -/
theorem anc_sound {v w : Version} (h : C10.Anc v w) : AncTable v w := by
  induction h with
  | refl =>
      show AncTable v v
      match v with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => simp [AncTable, ancOf]
      | n + 11 => simp [AncTable, ancOf]
  | tail _hab hbc ih =>
      rw [C10_E_iff] at hbc
      rcases hbc with
        ((((((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) |
          ⟨rfl | rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl | rfl, rfl⟩) |
          ⟨rfl | rfl, rfl⟩) | ⟨rfl | rfl, rfl⟩ <;>
        simp_all [AncTable, ancOf] <;> tauto

/-- A negative ancestry fact in the final graph, decided by the table. -/
theorem not_anc {v w : Version} (h : ¬ AncTable v w) : ¬ C10.Anc v w :=
  fun hanc => h (anc_sound hanc)

/-! ### Edge monotonicity

Each rule only *adds* edges, so ancestry transports forward along the execution
and non-ancestry transports backward. -/

theorem emono_01 (x y : Version) (h : C0.E x y) : C1.E x y := Or.inl h
theorem emono_12 (x y : Version) (h : C1.E x y) : C2.E x y := Or.inl h
theorem emono_23 (x y : Version) (h : C2.E x y) : C3.E x y := Or.inl h
theorem emono_34 (x y : Version) (h : C3.E x y) : C4.E x y := Or.inl h
theorem emono_45 (x y : Version) (h : C4.E x y) : C5.E x y := Or.inl h
theorem emono_56 (x y : Version) (h : C5.E x y) : C6.E x y := Or.inl h
theorem emono_67 (x y : Version) (h : C6.E x y) : C7.E x y := Or.inl h
theorem emono_78 (x y : Version) (h : C7.E x y) : C8.E x y := Or.inl h
theorem emono_89 (x y : Version) (h : C8.E x y) : C9.E x y := Or.inl h
theorem emono_910 (x y : Version) (h : C9.E x y) : C10.E x y := Or.inl h

theorem anc_to10_C4 {v w : Version} (h : C4.Anc v w) : C10.Anc v w :=
  Config.Anc.mono emono_910 (Config.Anc.mono emono_89 (Config.Anc.mono emono_78
    (Config.Anc.mono emono_67 (Config.Anc.mono emono_56
      (Config.Anc.mono emono_45 h)))))

theorem anc_to10_C7 {v w : Version} (h : C7.Anc v w) : C10.Anc v w :=
  Config.Anc.mono emono_910 (Config.Anc.mono emono_89
    (Config.Anc.mono emono_78 h))

theorem anc_to10_C8 {v w : Version} (h : C8.Anc v w) : C10.Anc v w :=
  Config.Anc.mono emono_910 (Config.Anc.mono emono_89 h)

theorem anc_to10_C9 {v w : Version} (h : C9.Anc v w) : C10.Anc v w :=
  Config.Anc.mono emono_910 h

/-! ### The edges, at their birth configuration and lifted where needed -/

theorem e01_C1 : C1.E 0 1 := Or.inr ⟨rfl, rfl⟩
theorem e02_C2 : C2.E 0 2 := Or.inr ⟨rfl, rfl⟩
theorem e13_C3 : C3.E 1 3 := Or.inr ⟨rfl, rfl⟩
theorem e24_C4 : C4.E 2 4 := Or.inr ⟨rfl, rfl⟩
theorem e45_C5 : C5.E 4 5 := Or.inr ⟨Or.inl rfl, rfl⟩
theorem e35_C5 : C5.E 3 5 := Or.inr ⟨Or.inr rfl, rfl⟩
theorem e26_C6 : C6.E 2 6 := Or.inr ⟨rfl, rfl⟩
theorem e37_C7 : C7.E 3 7 := Or.inr ⟨rfl, rfl⟩
theorem e68_C8 : C8.E 6 8 := Or.inr ⟨Or.inl rfl, rfl⟩
theorem e58_C8 : C8.E 5 8 := Or.inr ⟨Or.inr rfl, rfl⟩
theorem e79_C9 : C9.E 7 9 := Or.inr ⟨Or.inl rfl, rfl⟩
theorem e59_C9 : C9.E 5 9 := Or.inr ⟨Or.inr rfl, rfl⟩

/-- Ancestry from a single edge. -/
private theorem anc1 {C : Config AWSetT} {x y : Version} (h : C.E x y) :
    C.Anc x y := Config.Anc.of_edge h

/-! ## §7. The four LCA premises

Each is the paper's LCA definition verbatim: two ancestry facts plus maximality
over every vertex. For maximality, `anc_sound` bounds the candidate set to the
intersection of the two ancestor lists; each candidate then gets an explicit
chain or a `decide` refutation. -/

/-- `LCA(4, 3) = 0` at the staging merge. -/
theorem lca_staging : IsLCA C4 0 4 3 := by
  refine ⟨?_, ?_, ?_⟩
  · exact Config.Anc.trans (anc1 (emono_34 _ _ (emono_23 _ _ e02_C2)))
      (anc1 e24_C4)
  · exact Config.Anc.trans (anc1 (emono_34 _ _ (emono_23 _ _
      (emono_12 _ _ e01_C1)))) (anc1 (emono_34 _ _ e13_C3))
  · intro v _hv h4 h3
    have t4 := anc_sound (anc_to10_C4 h4)
    have t3 := anc_sound (anc_to10_C4 h3)
    simp only [AncTable, ancOf, List.mem_cons, List.not_mem_nil,
      or_false] at t4 t3
    rcases t4 with rfl | rfl | rfl
    · exact Config.Anc.refl _ _
    · exact absurd t3 (by decide)
    · exact absurd t3 (by decide)

/-- `LCA(6, 5) = 2` at `head_p`'s merge: `p₁` is the LCA of `p₂` and `v_s`. -/
theorem lca_headp : IsLCA C7 2 6 5 := by
  refine ⟨?_, ?_, ?_⟩
  · exact anc1 (emono_67 _ _ e26_C6)
  · exact Config.Anc.trans (anc1 (emono_67 _ _ (emono_56 _ _
      (emono_45 _ _ e24_C4)))) (anc1 (emono_67 _ _ (emono_56 _ _ e45_C5)))
  · intro v _hv h6 h5
    have t6 := anc_sound (anc_to10_C7 h6)
    have t5 := anc_sound (anc_to10_C7 h5)
    simp only [AncTable, ancOf, List.mem_cons, List.not_mem_nil,
      or_false] at t6 t5
    rcases t6 with rfl | rfl | rfl
    · exact anc1 (emono_67 _ _ (emono_56 _ _ (emono_45 _ _
        (emono_34 _ _ (emono_23 _ _ e02_C2)))))
    · exact Config.Anc.refl _ _
    · exact absurd t5 (by decide)

/-- `LCA(7, 5) = 3` at `head_q`'s merge: `q₁` is the LCA of `q₂` and `v_s`. -/
theorem lca_headq : IsLCA C8 3 7 5 := by
  refine ⟨?_, ?_, ?_⟩
  · exact anc1 (emono_78 _ _ e37_C7)
  · exact anc1 (emono_78 _ _ (emono_67 _ _ (emono_56 _ _ e35_C5)))
  · intro v _hv h7 h5
    have t7 := anc_sound (anc_to10_C8 h7)
    have t5 := anc_sound (anc_to10_C8 h5)
    simp only [AncTable, ancOf, List.mem_cons, List.not_mem_nil,
      or_false] at t7 t5
    have e13 : C8.E 1 3 := emono_78 _ _ (emono_67 _ _ (emono_56 _ _
      (emono_45 _ _ (emono_34 _ _ e13_C3))))
    rcases t7 with rfl | rfl | rfl | rfl
    · exact Config.Anc.trans (anc1 (emono_78 _ _ (emono_67 _ _ (emono_56 _ _
        (emono_45 _ _ (emono_34 _ _ (emono_23 _ _ (emono_12 _ _ e01_C1))))))))
        (anc1 e13)
    · exact anc1 e13
    · exact Config.Anc.refl _ _
    · exact absurd t5 (by decide)

/-- **The critical merge's LCA premise**: `v_s = LCA(head_p, head_q)`, i.e.
`LCA(8, 9) = 5` in the version DAG this execution built. This is the fact the
walkthrough asserts and the arbiter file assumes. -/
theorem lca_critical : IsLCA C9 5 8 9 := by
  have e45 : C9.E 4 5 := emono_89 _ _ (emono_78 _ _ (emono_67 _ _
    (emono_56 _ _ e45_C5)))
  have e35 : C9.E 3 5 := emono_89 _ _ (emono_78 _ _ (emono_67 _ _
    (emono_56 _ _ e35_C5)))
  have e24 : C9.E 2 4 := emono_89 _ _ (emono_78 _ _ (emono_67 _ _
    (emono_56 _ _ (emono_45 _ _ e24_C4))))
  have e13 : C9.E 1 3 := emono_89 _ _ (emono_78 _ _ (emono_67 _ _
    (emono_56 _ _ (emono_45 _ _ (emono_34 _ _ e13_C3)))))
  have e01 : C9.E 0 1 := emono_89 _ _ (emono_78 _ _ (emono_67 _ _
    (emono_56 _ _ (emono_45 _ _ (emono_34 _ _ (emono_23 _ _
      (emono_12 _ _ e01_C1)))))))
  refine ⟨anc1 (emono_89 _ _ e58_C8), anc1 e59_C9, ?_⟩
  intro v _hv h8 h9
  have t8 := anc_sound (anc_to10_C9 h8)
  have t9 := anc_sound (anc_to10_C9 h9)
  simp only [AncTable, ancOf, List.mem_cons, List.not_mem_nil,
    or_false] at t8 t9
  rcases t8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Config.Anc.trans (anc1 e01)
      (Config.Anc.trans (anc1 e13) (anc1 e35))
  · exact Config.Anc.trans (anc1 e13) (anc1 e35)
  · exact Config.Anc.trans (anc1 e24) (anc1 e45)
  · exact anc1 e35
  · exact anc1 e45
  · exact Config.Anc.refl _ _
  · exact absurd t9 (by decide)
  · exact absurd t9 (by decide)

/-! ## §8. Timestamp freshness

The `[Apply]` rule demands a globally fresh timestamp. The generic
`events_step*` lemmas of `Store_TS` read the event set off the trace, so no
enumeration of `dom(L)` is needed. -/

theorem events_C1 (e : Op AWOp) (h : C1.Events e) : False := by
  unfold C1 at h
  rcases events_stepCB h with h' | h'
  · exact h'
  · unfold C0 at h'; exact events_initConfig h'

theorem events_C2 (e : Op AWOp) (h : C2.Events e) : e = A_p := by
  unfold C2 at h
  rcases events_stepApply h with h' | h' | h'
  · exact absurd h' (by simp)
  · exact h'
  · exact absurd h' (fun h'' => events_C1 e h'')

theorem events_C3 (e : Op AWOp) (h : C3.Events e) : e = A_p ∨ e = A_q := by
  unfold C3 at h
  rcases events_stepApply h with h' | h' | h'
  · exact absurd h' (by simp)
  · exact Or.inr h'
  · exact Or.inl (events_C2 e h')

theorem events_C4 (e : Op AWOp) (h : C4.Events e) : e = A_p ∨ e = A_q := by
  unfold C4 at h
  rcases events_stepCB h with h' | h'
  · exact Or.inl (by simpa [evAp] using h')
  · exact events_C3 e h'

theorem events_C5 (e : Op AWOp) (h : C5.Events e) : e = A_p ∨ e = A_q := by
  unfold C5 at h
  rcases events_stepMerge h with h' | h' | h'
  · exact Or.inl (by simpa [evAp] using h')
  · exact Or.inr (by simpa [evAq] using h')
  · exact events_C4 e h'

theorem events_C6 (e : Op AWOp) (h : C6.Events e) :
    e = A_p ∨ e = A_q ∨ e = R_p := by
  unfold C6 at h
  rcases events_stepApply h with h' | h' | h'
  · exact Or.inl (by simpa [evAp] using h')
  · exact Or.inr (Or.inr h')
  · rcases events_C5 e h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl h'')

theorem fresh_C1 : ∀ e, C1.Events e → Op.time e ≠ 1 :=
  fun e h => absurd h (fun h' => events_C1 e h')

theorem fresh_C2 : ∀ e, C2.Events e → Op.time e ≠ 2 := by
  intro e h; rw [events_C2 e h]; decide

theorem fresh_C5 : ∀ e, C5.Events e → Op.time e ≠ 3 := by
  intro e h; rcases events_C5 e h with h | h <;> rw [h] <;> decide

theorem fresh_C6 : ∀ e, C6.Events e → Op.time e ≠ 4 := by
  intro e h; rcases events_C6 e h with h | h | h <;> rw [h] <;> decide

/-! ## §9. The lemma

Everything above is machinery for this statement's premises. -/

/-- **The defeater is obtainable by a sequence of store operations.**

There is a configuration reachable from the initial one — by the ten transitions
of `defeaterTrace`, each an instance of a rule of Fig. `sem` — whose versions
`5`, `8`, `9`, `10` carry the defeater's four states: the LCA `v_s`, the two
heads, and the all-dead merged version. Every premise of every rule is
discharged, including the four `LCA` side conditions.

The four states named here are the *same terms* the peel rules are refuted
against in `InterLca2op_Defeater_Arbiter.lean`, so the obstruction proved there
is an obstruction at a merge this store is obliged to allow. -/
theorem defeater_obtainable :
    ∃ C : Config AWSetT,
      ReachableFromInit AWSetT 0 0 C ∧
      C.N 5 = some Sal.Emulation.LCA ∧
      C.N 8 = some head_p ∧
      C.N 9 = some head_q ∧
      C.N 10 = some mergedState := by
  refine ⟨C10, ⟨defeaterTrace, ?_⟩, N10_5, N10_8, N10_9, N10_10⟩
  refine Exec.cons (step_cb (C := C0) (r := 0) (r' := 1) (v := 1) (vr := 0)
    rfl rfl rfl rfl rfl) ?_
  refine Exec.cons (step_apply fresh_C1 H1_p N1_2 N1_0 L1_0) ?_
  refine Exec.cons (step_apply fresh_C2 H2_q N2_3 N2_1 L2_1) ?_
  refine Exec.cons (step_cb H3_p H3_s N3_4 N3_2 L3_2) ?_
  refine Exec.cons (step_merge H4_s H4_q N4_5 lca_staging N4_0 N4_4 N4_3
    L4_4 L4_3) ?_
  refine Exec.cons (step_apply fresh_C5 H5_p N5_6 N5_2 L5_2) ?_
  refine Exec.cons (step_apply fresh_C6 H6_q N6_7 N6_3 L6_3) ?_
  refine Exec.cons (step_merge H7_p H7_s N7_8 lca_headp N7_2 N7_6 N7_5
    L7_6 L7_5) ?_
  refine Exec.cons (step_merge H8_q H8_s N8_9 lca_headq N8_3 N8_7 N8_5
    L8_7 L8_5) ?_
  refine Exec.cons (step_merge H9_p H9_q N9_10 lca_critical N9_5 N9_8 N9_9
    L9_8 L9_9) ?_
  exact Exec.nil _

end Sal.ConditionedMRDTs.Store.Defeater
