import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha

/-! # Shesha — SPOT (litmus witnesses + the two fooling-pair impossibilities)

Every fact below is `native_decide`/`decide` on a concrete execution built
through `fold`/`steps` (never hand-assembled states). The scenarios and their
expected outputs are the directed-witness table of `whiteboard/sl_pbt.py`
(§ "directed witnesses") and the litmus table of
`whiteboard/sibling-linked-rga-notes.md` §5; the impossibility pairs are
`whiteboard/sibling-linked-proof.md` §7 (I1, I2).

Cross-validation (Lean `#eval` vs `python3 whiteboard/sl_pbt.py`):

| litmus     | Lean          | Python        |
|------------|---------------|---------------|
| T2         | `[1, 10, 20]` | `[1, 10, 20]` |
| CX-F       | `[4, 2]`      | `[4, 2]`      |
| stale-LCA  | `[4, 2]`      | `[4, 2]`      |
| leapfrog   | `[3, 5, 2]`   | `[3, 5, 2]`   |
| both-del   | `[10, 9]`     | `[10, 9]`     |
| w-slot     | `[5, 7, 4, 1]`| `[5, 7, 4, 1]`|
| fooling w1 | `[10, 5]`     | `[10, 5]`     |
| fooling w2 | `[10, 5]`     | `[10, 5]`     |

(The port was additionally swept against `sl_pbt.py` on 480 enumerated
small merge scenarios — 4 LCA shapes × branch scripts with inserts at every
anchor, nested deletes, born-and-died runs, double deletes — generated from
the Python reference; 480/480 reads agreed, including argument-order
symmetry. The generator is reproducible from `sl_pbt.py`'s `merge`; it is
validation tooling, not a repo artifact.) -/

namespace Shesha_SPOT

open Shesha Shesha.Op

/-! ## 1. Litmus executions (design record §5)

Ids double as elements, per `sl_pbt.py`. Every state is built by `fold`
(from empty) or `steps` (branching a version), faithful to genuine
executions. -/

/-! ### T2 — markers position under a shared parent

LCA: `1` under root, siblings `3, 2` under `1` (newest first). A inserts `10`
under `3` then deletes `3`; B inserts `20` under `2` then deletes `2`. The
dead `3`, `2` are *markers* — each still live in one input — and hold the
slots: `[1, 10, 20]`, no timestamp comparison anywhere. (Killed the flat
sequential-merge phase-2 design.) -/

def t2L : St := fold [ins 1 0, ins 2 1, ins 3 1]
def t2A : St := steps t2L [ins 10 3, del 3]
def t2B : St := steps t2L [ins 20 2, del 2]

theorem t2_input_reads :
    (read t2L, read t2A, read t2B) = ([1, 3, 2], [1, 10, 2], [1, 3, 20]) := by
  native_decide

theorem litmus_T2 : read (merge t2L t2A t2B) = [1, 10, 20] := by native_decide

/-! ### CX-F — frame mismatch (B idle)

A builds `3` under `1`, `4` under `3`, then deletes `3` and `1`; B does
nothing. Pure Case 1/3 (one branch changed), structural: `[4, 2]`. Every
numeric-position scheme died here. -/

def cxL : St := fold [ins 1 0, ins 2 1]
def cxA : St := steps cxL [ins 3 1, ins 4 3, del 3, del 1]

theorem litmus_CXF : read (merge cxL cxA cxL) = [4, 2] := by native_decide

/-! ### Stale-LCA replay — the post-splice state is order-self-contained

Merging the CX-F result against the *old* fork point (idle fork, late merge)
must not lose or reorder anything: `[4, 2]` again. (Killed
rebuild-with-carried-graves.) -/

def cxM : St := merge cxL cxA cxL

theorem litmus_staleLCA : read (merge cxL cxM cxL) = [4, 2] := by native_decide

/-! ### Leapfrog — a collapsed chain lands by slot, not by own timestamp

A builds `4` under `1`, `5` under `4`, then deletes `4` and `1`: survivor `5`
arrives at the root through two splices, and must sit in `1`'s slot
(`[3, 5, 2]`), not re-sort by its own id `5 > 3`. -/

def lfL : St := fold [ins 1 0, ins 2 1, ins 3 0]
def lfA : St := steps lfL [ins 4 1, ins 5 4, del 4, del 1]

theorem litmus_leapfrog : read (merge lfL lfA lfL) = [3, 5, 2] := by native_decide

/-! ### Both delete the same node — Case 4c is benign on fresh-vs-fresh

Both branches delete `1` after inserting a fresh node under it. The fresh
pair `10 ∥ 9` was never co-displayed; newest-first timestamp order is the
*right* datum: `[10, 9]`. -/

def bdL : St := fold [ins 1 0]
def bdA : St := steps bdL [ins 10 1, del 1]
def bdB : St := steps bdL [ins 9 1, del 1]

theorem litmus_bothDel : read (merge bdL bdA bdB) = [10, 9] := by native_decide

/-! ### w-slot — the greedy weave is wrong; L-document order is essential

L: `3` and `1` at root, `4` under `3`. A inserts fresh `5` at the root;
B occupies dead `3`'s slot before `4` (insert `6` under `3`, `7` under `6`,
delete `6`, delete `3`). The skeleton/continuation rule gives
`[5, 7, 4, 1]` — a greedy head-to-head weave would misplace `7`.
(The session bug, caught by writing the algorithm down.) -/

def wsL : St := fold [ins 1 0, ins 3 0, ins 4 3]
def wsA : St := steps wsL [ins 5 0]
def wsB : St := steps wsL [ins 6 3, ins 7 6, del 6, del 3]

theorem ws_input_reads :
    (read wsL, read wsA, read wsB) = ([3, 4, 1], [5, 3, 4, 1], [7, 4, 1]) := by
  native_decide

theorem litmus_wslot : read (merge wsL wsA wsB) = [5, 7, 4, 1] := by native_decide

/-! ### Merge symmetry (Lemma M1's concrete instances)

`sl_pbt.py` asserts `merge(L,A,B).read() == merge(L,B,A).read()` on every
trial; pinned here on the litmus cases. -/

theorem merge_symm_T2 :
    read (merge t2L t2A t2B) = read (merge t2L t2B t2A) := by native_decide

theorem merge_symm_wslot :
    read (merge wsL wsA wsB) = read (merge wsL wsB wsA) := by native_decide

theorem merge_symm_bothDel :
    read (merge bdL bdA bdB) = read (merge bdL bdB bdA) := by native_decide

/-! ## 2. Fooling pair I1 — tombstoned-oracle fidelity is unattainable
(`sibling-linked-proof.md` §7 (I1), `fooling-pair.excalidraw`)

Two worlds. Both: LCA empty; A inserts `p·5` at the root. B (world 1):
`ins g·2 ← ⌂; ins k·10 ← g; del g`. B (world 2): the same script with `g·6`.
B's final state mentions `g` **nowhere** — the two worlds' inputs are
bit-identical — yet the tombstoned oracle demands `[5, 10]` in world 1
(`p·5` out-ranks the grave `g·2`) and `[10, 5]` in world 2 (`g·6` out-ranks
`p·5`). No deterministic state-function merge can satisfy both. -/

def foolL : St := init
def foolA : St := steps init [ins 5 0]
def foolB_w1 : St := steps init [ins 2 0, ins 10 2, del 2]
def foolB_w2 : St := steps init [ins 6 0, ins 10 6, del 6]

/-- The global op histories (which no tombstone-free state retains). -/
def w1Ins : List (Nat × Nat) := [(5, 0), (2, 0), (10, 2)]
def w1Del : List Nat := [2]
def w2Ins : List (Nat × Nat) := [(5, 0), (6, 0), (10, 6)]
def w2Del : List Nat := [6]

/-- (a) The three merge inputs are EQUAL across the worlds: the deleted `g`
left no trace in any field of any state. (`L` and `A` are shared by
construction; `B` is the load-bearing equality, `decide`d on the states.) -/
theorem I1_B_states_equal : foolB_w1 = foolB_w2 := by native_decide

/-- (b) The tombstoned oracles of the two worlds differ: `[5, 10]` vs
`[10, 5]` — the grave's timestamp decides, and it is gone. -/
theorem I1_oracle_w1 : oracleRead w1Ins w1Del = [5, 10] := by native_decide

theorem I1_oracle_w2 : oracleRead w2Ins w2Del = [10, 5] := by native_decide

theorem I1_oracles_differ :
    oracleRead w1Ins w1Del ≠ oracleRead w2Ins w2Del := by native_decide

/-- (c) **The impossibility, quantified over ALL merge functions**: no
`f : St → St → St → List Nat` — Shesha's or anyone's — matches the tombstoned
oracle in both worlds, because it receives identical inputs and the demanded
outputs differ. Tombstoned-oracle fidelity prices out to remembering dead
ranks: the deleted path ≡ the tombstones. -/
theorem I1_no_merge_function (f : St → St → St → List Nat) :
    ¬ (f foolL foolA foolB_w1 = oracleRead w1Ins w1Del ∧
       f foolL foolA foolB_w2 = oracleRead w2Ins w2Del) := by
  rintro ⟨h1, h2⟩
  rw [← I1_B_states_equal] at h2
  exact I1_oracles_differ (h1.symm.trans h2)

/-- What Shesha actually outputs: `[10, 5]` in both worlds — the match in
world 2, a *licensed divergence* in world 1 (`5` and `10` were never
co-displayed by any state; the pair is exactly the divergence the datatype's
published contract records). -/
theorem fool_merge_w1 : read (merge foolL foolA foolB_w1) = [10, 5] := by
  native_decide

theorem fool_merge_w2 : read (merge foolL foolA foolB_w2) = [10, 5] := by
  native_decide

theorem merge_symm_fool :
    read (merge foolL foolA foolB_w1) = read (merge foolL foolB_w1 foolA) := by
  native_decide

/-! ## 3. Fooling pair I2 — the strong-list spec is unattainable
(`sibling-linked-proof.md` §7 (I2); notes §7½ item 3 — "NOT a bug, a theorem")

Five nodes, two worlds. L: `m·1 ← ⌂, g·2 ← ⌂` (row `g, m`). B: `ins y·9 ← g`
(displays `g < y` and `y < m`). World 1: A runs `ins x·5 ← ⌂` (displays
`x < g`), `del g`, `del m` — the displays force `x < y` transitively
(`x < g < y`). World 2: A runs `ins x·5 ← m` (displays `m < x`), `del m`,
`del g` — the displays force `y < x` (`y < m < x`). A's final state is
`{x at root}` in both worlds, **bit-identical**; L and B are shared. The
constraints chain transitively *through dead nodes' past displays* — a
tombstone-free state cannot remember which side of a dead node its survivors
were shown on. Auditing through the dead is remembering the dead. -/

def i2L0 : St := fold [ins 1 0]
def i2L : St := steps i2L0 [ins 2 0]
def i2B : St := steps i2L [ins 9 2]

def i2A1a : St := steps i2L [ins 5 0]
def i2A1b : St := steps i2A1a [del 2]
def i2A1 : St := steps i2A1b [del 1]

def i2A2a : St := steps i2L [ins 5 1]
def i2A2b : St := steps i2A2a [del 1]
def i2A2 : St := steps i2A2b [del 2]

/-- The two worlds' A-states are EQUAL (both `{x·5 at root}`), though their
histories displayed `x` on opposite sides of the dead `g`, `m`. -/
theorem I2_A_states_equal : i2A1 = i2A2 := by native_decide

/-- The display logs: every read every session of each world produced. -/
def w1Reads : List (List Nat) :=
  [read i2L0, read i2L, read i2B, read i2A1a, read i2A1b, read i2A1]

def w2Reads : List (List Nat) :=
  [read i2L0, read i2L, read i2B, read i2A2a, read i2A2b, read i2A2]

/-- All ids ever alive in the executions. -/
def i2ids : List Nat := [1, 2, 5, 9]

/-- `x` strictly precedes `y` in the list `l`. -/
def precedes (l : List Nat) (x y : Nat) : Bool :=
  decide (y ∈ (l.dropWhile (fun u => u ≠ x)).drop 1)

/-- Some state of the log displayed `x` before `y`. -/
def displayed (reads : List (List Nat)) (x y : Nat) : Bool :=
  reads.any (fun r => precedes r x y)

def transStep (ids : List Nat) (e : Nat → Nat → Bool) (x y : Nat) : Bool :=
  e x y || ids.any (fun m => e x m && e m y)

def transN (ids : List Nat) : Nat → (Nat → Nat → Bool) → (Nat → Nat → Bool)
  | 0, e => e
  | n + 1, e => transN ids n (transStep ids e)

/-- Orders transitively forced by a display log (paths of any length over the
finite id universe: `ids.length` doublings ≥ any simple path). -/
def forced (ids : List Nat) (reads : List (List Nat)) (x y : Nat) : Bool :=
  transN ids ids.length (displayed reads) x y

/-- Strong-list consistency of a merge output with a display log: the output
never displays the reverse of a transitively forced order. (Already a
*weakening* of the full strong-list spec — even this much is unattainable,
which is the theorem.) -/
def SLConsistent (ids : List Nat) (reads : List (List Nat)) (out : List Nat) :
    Prop :=
  ∀ x y, forced ids reads x y = true → precedes out y x = false

/-- Any list containing two distinct elements displays them one way or the
other. -/
theorem precedes_total :
    ∀ (l : List Nat) (x y : Nat), x ∈ l → y ∈ l → x ≠ y →
      precedes l x y = true ∨ precedes l y x = true
  | [], _, _, hx, _, _ => nomatch hx
  | h :: t, x, y, hx, hy, hxy => by
      by_cases hhx : h = x
      · subst hhx
        left
        have hyt : y ∈ t := by
          rcases List.mem_cons.mp hy with rfl | hyt
          · exact absurd rfl hxy
          · exact hyt
        simpa [precedes] using hyt
      · by_cases hhy : h = y
        · subst hhy
          right
          have hxt : x ∈ t := by
            rcases List.mem_cons.mp hx with rfl | hxt
            · exact absurd rfl (Ne.symm hxy)
            · exact hxt
          simpa [precedes] using hxt
        · have hxt : x ∈ t := by
            rcases List.mem_cons.mp hx with rfl | hxt
            · exact absurd rfl hhx
            · exact hxt
          have hyt : y ∈ t := by
            rcases List.mem_cons.mp hy with rfl | hyt
            · exact absurd rfl hhy
            · exact hyt
          simpa [precedes, hhx, hhy] using precedes_total t x y hxt hyt hxy

/-- World 1's displays force `x·5` before `y·9` (via the dead `g·2`:
`x < g` in A's session, `g < y` in B's). -/
theorem I2_w1_forces_5_9 : forced i2ids w1Reads 5 9 = true := by native_decide

/-- World 2's displays force `y·9` before `x·5` (via the dead `m·1`:
`y < m` in B's session, `m < x` in A's). -/
theorem I2_w2_forces_9_5 : forced i2ids w2Reads 9 5 = true := by native_decide

/-- Each world is individually satisfiable — neither log forces the reverse
pair on its own. The contradiction below arises only for a single
state-function serving both. -/
theorem I2_worlds_individually_consistent :
    forced i2ids w1Reads 9 5 = false ∧ forced i2ids w2Reads 5 9 = false := by
  native_decide

/-- **The impossibility, quantified over ALL merge functions**: no
`f : St → St → St → List Nat` whose world-1 output shows the survivors
`{5, 9}` can be strong-list consistent in both worlds — the inputs are equal,
so the output is shared, and the forced orders contradict. A tombstone-free
state-function merge cannot satisfy the strong list spec; the constraints
chain through the dead. -/
theorem I2_no_merge_function (f : St → St → St → List Nat)
    (h5 : 5 ∈ f i2L i2A1 i2B) (h9 : 9 ∈ f i2L i2A1 i2B)
    (h1 : SLConsistent i2ids w1Reads (f i2L i2A1 i2B))
    (h2 : SLConsistent i2ids w2Reads (f i2L i2A2 i2B)) : False := by
  rw [← I2_A_states_equal] at h2
  have h95 : precedes (f i2L i2A1 i2B) 9 5 = false := h1 5 9 I2_w1_forces_5_9
  have h59 : precedes (f i2L i2A1 i2B) 5 9 = false := h2 9 5 I2_w2_forces_9_5
  rcases precedes_total (f i2L i2A1 i2B) 5 9 h5 h9 (by decide) with h | h
  · exact absurd (h59.symm.trans h) (by decide)
  · exact absurd (h95.symm.trans h) (by decide)

/-- Shesha itself, on the I2 worlds: converges (same inputs, same output,
`[9, 5]` — cross-validated against `sl_pbt.py`) and keeps both survivors.
The never-co-displayed pair `(9, 5)` is ordered by the free 4c rule
(newest-head-first); the output is inevitably inconsistent with one world's
dead-mediated *transitive* constraints (here world 1's `x < g < y`), exactly
as the impossibility dictates — while flipping no pair either world ever
co-displayed (pairwise display stability, the adopted spec §7¾). -/
theorem I2_shesha_output :
    read (merge i2L i2A1 i2B) = [9, 5] ∧
    read (merge i2L i2A2 i2B) = [9, 5] := by native_decide

/-! ## 4. Cross-validation `#eval` table (compare with
`python3 whiteboard/sl_pbt.py` directed witnesses) -/

#eval ("T2       ", read (merge t2L t2A t2B), "python: [1, 10, 20]")
#eval ("CX-F     ", read (merge cxL cxA cxL), "python: [4, 2]")
#eval ("staleLCA ", read (merge cxL cxM cxL), "python: [4, 2]")
#eval ("leapfrog ", read (merge lfL lfA lfL), "python: [3, 5, 2]")
#eval ("bothDel  ", read (merge bdL bdA bdB), "python: [10, 9]")
#eval ("w-slot   ", read (merge wsL wsA wsB), "python: [5, 7, 4, 1]")
#eval ("fool-w1  ", read (merge foolL foolA foolB_w1), "python: [10, 5]")
#eval ("fool-w2  ", read (merge foolL foolA foolB_w2), "python: [10, 5]")

end Shesha_SPOT

section AxiomAudit
/-! Acceptable: `propext`, `Classical.choice`, `Quot.sound` (kernel-clean) plus
`Lean.ofReduceBool`/`Lean.trustCompiler` for the `native_decide` witnesses.
Theorem S and its corollary are kernel-clean (no `native_decide` anywhere in
their proofs). -/
#print axioms Shesha.sequential_soundness
#print axioms Shesha.delete_preserves_survivor_order
#print axioms Shesha_SPOT.litmus_T2
#print axioms Shesha_SPOT.litmus_wslot
#print axioms Shesha_SPOT.I1_no_merge_function
#print axioms Shesha_SPOT.I2_no_merge_function
#print axioms Shesha_SPOT.precedes_total
end AxiomAudit
