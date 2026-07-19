import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA

/-!
# Sibling edges without retention cannot implement the embed RGA

KC's question (2026-07-18): the embed RGA works, but its proof rests on
keeping a deleted node's memory alive inside live descendants'
coordinates. Could a sibling-edge implementation, which splices a dead
node and lifts its children a level up, be shown equivalent to the embed
RGA, with no such retention? This file is the answer: **no**, by a
four-event fooling pair, and the counterexample names exactly the
information the splice destroys.

**The mechanism.** In the embed order, a lifted child displays at its
dead ancestor's rank: the subtree keyed by the ancestor's stamp holds its
slot, and the child sits in that slot. Splice-and-lift erases the
ancestor and re-ranks the child among its new siblings by the child's
OWN stamp. Whenever a concurrent sibling's stamp lies strictly between
the dead ancestor's and the child's, the two rankings disagree, and no
trace of the disagreement survives in the spliced state.

**The pair (Lamport-honest: the crossing rides on concurrency).** Both
worlds share the LCA (`ins a` stamp 1) and branch B (`ins c` stamp 2 at
the root: B saw only the LCA, so any stamp above 1 is honest, and `c` is
concurrent with everything on A). Only branch A differs. World 1: A
inserts `b` (stamp 5) under `a`, then deletes `a` (stamp 6); the splice
lifts `b` to the root. World 2: A deletes `a` (stamp 4), then inserts
`b` (stamp 5) at the root directly. Both A states are the one-node
forest `[b(5)]`: machine-checked equal; the representation has
forgotten, in world 1, that `b` occupies a slot keyed 1. Every stamp
exceeds everything its issuer observed (1 < 5 < 6; 1 < 4 < 5; 1 < 2
with `c` concurrent to A), so both worlds are honest. But the embed RGA
(the oracle, its read computed by `eFold` below) requires `[c, b]` in
world 1 (`b` ranks at dead `a`'s stamp 1, losing to `c`'s 2) and
`[b, c]` in world 2 (`b` ranks at its own stamp 5, winning). A merge
function sees identical arguments and owes different answers: there is
none. The knob: `a < c < b`, with `b` and `c` on different branches.

**What this does and does not say.** It kills sibling edges *without
retention* (the rose-tree splice, the state here being Shesha's own
`List Tree` with its splice delete: the sibling-edge story and the
rose-tree story are the same story). It does not touch the validated
sibling-edge design with carried spine paths: that design retains the
dead ancestor's key inside the path, which is the same memory the embed
keeps, in different clothes. The moral is the retention thesis with a
sharper edge: the living must remember the coordinates of the dead they
displaced, and a splice that re-keys the lifted child is not
timestamp-faithful. Choosing WHERE that memory lives (coordinate
prefixes, spine paths, tombstones) is an encoding decision; whether it
lives is not.

SPOT convention (PASS and FAIL): the state equalities and both oracle
reads are the hand-derived PASS pins; the oracle disagreement is the
FAIL pin; the headline theorem quantifies over every merge function.
-/

namespace SiblingSpliceFooling

open Shesha Shesha.Op
open Sal.Emulation
open Sal.EmbedRGA (unaryCode)
open Sal.ConditionedMRDTs

/-! ## The two worlds on the splice representation (Shesha's own forest) -/

/-- The shared LCA: `a`(1) at the root. -/
def wL : St := fold [ins 1 0]

/-- World 1 branch A: `b`(5) under `a`, then delete `a` (splice lifts
`b` to the root). -/
def w1A : St := steps wL [ins 5 1, del 1]

/-- World 2 branch A: delete `a` (childless splice), then `b`(5) at the
root directly. -/
def w2A : St := steps wL [del 1, ins 5 0]

/-- The shared branch B: `c`(2) at the root, concurrent with A. -/
def wB : St := steps wL [ins 2 0]

/-- PASS pin: the two branch-A states are EQUAL, one node `[5]` each.
The representation has forgotten that world 1's `b` occupies dead `a`'s
slot. -/
theorem states_equal_A : w1A = w2A := by native_decide

/-! ## The oracle: the embed RGA's own fold on the twin histories

Elements `101/105/102` stand for `a/b/c`; ids are the stamps `1/5/2`;
world 1's `b` carries `a`'s coordinate as its prefix (the retention the
splice lacks); the delete stamps `6`/`4` are Lamport-honest on branch A. -/

def ρ₁ : List (Op (EOp ℕ)) :=
  [ (1, 0, .ins 101 [] 0)
  , (5, 0, .ins 105 (unaryCode.enc 1) 1)
  , (6, 0, .del 1)
  , (2, 1, .ins 102 [] 0) ]

def ρ₂ : List (Op (EOp ℕ)) :=
  [ (1, 0, .ins 101 [] 0)
  , (4, 0, .del 1)
  , (5, 0, .ins 105 [] 0)
  , (2, 1, .ins 102 [] 0) ]

/-- PASS pin (hand-derived): world 1 reads `[c, b]`: `b`'s coordinate
begins with dead `a`'s code, so it ranks at `a`'s stamp 1 and `c`(2)
precedes it. -/
theorem embed_read_w1 :
    (eFold unaryCode ρ₁).map (fun r => r.2.1) = [102, 105] := by
  native_decide

/-- PASS pin (hand-derived): world 2 reads `[b, c]`: `b` ranks by its own
stamp 5 and precedes `c`(2). -/
theorem embed_read_w2 :
    (eFold unaryCode ρ₂).map (fun r => r.2.1) = [105, 102] := by
  native_decide

/-- FAIL pin: the two worlds' required reads genuinely differ. -/
theorem embed_reads_differ :
    (eFold unaryCode ρ₁).map (fun r => r.2.1) ≠
    (eFold unaryCode ρ₂).map (fun r => r.2.1) := by
  native_decide

/-! ## The impossibility -/

/-- **Sibling edges without retention cannot implement the embed RGA.**
No ternary merge function on the splice representation produces the
embed RGA's read in both worlds: its arguments are equal (the LCA and
branch B are shared verbatim; the branch-A states by
`states_equal_A`) while the owed outputs differ
(`embed_reads_differ`). Quantified over every
`f : St → St → St → List ℕ`, the Shesha fooling-pair shape; both
worlds Lamport-honest. -/
theorem sibling_splice_no_merge_function (f : St → St → St → List ℕ) :
    ¬ (f wL w1A wB = (eFold unaryCode ρ₁).map (fun r => r.2.1) ∧
       f wL w2A wB = (eFold unaryCode ρ₂).map (fun r => r.2.1)) := by
  rintro ⟨h1, h2⟩
  rw [← states_equal_A] at h2
  exact embed_reads_differ (h1.symm.trans h2)

#print axioms sibling_splice_no_merge_function

end SiblingSpliceFooling
