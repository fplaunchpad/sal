import Sal.MRDTs.RGA_Tombstone_Free.RGA_Reachability_Invariant
import Sal.ConditionedMRDTs.Development.RGA_Faithful_PBT

/-!
# Merge = fold-of-linearization: the decisive refutation test for the tombstone-free RGA

**This file is a TEST HARNESS, not a soundness-critical proof.**  It is the
DECISIVE experiment for whether the tombstone-free RGA can be verified
end-to-end: does the three-way `merge l a b` observationally equal a fold of a
*linearization* of the two branches' events over `l`?

    merge l a b  ≟  applySeqR l π      where π interleaves Ea (l→a) and Eb (l→b)

If merge fails to equal any tested fold, the end-to-end SEC design is wrong and
finding it now saves the M1–M4 investment; if it holds across the corner cases,
M-soundness is a proof problem, not a design problem.

Generator: reuses `RGAFaithfulPBT`'s reachable-state discipline (fold random
APPLICABLE ops from `init_st`, monotone id allocation via disjoint bands so
`fresh_ts`/`id_mono`/`accurate` all hold by construction).  The LCA `l` uses ids
[1,100); branch `a` uses [1000,2000); branch `b` uses [2000,3000).  Both branches
start from `l`'s live set, so they can delete the *same* LCA node and anchor
under LCA nodes the other branch removes — the shared-delete and cross-branch
anchor corners arise naturally, and are also pinned by hand SPOTs below.

`π` families:
* **lo-respecting** — merges of Ea and Eb that preserve each branch's internal
  order (all-Ea-first, all-Eb-first, random order-preserving interleavings);
* **arbitrary** — full seeded shuffles of `Ea ++ Eb`, which may violate a
  branch's causal order (insert-child before insert-parent) and are EXPECTED to
  sometimes diverge.

Everything here is `#eval`/`native_decide` scaffolding.  No real `sorry`.
-/

set_option maxHeartbeats 1000000

namespace RGAMergeFoldPBT

open RGAFaithfulPBT   -- reuse `pathOf`, `nextRand`

/-! ## 1. Fold of a linearization, and the Bool observational-eq checker -/

/-- Apply an event list left-to-right over `l` (a linearization fold). -/
def applySeqR (s : concrete_st) (evs : List op_t) : concrete_st := evs.foldl do_ s

/-- `Bool` mirror of `eq` (observational), restricted to a finite candidate id
set.  Sound because both `merge` and any fold only ever store allocated ids and
never store `0`, so ids outside the candidate set are absent in both. -/
def eqB (m f : concrete_st) (ids : List ℕ) : Bool :=
  ids.all (fun k => (contains m k == contains f k) && (!contains m k || (sel m k == sel f k)))

/-! ## 2. Reachable branch generator (monotone ids, applicable ops) -/

/-- A branch build: current state, live ids (most-recent first), next id, events
in application order, and all created ids (for the eqB candidate set). -/
structure BR where
  s    : concrete_st
  live : List ℕ
  ctr  : ℕ
  evs  : List op_t
  ids  : List ℕ

/-- One applicable step.  `delEvery = 0` disables deletes; otherwise a delete
fires when `rnd % delEvery == 0` and something is live.  `chain = true` anchors
inserts at the most-recent live node (builds a deep chain); else a random anchor
in `{0} ∪ live`.  Ids are allocated from `ctr`, strictly above every live id, so
every stored anchor is `0`-or-smaller-id (`id_mono`) and every path is accurate. -/
def brStep (delEvery : ℕ) (chain : Bool) (r : BR) (rnd : ℕ) : BR :=
  if delEvery != 0 && rnd % delEvery == 0 && !r.live.isEmpty then
    let x := r.live.getD ((rnd / 2) % r.live.length) 0
    let pth := pathOf r.s 300 x
    let o : op_t := (0, 0, .Del pth x)
    { r with s := do_ r.s o, live := r.live.filter (· != x), evs := r.evs ++ [o] }
  else
    let anchor :=
      if chain then r.live.headD 0
      else ((0 : ℕ) :: r.live).getD ((rnd / 2) % (r.live.length + 1)) 0
    let pth := pathOf r.s 300 anchor
    let t := r.ctr
    let o : op_t := (t, 0, .Ins ((t * 7) % 97) pth anchor)
    { r with s := do_ r.s o, live := t :: r.live, ctr := r.ctr + 1,
             evs := r.evs ++ [o], ids := t :: r.ids }

def runBranch (delEvery : ℕ) (chain : Bool) (r0 : BR) (seed len : ℕ) : BR :=
  ((List.range len).foldl
    (fun (acc : BR × ℕ) _ => let r := nextRand acc.2; (brStep delEvery chain acc.1 r, r))
    (r0, seed)).1

structure Mode where
  lcaLen      : ℕ
  lcaDelEvery : ℕ
  brLen       : ℕ
  brDelEvery  : ℕ
  chain       : Bool

/-- Build a triple `(l, a, b, Ea, Eb, candidateIds)` from a seed.  Both branches
fork from `l`'s live set; disjoint id bands keep allocation globally monotone. -/
def genTriple (mode : Mode) (seed : ℕ) :
    concrete_st × concrete_st × concrete_st × List op_t × List op_t × List ℕ :=
  let lca := runBranch mode.lcaDelEvery mode.chain ⟨init_st, [], 1, [], []⟩ (seed + 101) mode.lcaLen
  let l := lca.s
  let brA := runBranch mode.brDelEvery mode.chain ⟨l, lca.live, 1000, [], []⟩ (seed + 202) mode.brLen
  let brB := runBranch mode.brDelEvery mode.chain ⟨l, lca.live, 2000, [], []⟩ (seed + 303) mode.brLen
  (l, brA.s, brB.s, brA.evs, brB.evs, 0 :: (lca.ids ++ brA.ids ++ brB.ids))

/-! ## 3. Interleavings -/

/-- Order-preserving (lo-respecting) interleave driven by a random bitstream. -/
def interleaveLO : ℕ → ℕ → List op_t → List op_t → List op_t
  | 0,     _,    xs,      ys      => xs ++ ys
  | _,     _,    [],      ys      => ys
  | _,     _,    xs,      []      => xs
  | fuel+1, seed, x :: xs, y :: ys =>
      let r := nextRand seed
      if r % 2 == 0 then x :: interleaveLO fuel r xs (y :: ys)
      else y :: interleaveLO fuel r (x :: xs) ys

def removeIdx : List op_t → ℕ → Option op_t × List op_t
  | [],      _     => (none, [])
  | x :: xs, 0     => (some x, xs)
  | x :: xs, n + 1 => let (o, rest) := removeIdx xs n; (o, x :: rest)

/-- Full seeded shuffle (may break causal order within a branch). -/
def shuffle : ℕ → ℕ → List op_t → List op_t
  | 0,      _,    l  => l
  | _,      _,    [] => []
  | fuel+1, seed, l  =>
      let r := nextRand seed
      match removeIdx l (r % l.length) with
      | (some x, rest) => x :: shuffle fuel r rest
      | (none,   rest) => rest

def loInterleavings (seed : ℕ) (ea eb : List op_t) : List (List op_t) :=
  let f := ea.length + eb.length
  [ ea ++ eb, eb ++ ea,
    interleaveLO f (seed + 1) ea eb,
    interleaveLO f (seed + 2) ea eb,
    interleaveLO f (seed + 3) ea eb ]

def arbInterleavings (seed : ℕ) (ea eb : List op_t) : List (List op_t) :=
  let all := ea ++ eb
  let f := all.length
  [ shuffle f (seed + 10) all, shuffle f (seed + 11) all, shuffle f (seed + 12) all ]

/-! ## 4. Per-triple check and batch aggregation

`checkList` returns `[loPass, loTried, arbPass, arbTried, loFullTriple, 1]`,
where `loFullTriple = 1` iff EVERY lo-respecting fold matched merge for this
triple.  A refutation shows up as `loPass < loTried` (i.e. `loFullTriple = 0`). -/

def checkTriple (mode : Mode) (seed : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let (l, a, b, ea, eb, ids) := genTriple mode seed
  let M := merge l a b
  let los := loInterleavings seed ea eb
  let arbs := arbInterleavings seed ea eb
  ( (los.filter (fun π => eqB M (applySeqR l π) ids)).length, los.length,
    (arbs.filter (fun π => eqB M (applySeqR l π) ids)).length, arbs.length )

def checkList (mode : Mode) (seed : ℕ) : List ℕ :=
  let (lp, lt, ap, at') := checkTriple mode seed
  [lp, lt, ap, at', (if lp == lt then 1 else 0), 1]

def batch (mode : Mode) (n : ℕ) : List ℕ :=
  ((List.range n).map (fun i => checkList mode (i * 2654435761 + 12345))).foldl
    (fun a b => List.zipWith (· + ·) a b) [0, 0, 0, 0, 0, 0]

/-! ### Modes -/

def insMode   : Mode := ⟨6, 0, 6, 0, false⟩   -- plain concurrent inserts (no deletes)
def mixMode   : Mode := ⟨6, 3, 7, 3, false⟩   -- inserts+deletes, shared targets
def delMode   : Mode := ⟨6, 2, 7, 2, false⟩   -- delete-heavy, shared targets
def chainMode : Mode := ⟨8, 0, 6, 2, true⟩    -- deep LCA chain; branches delete mid-chain + extend

/-! Format of each line: `[loPass, loTried, arbPass, arbTried, triplesAllLoPass, nTriples]`. -/
#eval ("insMode  ", batch insMode 150)
#eval ("mixMode  ", batch mixMode 150)
#eval ("delMode  ", batch delMode 150)
#eval ("chainMode", batch chainMode 150)

/-! ## 5. Hand SPOTs at the named corners

`spotBools l Ea Eb ids = [ eq merge (fold Ea++Eb), eq merge (fold Eb++Ea) ]`. -/

def spotBools (l : concrete_st) (ea eb : List op_t) (ids : List ℕ) : List Bool :=
  let M := merge l (applySeqR l ea) (applySeqR l eb)
  [ eqB M (applySeqR l (ea ++ eb)) ids, eqB M (applySeqR l (eb ++ ea)) ids ]

/-- SPOT A — shared delete: both branches delete the SAME LCA node `2`
(the survival-set corner). `l = 0→1→2→3`; `3` rehomes to `1` in both orders. -/
def lA : concrete_st := mk [(1,10,0),(2,20,1),(3,30,2)]
def eaA : List op_t := [(0,0,.Del [1] 2)]
def ebA : List op_t := [(0,0,.Del [1] 2)]

/-- SPOT B — cross-branch anchor (the hardest): `a` inserts a child under node
`2` while `b` deletes `2`. `l = 0→1→2`; the new node must land on `1` under both
LCA-climb (merge) and fold-resolve (delete rehoming + path climb). -/
def lB : concrete_st := mk [(1,10,0),(2,20,1)]
def eaB : List op_t := [(1000,0,.Ins 55 [1] 2)]
def ebB : List op_t := [(0,0,.Del [1] 2)]

/-- SPOT C — nested chain: `a` deletes a mid-chain node (`5`) while `b` inserts
under a deeper node (`3`). `chain = 0→7→5→3→9`. -/
def eaC : List op_t := [(0,0,.Del [7] 5)]
def ebC : List op_t := [(1000,0,.Ins 42 [5,7] 3)]

/-- SPOT D — staggered nested deletes: `a` deletes `5`, `b` deletes `3`; node `9`
must climb past both dead interior nodes to the live `7`. -/
def eaD : List op_t := [(0,0,.Del [7] 5)]
def ebD : List op_t := [(0,0,.Del [5,7] 3)]

#eval ("spotA shared-delete ", spotBools lA eaA ebA [0,1,2,3])
#eval ("spotB cross-anchor   ", spotBools lB eaB ebB [0,1,2,1000])
#eval ("spotC chain mid-del  ", spotBools chain eaC ebC [0,3,5,7,9,1000])
#eval ("spotD staggered dels ", spotBools chain eaD ebD [0,3,5,7,9])

/-- Machine-checked anchors for the corner SPOTs (both fold orders match merge). -/
theorem spotA_shared_delete : spotBools lA eaA ebA [0,1,2,3] = [true, true] := by native_decide
theorem spotB_cross_anchor  : spotBools lB eaB ebB [0,1,2,1000] = [true, true] := by native_decide
theorem spotC_chain_middel  : spotBools chain eaC ebC [0,3,5,7,9,1000] = [true, true] := by native_decide
theorem spotD_staggered     : spotBools chain eaD ebD [0,3,5,7,9] = [true, true] := by native_decide

end RGAMergeFoldPBT
