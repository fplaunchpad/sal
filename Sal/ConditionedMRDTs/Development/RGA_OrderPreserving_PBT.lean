import Sal.ConditionedMRDTs.Development.RGA_OrderPreserving_Reference

/-!
# Property-based-testing harness for the order-preserving reference model

**Test harness, not a soundness-critical proof.** This file stress-tests the
`RGA_OrderPreserving` reference model (`RGA_OrderPreserving_Reference.lean`) with
genuine Plausible random sampling + shrinking, actively hunting for a concurrent
counterexample — above all to **merge convergence**, the one property that is not
a fully general theorem in the model file.

## Reachability discipline (critical)

Random `Node` lists with arbitrary `pos` are NOT reachable states and would give
bogus counterexamples. Every state here is built by folding a random command
sequence from the empty state: inserts allocate a fresh unique id/timestamp
(monotone counter) and anchor on `0` or an already-live id; deletes target a
currently-live id. For merges we build a shared LCA, then two independent branch
extensions with **disjoint id bands** (LCA `1..`, branch A `10000..`, branch B
`20000..`) so ids are globally unique and shared ids carry identical content
across branches — exactly the reachable-branch shape `merge3` is meant to face.

## Checker

`runCheck` mirrors `Plausible.Testable.check` (same `mk_decorations` +
`[Testable p']` signature, so we get real sampling and shrinking) but **reports**
the outcome via `IO.println` instead of throwing — a found counterexample is
printed loudly and the file still builds. A deterministic high-volume `#eval`
batch (a PRNG, no Plausible) backstops the sampled checks with larger case counts.

## Properties tested

1. `delete_order_preserving` over random reachable states (belt-and-suspenders;
   it is a proved theorem in the model file).
2. **merge3 convergence** `read (merge3 L A B) = read (merge3 L B A)` — most
   important.
3. **merge3 order-preservation**: no survivor pair present in both a branch and
   the merge is swapped (relative order of the common ids agrees).
4. non-interleaving of two concurrent same-anchor runs.

Read the `#eval` output lines: `[PASS]` = no counterexample found;
`[COUNTEREXAMPLE]` = a failing shrunk instance (report it).
-/

set_option maxHeartbeats 1000000

open RGA_OrderPreserving
open Plausible Plausible.Decorations

namespace RGA_OrderPreserving_PBT

/-! ## 1. Reachable-state generator -/

/-- A branch build in progress: current state, live ids (newest first), and the
strictly-increasing id/timestamp counter. -/
structure Br where
  s : St
  live : List ℕ
  ctr : ℕ

/-- One reachable step from a raw random `ℕ`: ~1/3 deletes (of a live id),
otherwise a fresh insert anchored at `0` or a random live id. The new id and
timestamp are `ctr`, strictly above every live id — so positions are always
distinct and every anchor resolves. -/
def brStep (r : Br) (cmd : ℕ) : Br :=
  if cmd % 3 == 0 && !r.live.isEmpty then
    let x := r.live.getD ((cmd / 3) % r.live.length) 0
    { r with s := del r.s x, live := r.live.filter (· != x) }
  else
    let anchors := (0 : ℕ) :: r.live
    let anchor := anchors.getD ((cmd / 3) % anchors.length) 0
    let t := r.ctr
    { s := insert r.s t ((t * 7) % 97) t anchor, live := t :: r.live, ctr := r.ctr + 1 }

def buildBr (start : Br) (cmds : List ℕ) : Br := cmds.foldl brStep start

/-- A single reachable state from a random command list. -/
def genState (cmds : List ℕ) : St := (buildBr ⟨[], [], 1⟩ cmds).s

/-- LCA + two independent branch extensions, disjoint id bands. -/
def genTriple (lc ac bc : List ℕ) : St × St × St :=
  let L := buildBr ⟨[], [], 1⟩ lc
  let A := buildBr ⟨L.s, L.live, 10000⟩ ac
  let B := buildBr ⟨L.s, L.live, 20000⟩ bc
  (L.s, A.s, B.s)

/-! ## 2. Order-relation checkers (Bool) -/

/-- The common ids of `r1` and `r2` appear in the same relative order in each
(no swap of a pair present in both). -/
def commonConsistent (r1 r2 : List ℕ) : Bool :=
  (r1.filter (fun i => r2.contains i)) == (r2.filter (fun i => r1.contains i))

/-- The ids of the two runs form contiguous, non-interleaved blocks in `rm`. -/
def noInterleave (rm sa sb : List ℕ) : Bool :=
  let sub := rm.filter (fun i => sa.contains i || sb.contains i)
  (sub == sub.filter (fun i => sa.contains i) ++ sub.filter (fun i => sb.contains i)) ||
  (sub == sub.filter (fun i => sb.contains i) ++ sub.filter (fun i => sa.contains i))

/-- Build a chain of `n` inserts, each anchored on the previously inserted node
(so the whole run shares an anchor prefix). Returns the branch and the run ids. -/
def buildChain : Br → ℕ → ℕ → Br × List ℕ
  | r, _, 0 => (r, [])
  | r, anchor, (n + 1) =>
      let t := r.ctr
      let r' : Br := ⟨insert r.s t ((t * 7) % 97) t anchor, t :: r.live, r.ctr + 1⟩
      let (r'', ids) := buildChain r' t n
      (r'', t :: ids)

/-- LCA with one node `a (id 1)`; two concurrent chains anchored under `a`.
Returns `(mergedRead, aRunIds, bRunIds)`. -/
def genRuns (lenA lenB : ℕ) : List ℕ × List ℕ × List ℕ :=
  let L : St := insert ([] : St) 1 10 1 0
  let (A, sa) := buildChain ⟨L, [1], 10000⟩ 1 lenA
  let (B, sb) := buildChain ⟨L, [1], 20000⟩ 1 lenB
  (read (merge3 L A.s B.s), sa, sb)

/-! ## 3. Non-throwing Plausible harness

`runCheck` is `Plausible.Testable.check` with the throw on counterexample
replaced by an `IO.println` report, so counterexamples are surfaced without
failing the build. -/

def runCheck (name : String) (p : Prop) (cfg : Configuration := {})
    (p' : DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit := do
  match ← Testable.checkIO p' cfg with
  | .success _ =>
      IO.println s!"[PASS] {name} — no counterexample in {cfg.numInst} cases"
  | .gaveUp n =>
      IO.println s!"[gaveUp {n}] {name} — could not generate enough valid cases"
  | .failure _ xs n =>
      IO.println s!"[✗ COUNTEREXAMPLE] {name} (shrunk {n}×): {String.intercalate "  |  " xs}"

/-! ## 4. Sampled checks (Plausible, with shrinking) -/

-- 1. delete-order-preservation over random reachable states.
#eval runCheck "prop1 delete-order-preserving (random reachable states)"
  (∀ (cmds : List ℕ) (x : ℕ),
    read (del (genState cmds) x) = (read (genState cmds)).filter (· != x))
  { numInst := 400, maxSize := 40, randomSeed := some 1 }

-- 2. merge3 CONVERGENCE (the decisive test). Two seeds.
#eval runCheck "prop2 merge3 convergence  read(merge L A B) = read(merge L B A)"
  (∀ (lc ac bc : List ℕ),
    (let (L, A, B) := genTriple lc ac bc; read (merge3 L A B))
      = (let (L, A, B) := genTriple lc ac bc; read (merge3 L B A)))
  { numInst := 500, maxSize := 28, randomSeed := some 2 }

#eval runCheck "prop2 merge3 convergence  (second seed, delete-heavy sizes)"
  (∀ (lc ac bc : List ℕ),
    (let (L, A, B) := genTriple lc ac bc; read (merge3 L A B))
      = (let (L, A, B) := genTriple lc ac bc; read (merge3 L B A)))
  { numInst := 500, maxSize := 36, randomSeed := some 314159 }

-- 3. merge3 preserves each branch's survivor order (no swap).
#eval runCheck "prop3 merge3 order-preservation vs both branches"
  (∀ (lc ac bc : List ℕ),
    (let (L, A, B) := genTriple lc ac bc
     commonConsistent (read (merge3 L A B)) (read A)
       && commonConsistent (read (merge3 L A B)) (read B)) = true)
  { numInst := 500, maxSize := 30, randomSeed := some 7 }

-- 4. non-interleaving of concurrent same-anchor runs.
#eval runCheck "prop4 non-interleaving of concurrent same-anchor runs"
  (∀ (la lb : ℕ),
    (let (m, sa, sb) := genRuns (la % 7) (lb % 7); noInterleave m sa sb) = true)
  { numInst := 400, maxSize := 60, randomSeed := some 5 }

/-! ## 5. Deterministic high-volume batch backstop (no Plausible, never throws)

A linear-congruential PRNG drives large case counts; each line reports
`(passes, total)` and `failures`. This complements the sampled checks with
volume and is fully reproducible. -/

def nextRand (x : ℕ) : ℕ := (x * 1103515245 + 12345) % 2147483648

/-- `len` raw random commands from a seed. -/
def randCmds (seed len : ℕ) : List ℕ :=
  ((List.range len).foldl
    (fun (acc : List ℕ × ℕ) _ => let r := nextRand acc.2; (acc.1 ++ [r], r)) ([], seed + 7919)).1

/-- Per-seed: [prop1 ok, prop2 ok, prop3 ok, 1] as 0/1 flags. -/
def checkSeed (i : ℕ) : List ℕ :=
  let cmds := randCmds (i * 2654435761 + 1) ((i % 10) + 3)
  let lc := randCmds (i * 40503 + 11) ((i % 7) + 2)
  let ac := randCmds (i * 69069 + 22) ((i % 6) + 3)
  let bc := randCmds (i * 30011 + 33) ((i % 6) + 3)
  let (L, A, B) := genTriple lc ac bc
  let mAB := read (merge3 L A B)
  let mBA := read (merge3 L B A)
  let p1 := decide (read (del (genState cmds) 3) = (read (genState cmds)).filter (· != 3))
  let p2 := mAB == mBA
  let p3 := commonConsistent mAB (read A) && commonConsistent mAB (read B)
  [ (if p1 then 1 else 0), (if p2 then 1 else 0), (if p3 then 1 else 0), 1 ]

def batch (n : ℕ) : List ℕ :=
  ((List.range n).map checkSeed).foldl (fun a b => List.zipWith (· + ·) a b) [0, 0, 0, 0]

/-! Format: `[prop1Pass, prop2Pass(convergence), prop3Pass, totalSeeds]`. -/
#eval ("batch 3000 [p1, p2-convergence, p3, total]: ", batch 3000)

/-! Non-interleaving batch: `(passes, total)` over concurrent-run length pairs. -/
#eval ("prop4 non-interleave batch (pass, total): ",
  ((List.range 40).foldl (fun (acc : ℕ × ℕ) a =>
    (List.range 40).foldl (fun (acc2 : ℕ × ℕ) b =>
      let (m, sa, sb) := genRuns (a % 7) (b % 7)
      (acc2.1 + (if noInterleave m sa sb then 1 else 0), acc2.2 + 1)) acc) (0, 0)))

end RGA_OrderPreserving_PBT
