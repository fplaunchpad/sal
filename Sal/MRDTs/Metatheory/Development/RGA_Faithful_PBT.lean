import Sal.MRDTs.Metatheory.Development.RGA_BubbleWiring
import Sal.MRDTs.RGA_Tombstone_Free.RGA_Tombstone_Free_MRDT

/-!
# Property-based-testing + SPOT harness for the tombstone-free RGA

**This file is a TEST HARNESS, not a soundness-critical proof.**  It builds a
computable `Bool` mirror of `ChainFaithful`, a reachable-state generator, and runs
many random applicable op-sequences from `init_st` to gather empirical evidence for
(or a counterexample to) the two open risks:

* `chainFaithful_doDel` — `ChainFaithful` is preserved by an accurate `Del`;
* Faithful-threading — `ChainFaithful` of every op's `recList` survives along a full
  random valid op-sequence (Ins steps are proven; Del steps are the conjecture).

The only proved lemma here is `chainFaithfulB_iff`, certifying the `Bool` checker
faithfully matches the `ChainFaithfulAux`/`ChainFaithful` `Prop`.  Everything else is
`#eval`/`decide` test scaffolding, clearly separated.
-/

set_option maxHeartbeats 1000000

open Sal.Metatheory.RGABubbleWiring
open Sal.Metatheory.RGAGeneralSwap

namespace RGAFaithfulPBT

/-! ## 1. Computable `Bool` checkers -/

/-- `Bool` mirror of `IsAncPath` (structural on the list, matches the `Prop`). -/
def isAncPathB (s : concrete_st) : ℕ → List ℕ → Bool
  | leaf, []      => anc s leaf == 0
  | leaf, p :: ps => (anc s leaf == p) && contains s p && isAncPathB s p ps

/-- `Bool` mirror of `accurate` (matches the `Prop`'s two disjuncts). -/
def accurateB (o : op_t) (s : concrete_st) : Bool :=
  ((opLeaf o.2.2 == 0) && (opPath o.2.2).isEmpty) ||
    (contains s (opLeaf o.2.2) && isAncPathB s (opLeaf o.2.2) (opPath o.2.2))

/-- `Bool` mirror of `ChainFaithfulAux`, structurally identical to the `Prop`. -/
def chainFaithfulAuxB (s : concrete_st) : Nat → List ℕ → Bool
  | 0, _ => true
  | fuel + 1, L =>
      !(contains s (resolve s L)) ||
        ((resolve s (L.filter (fun c => c != resolve s L)) == anc s (resolve s L))
          && chainFaithfulAuxB s fuel (L.filter (fun c => c != resolve s L)))

/-- `Bool` mirror of `ChainFaithful`. -/
def chainFaithfulB (s : concrete_st) (L : List ℕ) : Bool := chainFaithfulAuxB s L.length L

/-! ### Correspondence: the `Bool` checker matches the `Prop` (the only real lemma) -/

theorem chainFaithfulAuxB_iff (s : concrete_st) :
    ∀ (fuel : Nat) (L : List ℕ),
      chainFaithfulAuxB s fuel L = true ↔ ChainFaithfulAux s fuel L := by
  intro fuel
  induction fuel with
  | zero =>
      intro L
      constructor
      · intro _; exact trivial
      · intro _; rfl
  | succ fuel ih =>
      intro L
      set v := resolve s L with hv
      set filt := L.filter (fun c => c != v) with hfilt
      have hB : chainFaithfulAuxB s (fuel + 1) L
          = (!(contains s v) || ((resolve s filt == anc s v) && chainFaithfulAuxB s fuel filt)) :=
        rfl
      have hP : ChainFaithfulAux s (fuel + 1) L
          = (contains s v = true → resolve s filt = anc s v ∧ ChainFaithfulAux s fuel filt) :=
        rfl
      rw [hB, hP]
      by_cases hc : contains s v = true
      · rw [hc]
        constructor
        · intro hb _
          simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hb
          exact ⟨hb.1, (ih filt).mp hb.2⟩
        · intro hp
          have hpp := hp rfl
          simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq]
          exact ⟨hpp.1, (ih filt).mpr hpp.2⟩
      · have hc' : contains s v = false := by
          cases h : contains s v with
          | true => exact absurd h hc
          | false => rfl
        rw [hc']
        constructor
        · intro _ h; exact absurd h (by simp)
        · intro _; simp

theorem chainFaithfulB_iff (s : concrete_st) (L : List ℕ) :
    chainFaithfulB s L = true ↔ ChainFaithful s L :=
  chainFaithfulAuxB_iff s L.length L

#print axioms chainFaithfulB_iff

/-! ## 2. The reachable-state generator

Folds APPLICABLE ops from `init_st`.  A running `(state, liveIds, counter)` triple
keeps ids monotone: every new `Ins` id is `counter`, strictly greater than every
live id, so `fresh_ts`, `id_mono`'s discipline (`mono_alloc`), and `accurate` all
hold by construction.  Hence every state produced is `wf ∧ id_mono ∧ contains 0 =
false` reachable — the true domain of the conditioned VC. -/

/-- Accurate ancestor chain of `x` in `s` (root-excluded, nearest first). -/
def pathOf (s : concrete_st) : Nat → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, x =>
      let p := anc s x
      if p = 0 then [] else p :: pathOf s fuel p

inductive Cmd where
  | ins : ℕ → Cmd
  | del : ℕ → Cmd

/-- A run: current reachable state, live ids, id counter, the `recList`s captured at
each op's birth, plus test counters.  `bFail`/`tFail*`/`aFail` count VIOLATIONS. -/
structure Run where
  s     : concrete_st
  live  : List ℕ
  ctr   : ℕ
  tracked : List (List ℕ)
  bChk  : ℕ   -- base-case checks:  chainFaithfulB (pre-state) (recList o)
  bFail : ℕ
  tChk  : ℕ   -- threading checks:  chainFaithfulB (post-state) L for all tracked L
  tFailIns : ℕ
  tFailDel : ℕ
  aChk  : ℕ   -- generator self-check: is each generated op accurate?
  aFail : ℕ

def initRun : Run := ⟨init_st, [], 1, [], 0, 0, 0, 0, 0, 0, 0⟩

def stepRun (r : Run) (c : Cmd) : Run :=
  match c with
  | Cmd.ins k =>
      let cands := (0 : ℕ) :: r.live
      let anchor := cands.getD (k % cands.length) 0
      let pth := pathOf r.s 200 anchor
      let t := r.ctr
      let o : op_t := (t, 0, .Ins ((t * 7) % 97) pth anchor)
      let rl := recList o
      let accOk := accurateB o r.s
      let bOk := chainFaithfulB r.s rl
      let s' := do_ r.s o
      let newTracked := rl :: r.tracked
      let failsHere := (newTracked.filter (fun L => !(chainFaithfulB s' L))).length
      { r with
        s := s', live := t :: r.live, ctr := r.ctr + 1, tracked := newTracked,
        bChk := r.bChk + 1, bFail := r.bFail + (if bOk then 0 else 1),
        tChk := r.tChk + newTracked.length, tFailIns := r.tFailIns + failsHere,
        aChk := r.aChk + 1, aFail := r.aFail + (if accOk then 0 else 1) }
  | Cmd.del k =>
      match r.live with
      | [] => r
      | _ =>
          let x := r.live.getD (k % r.live.length) 0
          let pth := pathOf r.s 200 x
          let o : op_t := (0, 0, .Del pth x)
          let rl := recList o
          let accOk := accurateB o r.s
          let bOk := chainFaithfulB r.s rl
          let s' := do_ r.s o
          let newTracked := rl :: r.tracked
          let failsHere := (newTracked.filter (fun L => !(chainFaithfulB s' L))).length
          { r with
            s := s', live := r.live.filter (fun y => y != x), ctr := r.ctr + 1,
            tracked := newTracked,
            bChk := r.bChk + 1, bFail := r.bFail + (if bOk then 0 else 1),
            tChk := r.tChk + newTracked.length, tFailDel := r.tFailDel + failsHere,
            aChk := r.aChk + 1, aFail := r.aFail + (if accOk then 0 else 1) }

/-! ### Deterministic pseudo-random command sequences (robust, no `Gen` plumbing) -/

def nextRand (x : ℕ) : ℕ := (x * 1103515245 + 12345) % 2147483648

/-- `len` commands from a seed; ~1/3 deletes, ~2/3 inserts. -/
def cmdsFromSeed (seed len : ℕ) : List Cmd :=
  ((List.range len).foldl
    (fun (acc : List Cmd × ℕ) _ =>
      let r := nextRand acc.2
      let c := if r % 3 == 0 then Cmd.del (r / 3) else Cmd.ins (r / 3)
      (acc.1 ++ [c], r)) ([], seed + 7919)).1

def runSeed (seed len : ℕ) : Run := (cmdsFromSeed seed len).foldl stepRun initRun

/-! ## 3a. Threading test (base-case b-i + end-to-end b-ii) + generator self-check

Returns `[bChk, bFail, tChk, tFailIns, tFailDel, aChk, aFail]`. -/
def runSeedC (seed len : ℕ) : List ℕ :=
  let r := runSeed seed len
  [r.bChk, r.bFail, r.tChk, r.tFailIns, r.tFailDel, r.aChk, r.aFail]

def sumLists (ls : List (List ℕ)) : List ℕ :=
  ls.foldl (fun a b => List.zipWith (· + ·) a b) [0, 0, 0, 0, 0, 0, 0]

/-! 200 seeds × 12 commands.  Format:
`[baseChecks, baseFails, threadChecks, threadFailsIns, threadFailsDel, accChecks, accFails]`. -/
#eval sumLists ((List.range 200).map (fun i => runSeedC (i * 2654435761 + 12345) 12))

/-! Wider/deeper: 120 seeds × 20 commands. -/
#eval sumLists ((List.range 120).map (fun i => runSeedC (i * 40503 + 99991) 20))

/-! ## 3b. Standalone `chainFaithful_doDel` test (risk a)

At each seed's final reachable state `s`: take every candidate list `L` that is
currently `chainFaithfulB s L = true` (tracked staled `recList`s ∪ every live node's
accurate chain), apply an accurate `Del` of every live node, and check
`chainFaithfulB (do_ s Del) L = true`.  Returns `(checksA, failsA)`. -/
def testA_oneState (r : Run) : ℕ × ℕ :=
  let s := r.s
  let liveChains := r.live.map (fun y => y :: pathOf s 200 y)
  let cands := (r.tracked ++ liveChains).filter (fun L => chainFaithfulB s L)
  r.live.foldl (fun (acc : ℕ × ℕ) x =>
    let o : op_t := (0, 0, .Del (pathOf s 200 x) x)
    let s' := do_ s o
    cands.foldl (fun (a2 : ℕ × ℕ) L =>
      (a2.1 + 1, a2.2 + (if chainFaithfulB s' L then 0 else 1))) acc) (0, 0)

def testA (seeds len : ℕ) : ℕ × ℕ :=
  (List.range seeds).foldl (fun (acc : ℕ × ℕ) i =>
    let r := runSeed (i * 2654435761 + 777) len
    let p := testA_oneState r
    (acc.1 + p.1, acc.2 + p.2)) (0, 0)

/-! risk (a): `(totalChecks, totalFailures)` — failures must be 0. -/
#eval testA 200 12

/-! ## 4. Hand SPOTs at the scary shapes (kernel `decide`) -/

/-! ### SPOT 0 (confirmatory): the exact config where `ClimbFaithful` FAILS under Del.
`sCex`, `Lcex`, `delOp` come from `climbFaithful_not_preserved_under_del`.  There
`ClimbFaithful sCex Lcex` holds but fails after `delOp`.  `ChainFaithful` is the
corrected invariant: it must REJECT `Lcex` (which is chain-wrong below the deleted
node), so `chainFaithful_doDel`'s hypothesis never applies to this config. -/

/-- `ChainFaithful` correctly EXCLUDES the pathological list `Lcex = [3,2,5]`
(chain-wrong below `2`: records `5`, not `2`'s true parent `1`). -/
theorem spot0_chainFaithful_rejects_Lcex : chainFaithfulB sCex Lcex = false := by decide

/-- The corrected, genuinely chain-faithful list `[3,2,1]` (node `3`'s true chain)
IS accepted, AND IS PRESERVED under the same accurate `delOp` that broke
`ClimbFaithful`.  This is the positive confirmation `ChainFaithful` is delete-stable
exactly where `ClimbFaithful` was not. -/
theorem spot0_chainFaithful_holds_true_chain : chainFaithfulB sCex [3, 2, 1] = true := by decide
theorem spot0_chainFaithful_preserved : chainFaithfulB (do_ sCex delOp) [3, 2, 1] = true := by decide

/-! ### SPOT 1 (chain-merge): delete a mid-chain node collapsing two anc-levels.
`chain = root→7→5→3→9`.  Track node `9`'s list `[9,3,5,7]`; delete `5` (accurate,
path `[7]`), which reparents `3` to `7`, merging levels `5` and `7`. -/
theorem spot1_before : chainFaithfulB chain [9, 3, 5, 7] = true := by decide
theorem spot1_after_del5 :
    chainFaithfulB (do_ chain (0, 0, .Del [7] 5)) [9, 3, 5, 7] = true := by decide

/-! ### SPOT 2 (deep delete): delete the deep interior `3` (path `[5,7]`). -/
theorem spot2_after_del3 :
    chainFaithfulB (do_ chain (0, 0, .Del [5, 7] 3)) [9, 3, 5, 7] = true := by decide

/-! ### SPOT 3 (multi-delete staling): delete `5` then `3`; `[9,3,5,7]` stays faithful.
After deleting `5`, node `3`'s accurate path is `[7]` (it rehomed to `7`). -/
theorem spot3_multidel :
    chainFaithfulB (do_ (do_ chain (0, 0, .Del [7] 5)) (0, 0, .Del [7] 3)) [9, 3, 5, 7] = true := by
  decide

/-! Non-vacuity #eval: confirm the SPOT lists actually exercise live climb-targets
(not trivially true via a dead head). Format: pairs of (before, after) Bool. -/
#eval ( (chainFaithfulB sCex Lcex, chainFaithfulB (do_ sCex delOp) Lcex)          -- (false, ...)
      , (chainFaithfulB chain [9,3,5,7], chainFaithfulB (do_ chain (0,0,.Del [7] 5)) [9,3,5,7]) )

end RGAFaithfulPBT
