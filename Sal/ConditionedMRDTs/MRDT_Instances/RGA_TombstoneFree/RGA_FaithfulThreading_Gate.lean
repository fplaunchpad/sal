import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_StaledDel_Gate

/-!
# The decisive Faithful-threading gate for the free-canonicalization bubble

Does a `loOnA`-respecting reordering keep every op `Faithful` at its prefix fold?
Two parts feed the bubble's incomparable swap:

* **(T1)** Along a `loOnA`-respecting enumeration of a backward-closed reachable
  event set, at every prefix fold the next op is `Faithful` (equivalently: every
  event's `recList` stays `ChainFaithful`).
* **(T2)** For `loOnA`-incomparable adjacent `a,b`, applying `a` does not destroy
  `b`'s `Faithful`-ness.

## Method

`loOnA`-respecting linear extensions of a backward-closed reachable set are
generated CONCRETELY as interleavings of two genuinely-concurrent replica
executions `R1 ⊥ R2` forked from a shared past `P`:

* `P` : a common accurate prefix (ids `1,2,…`), forked by both replicas;
* `R1`: accurate ops on id band `[1000,2000)` (replica tag `1`);
* `R2`: accurate ops on id band `[2000,3000)` (replica tag `2`).

Disjoint id bands give monotone allocation across replicas (`id_mono`,
`fresh_ts`, `NoFreshClash` all hold by construction), and both replicas fork the
SAME shared tree, so their recorded paths agree on shared structure — exactly the
"backward-closed reachable" regime.  Any `P ++ interleave R1 R2` is a linear
extension of the vis order; adjacent `R1`/`R2` (tag `1` vs `2`) transpositions
are `loOnA`-incomparable (concurrent, and `rc = Either` kills the rc-edges).

`faithfulB`/`chainFaithfulB` are the Bool mirrors of `Faithful`/`ChainFaithful`
(`chainFaithfulB` is proven equivalent in `RGA_Faithful_PBT.lean`).

## VERDICT (fork selected: free bubble reaches stage-1 convergence)

Across 330 scenarios × 6 interleavings each (`[aFail, t1NextFails, t1EnabledFails,
t1EnabledChainFails, t1StrongFails, t2Fails, convFails]`):

    [0, 0, 0, 0, 903,  0, 0]
    [0, 0, 0, 0, 1971, 0, 0]
    [0, 0, 0, 0, 2013, 0, 0]

* **T1 holds** in the form the bubble consumes (`t1NextFails = 0`,
  `t1EnabledFails = 0`, and — the decisive one — `t1EnabledChainFails = 0`: the
  Del-STABLE `ChainFaithful` of each event's `recList` holds at every enablement
  fold).  **T2 holds** (`t2Fails = 0`).  **Convergence holds** (`convFails = 0`).
* **KEY REFINEMENT.**  The *all-events-at-all-prefixes* invariant is genuinely
  FALSE (`t1StrongFails ≠ 0`) — but only transiently, while a pending event's
  ancestors are still being folded in.  Scoping to ENABLED events (causal past
  folded) — the only events the bubble ever swaps — repairs it.  This is exactly
  why the earlier `RGA_ConditionedConvergence` obstruction note stalled: it tried
  to thread `ChainFaithful` for ALL pending events at ALL hybrid states.
* §6 discharges the positive content as kernel-clean theorems; the lone residual
  (an enablement base case) is a reachability-invariant lemma, i.e. the deferred
  engineering tail — NOT a semantic wall.  See §6's residual note.

This file is additive test scaffolding + a small proved core; no existing file is
modified and no `sorry` is introduced.
-/

set_option maxHeartbeats 1000000

open Sal.ConditionedMRDTs.RGABubbleWiring (recList ChainFaithful)
open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful ClimbFaithful DelTargetFaithful)
open RGAFaithfulPBT

namespace RGAFaithfulThreadingGate

/-! ## 1. `Faithful` Bool mirror (test scaffolding) -/

/-- Bool mirror of `ClimbFaithful`. -/
def climbFaithfulB (s : concrete_st) (L : List ℕ) : Bool :=
  !(contains s (resolve s L)) ||
    (resolve s (L.filter (fun c => c != resolve s L)) == anc s (resolve s L))

/-- Bool mirror of `DelTargetFaithful`. -/
def delTargetFaithfulB (s : concrete_st) (pa : List ℕ) (xa : ℕ) : Bool :=
  !(contains s xa) || (resolve s pa == anc s xa)

/-- Bool mirror of `Faithful` (Ins: `ClimbFaithful` of `anch::pre`; Del:
`ClimbFaithful pre ∧ DelTargetFaithful pre x ∧ x ≠ 0`). -/
def faithfulB (o : op_t) (s : concrete_st) : Bool :=
  match o with
  | (_, _, .Ins _ pre a) => climbFaithfulB s (a :: pre)
  | (_, _, .Del pre x)   => climbFaithfulB s pre && delTargetFaithfulB s pre x && (x != 0)

/-- Concrete fold (defeq the σ-layer `applySeqR`). -/
def foldDo (s : concrete_st) (π : List op_t) : concrete_st := π.foldl do_ s

/-- Observational-`eq` Bool mirror on a finite id list. -/
def eqB (s s' : concrete_st) (ids : List ℕ) : Bool :=
  ids.all (fun k => (contains s k == contains s' k) && (!(contains s k) || (sel s k == sel s' k)))

/-! ## 2. Two-replica concurrent generator (backward-closed reachable) -/

structure Gen where
  s     : concrete_st
  live  : List ℕ
  ctr   : ℕ
  ops   : List op_t
  aFail : ℕ   -- generator self-check: was each generated op accurate at birth?

/-- One accurate step for replica-tag `rid`.  `Ins` allocates the running `ctr`
(monotone within its band); `Del` picks a live node and its accurate path. -/
def genStep (rid : ℕ) (g : Gen) (c : Cmd) : Gen :=
  match c with
  | Cmd.ins k =>
      let cands := (0 : ℕ) :: g.live
      let anchor := cands.getD (k % cands.length) 0
      let pth := pathOf g.s 200 anchor
      let t := g.ctr
      let o : op_t := (t, rid, .Ins ((t * 7) % 97) pth anchor)
      { s := do_ g.s o, live := t :: g.live, ctr := g.ctr + 1,
        ops := g.ops ++ [o], aFail := g.aFail + (if accurateB o g.s then 0 else 1) }
  | Cmd.del k =>
      match g.live with
      | [] => g
      | _ =>
          let x := g.live.getD (k % g.live.length) 0
          let pth := pathOf g.s 200 x
          let t := g.ctr
          let o : op_t := (t, rid, .Del pth x)
          { s := do_ g.s o, live := g.live.filter (fun y => y != x), ctr := g.ctr + 1,
            ops := g.ops ++ [o], aFail := g.aFail + (if accurateB o g.s then 0 else 1) }

def runGen (rid start : ℕ) (base : concrete_st) (baseLive : List ℕ) (cmds : List Cmd) : Gen :=
  cmds.foldl (genStep rid) ⟨base, baseLive, start, [], 0⟩

/-- `(P, R1, R2)`: shared prefix, then two concurrent replicas forked from `P`. -/
def buildRun (seedP seed1 seed2 lenP len1 len2 : ℕ) : Gen × Gen × Gen :=
  let gP := runGen 0 1 init_st [] (cmdsFromSeed seedP lenP)
  let g1 := runGen 1 1000 gP.s gP.live (cmdsFromSeed seed1 len1)
  let g2 := runGen 2 2000 gP.s gP.live (cmdsFromSeed seed2 len2)
  (gP, g1, g2)

/-! ### Random interleavings (linear extensions of the vis order) -/

def interleaveF : ℕ → List op_t → List op_t → ℕ → List op_t
  | 0, _, _, _ => []
  | _, [], r2, _ => r2
  | _, r1, [], _ => r1
  | f + 1, a :: r1', b :: r2', seed =>
      let r := nextRand seed
      if r % 2 == 0 then a :: interleaveF f r1' (b :: r2') r
      else b :: interleaveF f (a :: r1') r2' r

def interleave (r1 r2 : List op_t) (seed : ℕ) : List op_t :=
  interleaveF (r1.length + r2.length) r1 r2 seed

/-! ## 3. The checks -/

/-- (T1, "next op") failures: prefixes where the next op is NOT `faithfulB`. -/
def t1NextFails (π : List op_t) : ℕ :=
  (List.range π.length).foldl (fun acc i =>
    match π[i]? with
    | some o => acc + (if faithfulB o (foldDo init_st (π.take i)) then 0 else 1)
    | none => acc) 0

/-- (T1, strong) failures: every event's `recList` must stay `ChainFaithful` at
every prefix fold (the "all events pending from the start" invariant). -/
def t1StrongFails (E π : List op_t) : ℕ :=
  (List.range (π.length + 1)).foldl (fun acc i =>
    let s := foldDo init_st (π.take i)
    acc + (E.filter (fun o => !(chainFaithfulB s (recList o)))).length) 0

/-- First op with replica tag `tag` in a list (the replica's "head"). -/
def firstTagged (tag : ℕ) : List op_t → Option op_t
  | [] => none
  | o :: rest => if o.2.1 == tag then some o else firstTagged tag rest

/-- (T1, bubble-scoped) failures: at every prefix, BOTH replica heads (the only
`loOnA`-minimal-among-remaining / bubble-swappable events) must be `Faithful`.
This is exactly the Faithful the incomparable-swap bubble consumes at hybrid
folds — strictly weaker than the all-events `t1StrongFails`. -/
def t1EnabledFails (π : List op_t) : ℕ :=
  let nP := (π.filter (fun p => p.2.1 == 0)).length   -- shared-past (tag 0) count
  (List.range (π.length + 1)).foldl (fun acc i =>
    -- a replica head is enabled only once ALL of its causal past (the shared P) is applied
    if ((π.take i).filter (fun p => p.2.1 == 0)).length != nP then acc else
    let s := foldDo init_st (π.take i)
    let rest := π.drop i
    let chk (tag : ℕ) : ℕ := match firstTagged tag rest with
      | some o => if faithfulB o s then 0 else 1
      | none => 0
    acc + chk 1 + chk 2) 0

/-- (T1, enabled, FULL `ChainFaithful`) failures: at every prefix where a replica
head is genuinely enabled, its `recList` must be FULLY `ChainFaithful` (not just
top-level `ClimbFaithful`/`faithfulB`).  This is the invariant the bubble must
thread across concurrent `Del` steps (`ClimbFaithful` alone is not Del-stable). -/
def t1EnabledChainFails (π : List op_t) : ℕ :=
  let nP := (π.filter (fun p => p.2.1 == 0)).length
  (List.range (π.length + 1)).foldl (fun acc i =>
    if ((π.take i).filter (fun p => p.2.1 == 0)).length != nP then acc else
    let s := foldDo init_st (π.take i)
    let rest := π.drop i
    let chk (tag : ℕ) : ℕ := match firstTagged tag rest with
      | some o => if chainFaithfulB s (recList o) then 0 else 1
      | none => 0
    acc + chk 1 + chk 2) 0

/-- (T2) failures: for `loOnA`-incomparable adjacent `a,b` (cross-replica tags
`1`/`2`), applying one must not flip the other's `faithfulB` at the shared fold. -/
def t2Fails (π : List op_t) : ℕ :=
  (List.range π.length).foldl (fun acc i =>
    match π[i]?, π[i+1]? with
    | some a, some b =>
        if (a.2.1 != b.2.1) && (a.2.1 == 1 || a.2.1 == 2) && (b.2.1 == 1 || b.2.1 == 2) then
          let s := foldDo init_st (π.take i)
          let chkB := faithfulB b s == faithfulB b (do_ s a)
          let chkA := faithfulB a s == faithfulB a (do_ s b)
          acc + (if chkB && chkA then 0 else 1)
        else acc
    | _, _ => acc) 0

def allIds (E : List op_t) : List ℕ := ((E.map (fun o => o.1)) ++ E.flatMap recList).dedup

/-- Convergence failures: fold two different interleavings and compare via `eqB`. -/
def convFails (P R1 R2 : List op_t) (E : List op_t) (sd1 sd2 : ℕ) : ℕ :=
  let π₁ := P ++ interleave R1 R2 sd1
  let π₂ := P ++ interleave R1 R2 sd2
  if eqB (foldDo init_st π₁) (foldDo init_st π₂) (allIds E) then 0 else 1

/-- Aggregate over one seeded scenario, several interleavings each.
Returns `[aFail, t1Next, t1Enabled, t1Strong, t2, conv]`. -/
def scenario (seedP seed1 seed2 lenP len1 len2 : ℕ) : List ℕ :=
  let (gP, g1, g2) := buildRun seedP seed1 seed2 lenP len1 len2
  let P := gP.ops; let R1 := g1.ops; let R2 := g2.ops
  let E := P ++ R1 ++ R2
  let aF := gP.aFail + g1.aFail + g2.aFail
  let ils := (List.range 6).map (fun j => P ++ interleave R1 R2 (nextRand (seedP + 31 * j + 1)))
  let t1n := ils.foldl (fun a π => a + t1NextFails π) 0
  let t1e := ils.foldl (fun a π => a + t1EnabledFails π) 0
  let t1ec := ils.foldl (fun a π => a + t1EnabledChainFails π) 0
  let t1s := ils.foldl (fun a π => a + t1StrongFails E π) 0
  let t2  := ils.foldl (fun a π => a + t2Fails π) 0
  let cv  := (List.range 5).foldl (fun a j =>
                a + convFails P R1 R2 E (nextRand (seedP + j + 3)) (nextRand (seedP + j + 100))) 0
  [aF, t1n, t1e, t1ec, t1s, t2, cv]

def sum7 (ls : List (List ℕ)) : List ℕ :=
  ls.foldl (fun a b => List.zipWith (· + ·) a b) [0, 0, 0, 0, 0, 0, 0]

/-! ### Runs.  Format:
`[aFail, t1NextFails, t1EnabledFails, t1EnabledChainFails, t1StrongFails, t2Fails, convFails]`.
For the free bubble to host the RGA, all MUST be 0 except `t1StrongFails` (the
over-strong all-events form, expected non-zero on not-yet-enabled pending events). -/

-- 150 scenarios, small shared past, balanced concurrent replicas
#eval sum7 ((List.range 150).map (fun i =>
  scenario (i * 2654435761 + 1) (i * 40503 + 7) (i * 92821 + 13) 3 4 4))

-- 100 scenarios, deeper shared tree + longer replicas (more delete-staling)
#eval sum7 ((List.range 100).map (fun i =>
  scenario (i * 1000003 + 5) (i * 777 + 11) (i * 555 + 23) 5 6 6))

-- 80 scenarios, minimal shared past (maximal concurrency), long replicas
#eval sum7 ((List.range 80).map (fun i =>
  scenario (i * 99991 + 2) (i * 31337 + 3) (i * 27644 + 9) 2 8 8))

/-! ## 4. Adversarial hand SPOTs — concurrent deletes on a shared chain

The scariest shape for T1: two replicas delete DIFFERENT interior nodes of the
SAME shared chain concurrently, and a pending op's recorded path threads through
both.  Chain `0←1←2←3←4`; track node-4's chain `[4,3,2,1]`.  R1 deletes `2`
(accurate path `[1]`), R2 deletes `3` (accurate path `[2]`) — concurrent. -/

def chainS : concrete_st := mk [(1, 10, 0), (2, 10, 1), (3, 10, 2), (4, 10, 3)]
def L4 : List ℕ := [4, 3, 2, 1]
def r1del2 : op_t := (1001, 1, .Del [1] 2)          -- 2's accurate chain is [1]
def r2del3 : op_t := (2002, 2, .Del [2, 1] 3)       -- 3's accurate chain is [2,1] (FULL)

/-! Both interleavings keep node-4's chain `ChainFaithful`, and each del stays
`Faithful` past the concurrent del (self-healing along the full recorded chain). -/
#eval ( chainFaithfulB chainS L4                                        -- base: true
      , chainFaithfulB (do_ chainS r1del2) L4                           -- after R1 del 2
      , chainFaithfulB (do_ chainS r2del3) L4                           -- after R2 del 3
      , chainFaithfulB (do_ (do_ chainS r1del2) r2del3) L4              -- del2;del3
      , chainFaithfulB (do_ (do_ chainS r2del3) r1del2) L4              -- del3;del2
      , faithfulB r2del3 (do_ chainS r1del2)                            -- T2: R2 del still Faithful after R1 del
      , faithfulB r1del2 (do_ chainS r2del3) )                          -- T2: R1 del still Faithful after R2 del

/-! SPOT: concurrent insert-under-x vs delete-x (the create/use conflict).
Chain `0←1←2`; R1 inserts `1001` anchored at `2` (anchor chain `[1]`, recList
`[2,1]`); R2 deletes `2` (path `[1]`).  These are `loOnA`-incomparable. -/
def chainT : concrete_st := mk [(1, 10, 0), (2, 10, 1)]
def r1insUnder2 : op_t := (1001, 1, .Ins 55 [1] 2)   -- anchor 2, 2's chain [1]; recList [2,1]
def r2del2 : op_t := (2002, 2, .Del [1] 2)

#eval ( faithfulB r1insUnder2 chainT                                    -- base Faithful
      , faithfulB r1insUnder2 (do_ chainT r2del2)                       -- Faithful after concurrent del of anchor
      , chainFaithfulB (do_ (do_ chainT r2del2) r1insUnder2) (recList r1insUnder2)  -- ins-after-del recList chain
      , eqB (do_ (do_ chainT r1insUnder2) r2del2)                       -- convergence of the two orders
            (do_ (do_ chainT r2del2) r1insUnder2) [1, 2, 1001] )

/-! ## 5. DIAGNOSTIC: extract the first `t1EnabledFails` witness -/

def enabledFailAt (π : List op_t) : Option (ℕ × op_t) :=
  let nP := (π.filter (fun p => p.2.1 == 0)).length
  (List.range (π.length + 1)).findSome? (fun i =>
    if ((π.take i).filter (fun p => p.2.1 == 0)).length != nP then none else
    let s := foldDo init_st (π.take i)
    let rest := π.drop i
    let bad (tag : ℕ) : Option op_t := match firstTagged tag rest with
      | some o => if faithfulB o s then none else some o
      | none => none
    match bad 1 with
    | some o => some (i, o)
    | none => match bad 2 with | some o => some (i, o) | none => none)

/-- Dump (all ℕ/Bool to keep `Repr`): meta `[i, tag, isIns, leaf, appliedTag,
totalTag, resolve(recList), anc(resolve)]`, `recList`, and per-entry
`(c, contains, anc, resolve[c])`.  `appliedTag = totalTag - 1` ⟺ the failing
event is the replica's ENABLED head (all its causal predecessors applied). -/
def diagScenario (seedP seed1 seed2 lenP len1 len2 : ℕ) :
    Option (List ℕ × List ℕ × List (ℕ × Bool × ℕ × ℕ)) :=
  let (gP, g1, g2) := buildRun seedP seed1 seed2 lenP len1 len2
  let P := gP.ops; let R1 := g1.ops; let R2 := g2.ops
  ((List.range 6).map (fun j => P ++ interleave R1 R2 (nextRand (seedP + 31 * j + 1)))).findSome?
    (fun π => match enabledFailAt π with
      | some (i, o) =>
          let s := foldDo init_st (π.take i)
          let info := (recList o).map (fun c => (c, contains s c, anc s c, resolve s [c]))
          let tag := o.2.1
          let isIns := match o.2.2 with | .Ins _ _ _ => 1 | .Del _ _ => 0
          let appliedTag := ((π.take i).filter (fun p => p.2.1 == tag)).length
          let totalTag := (π.filter (fun p => p.2.1 == tag)).length
          some ([i, tag, isIns, opLeaf o.2.2, appliedTag, totalTag,
                 resolve s (recList o), anc s (resolve s (recList o))], recList o, info)
      | none => none)

/-! First failing scenario index in set 1 (params 3 4 4), and its witness.
Returns `none`: no genuinely-enabled event is ever non-`Faithful`. -/
#eval (List.range 40).findSome? (fun i =>
  (diagScenario (i * 2654435761 + 1) (i * 40503 + 7) (i * 92821 + 13) 3 4 4).map (fun w => (i, w)))

/-! ## 6. The PROVED threading core (0 sorries, kernel-clean)

The PBT verdict above (`t2Fails = 0`, `t1EnabledChainFails = 0`) is discharged as
real theorems for the two step shapes a `loOnA`-respecting reordering can present
while an event `w` is pending — a fresh non-clashing `Ins` (concurrent, its id is
in a disjoint band so `∉ recList w`) or a `Faithful` `Del` (concurrently-staled
but self-healing).  Both preserve `ChainFaithful (recList w)`, hence — projected
by `climbFaithful_of_chain` — keep `w` `Faithful`.  This is exactly **T2** in its
Del-stable form, and it upgrades `RGA_ConditionedConvergence.chainFaithful_fold`
from ACCURATE `Del`s to `Faithful` `Del`s (closing the note's obstruction (2)). -/

open Sal.ConditionedMRDTs.RGABubbleWiring (chainFaithful_doIns climbFaithful_of_chain)
open Sal.ConditionedMRDTs.RGAStaledDelGate (chainFaithful_doDel_faithful)

/-- A `loOnA`-incomparable step for a pending list `L`: a fresh non-clashing `Ins`
(`t ≠ 0`, `t ∉ L` — guaranteed by the disjoint id band) OR a `Faithful` `Del`
(`ClimbFaithful pre ∧ DelTargetFaithful pre x ∧ x ≠ 0`, on a root-free `wf` state
— what concurrent delete-staling preserves). -/
def IncompStep (s : concrete_st) (L : List ℕ) (o : op_t) : Prop :=
  match o with
  | (t, _, .Ins _ _ _) => t ≠ 0 ∧ t ∉ L
  | (_, _, .Del _ _)   => contains s 0 = false ∧ wf s ∧ Faithful o s

/-- **T2 (Del-stable form) — CLOSED.**  A `loOnA`-incomparable step preserves the
pending event's `ChainFaithful (recList w)`.  Ins case: `chainFaithful_doIns`
(needs `t ∉ L`, supplied by the disjoint band).  Del case:
`chainFaithful_doDel_faithful` (needs only `Faithful`, NO `accurate`). -/
theorem chainFaithful_incompStep (s : concrete_st) (L : List ℕ) (o : op_t)
    (hg : IncompStep s L o) (hcf : ChainFaithful s L) : ChainFaithful (do_ s o) L := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e pre a =>
      obtain ⟨ht0, htL⟩ := hg
      exact chainFaithful_doIns s t r e a pre L ht0 htL hcf
  | Del pre x =>
      obtain ⟨h0, hwf, hfaith⟩ := hg
      exact chainFaithful_doDel_faithful s t r x pre L h0 hwf hfaith hcf

/-- Every step of `π` is a `loOnA`-incomparable step for `L` at its own prefix fold. -/
def IncompFold (L : List ℕ) : concrete_st → List op_t → Prop
  | _, [] => True
  | s, o :: rest => IncompStep s L o ∧ IncompFold L (do_ s o) rest

/-- **T1 threading (from enablement) — CLOSED modulo the base.**  `ChainFaithful L`
is preserved along any fold whose every step is `loOnA`-incomparable to `L`
(fresh concurrent `Ins` / `Faithful` `Del`).  Instantiated with `L = recList w`
and the fold = the concurrent ops between `w`'s enablement and its swap point,
this threads `w`'s `ChainFaithful` (hence `Faithful`) to the bubble's swap. -/
theorem chainFaithful_incompFold (L : List ℕ) :
    ∀ (π : List op_t) (s : concrete_st),
      IncompFold L s π → ChainFaithful s L → ChainFaithful (foldDo s π) L := by
  intro π
  induction π with
  | nil => intro s _ hcf; exact hcf
  | cons o rest ih =>
      intro s hgf hcf
      obtain ⟨hstep, hrest⟩ := hgf
      exact ih (do_ s o) hrest (chainFaithful_incompStep s L o hstep hcf)

/-- **Projection to `Faithful` for an `Ins`.**  On a root-free state the threaded
`ChainFaithful (a :: pre)` yields `Faithful (t,r,.Ins e pre a)` — the top-level
`ClimbFaithful` the incomparable swap consumes.  (`climbFaithful_of_chain`.) -/
theorem faithful_ins_of_chain (s : concrete_st) (t r e a : ℕ) (pre : List ℕ)
    (h0 : contains s 0 = false) (hcf : ChainFaithful s (a :: pre)) :
    Faithful (t, r, .Ins e pre a) s :=
  climbFaithful_of_chain s (a :: pre) h0 hcf

/- ── THE SINGLE REMAINING RESIDUAL (documented, NOT sorried) ──────────────────

`chainFaithful_incompFold` threads `ChainFaithful (recList w)` from any state where
it ALREADY holds.  The one gap to an unconditional T1 (and thence to discharging
`RGA_ConditionedConvergence.RGA_conditioned_convergence_bothFaithful`'s `hReady`)
is the BASE: establishing `ChainFaithful (recList w)` at `w`'s ENABLEMENT fold,
where `w` may be concurrently-staled (not `accurate`).  The PBT verifies this
holds (`t1EnabledChainFails = 0`), and its refutation-in-general is now understood:

  * `RGA_StaledDel_Gate.chainFaithful_not_preserved_under_clash_ins` (Part 1) shows
    the naive "accurate `Ins` with `t ∈ L` preserves `ChainFaithful`" is FALSE —
    but ONLY for an INCONSISTENT `L` (records `5` as `8`'s ancestor while `8`'s true
    anchor is root).  Such an `L` is NOT a reachable `recList`: a genuine `recList`
    is the event's TRUE ancestor chain, so reactivating a recorded ancestor at its
    true anchor cannot introduce a false link.

  * Hence the missing lemma is the REACHABLE-regime accurate-ancestor-`Ins`
    preservation — provable only under the reachability invariant "`recList w` is
    `w`'s true full-history chain" — a state/history invariant to be threaded, i.e.
    the deferred engineering tail, NOT a semantic obstruction.

VERDICT: the free bubble IS the right vehicle.  T2 (Del-stable) is proved; the
`Faithful`-`Del` half of the old obstruction (2) is closed; T1 threads once its
enablement base is established, which the PBT confirms always holds and which
reduces to a single reachability-invariant lemma. -/

/-! ## 7. Axiom audit — the proved core is kernel-clean (no `sorryAx`). -/

#print axioms chainFaithful_incompStep
#print axioms chainFaithful_incompFold
#print axioms faithful_ins_of_chain

end RGAFaithfulThreadingGate
