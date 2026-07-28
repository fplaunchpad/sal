/-!
# Shesha: the sibling-linked tombstone-free replicated list

Design record: `whiteboard/sibling-linked-rga-notes.md`. Pen-and-paper proofs:
`whiteboard/sibling-linked-proof.md`. Executable reference semantics (THE oracle
for this port): `whiteboard/sl_pbt.py`, every definition here is
observationally cross-validated against it in `Shesha_SPOT.lean`.

**Scope of this file.** This file delivers the executable datatype (`read`,
`insert`, `delete`, the three-way `merge`), the tombstoned oracle
(`oracleRead`), the naive sequential list model, and the machine-checked
sequential soundness theorems (Theorem S, Corollary S1), all kernel-clean, no
`sorry`. The 24 RA-linearizability VCs, the merge lemmas M0–M3, Theorem P
(causal pairwise display stability), and the `ConditionedMRDTSig` packaging
live in the other `Shesha_*.lean` files; this module is deliberately NOT
imported by `MRDT_Instances/MRDT_Instances.lean` (the umbrella imports
conditioned capstones only).

## Representation

The design's per-replica state is `(V, par : V → V ∪ {⌂}, sib : V ⇀ V)` with
the row head *derived* (the unique child no sibling points to). This port uses
the equivalent **explicit-rows** form, taken to its natural conclusion: a rose
forest, each node's row stored in place, head = first list element,
`sib(u)` = the next list element. The two encodings carry exactly the same
information (the sibling chain *is* the row), and the explicit form is what
`sl_pbt.py`'s own merge computes internally (`out_rows`); the O(1)-per-node
boundedness claim lives in the pointer encoding, recoverable from this one via
an encoding isomorphism. What the explicit-rows form buys: `read`,
`insert`, `delete` are fuel-free structural recursions, so Theorem S is an
honest structural induction, no well-formedness hypotheses, no fuel
bookkeeping. Observational agreement with the pointer-based Python reference
is machine-checked litmus-by-litmus in `Shesha_SPOT.lean`.

Ids are Lamport timestamps (`Nat`), the root is the implicit `0`, and, as in
`sl_pbt.py`, nodes carry no payload: the id doubles as the element.
-/

namespace Shesha

/-! ## State: a rose forest of ids

`St` is the root row; each `Tree.node i cs` is a live node `i` with its row
`cs` (children, display order, newest-first among concurrent same-anchor
inserts by construction). A deleted node appears **nowhere**, the state never
mentions a dead id. -/

/-- A live node: id and its row (ordered children). -/
inductive Tree where
  | node : Nat → List Tree → Tree
deriving Repr

/-- A state is the root's row. `⌂` (the root, id `0`) is implicit. -/
abbrev St := List Tree

/-- The empty document. -/
def init : St := []

/-! Nested inductives don't get a derived `DecidableEq`; hand-rolled here.
Needed by the SPOT layer: the fooling-pair impossibilities rest on
`decide`-checked *state equality* across two worlds. -/

mutual
  def decEqT : (a b : Tree) → Decidable (a = b)
    | .node i cs, .node j ds =>
      match Nat.decEq i j with
      | isFalse h => isFalse (by simp [Tree.node.injEq]; intro hc; exact absurd hc h)
      | isTrue h1 =>
        match decEqL cs ds with
        | isTrue h2 => isTrue (by rw [h1, h2])
        | isFalse h => isFalse (by simp [Tree.node.injEq, h1]; exact h)
  def decEqL : (as bs : List Tree) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by simp)
    | _ :: _, [] => isFalse (by simp)
    | a :: as, b :: bs =>
      match decEqT a b with
      | isFalse h => isFalse (by simp [h])
      | isTrue h1 =>
        match decEqL as bs with
        | isTrue h2 => isTrue (by rw [h1, h2])
        | isFalse h => isFalse (by simp [h1]; exact h)
end

instance : DecidableEq Tree := decEqT

/-! ## `read`: depth-first document order

Per node: emit the id, then recurse into its row. Siblings are read in row
order (newest concurrent insert first). Structural recursion, total, no fuel. -/

mutual
  def readT : Tree → List Nat
    | .node i cs => i :: readF cs
  def readF : List Tree → List Nat
    | [] => []
    | t :: ts => readT t ++ readF ts
end

/-- The document: depth-first from the root. -/
def read (s : St) : List Nat := readF s

/-! ## `insert (x after a)`: x becomes the head of a's row

Nothing else changes (`sl_pbt.py` `insert`: `par(x) := a`,
`sib(x) := old head`). `a = 0` inserts at the front of the root row. On
well-formed histories the anchor occurs at most once; for totality the
insertion happens at every occurrence (and is a no-op when the anchor is
absent), which is also exactly what makes the sequential lemma unconditional. -/

mutual
  def insT (x a : Nat) : Tree → Tree
    | .node i cs =>
        if i = a then .node i (.node x [] :: insF x a cs)
        else .node i (insF x a cs)
  def insF (x a : Nat) : List Tree → List Tree
    | [] => []
    | t :: ts => insT x a t :: insF x a ts
end

/-- Insert `x` after anchor `a` (`0` = root: front of the document). -/
def insert (s : St) (x a : Nat) : St :=
  if a = 0 then .node x [] :: s else insF x a s

/-! ## `delete d`: the splice

`d`'s row replaces `d` in its parent's row, in place; then `d` is gone,
**after this line the state contains no trace of d** (`sl_pbt.py` `delete`).
Locally order-preserving by construction (Corollary S1 below). No-op when `d`
is absent. -/

mutual
  def delT (d : Nat) : Tree → List Tree
    | .node i cs => if i = d then delF d cs else [.node i (delF d cs)]
  def delF (d : Nat) : List Tree → List Tree
    | [] => []
    | t :: ts => delT d t ++ delF d ts
end

/-- Delete `d`: splice its row into its slot, erase `d` everywhere. -/
def delete (s : St) (d : Nat) : St := delF d s

/-! ## Operations and folds -/

/-- The op alphabet, consumed by both the datatype fold and the naive-list
fold (Theorem S relates the two on the *same* op list). -/
inductive Op where
  | ins (x a : Nat)
  | del (d : Nat)
deriving DecidableEq, Repr

def applyOp (s : St) : Op → St
  | .ins x a => Shesha.insert s x a
  | .del d => Shesha.delete s d

/-- Apply an op list to a state (single-replica session). -/
def steps (s : St) (ops : List Op) : St := ops.foldl applyOp s

/-- Apply an op list from the empty document. -/
def fold (ops : List Op) : St := steps init ops

/-! ## The naive sequential list model (`SeqList`)

The obvious spec: a flat `List Nat`; `ins x a` places `x` immediately after
`a` (at the front for `a = 0`); `del d` removes `d`. Same totality choices as
the datatype (insert after every occurrence of the anchor, no-op when absent),
so the simulation below is unconditional. -/

/-- `SeqList`, the naive sequential document. -/
abbrev SeqList := List Nat

/-- Pointwise insert action: after the anchor, emit the new element. -/
def seqInsAt (x a u : Nat) : List Nat := if u = a then [u, x] else [u]

/-- Naive-list insert: `x` immediately after `a` (front for `a = 0`). -/
def seqIns (l : SeqList) (x a : Nat) : SeqList :=
  if a = 0 then x :: l else l.flatMap (seqInsAt x a)

/-- Naive-list delete: remove `d`, everything else untouched. -/
def seqDel (l : SeqList) (d : Nat) : SeqList := l.filter (· ≠ d)

def seqApply (l : SeqList) : Op → SeqList
  | .ins x a => seqIns l x a
  | .del d => seqDel l d

/-- The naive-list fold from the empty document. -/
def seqFold (ops : List Op) : SeqList := ops.foldl seqApply []

/-! ## Theorem S: sequential soundness

`read` is a simulation from Shesha states to naive lists: every op commutes
with `read`. Structural induction over the forest, unconditional (no
well-formedness needed, the totality choices of both sides agree). This is
the per-datatype "obvious spec" theorem (`sibling-linked-proof.md` §2), and
precisely the property the flat tombstone-free RGA *fails*
(`tombstone_free_violates_delete_order`, `Sal/MRDTs/RGA_Rehoming/RGA_Tombstone_Free_SPOT.lean`). -/

theorem readF_append :
    ∀ f g : List Tree, readF (f ++ g) = readF f ++ readF g
  | [], _ => by simp [readF]
  | t :: ts, g => by simp [readF, readF_append ts g]

mutual
  theorem readT_insT (x a : Nat) :
      ∀ t : Tree, readT (insT x a t) = (readT t).flatMap (seqInsAt x a)
    | .node i cs => by
        by_cases h : i = a <;>
          simp [insT, readT, readF, readF_insF x a cs, seqInsAt, h]
  theorem readF_insF (x a : Nat) :
      ∀ ts : List Tree, readF (insF x a ts) = (readF ts).flatMap (seqInsAt x a)
    | [] => by simp [insF, readF]
    | t :: ts => by
        simp [insF, readF, readT_insT x a t, readF_insF x a ts]
end

/-- Insert simulation: the datatype's insert *is* the naive-list insert at the
read. -/
theorem read_insert (s : St) (x a : Nat) :
    read (Shesha.insert s x a) = seqIns (read s) x a := by
  by_cases h : a = 0 <;>
    simp [Shesha.insert, read, seqIns, h, readF, readT, readF_insF]

mutual
  theorem readF_delT (d : Nat) :
      ∀ t : Tree, readF (delT d t) = (readT t).filter (· ≠ d)
    | .node i cs => by
        by_cases h : i = d <;>
          simp [delT, readT, readF, readF_delF d cs, h]
  theorem readF_delF (d : Nat) :
      ∀ ts : List Tree, readF (delF d ts) = (readF ts).filter (· ≠ d)
    | [] => by simp [delF, readF]
    | t :: ts => by
        simp [delF, readF, readF_append, readF_delT d t, readF_delF d ts]
end

/-- Delete simulation: the splice removes exactly `d` from the read.
Order-preservation of survivors is on the surface of the statement. -/
theorem read_delete (s : St) (d : Nat) :
    read (Shesha.delete s d) = seqDel (read s) d :=
  readF_delF d s

/-- Every op commutes with `read`. -/
theorem read_applyOp (s : St) (o : Op) :
    read (applyOp s o) = seqApply (read s) o := by
  cases o with
  | ins x a => exact read_insert s x a
  | del d => exact read_delete s d

theorem read_steps :
    ∀ (ops : List Op) (s : St), read (steps s ops) = ops.foldl seqApply (read s)
  | [], _ => rfl
  | o :: ops, s => by
      show read (steps (applyOp s o) ops) = _
      rw [read_steps ops (applyOp s o), read_applyOp]
      rfl

/-- **Theorem S (sequential soundness).** For any op list applied
single-replica from the empty document, the datatype's read equals the
naive-list fold of the same ops (`sibling-linked-proof.md` §2). -/
theorem sequential_soundness (ops : List Op) : read (fold ops) = seqFold ops :=
  read_steps ops init

/-- **Corollary S1 (sequential delete-order preservation).** A delete never
reorders survivors: the post-delete read is the pre-delete read with the
target filtered out, for *every* state, not just reachable ones. This is the
anomaly the flat tombstone-free RGA exhibits (its witness: `b a c → del a →
c b`) and the original motivation for the sibling-linked design: here order is
stored in the links and the splice preserves it by construction. -/
theorem delete_preserves_survivor_order (s : St) (d : Nat) :
    read (Shesha.delete s d) = (read s).filter (· ≠ d) :=
  read_delete s d

/-! ## Query helpers (merge ingredients)

Total, fuel-free structural searches over the forest. On well-formed states
(unique ids) they agree with `sl_pbt.py`'s `V`/`row`/`par`. -/

/-- Root id of a tree. -/
def topId : Tree → Nat
  | .node i _ => i

mutual
  def containsT (u : Nat) : Tree → Bool
    | .node i cs => i == u || containsF u cs
  def containsF (u : Nat) : List Tree → Bool
    | [] => false
    | t :: ts => containsT u t || containsF u ts
end

/-- Is `u` a live node of `s`? (`u ∈ V`.) -/
def contains (s : St) (u : Nat) : Bool := containsF u s

mutual
  def rowT (p : Nat) : Tree → List Nat
    | .node i cs => if i = p then cs.map topId else rowF p cs
  def rowF (p : Nat) : List Tree → List Nat
    | [] => []
    | t :: ts => rowT p t ++ rowF p ts
end

/-- The row of `p`: its children's ids in display order (`p = 0` = root row). -/
def row (s : St) (p : Nat) : List Nat :=
  if p = 0 then s.map topId else rowF p s

mutual
  def parT (cur u : Nat) : Tree → Option Nat
    | .node i cs => if i = u then some cur else parF i u cs
  def parF (cur u : Nat) : List Tree → Option Nat
    | [] => none
    | t :: ts =>
        match parT cur u t with
        | some r => some r
        | none => parF cur u ts
end

/-- Parent id of `u` in `s` (`0` = root level; also `0` when absent). -/
def parOf (s : St) (u : Nat) : Nat := (parF 0 u s).getD 0

/-! ## The three-way merge: `sl_pbt.py`'s algorithm, ported clause by clause

Membership analysis (design record §3): `liveM` = patterns 2/6/7, `markers` =
L-nodes live in exactly one branch (patterns 3/4, dead, but their entries in
the surviving input still position things). Then: skeleton in L-document order
grouped under the deepest surviving L-ancestor (attach-deep); branch-born
wholesale rows; runs with predecessor-riding / head jump-back over own-deleted
markers / end placement; same-slot runs contiguous, newest-head-first; finally
markers are spliced out. Python dicts become association lists. -/

/-- Merge-live (patterns 2, 6, 7): in both branches, or born in exactly one. -/
def liveMp (L A B : St) (u : Nat) : Bool :=
  (contains A u && contains B u) ||
  (contains A u && !contains L u) ||
  (contains B u && !contains L u)

/-- Markers (patterns 3, 4): L-nodes live in exactly one branch. -/
def markerp (L A B : St) (u : Nat) : Bool :=
  contains L u && (contains A u != contains B u)

/-- The working set `W = liveM ∪ markers`. -/
def wp (L A B : St) (u : Nat) : Bool := liveMp L A B u || markerp L A B u

/-- Climb `L`'s parent chain until the root or a `W`-member (fueled). -/
def wparGo (L : St) (W : Nat → Bool) : Nat → Nat → Nat
  | 0, p => p
  | fuel + 1, p => if p == 0 || W p then p else wparGo L W fuel (parOf L p)

/-- Deepest surviving-or-marker L-ancestor of an L-node (attach-deep host). -/
def wpar (L : St) (W : Nat → Bool) (u : Nat) : Nat :=
  wparGo L W ((read L).length + 1) (parOf L u)

/-! Association-list plumbing (`Nat`-keyed rows, insertion-ordered). -/

def alGet (al : List (Nat × List Nat)) (k : Nat) : List Nat :=
  match al.find? (fun kv => kv.1 == k) with
  | some kv => kv.2
  | none => []

def alHas (al : List (Nat × List Nat)) (k : Nat) : Bool :=
  al.any (fun kv => kv.1 == k)

/-- Append `v` to row `k` (creating `k` at the end if absent). -/
def alApp (al : List (Nat × List Nat)) (k v : Nat) : List (Nat × List Nat) :=
  if alHas al k then
    al.map (fun kv => if kv.1 == k then (kv.1, kv.2 ++ [v]) else kv)
  else al ++ [(k, [v])]

/-- Ensure key `k` exists (empty row if absent). -/
def alEnsure (al : List (Nat × List Nat)) (k : Nat) : List (Nat × List Nat) :=
  if alHas al k then al else al ++ [(k, [])]

def idxOf' : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, u => if x == u then 0 else idxOf' xs u + 1

def dedupNat : List Nat → List Nat
  | [] => []
  | x :: xs => if xs.contains x then dedupNat xs else x :: dedupNat xs

/-- The skeleton: per host, the L-nodes of `W` in L-document order; `rowof`
records each L-node's host. -/
structure Skel where
  rows : List (Nat × List Nat)
  rowof : List (Nat × Nat)
deriving Repr

def skelOf (L A B : St) : Skel :=
  let W := wp L A B
  ((read L).filter W).foldl
    (fun sk u =>
      let p := wpar L W u
      { rows := alEnsure (alApp sk.rows p u) u
        rowof := sk.rowof ++ [(u, p)] })
    ⟨[(0, [])], []⟩

def rowofGet (sk : Skel) (u : Nat) : Nat :=
  match sk.rowof.find? (fun kv => kv.1 == u) with
  | some kv => kv.2
  | none => 0

/-- Ids born in branch `X` (present in `X`, absent from `L`), document order. -/
def bornIds (L X : St) : List Nat := (read X).filter (fun u => !contains L u)

/-- Wholesale rows: a branch-born node's row travels with it verbatim. -/
def bbrows (L X : St) : List (Nat × List Nat) :=
  (bornIds L X).filterMap (fun q =>
    let r := row X q
    if r.isEmpty then none else some (q, r))

/-- Hosts: parents (in `X`) of branch-born nodes that are the root or L-nodes,
the rows whose branch-born runs need placing. -/
def hosts (L X : St) : List Nat :=
  dedupNat (((bornIds L X).map (fun u => parOf X u)).filter
    (fun p => p == 0 || contains L p))

/-- A placement command: a run of branch-born ids destined for slot `k` of
skeleton row `tr`, or for the end of host `host`'s row. -/
inductive Cmd where
  | slot (tr k : Nat) (run : List Nat)
  | atEnd (host : Nat) (run : List Nat)
deriving Repr

/-- Split a branch row into maximal runs of non-L ids, each tagged with its
L-predecessor (the last L-node before it) and its L-successor (fueled). -/
def runsGo (isL : Nat → Bool) :
    Nat → Option Nat → List Nat → List (Option Nat × List Nat × Option Nat)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, pre, u :: rest =>
      if isL u then runsGo isL fuel (some u) rest
      else
        let run := (u :: rest).takeWhile (fun v => !isL v)
        let rest' := (u :: rest).dropWhile (fun v => !isL v)
        (pre, run, rest'.head?) :: runsGo isL fuel pre rest'

/-- Head jump-back: a head run placed before its L-successor at slot `k` jumps
back over markers its own branch deleted (design record §4, refinement iii). -/
def jumpBack (skelRow : List Nat) (isMarker inX : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      let w := skelRow.getD k 0
      if isMarker w && !inX w then jumpBack skelRow isMarker inX k else k + 1

/-- All placement commands contributed by branch `X`: predecessor-riding (a),
head jump-back (b), end placement (c). -/
def branchCmds (L X : St) (sk : Skel) (isMarker : Nat → Bool) : List Cmd :=
  (hosts L X).flatMap (fun p =>
    let r := row X p
    (runsGo (contains L) (r.length + 1) none r).map (fun pr =>
      match pr with
      | (some pre, run, _) =>
          let tr := rowofGet sk pre
          Cmd.slot tr (idxOf' (alGet sk.rows tr) pre + 1) run
      | (none, run, some s) =>
          let tr := rowofGet sk s
          let k := idxOf' (alGet sk.rows tr) s
          Cmd.slot tr (jumpBack (alGet sk.rows tr) isMarker (contains X) k) run
      | (none, run, none) => Cmd.atEnd p run))

def slotRuns (cmds : List Cmd) (p k : Nat) : List (List Nat) :=
  cmds.filterMap (fun c =>
    match c with
    | .slot tr k' run => if tr == p && k' == k then some run else none
    | _ => none)

def endRuns (cmds : List Cmd) (p : Nat) : List (List Nat) :=
  cmds.filterMap (fun c =>
    match c with
    | .atEnd q run => if q == p then some run else none
    | _ => none)

/-- Same-slot runs stay contiguous, newest head first. -/
def sortRunsDesc (rs : List (List Nat)) : List (List Nat) :=
  rs.mergeSort (fun r₁ r₂ => Nat.ble (r₂.headD 0) (r₁.headD 0))

/-- Assemble one skeleton row: at each gap `k`, the runs slotted there
(newest-head-first), then the skeleton element; end runs last. -/
def rowAssemble (cmds : List Cmd) (p : Nat) (skelRow : List Nat) : List Nat :=
  ((List.range (skelRow.length + 1)).flatMap (fun k =>
      (sortRunsDesc (slotRuns cmds p k)).flatten ++ (skelRow.drop k).take 1))
    ++ (sortRunsDesc (endRuns cmds p)).flatten

/-- All merged rows, markers still in place (spliced by `expandRow`). -/
def outRows (L A B : St) : List (Nat × List Nat) :=
  let sk := skelOf L A B
  let mk := markerp L A B
  let cmds := branchCmds L A sk mk ++ branchCmds L B sk mk
  sk.rows.map (fun kv => (kv.1, rowAssemble cmds kv.1 kv.2))
    ++ bbrows L A ++ bbrows L B

/-- The marker splice: replace each marker in a row by its own (recursively
expanded) row, the same splice as `delete`, performed at assembly (fueled). -/
def expandRow (rows : List (Nat × List Nat)) (isMarker : Nat → Bool) :
    Nat → List Nat → List Nat
  | 0, r => r
  | fuel + 1, r =>
      r.flatMap (fun u =>
        if isMarker u then expandRow rows isMarker fuel (alGet rows u) else [u])

/-- Rebuild the forest from the merged rows, root down (fueled). -/
def buildF (rows : List (Nat × List Nat)) (isMarker : Nat → Bool) (mfuel : Nat) :
    Nat → Nat → St
  | 0, _ => []
  | fuel + 1, p =>
      (expandRow rows isMarker mfuel (alGet rows p)).map
        (fun c => Tree.node c (buildF rows isMarker mfuel fuel c))

/-- **The three-way merge** (`merge L A B`, `L` = LCA), `sl_pbt.py`'s
`merge`, ported faithfully. Owed on top of this definition: M0
(well-formedness), M1 (symmetry), M2/M3 (order extension), and Theorem P. -/
def merge (L A B : St) : St :=
  let rows := outRows L A B
  let n := (read L).length + (read A).length + (read B).length + 1
  buildF rows (markerp L A B) n n 0

/-! ## The tombstoned oracle

`sl_pbt.py`'s `oracle_read`: the full tree of *original* insert anchors
(graves included as position-holders), siblings by descending id, graves emit
nothing. Takes the global op history, `inserts` as `(id, original anchor)`
pairs, `deleted` as the set of deleted ids, because no tombstone-free state
retains it; that gap is exactly the fooling-pair impossibility (I1) checked in
`Shesha_SPOT.lean`. -/

def sortDesc (l : List Nat) : List Nat :=
  l.mergeSort (fun a b => Nat.ble b a)

def oracleChildren (inserts : List (Nat × Nat)) (p : Nat) : List Nat :=
  sortDesc ((inserts.filter (fun ia => ia.2 == p)).map (·.1))

def oracleGo (inserts : List (Nat × Nat)) (deleted : List Nat) :
    Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, p =>
      (oracleChildren inserts p).flatMap (fun c =>
        (if deleted.contains c then [] else [c])
          ++ oracleGo inserts deleted fuel c)

/-- The tombstoned RGA's read over a global op history. -/
def oracleRead (inserts : List (Nat × Nat)) (deleted : List Nat) : List Nat :=
  oracleGo inserts deleted (inserts.length + 1) 0

end Shesha
