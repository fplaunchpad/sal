import Sal.MRDTs.Instances.SidedEmbedRGA_Intent

/-!
# Sided RGA under the Fugue policy: the Weidner-Kleppmann statement

The maximal non-interleaving statement of Weidner and Kleppmann ("The Art
of the Fugue", arXiv:2305.00583v3, Definition 4 + Lemma 5), adapted to the
sided embedded-chain RGA under the Fugue side-selection policy.

Layers in this file:

* **§1 The generation layer.** `GRec` records a datatype op together with
  its generation-time metadata (left origin = the intent anchor, right
  origin = the tombstone-visible successor, the minted birth chain);
  `fugueChoose` is the paper's insert rule exactly (right child of the
  anchor when it has never had a right child, dead nodes included, else
  left child of the anchor's successor);
  `genInsAt` is the positional intent op ("insert at index i of my view");
  `FugueReach` is reachability by local Fugue inserts (Lamport-fresh ids),
  local deletes, and pairwise knowledge sync (causal delivery is automatic
  because whole knowledge sets transfer).

* **§2 The statement (the core deliverable).** `ForwardNI` (Definition 2),
  `BackwardNIExc` (condition (2) with the Lemma-5 `BackwardException`),
  `SameOriginLowFirst` (condition (3)), bundled as `MaxNonInterleaving`,
  and the algorithm-level `FugueMaximallyNonInterleaving` /
  `FugueForwardNonInterleaving` over `FugueReach`. The comparison
  quantifiers range over ALL minted elements, tombstones included, in the
  key order (the strict reading): a countermodel shows the live-only
  reading is unsatisfiable for the whole Fugue family.

* **§3 Invariants.** `fugueReach_inv` / `fugueReach_chain_gen`: every
  reachable knowledge is chain-generated in exactly the honesty layer's
  `chain_gen` shape, so the fold intent theorems apply to every reachable
  state.

* **§4 Candidate (a), proved.** `fugue_two_runs_no_interleave` and
  `fugue_concurrent_runs_no_interleave`: members of two runs whose head
  chains are prefix-incomparable (the concurrency consequence) never
  interleave in any chain-generated fold; via `sided_fold_subtree_convex`.
  `fugue_reachable_runs_no_interleave` instantiates it at any reachable
  Fugue configuration.

* **§5 The policy half.** `fugue_forward_run_chains`: forward Fugue runs
  chain (each element is minted as R-child of the previous, because a
  fresh element has never had an R-child). `schainBefore_snoc_newest` is
  the kernel piece of the backward case.

* **§6 The refutations (first-class results).**
  `fugue_not_maximally_noninterleaving`: condition (3) fails on a
  two-insert reachable trace (the kernel's newest-first R-sibling order
  reverses the paper's lowest-ID-first tiebreak).
  `fugue_backward_gap`: condition (2) fails on the paper's own Figure-7
  execution with the Lemma-5 exception refuted pointwise; this is the
  Fugue-vs-FugueMax gap the paper proves, so it is independent of the
  tiebreak clause.

* **§7 SPOTs**, PASS+FAIL shaped: the positional generator replays L19
  (and literally regenerates `SidedSPOT.opsL19`), the forward twin, the
  mixed forward/backward case, and the two refutation traces, with
  hand-derived expected displays and interleaved-order (or
  FugueMax-order) pins.

**Honest gap analysis** (no proof placeholders; gaps are absences, not
holes): (G1) backward-run chaining needs "the successor of the fixed
anchor is the previously minted run element" (newest-mint adjacency); the
kernel lemma is here, the `succOf`-to-`schainBefore` bridge is not, so
backward runs enter §4 through the `RunChains` hypothesis (discharged
concretely in the SPOTs). (G2) `FugueForwardNonInterleaving` is stated
and unproved: a proof needs the display-to-tree-traversal theory (the
paper's Lemma 7/8 layer). (G3) the
prefix-incomparability of concurrent run heads is a hypothesis of §4; the
telescoping argument and the `GInv` invariants that feed it are in place.
-/

namespace Sal.MRDTs.Instances.SidedEmbedRGA

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode keyLt sKey sBlock Side SChain PosSChain
  sidedCoordOf sidedCoordOf_append unaryCode schainBefore schainBefore_inv
  sEntryBefore)

set_option linter.unusedSectionVars false

/-! ## §1  The generation layer -/

/-- One generation record: the datatype op plus the generation-time
metadata the W-K statement needs. `lo` is the left origin (the intent
anchor; 0 = start), `ro` the right origin (the tombstone-visible successor
at generation time; `none` = end), `chain` the minted birth chain (`[]`
for deletes). -/
structure GRec where
  op : Op SOp
  lo : ℕ
  ro : Option ℕ
  chain : SChain
deriving DecidableEq

/-- A replica's knowledge: its generation records, in arrival order. -/
abbrev Know : Type := List GRec

def gOps (K : Know) : List (Op SOp) := K.map GRec.op

def gFold (Γ : OrderedPrefixCode) (K : Know) : SState := sFold Γ (gOps K)

/-- The live display: ids in document order (descending key). -/
def gView (Γ : OrderedPrefixCode) (K : Know) : List ℕ := sIds (gFold Γ K)

/-- The minted elements: the insert records (grow-only, dead included). -/
def gMinted (K : Know) : List GRec := K.filter (fun g => sIsIns g.op)

def gMintedIds (K : Know) : List ℕ := (gMinted K).map (fun g => g.op.1)

def gRecOfId (K : Know) (x : ℕ) : Option GRec :=
  (gMinted K).find? (fun g => g.op.1 == x)

/-- The birth chain of a minted id (the root 0 has the empty chain). -/
def gChainOf (K : Know) (x : ℕ) : SChain :=
  ((gRecOfId K x).map GRec.chain).getD []

/-- The strong-list sort key of an element, tombstones included. -/
def gKey (Γ : OrderedPrefixCode) (K : Know) (x : ℕ) : List ℕ :=
  sKey (sidedCoordOf Γ (gChainOf K x))

/-- Pick the display-first (key-largest) of the candidates seen so far. -/
def maxKey (acc : Option (ℕ × List ℕ))
    (p : ℕ × List ℕ) : Option (ℕ × List ℕ) :=
  match acc with
  | none => some p
  | some b => if keyLt b.2 p.2 = true then some p else some b

def gKeys (Γ : OrderedPrefixCode) (K : Know) : List (ℕ × List ℕ) :=
  (gMinted K).map (fun g => (g.op.1, sKey (sidedCoordOf Γ g.chain)))

/-- Candidates for the successor of `a`: everything displayed after `a`
(for `a = 0`, start, everything). -/
def succCand (Γ : OrderedPrefixCode) (K : Know) (a : ℕ) : List (ℕ × List ℕ) :=
  if a = 0 then gKeys Γ K
  else (gKeys Γ K).filter (fun p => keyLt p.2 (gKey Γ K a))

/-- The tombstone-visible successor of `a` in the replica's local order
over all minted nodes: the display-first element after `a`. -/
def succOf (Γ : OrderedPrefixCode) (K : Know) (a : ℕ) : Option ℕ :=
  ((succCand Γ K a).foldl maxKey none).map Prod.fst

/-- Does `g` record an insert anchored at `a` on the R side? -/
def gAnchorR (a : ℕ) (g : GRec) : Bool :=
  match g.op.2.2 with
  | .ins _ _ p sd => decide (p = a) && decide (sd = Side.R)
  | .del _ => false

/-- Has `a` ever had a right child (dead nodes included)? -/
def hasRChild (K : Know) (a : ℕ) : Bool := K.any (gAnchorR a)

/-- **The Fugue insert rule**, mirroring `embed_sided.py`'s `choose`:
right child of the anchor when it has never had a right child or has no
successor, else left child of the successor. -/
def fugueChoose (Γ : OrderedPrefixCode) (K : Know) (a : ℕ) : Side × ℕ :=
  match succOf Γ K a with
  | some n => if hasRChild K a then (Side.L, n) else (Side.R, a)
  | none => (Side.R, a)

/-- Generate an insert of fresh id `x` with intent "after element `a`"
(`a = 0`: at the front): the policy picks `(side, parent)`, the mint
extends the parent's chain, and the origins are recorded. -/
def genInsAfter (Γ : OrderedPrefixCode) (K : Know) (rep : Replica)
    (x a : ℕ) : GRec :=
  { op := (x, rep, SOp.ins x
      (sidedCoordOf Γ (gChainOf K (fugueChoose Γ K a).2))
      (fugueChoose Γ K a).2 (fugueChoose Γ K a).1)
    lo := a
    ro := succOf Γ K a
    chain := gChainOf K (fugueChoose Γ K a).2 ++
      [((fugueChoose Γ K a).1, x - (fugueChoose Γ K a).2)] }

/-- The intent anchor of "insert at index `i` of my view": the live
element at index `i - 1`, or start. -/
def anchorAt (Γ : OrderedPrefixCode) (K : Know) (i : ℕ) : ℕ :=
  if i = 0 then 0 else (gView Γ K).getD (i - 1) 0

/-- Positional intent: insert fresh id `x` at index `i` of the view. -/
def genInsAt (Γ : OrderedPrefixCode) (K : Know) (rep : Replica)
    (x i : ℕ) : GRec :=
  genInsAfter Γ K rep x (anchorAt Γ K i)

/-- Positional intent: delete the element at index `i` of the view. -/
def genDelAt (Γ : OrderedPrefixCode) (K : Know) (rep : Replica)
    (t i : ℕ) : GRec :=
  { op := (t, rep, SOp.del ((gView Γ K).getD i 0))
    lo := 0, ro := none, chain := [] }

/-- Knowledge sync: absorb everything of `K'` not already known. Whole
knowledge sets transfer, so causal delivery is automatic and the appended
records keep their source order (inserts stay before their deletes). -/
def syncK (K K' : Know) : Know := K ++ K'.filter (fun g => decide (g ∉ K))

/-- Reachability of a global configuration (replica index ↦ knowledge)
under the Fugue generation policy: local positional inserts with globally
fresh, locally dominant (Lamport) ids; local positional deletes with fresh
timestamps; pairwise sync. -/
inductive FugueReach (Γ : OrderedPrefixCode) : (ℕ → Know) → Prop where
  | init : FugueReach Γ (fun _ => [])
  | ins {G : ℕ → Know} (r x i : ℕ) :
      FugueReach Γ G → 0 < x →
      (∀ q, ∀ g ∈ G q, g.op.1 ≠ x) →
      (∀ m ∈ gMintedIds (G r), m < x) →
      FugueReach Γ (Function.update G r (G r ++ [genInsAt Γ (G r) r x i]))
  | del {G : ℕ → Know} (r t i : ℕ) :
      FugueReach Γ G → 0 < t →
      (∀ q, ∀ g ∈ G q, g.op.1 ≠ t) →
      FugueReach Γ (Function.update G r (G r ++ [genDelAt Γ (G r) r t i]))
  | sync {G : ℕ → Know} (r r' : ℕ) :
      FugueReach Γ G →
      FugueReach Γ (Function.update G r (syncK (G r) (G r')))

/-! ## §2  The adapted W-K statement

Definition 4 of arXiv:2305.00583v3, restated over one replica's knowledge.
The list order `<` (the strong list specification's total order, elements
including tombstones) is `gBefore`: descending key order over minted
coordinates. The comparison quantifiers range over `gMintedIds` (all
minted elements, dead included): the strict reading, which is the one the
paper's Theorem-9 proof requires (the live-only reading is unsatisfiable
for this family). `start` is the empty chain (the root key); under
the Fugue policy every minted element sits below it, so "start before
everything" holds literally in the key order. -/

def gLoOf (K : Know) (x : ℕ) : ℕ := ((gRecOfId K x).map GRec.lo).getD 0

def gRoOf (K : Know) (x : ℕ) : Option ℕ :=
  ((gRecOfId K x).map GRec.ro).getD none

/-- The strong-list total order: `x` displays before `y`. -/
def gBefore (Γ : OrderedPrefixCode) (K : Know) (x y : ℕ) : Prop :=
  keyLt (gKey Γ K y) (gKey Γ K x) = true

instance (Γ : OrderedPrefixCode) (K : Know) (x y : ℕ) :
    Decidable (gBefore Γ K x y) :=
  inferInstanceAs (Decidable (_ = true))

/-- `x` is a live list element. -/
def gLive (Γ : OrderedPrefixCode) (K : Know) (x : ℕ) : Prop :=
  x ∈ gView Γ K

instance (Γ : OrderedPrefixCode) (K : Know) (x : ℕ) :
    Decidable (gLive Γ K x) :=
  inferInstanceAs (Decidable (x ∈ gView Γ K))

/-- `x` and `y` are consecutive list elements: `x` before `y` and no LIVE
element strictly between (tombstones are skipped by the visible list). -/
def gConsecutive (Γ : OrderedPrefixCode) (K : Know) (x y : ℕ) : Prop :=
  gBefore Γ K x y ∧
    ∀ c, gLive Γ K c → ¬ (gBefore Γ K x c ∧ gBefore Γ K c y)

/-- `c` is a descendant of `p` in the left-origin tree (the tree whose
edges are the recorded `lo` fields, rooted at start = 0). -/
def loDesc (K : Know) (c p : ℕ) : Prop := ∃ n : ℕ, (gLoOf K)^[n] c = p

/-- **Lemma 5's exception** for the backward condition at the pair
`(A, B)`: (i) different left origins, and (ii) some live `C` strictly
between `A.leftOrigin` and `B` is not a descendant of `A.leftOrigin` in
the left-origin tree. -/
def BackwardException (Γ : OrderedPrefixCode) (K : Know) (A B : ℕ) : Prop :=
  gLoOf K A ≠ gLoOf K B ∧
  ∃ C ∈ gMintedIds K, gLive Γ K C ∧
    gBefore Γ K (gLoOf K A) C ∧ gBefore Γ K C B ∧ ¬ loDesc K C (gLoOf K A)

/-- **Condition (1), forward non-interleaving** (Definition 2): if `A` is
the left origin of `B` and `B` is earliest (in the tombstone-including
order) among elements with left origin `A`, then `A` and `B` are
consecutive list elements. -/
def ForwardNI (Γ : OrderedPrefixCode) (K : Know) : Prop :=
  ∀ A ∈ gMintedIds K, ∀ B ∈ gMintedIds K,
    gLive Γ K A → gLive Γ K B → gLoOf K B = A →
    (∀ D ∈ gMintedIds K, gLoOf K D = A → D ≠ B → gBefore Γ K B D) →
    gConsecutive Γ K A B

/-- **Condition (2), backward non-interleaving with exceptions**: if `B`
is the right origin of `A` and `A` is latest among elements with right
origin `B`, then `A` and `B` are consecutive, unless Lemma 5's exception
applies. -/
def BackwardNIExc (Γ : OrderedPrefixCode) (K : Know) : Prop :=
  ∀ A ∈ gMintedIds K, ∀ B ∈ gMintedIds K,
    gLive Γ K A → gLive Γ K B → gRoOf K A = some B →
    (∀ D ∈ gMintedIds K, gRoOf K D = some B → D ≠ A → gBefore Γ K D A) →
    ¬ BackwardException Γ K A B →
    gConsecutive Γ K A B

/-- **Condition (3), the same-origin tiebreak**: same left origin and same
right origin implies the lower id displays earlier. -/
def SameOriginLowFirst (Γ : OrderedPrefixCode) (K : Know) : Prop :=
  ∀ A ∈ gMintedIds K, ∀ B ∈ gMintedIds K,
    gLive Γ K A → gLive Γ K B →
    gLoOf K A = gLoOf K B → gRoOf K A = gRoOf K B → A < B →
    gBefore Γ K A B

/-- **The adapted Definition 4** at one state. -/
def MaxNonInterleaving (Γ : OrderedPrefixCode) (K : Know) : Prop :=
  ForwardNI Γ K ∧ BackwardNIExc Γ K ∧ SameOriginLowFirst Γ K

/-- **The full W-K maximal non-interleaving statement** for the sided
embed under the Fugue policy: every replica state of every reachable
configuration satisfies the three conditions. REFUTED below, twice
(`fugue_not_maximally_noninterleaving`, condition (3);
`fugue_backward_gap` + `fugue_not_maximally_noninterleaving_backward`,
condition (2), the paper's own Fugue-vs-FugueMax gap). -/
def FugueMaximallyNonInterleaving (Γ : OrderedPrefixCode) : Prop :=
  ∀ G : ℕ → Know, FugueReach Γ G → ∀ r, MaxNonInterleaving Γ (G r)

/-- **Forward non-interleaving** for the sided embed under the Fugue
policy (Definition 2). Stated; unproved here (gap G2: needs the
display-to-tree-traversal theory, the paper's Lemma 7/8 layer). -/
def FugueForwardNonInterleaving (Γ : OrderedPrefixCode) : Prop :=
  ∀ G : ℕ → Know, FugueReach Γ G → ∀ r, ForwardNI Γ (G r)

/-! ## §3  Invariants: reachable knowledge is chain-generated -/

theorem gMinted_append (K K' : Know) :
    gMinted (K ++ K') = gMinted K ++ gMinted K' :=
  List.filter_append ..

theorem gMintedIds_append (K K' : Know) :
    gMintedIds (K ++ K') = gMintedIds K ++ gMintedIds K' := by
  simp [gMintedIds, gMinted_append]

theorem hasRChild_append (K K' : Know) (v : ℕ) :
    hasRChild (K ++ K') v = (hasRChild K v || hasRChild K' v) :=
  List.any_append

theorem gChainOf_eq_of_rec {K : Know} {x : ℕ} {g : GRec}
    (h : gRecOfId K x = some g) : gChainOf K x = g.chain := by
  unfold gChainOf
  rw [h]
  rfl

theorem gRecOfId_append_left {K : Know} {x : ℕ} {g : GRec}
    (h : gRecOfId K x = some g) (K' : Know) :
    gRecOfId (K ++ K') x = some g := by
  unfold gRecOfId at h ⊢
  rw [gMinted_append, List.find?_append, h]
  rfl

theorem gRecOfId_append_fresh {K : Know} {x : ℕ}
    (hK : ∀ g ∈ K, sIsIns g.op = true → g.op.1 ≠ x) {r : GRec}
    (hr : sIsIns r.op = true) (hrx : r.op.1 = x) :
    gRecOfId (K ++ [r]) x = some r := by
  unfold gRecOfId
  rw [gMinted_append, List.find?_append]
  have h1 : (gMinted K).find? (fun g => g.op.1 == x) = none := by
    rw [List.find?_eq_none]
    intro g hg
    have hm := List.mem_filter.mp hg
    simp only [beq_iff_eq]
    exact hK g hm.1 hm.2
  have h2 : gMinted [r] = [r] := by
    simp [gMinted, hr]
  rw [h1, h2]
  simp [List.find?, hrx]

theorem not_mem_minted {K : Know} {y : ℕ}
    (h : ∀ g ∈ K, sIsIns g.op = true → g.op.1 ≠ y) :
    y ∉ gMintedIds K := by
  intro hy
  obtain ⟨g, hg, hgy⟩ := List.mem_map.mp hy
  have hm := List.mem_filter.mp hg
  exact h g hm.1 hm.2 hgy

theorem gRecOfId_of_minted {K : Know} {p : ℕ} (hp : p ∈ gMintedIds K) :
    ∃ g, gRecOfId K p = some g ∧ g ∈ K ∧ sIsIns g.op = true ∧ g.op.1 = p := by
  obtain ⟨g0, hg0, hid⟩ := List.mem_map.mp hp
  have hsome : (gRecOfId K p).isSome := by
    rw [gRecOfId, List.find?_isSome]
    exact ⟨g0, hg0, by simp [hid]⟩
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hsome
  have hmem := List.mem_of_find?_eq_some hg
  have hpg := List.find?_some hg
  refine ⟨g, hg, List.mem_of_mem_filter hmem,
    (List.mem_filter.mp hmem).2, ?_⟩
  simpa using hpg

theorem gChainOf_zero {K : Know} (hpos : ∀ g ∈ K, 1 ≤ g.op.1) :
    gChainOf K 0 = [] := by
  unfold gChainOf gRecOfId
  rw [List.find?_eq_none.mpr]
  · rfl
  · intro g hg
    have h1 := hpos g (List.mem_of_mem_filter hg)
    simp only [beq_iff_eq]
    intro h
    rw [h] at h1
    exact absurd h1 (by decide)

theorem foldl_maxKey_mem :
    ∀ (l : List (ℕ × List ℕ)) (acc : Option (ℕ × List ℕ)) {p : ℕ × List ℕ},
      l.foldl maxKey acc = some p → acc = some p ∨ p ∈ l := by
  intro l
  induction l with
  | nil => intro acc p h; exact Or.inl h
  | cons q t ih =>
      intro acc p h
      rw [List.foldl_cons] at h
      rcases ih (maxKey acc q) h with h' | h'
      · cases acc with
        | none =>
            simp only [maxKey] at h'
            injection h' with h''
            subst h''
            exact Or.inr List.mem_cons_self
        | some b =>
            simp only [maxKey] at h'
            by_cases hk : keyLt b.2 q.2 = true
            · rw [if_pos hk] at h'
              injection h' with h''
              subst h''
              exact Or.inr List.mem_cons_self
            · rw [if_neg hk] at h'
              exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')

theorem succCand_sub {Γ : OrderedPrefixCode} {K : Know} {a : ℕ}
    {p : ℕ × List ℕ} (h : p ∈ succCand Γ K a) : p ∈ gKeys Γ K := by
  unfold succCand at h
  by_cases h0 : a = 0
  · rwa [if_pos h0] at h
  · rw [if_neg h0] at h
    exact List.mem_of_mem_filter h

theorem succOf_mem {Γ : OrderedPrefixCode} {K : Know} {a n : ℕ}
    (h : succOf Γ K a = some n) : n ∈ gMintedIds K := by
  unfold succOf at h
  cases hf : (succCand Γ K a).foldl maxKey none with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some p =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      rcases foldl_maxKey_mem _ none hf with h' | h'
      · exact absurd h' (by simp)
      · obtain ⟨g, hg, hpg⟩ := List.mem_map.mp (succCand_sub h')
        subst hpg
        exact List.mem_map.mpr ⟨g, hg, rfl⟩

theorem fugueChoose_of_not_hasR (Γ : OrderedPrefixCode) (K : Know) (a : ℕ)
    (h : hasRChild K a = false) : fugueChoose Γ K a = (Side.R, a) := by
  unfold fugueChoose
  rw [h]
  cases succOf Γ K a with
  | none => rfl
  | some n => rfl

theorem fugueChoose_parent_or (Γ : OrderedPrefixCode) (K : Know) (a : ℕ) :
    (fugueChoose Γ K a).2 = a ∨ succOf Γ K a = some (fugueChoose Γ K a).2 := by
  unfold fugueChoose
  cases hs : succOf Γ K a with
  | none => exact Or.inl rfl
  | some n =>
      cases hR : hasRChild K a with
      | false => exact Or.inl rfl
      | true => exact Or.inr rfl

theorem gView_sub_minted (Γ : OrderedPrefixCode) (K : Know) :
    ∀ t ∈ gView Γ K, t ∈ gMintedIds K := by
  intro t ht
  obtain ⟨r, hr, hrt⟩ := List.mem_map.mp ht
  obtain ⟨o, ho, hins, hrec⟩ := s_fold_rec_sub Γ (gOps K) r hr
  obtain ⟨g, hg, hgo⟩ := List.mem_map.mp ho
  refine List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, ?_⟩, ?_⟩
  · rw [hgo]; exact hins
  · rw [← hrt, hrec, ← hgo]
    rfl

theorem anchorAt_cases (Γ : OrderedPrefixCode) (K : Know) (i : ℕ) :
    anchorAt Γ K i = 0 ∨ anchorAt Γ K i ∈ gView Γ K := by
  unfold anchorAt
  by_cases h0 : i = 0
  · rw [if_pos h0]; exact Or.inl rfl
  · rw [if_neg h0]
    by_cases hlt : i - 1 < (gView Γ K).length
    · right
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
        Option.getD_some]
      exact List.getElem_mem hlt
    · left
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none
        (Nat.le_of_not_lt hlt)]
      rfl

/-- Projection equations for `genInsAfter` (plain `rfl`, packaged so the
goals never force deep `whnf` through the policy functions). -/
theorem genInsAfter_chain (Γ : OrderedPrefixCode) (K : Know) (rep : Replica)
    (x a : ℕ) :
    (genInsAfter Γ K rep x a).chain
      = gChainOf K (fugueChoose Γ K a).2 ++
        [((fugueChoose Γ K a).1, x - (fugueChoose Γ K a).2)] := rfl

theorem genInsAfter_op (Γ : OrderedPrefixCode) (K : Know) (rep : Replica)
    (x a : ℕ) :
    (genInsAfter Γ K rep x a).op
      = (x, rep, SOp.ins x
          (sidedCoordOf Γ (gChainOf K (fugueChoose Γ K a).2))
          (fugueChoose Γ K a).2 (fugueChoose Γ K a).1) := rfl

/-- The wf triple of a freshly generated insert: positive chain,
telescoping sum, coordinate coherence. -/
theorem genInsAfter_wf (Γ : OrderedPrefixCode) {K : Know} (rep : Replica)
    {x : ℕ} (a : ℕ) (hx : 0 < x)
    (hpos : ∀ g ∈ K, 1 ≤ g.op.1)
    (hwfK : ∀ g ∈ K, sIsIns g.op = true →
      PosSChain g.chain ∧ ((g.chain.map Prod.snd).sum = g.op.1) ∧
      sCoord Γ g.op = sidedCoordOf Γ g.chain)
    (hlam : ∀ m ∈ gMintedIds K, m < x)
    (ha : a = 0 ∨ a ∈ gMintedIds K) :
    PosSChain (genInsAfter Γ K rep x a).chain ∧
    (((genInsAfter Γ K rep x a).chain.map Prod.snd).sum
      = (genInsAfter Γ K rep x a).op.1) ∧
    sCoord Γ (genInsAfter Γ K rep x a).op
      = sidedCoordOf Γ (genInsAfter Γ K rep x a).chain := by
  have hp : (fugueChoose Γ K a).2 = 0 ∨ (fugueChoose Γ K a).2 ∈ gMintedIds K := by
    rcases fugueChoose_parent_or Γ K a with h | h
    · rw [h]; exact ha
    · exact Or.inr (succOf_mem h)
  have hpc : PosSChain (gChainOf K (fugueChoose Γ K a).2) ∧
      ((gChainOf K (fugueChoose Γ K a).2).map Prod.snd).sum
        = (fugueChoose Γ K a).2 := by
    rcases hp with h0 | hm
    · rw [h0, gChainOf_zero hpos]
      exact ⟨by intro e he; simp at he, rfl⟩
    · obtain ⟨g, hfind, hgK, hins, hid⟩ := gRecOfId_of_minted hm
      rw [gChainOf_eq_of_rec hfind]
      obtain ⟨h1, h2, -⟩ := hwfK g hgK hins
      exact ⟨h1, by rw [h2, hid]⟩
  have hplt : (fugueChoose Γ K a).2 < x := by
    rcases hp with h0 | hm
    · rw [h0]; exact hx
    · exact hlam _ hm
  rw [genInsAfter_chain, genInsAfter_op]
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.mp he with h | h
    · exact hpc.1 e h
    · rw [List.mem_singleton] at h
      subst h
      exact Nat.sub_pos_of_lt hplt
  · rw [List.map_append, List.sum_append, hpc.2]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero]
    exact Nat.add_sub_cancel' (Nat.le_of_lt hplt)
  · rw [sidedCoordOf_append]
    simp [sCoord, sidedCoordOf]

/-- The reachability invariant: ids are positive, insert records carry
positive chains telescoping to their ids with coherent coordinates, and
insert ids are globally unique (record-identifying). -/
structure GInv (Γ : OrderedPrefixCode) (G : ℕ → Know) : Prop where
  pos : ∀ q, ∀ g ∈ G q, 1 ≤ g.op.1
  wf : ∀ q, ∀ g ∈ G q, sIsIns g.op = true →
    PosSChain g.chain ∧ ((g.chain.map Prod.snd).sum = g.op.1) ∧
    sCoord Γ g.op = sidedCoordOf Γ g.chain
  uniq : ∀ q q', ∀ g ∈ G q, ∀ g' ∈ G q', sIsIns g.op = true →
    sIsIns g'.op = true → g.op.1 = g'.op.1 → g = g'

theorem mem_update_elim {G : ℕ → Know} {r : ℕ} {K : Know} {q : ℕ} {g : GRec}
    (hg : g ∈ Function.update G r K q) :
    (q ≠ r ∧ g ∈ G q) ∨ (q = r ∧ g ∈ K) := by
  by_cases hq : q = r
  · subst hq
    rw [Function.update_self] at hg
    exact Or.inr ⟨rfl, hg⟩
  · rw [Function.update_of_ne hq] at hg
    exact Or.inl ⟨hq, hg⟩

theorem mem_syncK {g : GRec} {K K' : Know} (h : g ∈ syncK K K') :
    g ∈ K ∨ g ∈ K' := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_of_mem_filter h)

theorem fugueReach_inv (Γ : OrderedPrefixCode) {G : ℕ → Know}
    (h : FugueReach Γ G) : GInv Γ G := by
  induction h with
  | init =>
      exact ⟨fun q g hg => absurd hg (by simp),
        fun q g hg => absurd hg (by simp),
        fun q q' g hg => absurd hg (by simp)⟩
  | @ins G r x i hG hx hfresh hlam ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro q g hg
        rcases mem_update_elim hg with ⟨-, hg'⟩ | ⟨-, hg'⟩
        · exact ih.pos q g hg'
        · rcases List.mem_append.mp hg' with h' | h'
          · exact ih.pos r g h'
          · rw [List.mem_singleton] at h'
            subst h'
            exact hx
      · intro q g hg hins
        rcases mem_update_elim hg with ⟨-, hg'⟩ | ⟨-, hg'⟩
        · exact ih.wf q g hg' hins
        · rcases List.mem_append.mp hg' with h' | h'
          · exact ih.wf r g h' hins
          · rw [List.mem_singleton] at h'
            subst h'
            have ha : anchorAt Γ (G r) i = 0 ∨
                anchorAt Γ (G r) i ∈ gMintedIds (G r) := by
              rcases anchorAt_cases Γ (G r) i with h0 | hv
              · exact Or.inl h0
              · exact Or.inr (gView_sub_minted Γ (G r) _ hv)
            exact genInsAfter_wf Γ r (anchorAt Γ (G r) i) hx
              (ih.pos r) (ih.wf r) hlam ha
      · intro q q' g hg g' hg' hins hins' hid
        rcases mem_update_elim hg with ⟨-, hg1⟩ | ⟨-, hg1⟩ <;>
          rcases mem_update_elim hg' with ⟨-, hg2⟩ | ⟨-, hg2⟩
        · exact ih.uniq q q' g hg1 g' hg2 hins hins' hid
        · rcases List.mem_append.mp hg2 with h2 | h2
          · exact ih.uniq q r g hg1 g' h2 hins hins' hid
          · rw [List.mem_singleton] at h2
            subst h2
            exact absurd (by rw [hid]; rfl) (hfresh q g hg1)
        · rcases List.mem_append.mp hg1 with h1 | h1
          · exact ih.uniq r q' g h1 g' hg2 hins hins' hid
          · rw [List.mem_singleton] at h1
            subst h1
            exact absurd (by rw [← hid]; rfl) (hfresh q' g' hg2)
        · rcases List.mem_append.mp hg1 with h1 | h1 <;>
            rcases List.mem_append.mp hg2 with h2 | h2
          · exact ih.uniq r r g h1 g' h2 hins hins' hid
          · rw [List.mem_singleton] at h2
            subst h2
            exact absurd (by rw [hid]; rfl) (hfresh r g h1)
          · rw [List.mem_singleton] at h1
            subst h1
            exact absurd (by rw [← hid]; rfl) (hfresh r g' h2)
          · rw [List.mem_singleton] at h1
            rw [List.mem_singleton] at h2
            rw [h1, h2]
  | @del G r t i hG ht hfresh ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro q g hg
        rcases mem_update_elim hg with ⟨-, hg'⟩ | ⟨-, hg'⟩
        · exact ih.pos q g hg'
        · rcases List.mem_append.mp hg' with h' | h'
          · exact ih.pos r g h'
          · rw [List.mem_singleton] at h'
            subst h'
            exact ht
      · intro q g hg hins
        rcases mem_update_elim hg with ⟨-, hg'⟩ | ⟨-, hg'⟩
        · exact ih.wf q g hg' hins
        · rcases List.mem_append.mp hg' with h' | h'
          · exact ih.wf r g h' hins
          · rw [List.mem_singleton] at h'
            subst h'
            simp [genDelAt, sIsIns] at hins
      · intro q q' g hg g' hg' hins hins' hid
        have hmem : ∀ {qq : ℕ} {gg : GRec},
            gg ∈ Function.update G r (G r ++ [genDelAt Γ (G r) r t i]) qq →
            sIsIns gg.op = true → ∃ q₀, gg ∈ G q₀ := by
          intro qq gg hgg hi
          rcases mem_update_elim hgg with ⟨-, h'⟩ | ⟨-, h'⟩
          · exact ⟨qq, h'⟩
          · rcases List.mem_append.mp h' with h'' | h''
            · exact ⟨r, h''⟩
            · rw [List.mem_singleton] at h''
              subst h''
              simp [genDelAt, sIsIns] at hi
        obtain ⟨q1, h1⟩ := hmem hg hins
        obtain ⟨q2, h2⟩ := hmem hg' hins'
        exact ih.uniq q1 q2 g h1 g' h2 hins hins' hid
  | @sync G r r' hG ih =>
      have hmem : ∀ {qq : ℕ} {gg : GRec},
          gg ∈ Function.update G r (syncK (G r) (G r')) qq →
          ∃ q₀, gg ∈ G q₀ := by
        intro qq gg hgg
        rcases mem_update_elim hgg with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact ⟨qq, h'⟩
        · rcases mem_syncK h' with h'' | h''
          · exact ⟨r, h''⟩
          · exact ⟨r', h''⟩
      refine ⟨?_, ?_, ?_⟩
      · intro q g hg
        obtain ⟨q0, h0⟩ := hmem hg
        exact ih.pos q0 g h0
      · intro q g hg hins
        obtain ⟨q0, h0⟩ := hmem hg
        exact ih.wf q0 g h0 hins
      · intro q q' g hg g' hg' hins hins' hid
        obtain ⟨q1, h1⟩ := hmem hg
        obtain ⟨q2, h2⟩ := hmem hg'
        exact ih.uniq q1 q2 g h1 g' h2 hins hins' hid

#print axioms fugueReach_inv

/-- The record found for a stored id is the record itself (insert ids are
record-identifying on reachable knowledge). -/
theorem gChainOf_spec {Γ : OrderedPrefixCode} {G : ℕ → Know}
    (inv : GInv Γ G) {q : ℕ} {g : GRec} (hg : g ∈ G q)
    (hins : sIsIns g.op = true) : gChainOf (G q) g.op.1 = g.chain := by
  have hmem : g.op.1 ∈ gMintedIds (G q) :=
    List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, hins⟩, rfl⟩
  obtain ⟨g', hfind, hg'K, hins', hid⟩ := gRecOfId_of_minted hmem
  have : g' = g := inv.uniq q q g' hg'K g hg hins' hins hid
  rw [gChainOf_eq_of_rec hfind, this]

/-- **Reachable knowledge is chain-generated**: exactly the honesty
layer's `chain_gen` shape, with `gChainOf` as the chain witness. Feeds
`sided_fold_subtree_convex` at every reachable state. -/
theorem fugueReach_chain_gen (Γ : OrderedPrefixCode) {G : ℕ → Know}
    (h : FugueReach Γ G) (r : ℕ) :
    ∀ o ∈ gOps (G r), sIsIns o = true →
      PosSChain (gChainOf (G r) o.1) ∧
      sCoord Γ o = sidedCoordOf Γ (gChainOf (G r) o.1) ∧
      ((gChainOf (G r) o.1).map Prod.snd).sum = o.1 := by
  have inv := fugueReach_inv Γ h
  intro o ho hins
  obtain ⟨g, hg, hgo⟩ := List.mem_map.mp ho
  subst hgo
  rw [gChainOf_spec inv hg hins]
  obtain ⟨h1, h2, h3⟩ := inv.wf r g hg hins
  exact ⟨h1, h3, h2⟩

#print axioms fugueReach_chain_gen

/-! ## §4  Candidate (a): two concurrent runs never interleave -/

/-- Two subtree families with prefix-incomparable roots never interleave
in a chain-generated fold: no member of the second family displays
strictly between two members of the first. The display half is
`sided_fold_subtree_convex`; the rest is prefix algebra. -/
theorem fugue_two_runs_no_interleave (Γ : OrderedPrefixCode)
    {ρ : List (Op SOp)} (chainOf : ℕ → SChain)
    (hch : ∀ o ∈ ρ, sIsIns o = true →
      PosSChain (chainOf o.1) ∧ sCoord Γ o = sidedCoordOf Γ (chainOf o.1) ∧
      ((chainOf o.1).map Prod.snd).sum = o.1)
    {px py : SChain}
    (hpq : ¬ px <+: py) (hqp : ¬ py <+: px)
    {x z y : SRec}
    (hx : x ∈ sFold Γ ρ) (hz : z ∈ sFold Γ ρ) (hy : y ∈ sFold Γ ρ)
    (hxs : px <+: chainOf x.1) (hys : px <+: chainOf y.1)
    (hzs : py <+: chainOf z.1)
    (hzx : keyLt (sKey z.2.2) (sKey x.2.2) = true)
    (hyz : keyLt (sKey y.2.2) (sKey z.2.2) = true) : False := by
  obtain ⟨ex, hex⟩ := hxs
  obtain ⟨ey, hey⟩ := hys
  obtain ⟨ez, hez⟩ := sided_fold_subtree_convex Γ chainOf hch hx hz hy
    ⟨ex, hex.symm⟩ ⟨ey, hey.symm⟩ hzx hyz
  have h1 : px <+: chainOf z.1 := ⟨ez, hez.symm⟩
  rcases List.prefix_or_prefix_of_prefix h1 hzs with h | h
  · exact hpq h
  · exact hqp h

#print axioms fugue_two_runs_no_interleave

/-- A run whose elements chain: each element's birth chain extends the
previous element's chain by one entry. This is what the Fugue policy
generates for forward runs (R-entries) and backward runs (L-entries)
alike. -/
def RunChains (chainOf : ℕ → SChain) : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      (∃ e, chainOf b = chainOf a ++ [e]) ∧ RunChains chainOf (b :: rest)

theorem runChains_head_prefix (chainOf : ℕ → SChain) :
    ∀ (xs : List ℕ) (h : ℕ), RunChains chainOf (h :: xs) →
      ∀ m ∈ h :: xs, chainOf h <+: chainOf m := by
  intro xs
  induction xs with
  | nil =>
      intro h _ m hm
      rw [List.mem_singleton] at hm
      subst hm
      exact List.prefix_refl _
  | cons b rest ih =>
      intro h hrc m hm
      obtain ⟨⟨e, he⟩, hrest⟩ := hrc
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact List.prefix_refl _
      · exact List.IsPrefix.trans ⟨[e], he.symm⟩ (ih b hrest m hm')

/-- **Candidate (a), the kernel half**: members of two runs whose chains
nest (each op anchored at the previous, the Fugue shape) and whose head
chains are prefix-incomparable (the concurrency consequence: a replica
cannot extend a chain it has never seen) never interleave in any
chain-generated fold. -/
theorem fugue_concurrent_runs_no_interleave (Γ : OrderedPrefixCode)
    {ρ : List (Op SOp)} (chainOf : ℕ → SChain)
    (hch : ∀ o ∈ ρ, sIsIns o = true →
      PosSChain (chainOf o.1) ∧ sCoord Γ o = sidedCoordOf Γ (chainOf o.1) ∧
      ((chainOf o.1).map Prod.snd).sum = o.1)
    {h1 h2 : ℕ} {run1 run2 : List ℕ}
    (hrc1 : RunChains chainOf (h1 :: run1))
    (hrc2 : RunChains chainOf (h2 :: run2))
    (hpq : ¬ chainOf h1 <+: chainOf h2) (hqp : ¬ chainOf h2 <+: chainOf h1)
    {x z y : SRec}
    (hx : x ∈ sFold Γ ρ) (hz : z ∈ sFold Γ ρ) (hy : y ∈ sFold Γ ρ)
    (hxm : x.1 ∈ h1 :: run1) (hym : y.1 ∈ h1 :: run1)
    (hzm : z.1 ∈ h2 :: run2)
    (hzx : keyLt (sKey z.2.2) (sKey x.2.2) = true)
    (hyz : keyLt (sKey y.2.2) (sKey z.2.2) = true) : False :=
  fugue_two_runs_no_interleave Γ chainOf hch hpq hqp hx hz hy
    (runChains_head_prefix chainOf run1 h1 hrc1 x.1 hxm)
    (runChains_head_prefix chainOf run1 h1 hrc1 y.1 hym)
    (runChains_head_prefix chainOf run2 h2 hrc2 z.1 hzm) hzx hyz

#print axioms fugue_concurrent_runs_no_interleave

/-- Candidate (a) at any reachable Fugue configuration: the fold of any
replica's knowledge never interleaves two runs with prefix-incomparable
heads. -/
theorem fugue_reachable_runs_no_interleave (Γ : OrderedPrefixCode)
    {G : ℕ → Know} (hreach : FugueReach Γ G) (r : ℕ)
    {h1 h2 : ℕ} {run1 run2 : List ℕ}
    (hrc1 : RunChains (gChainOf (G r)) (h1 :: run1))
    (hrc2 : RunChains (gChainOf (G r)) (h2 :: run2))
    (hpq : ¬ gChainOf (G r) h1 <+: gChainOf (G r) h2)
    (hqp : ¬ gChainOf (G r) h2 <+: gChainOf (G r) h1)
    {x z y : SRec}
    (hx : x ∈ gFold Γ (G r)) (hz : z ∈ gFold Γ (G r))
    (hy : y ∈ gFold Γ (G r))
    (hxm : x.1 ∈ h1 :: run1) (hym : y.1 ∈ h1 :: run1)
    (hzm : z.1 ∈ h2 :: run2)
    (hzx : keyLt (sKey z.2.2) (sKey x.2.2) = true)
    (hyz : keyLt (sKey y.2.2) (sKey z.2.2) = true) : False :=
  fugue_concurrent_runs_no_interleave Γ (gChainOf (G r))
    (fugueReach_chain_gen Γ hreach r) hrc1 hrc2 hpq hqp hx hz hy
    hxm hym hzm hzx hyz

#print axioms fugue_reachable_runs_no_interleave

/-! ## §5  The policy half: forward runs chain -/

/-- Generate a forward run: insert the first element after `a`, then each
next element after the previous one. -/
def genForwardRun (Γ : OrderedPrefixCode) (rep : Replica) :
    Know → ℕ → List ℕ → Know
  | K, _, [] => K
  | K, a, x :: xs =>
      genForwardRun Γ rep (K ++ [genInsAfter Γ K rep x a]) x xs

theorem genForwardRun_prefix (Γ : OrderedPrefixCode) (rep : Replica) :
    ∀ (xs : List ℕ) (K : Know) (a : ℕ),
      K <+: genForwardRun Γ rep K a xs := by
  intro xs
  induction xs with
  | nil => intro K a; exact List.prefix_refl K
  | cons x tail ih =>
      intro K a
      exact List.IsPrefix.trans (List.prefix_append K _)
        (ih (K ++ [genInsAfter Γ K rep x a]) x)

theorem gAnchorR_genInsAfter_eq_false (Γ : OrderedPrefixCode) (K : Know)
    (rep : Replica) {x a v : ℕ} (hav : a ≠ v)
    (hsucc : ∀ n, succOf Γ K a = some n → n ≠ v) :
    gAnchorR v (genInsAfter Γ K rep x a) = false := by
  have hpv : (fugueChoose Γ K a).2 ≠ v := by
    rcases fugueChoose_parent_or Γ K a with h | h
    · rw [h]; exact hav
    · exact hsucc _ h
  simp [gAnchorR, genInsAfter, hpv]

/-- **Forward Fugue runs chain**: anchoring each insert at the previous
run element mints each element as an R-child of the previous (the anchor
is fresh, so it has never had an R-child), so the run's chains nest. The
hypotheses say the run ids are fresh for `K` (never minted, never already
R-anchored, distinct from the launch anchor) and mutually distinct. -/
theorem fugue_forward_run_chains (Γ : OrderedPrefixCode) (rep : Replica) :
    ∀ (xs : List ℕ) (K : Know) (a : ℕ),
      (∀ y ∈ xs, hasRChild K y = false) →
      (∀ y ∈ xs, ∀ g ∈ K, sIsIns g.op = true → g.op.1 ≠ y) →
      xs.Nodup →
      (∀ y ∈ xs, a ≠ y) →
      RunChains (gChainOf (genForwardRun Γ rep K a xs)) xs := by
  intro xs
  induction xs with
  | nil => intro K a _ _ _ _; exact trivial
  | cons x tail ih =>
      intro K a hR hfresh hnd hax
      have hxfresh : ∀ g ∈ K, sIsIns g.op = true → g.op.1 ≠ x :=
        hfresh x List.mem_cons_self
      have hsucc_ne : ∀ y, y ∈ x :: tail →
          ∀ n, succOf Γ K a = some n → n ≠ y := by
        intro y hy n hn hny
        exact not_mem_minted (hfresh y hy) (hny ▸ succOf_mem hn)
      -- the freshly minted head record
      have hrecR : ∀ y ∈ x :: tail,
          gAnchorR y (genInsAfter Γ K rep x a) = false := by
        intro y hy
        exact gAnchorR_genInsAfter_eq_false Γ K rep (hax y hy) (hsucc_ne y hy)
      have hstep_R : ∀ y ∈ tail,
          hasRChild (K ++ [genInsAfter Γ K rep x a]) y = false := by
        intro y hy
        rw [hasRChild_append, hR y (List.mem_cons_of_mem _ hy)]
        show (false || hasRChild [genInsAfter Γ K rep x a] y) = false
        simp only [Bool.false_or, hasRChild, List.any_cons, List.any_nil,
          Bool.or_false]
        exact hrecR y (List.mem_cons_of_mem _ hy)
      have hstep_fresh : ∀ y ∈ tail,
          ∀ g ∈ K ++ [genInsAfter Γ K rep x a],
            sIsIns g.op = true → g.op.1 ≠ y := by
        intro y hy g hg hins
        rcases List.mem_append.mp hg with h' | h'
        · exact hfresh y (List.mem_cons_of_mem _ hy) g h' hins
        · rw [List.mem_singleton] at h'
          subst h'
          show x ≠ y
          intro hxy
          exact (List.nodup_cons.mp hnd).1 (hxy ▸ hy)
      have hstep_ax : ∀ y ∈ tail, x ≠ y := by
        intro y hy hxy
        exact (List.nodup_cons.mp hnd).1 (hxy ▸ hy)
      have htail := ih (K ++ [genInsAfter Γ K rep x a]) x hstep_R
        hstep_fresh (List.nodup_cons.mp hnd).2 hstep_ax
      cases tail with
      | nil => exact trivial
      | cons y rest =>
          refine ⟨?_, htail⟩
          -- the head link: y is minted as R-child of x
          have hfx : hasRChild (K ++ [genInsAfter Γ K rep x a]) x = false := by
            rw [hasRChild_append, hR x List.mem_cons_self]
            show (false || hasRChild [genInsAfter Γ K rep x a] x) = false
            simp only [Bool.false_or, hasRChild, List.any_cons, List.any_nil,
              Bool.or_false]
            exact hrecR x List.mem_cons_self
          have f2 : fugueChoose Γ (K ++ [genInsAfter Γ K rep x a]) x
              = (Side.R, x) := fugueChoose_of_not_hasR Γ _ x hfx
          have hchainy : (genInsAfter Γ (K ++ [genInsAfter Γ K rep x a])
                rep y x).chain
              = gChainOf (K ++ [genInsAfter Γ K rep x a]) x ++
                [(Side.R, y - x)] := by
            rw [genInsAfter_chain, f2]
          have hrecfind : gRecOfId (K ++ [genInsAfter Γ K rep x a]) x
              = some (genInsAfter Γ K rep x a) :=
            gRecOfId_append_fresh hxfresh rfl rfl
          have hrecyfind : gRecOfId ((K ++ [genInsAfter Γ K rep x a]) ++
                [genInsAfter Γ (K ++ [genInsAfter Γ K rep x a]) rep y x]) y
              = some (genInsAfter Γ (K ++ [genInsAfter Γ K rep x a]) rep y x) :=
            gRecOfId_append_fresh (hstep_fresh y List.mem_cons_self) rfl rfl
          obtain ⟨T, hT⟩ := genForwardRun_prefix Γ rep rest
            ((K ++ [genInsAfter Γ K rep x a]) ++
              [genInsAfter Γ (K ++ [genInsAfter Γ K rep x a]) rep y x]) y
          have hfinx : gRecOfId (genForwardRun Γ rep K a (x :: y :: rest)) x
              = some (genInsAfter Γ K rep x a) := by
            show gRecOfId (genForwardRun Γ rep
              ((K ++ [genInsAfter Γ K rep x a]) ++
                [genInsAfter Γ (K ++ [genInsAfter Γ K rep x a]) rep y x])
              y rest) x = _
            rw [← hT]
            exact gRecOfId_append_left (gRecOfId_append_left hrecfind _) T
          have hfiny : gRecOfId (genForwardRun Γ rep K a (x :: y :: rest)) y
              = some (genInsAfter Γ (K ++ [genInsAfter Γ K rep x a]) rep y x) := by
            show gRecOfId (genForwardRun Γ rep
              ((K ++ [genInsAfter Γ K rep x a]) ++
                [genInsAfter Γ (K ++ [genInsAfter Γ K rep x a]) rep y x])
              y rest) y = _
            rw [← hT]
            exact gRecOfId_append_left hrecyfind T
          refine ⟨(Side.R, y - x), ?_⟩
          rw [gChainOf_eq_of_rec hfiny, gChainOf_eq_of_rec hfinx, hchainy,
            gChainOf_eq_of_rec hrecfind]

#print axioms fugue_forward_run_chains

/-- The kernel piece of the backward gap (G1): extending a chain by a
NEWEST R-entry (larger delta than any existing R-continuation at that
point) preserves display precedence. This is why the freshest mint sits
adjacent to its anchor; the remaining glue, relating `succOf`'s argmax to
`schainBefore`, is the identified gap. -/
theorem schainBefore_snoc_newest {ca cm : SChain} {δ : ℕ}
    (h : schainBefore ca cm)
    (hmax : ∀ d rest, cm = ca ++ (Side.R, d) :: rest → d < δ) :
    schainBefore (ca ++ [(Side.R, δ)]) cm := by
  rcases schainBefore_inv h with ⟨d, rest, heq⟩ | ⟨d, rest, heq⟩ |
    ⟨q, e1, e2, t1, t2, hlt, h1, h2⟩
  · -- ca extends cm on the L side: still an L-extension after the snoc
    rw [heq, List.append_assoc]
    exact schainBefore.extL cm d _
  · -- cm is an R-continuation of ca: diverge at the newest entry
    have hd : d < δ := hmax d rest heq
    rw [heq, show ca ++ [(Side.R, δ)] = ca ++ (Side.R, δ) :: [] from rfl]
    exact schainBefore.diverge ca (Side.R, δ) (Side.R, d) [] rest hd
  · -- divergence below the snoc point survives
    rw [h1, h2, List.append_assoc]
    exact schainBefore.diverge q e1 e2 _ t2 hlt

#print axioms schainBefore_snoc_newest

/-! ## §6  The refutations

Both are reachable-trace countermodels, machine-checked end to end: the
full W-K statement fails for THIS policy at condition (3) (the tiebreak: the
kernel's newest-first R-sibling order is the reverse of the paper's
lowest-ID-first choice) and, independently, at condition (2) (the
Figure-7 execution: the repo policy is Fugue, not FugueMax, and this is
exactly the gap the paper proves between them). -/

theorem fresh_nil {x : ℕ} :
    ∀ q : ℕ, ∀ g ∈ (fun _ : ℕ => ([] : Know)) q, g.op.1 ≠ x := by
  intro q g hg
  simp at hg

theorem fresh_update {G : ℕ → Know} {r : ℕ} {K : Know} {x : ℕ}
    (hG : ∀ q, ∀ g ∈ G q, g.op.1 ≠ x) (hK : ∀ g ∈ K, g.op.1 ≠ x) :
    ∀ q, ∀ g ∈ Function.update G r K q, g.op.1 ≠ x := by
  intro q g hg
  rcases mem_update_elim hg with ⟨-, hg'⟩ | ⟨-, hg'⟩
  · exact hG q g hg'
  · exact hK g hg'

/-! ### §6a  Condition (3): two concurrent front inserts -/

def recT1 : GRec := genInsAt unaryCode [] 0 1 0
def recT2 : GRec := genInsAt unaryCode [] 1 2 0
def KTie : Know := syncK [recT1] [recT2]
def GT1 : ℕ → Know := Function.update (fun _ => []) 0 [recT1]
def GT2 : ℕ → Know := Function.update GT1 1 [recT2]
def GTie : ℕ → Know := Function.update GT2 0 KTie

theorem gtie_reach : FugueReach unaryCode GTie := by
  have h0 : FugueReach unaryCode (fun _ => []) := FugueReach.init
  have h1 : FugueReach unaryCode GT1 :=
    FugueReach.ins 0 1 0 h0 (by decide) fresh_nil
      (by intro m hm; simp [gMintedIds, gMinted] at hm)
  have h2 : FugueReach unaryCode GT2 :=
    FugueReach.ins 1 2 0 h1 (by decide)
      (fresh_update fresh_nil (by native_decide))
      (by intro m hm
          rw [show GT1 1 = [] from rfl] at hm
          simp [gMintedIds, gMinted] at hm)
  exact FugueReach.sync 0 1 h2

/-- **The full W-K statement is FALSE for the sided embed under the Fugue
policy** (condition 3): after two concurrent front inserts 1 and 2, both
with left origin start and right origin end, the display is `[2, 1]`, so
the lower id displays later. The kernel's newest-first sibling order is
the exact reverse of the paper's (arbitrary, but by their Theorem 10 not
optional) lowest-ID-first choice. -/
theorem fugue_not_maximally_noninterleaving :
    ¬ FugueMaximallyNonInterleaving unaryCode := by
  intro h
  obtain ⟨-, -, htb⟩ := h GTie gtie_reach 0
  have hb := htb 1 (by native_decide) 2 (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by decide)
  exact absurd hb (by native_decide)

#print axioms fugue_not_maximally_noninterleaving

/-! ### §6b  Condition (2): the paper's Figure-7 execution

Three concurrent front inserts A=5, B=4, C=3; replica 0 (knowing 5, 3)
inserts X=6 between 5 and 3; replica 1 (knowing 5, 4) inserts Y=7 between
5 and 4. Merged display `[5, 7, 6, 4, 3]`: Y=7 is the only element with
right origin B=4, yet 6 sits between 7 and 4, and the Lemma-5 exception
does not apply (everything between is a descendant of Y's left origin 5
in the left-origin tree). -/

def recF5 : GRec := genInsAt unaryCode [] 0 5 0
def recF4 : GRec := genInsAt unaryCode [] 1 4 0
def KFc1 : Know := syncK [recF4] [recF5]
def recF7 : GRec := genInsAt unaryCode KFc1 1 7 1
def KFd1 : Know := KFc1 ++ [recF7]
def recF3 : GRec := genInsAt unaryCode [] 2 3 0
def KFf0 : Know := syncK [recF5] [recF3]
def recF6 : GRec := genInsAt unaryCode KFf0 0 6 1
def KFg0 : Know := KFf0 ++ [recF6]
def KFig : Know := syncK KFg0 KFd1

def GFa : ℕ → Know := Function.update (fun _ => []) 0 [recF5]
def GFb : ℕ → Know := Function.update GFa 1 [recF4]
def GFc : ℕ → Know := Function.update GFb 1 KFc1
def GFd : ℕ → Know := Function.update GFc 1 KFd1
def GFe : ℕ → Know := Function.update GFd 2 [recF3]
def GFf : ℕ → Know := Function.update GFe 0 KFf0
def GFg : ℕ → Know := Function.update GFf 0 KFg0
def GFig : ℕ → Know := Function.update GFg 0 KFig

theorem gfig_reach : FugueReach unaryCode GFig := by
  have h0 : FugueReach unaryCode (fun _ => []) := FugueReach.init
  have ha : FugueReach unaryCode GFa :=
    FugueReach.ins 0 5 0 h0 (by decide) fresh_nil
      (by intro m hm; simp [gMintedIds, gMinted] at hm)
  have hb : FugueReach unaryCode GFb :=
    FugueReach.ins 1 4 0 ha (by decide)
      (fresh_update fresh_nil (by native_decide))
      (by intro m hm
          rw [show GFa 1 = [] from rfl] at hm
          simp [gMintedIds, gMinted] at hm)
  have hc : FugueReach unaryCode GFc := FugueReach.sync 1 0 hb
  have hd : FugueReach unaryCode GFd :=
    FugueReach.ins 1 7 1 hc (by decide)
      (fresh_update (fresh_update (fresh_update fresh_nil
        (by native_decide)) (by native_decide)) (by native_decide))
      (by native_decide)
  have he : FugueReach unaryCode GFe :=
    FugueReach.ins 2 3 0 hd (by decide)
      (fresh_update (fresh_update (fresh_update (fresh_update fresh_nil
        (by native_decide)) (by native_decide)) (by native_decide))
        (by native_decide))
      (by native_decide)
  have hf : FugueReach unaryCode GFf := FugueReach.sync 0 2 he
  have hg : FugueReach unaryCode GFg :=
    FugueReach.ins 0 6 1 hf (by decide)
      (fresh_update (fresh_update (fresh_update (fresh_update
        (fresh_update (fresh_update fresh_nil (by native_decide))
          (by native_decide)) (by native_decide)) (by native_decide))
        (by native_decide)) (by native_decide))
      (by native_decide)
  exact FugueReach.sync 0 1 hg

/-- **Condition (2) fails on the Figure-7 trace**: the backward clause
with the Lemma-5 exception refuted pointwise. This is the paper's
Fugue-vs-FugueMax gap, so the refutation of the full statement does not
hinge on the tiebreak clause. -/
theorem fugue_backward_gap : ¬ BackwardNIExc unaryCode KFig := by
  intro h
  have hcons := h 7 (by native_decide) 4 (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) ?noexc
  · obtain ⟨-, hno⟩ := hcons
    exact hno 6 (by native_decide) ⟨by native_decide, by native_decide⟩
  case noexc =>
    rintro ⟨-, C, hCmem, hClive, hb1, hb2, hnd⟩
    have hlist : gMintedIds KFig = [5, 3, 6, 4, 7] := by native_decide
    rw [hlist] at hCmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hCmem
    rcases hCmem with rfl | rfl | rfl | rfl | rfl
    · exact absurd hb1 (by native_decide)
    · exact absurd hb2 (by native_decide)
    · exact hnd ⟨1, by native_decide⟩
    · exact absurd hb2 (by native_decide)
    · exact hnd ⟨1, by native_decide⟩

#print axioms fugue_backward_gap

/-- The condition-(2) refutation lifted to the full statement, at the
reachable Figure-7 configuration. -/
theorem fugue_not_maximally_noninterleaving_backward :
    ¬ FugueMaximallyNonInterleaving unaryCode := by
  intro h
  exact fugue_backward_gap (h GFig gfig_reach 0).2.1

#print axioms fugue_not_maximally_noninterleaving_backward

/-! ## §7  SPOTs (PASS+FAIL shaped, hand-derived expected values)

Every display below was derived by hand; the FAIL pins assert the
interleaved (or FugueMax-ordered) alternative is NOT what the datatype
displays. -/

namespace FugueSPOT

/-- Extend a knowledge with one positional insert. -/
def gIns (K : Know) (rep x i : ℕ) : Know :=
  K ++ [genInsAt unaryCode K rep x i]

/-- The shared GCA: element 1 at the front. -/
def kL : Know := gIns [] 0 1 0

/-! ### L19, generated by the policy

Replica 0 backward-types 10, 30, 50 at the front; replica 1 backward-types
21, 41, 61 at the front. The generator reproduces the hand-written
`SidedSPOT.opsL19` trace literally, ops for ops. -/

def kA19 : Know := gIns (gIns (gIns kL 0 10 0) 0 30 0) 0 50 0
def kB19 : Know := gIns (gIns (gIns kL 1 21 0) 1 41 0) 1 61 0
def k19 : Know := syncK kA19 kB19

/-- PASS: the positional Fugue generator regenerates the L19 trace of
`SidedRGA_Intent.lean`'s SPOT, op for op (anchors, prefixes, sides). -/
theorem l19_policy_generates : gOps k19 = SidedSPOT.opsL19 := by
  native_decide

/-- PASS: the merged display keeps both backward runs contiguous, in text
order. -/
theorem l19_policy_display :
    gView unaryCode k19 = [50, 30, 10, 61, 41, 21, 1] := by native_decide

/-- FAIL pin: the one-sided fan's interleaved verdict on the same stamps
is exactly what this policy does NOT produce. -/
theorem l19_policy_not_interleaved :
    gView unaryCode k19 ≠ [61, 50, 41, 30, 21, 10, 1] := by native_decide

/-! ### The forward twin -/

def kAf : Know := gIns (gIns (gIns kL 0 10 1) 0 30 2) 0 50 3
def kBf : Know := gIns (gIns (gIns kL 1 21 1) 1 41 2) 1 61 3
def kFwd : Know := syncK kAf kBf

/-- PASS: two concurrent forward runs at one position stay contiguous;
the newer head's block displays first (the recency tiebreak). -/
theorem forward_twin_display :
    gView unaryCode kFwd = [1, 21, 41, 61, 10, 30, 50] := by native_decide

/-- FAIL pin: the character-interleaved order. -/
theorem forward_twin_not_interleaved :
    gView unaryCode kFwd ≠ [1, 21, 10, 41, 30, 61, 50] := by native_decide

/-! ### The mixed case: one backward run, one forward run, same position -/

def kAm : Know := gIns (gIns (gIns kL 0 10 1) 0 30 1) 0 50 1
def kMix : Know := syncK kAm kBf

/-- PASS: replica 0 backward-types after element 1 (fixed index 1) while
replica 1 forward-types after it; both blocks stay contiguous in text
order. -/
theorem mixed_display :
    gView unaryCode kMix = [1, 21, 41, 61, 50, 30, 10] := by native_decide

/-- FAIL pin: the interleaved order. -/
theorem mixed_not_interleaved :
    gView unaryCode kMix ≠ [1, 21, 50, 41, 30, 61, 10] := by native_decide

/-- The backward run of the mixed case chains (the `RunChains` shape §4
consumes), witnessed concretely: 30 is an L-child of 10, 50 of 30. -/
theorem mixed_backward_run_chains :
    RunChains (gChainOf kMix) [10, 30, 50] :=
  ⟨⟨(Side.L, 20), by native_decide⟩, ⟨(Side.L, 20), by native_decide⟩,
    trivial⟩

/-! ### The refutation traces -/

/-- PASS: the tiebreak trace displays newest first. -/
theorem tiebreak_display : gView unaryCode KTie = [2, 1] := by native_decide

/-- FAIL pin: the FugueMax (lowest-ID-first) order is NOT displayed. -/
theorem tiebreak_not_id_order : gView unaryCode KTie ≠ [1, 2] := by
  native_decide

/-- PASS: the Figure-7 display, hand-derived. -/
theorem fig7_display : gView unaryCode KFig = [5, 7, 6, 4, 3] := by
  native_decide

/-- FAIL pin: the unique maximally-non-interleaving order for this
execution (the paper's §5.2 analysis: A X Y B C) is NOT displayed. -/
theorem fig7_not_fuguemax_order : gView unaryCode KFig ≠ [5, 6, 7, 4, 3] := by
  native_decide

end FugueSPOT

#print axioms FugueSPOT.l19_policy_generates
#print axioms FugueSPOT.mixed_display

end Sal.MRDTs.Instances.SidedEmbedRGA
