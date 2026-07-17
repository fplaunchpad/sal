import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_Fugue
import Sal.MRDTs.RGA_Embed.SidedMax_ChainLex

/-!
# The FugueMax policy on the embedded-chain family: the positive twin (task #87a)

Weidner-Kleppmann Definition 6 / Theorem 9 (arXiv:2305.00583v3): FugueMax
is Fugue with right-side siblings traversed in the REVERSE order of their
right origins (ties ascending by ID), and it IS maximally non-interleaving.
The completed #84 arc refuted the full statement for the repo's
Fugue-with-recency-tiebreak policy; this file realizes FugueMax and proves
the positive twin of that arc's first refutation.

**The realization** (design section in
`whiteboard/fugue-maximal-noninterleaving.md`; Python validation
`whiteboard/litmus/fuguemax_check.py`, gauntlet + directed cases + 1500
randomized states all clean): the R-sibling order depends on the right
origin, which is not a function of `(side, delta)`, so no re-banding of
the sided alphabet realizes FugueMax (the Python `mirror` control fails
condition (2) on the adverse Figure-7 trace). The realization is the
kernel VARIANT alphabet `Sal/MRDTs/RGA_Embed/SidedMax_ChainLex.lean`:
R entries carry the mint-time KEY of the right origin (`[0]` for end),
R-siblings compare tags first (smaller tag = display-later right origin =
earlier sibling) then deltas ascending; the L band is unchanged.

Layers:

* **§1 The generation layer**: `MRec` records (op + generation-time left
  origin, right origin, FugueMax birth chain), the display fold `mFold`
  (canonical sorted state over the variant coordinates), the
  tombstone-visible successor `succOfM`, the FugueMax insert rule
  `mGenInsAfter` (Fugue's tree-position rule; R mints carry the
  successor's key as the sibling tag), positional intent, and reachability
  `MaxReach` (Lamport-fresh local inserts, local deletes, pairwise sync).

* **§2 The reachability invariant** `MInv`: ids positive and unique,
  chains wellformed (positive deltas, wellformed tags, telescoping sum),
  and the LINK clauses tying every insert record to its parent's chain —
  including the two mint-time GEOMETRY facts that make condition (3)
  provable: an R mint's right origin is NOT an R-descendant of the left
  origin (the minter had seen no R-child), and an L mint's parent (= its
  right origin) IS an R-descendant of the left origin (the argmax
  successor lands in the R-subtree; via `fm_subtree_convex`).

* **§3 The adapted W-K statement** over `MaxReach` (strict reading, as in
  the Fugue file): `ForwardNIM`, `BackwardNIExcM`, `SameOriginLowFirstM`,
  `MaxNonInterleavingM`, `FugueMaxMaximallyNonInterleaving`.

* **§4 The positive twin, PROVED**: `fuguemax_same_origin_low_first` —
  condition (3) holds at every replica of every reachable configuration.
  Same recorded origins force the same policy branch (the two geometry
  clauses collide otherwise), and same-branch siblings are kernel-ordered
  ascending.

* **§5 Run contiguity**: `fuguemax_reachable_runs_no_interleave`, the
  variant transport of the Fugue file's candidate (a).

* **§6 SPOTs** (PASS+FAIL, hand-derived, Python-matched): two front
  inserts `[1,2]`, the forward twin (lower-ID block first), L19 backward
  (unchanged), the mixed case, and BOTH Figure-7 mint orders — the
  adverse one is the trace that kills every plain re-banding.

**Honest gaps** (stated, not proved; no `sorry` anywhere): conditions (1)
and (2) (`FugueMaxForwardNonInterleaving`, `FugueMaxBackwardNonInterleaving`)
need the display-to-tree-traversal theory (the paper's Lemma 7/8 layer,
gap G2 of the completed arc), which is not built here; both are
Python-clean over 1500 randomized states and every directed case.
`fuguemax_max_noninterleaving_of_gaps` records that the full Theorem-9
statement reduces to exactly those two gaps plus the proved condition (3).
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode keyLt sKey unaryCode Side
  keyLt_irrefl keyLt_asymm keyLt_trans keyLt_total
  FMEntry FMChain fmδ PosFMChain TagOK fmTagOK TagsOK
  fw fwTag fmBlock fmCoordOf fmCoordOf_append fmCoordOf_inj
  fmEntryBefore fmChainBefore fmChainBefore_display
  fmdisplay_iff_fmChainBefore fm_subtree_convex fm_ext_after_is_R
  tagOK_key fmChainBefore_ne)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## §1  The generation layer -/

inductive MOp : Type where
  | ins (parent : ℕ) (sd : Side)
  | del (x : ℕ)
deriving DecidableEq

/-- One generation record: `ts` doubles as the element identity, `lo` is
the left origin (the intent anchor, 0 = start), `ro` the right origin (the
tombstone-visible successor at mint time, `none` = end), `chain` the
minted FugueMax birth chain. -/
structure MRec where
  ts : ℕ
  rep : ℕ
  op : MOp
  lo : ℕ
  ro : Option ℕ
  chain : FMChain
deriving DecidableEq

abbrev KnowM : Type := List MRec

def mIsIns (g : MRec) : Bool :=
  match g.op with
  | .ins _ _ => true
  | .del _ => false

theorem mIsIns_shape {g : MRec} (h : mIsIns g = true) :
    ∃ p sd, g.op = MOp.ins p sd := by
  unfold mIsIns at h
  cases hop : g.op with
  | ins p sd => exact ⟨p, sd, rfl⟩
  | del x => rw [hop] at h; simp at h

def mMinted (K : KnowM) : List MRec := K.filter (fun g => mIsIns g)

def mMintedIds (K : KnowM) : List ℕ := (mMinted K).map MRec.ts

def mRecOfId (K : KnowM) (x : ℕ) : Option MRec :=
  (mMinted K).find? (fun g => g.ts == x)

/-- The birth chain of a minted id (0, the root, has the empty chain). -/
def mChainOf (K : KnowM) (x : ℕ) : FMChain :=
  ((mRecOfId K x).map MRec.chain).getD []

/-- The strong-list sort key, tombstones included. -/
def mKey (Γ : OrderedPrefixCode) (K : KnowM) (x : ℕ) : List ℕ :=
  sKey (fmCoordOf Γ (mChainOf K x))

/-- The display fold: the canonical sorted state (reusing the sided
instance's record type and sorted insert). -/
def mStep (Γ : OrderedPrefixCode) (s : SState) (g : MRec) : SState :=
  match g.op with
  | .ins _ _ =>
      if g.ts ∈ sIds s then s
      else sInsert (g.ts, g.ts, fmCoordOf Γ g.chain) s
  | .del x => s.filter (fun r => decide (r.1 ≠ x))

def mFold (Γ : OrderedPrefixCode) (K : KnowM) : SState :=
  K.foldl (mStep Γ) []

/-- The live display: ids in document order. -/
def mView (Γ : OrderedPrefixCode) (K : KnowM) : List ℕ :=
  sIds (mFold Γ K)

theorem mFold_snoc (Γ : OrderedPrefixCode) (K : KnowM) (g : MRec) :
    mFold Γ (K ++ [g]) = mStep Γ (mFold Γ K) g := by
  unfold mFold
  rw [List.foldl_append]
  rfl

/-- Fold provenance: everything in the fold was written by a minted
record. -/
theorem m_fold_rec_sub (Γ : OrderedPrefixCode) : ∀ (K : KnowM) (r : SRec),
    r ∈ mFold Γ K → ∃ g ∈ K, mIsIns g = true ∧
      r = (g.ts, g.ts, fmCoordOf Γ g.chain) := by
  intro K
  induction K using List.reverseRecOn with
  | nil =>
      intro r hr
      exact absurd hr (by simp [mFold])
  | append_singleton K g ih =>
      intro r hr
      rw [mFold_snoc] at hr
      cases hop : g.op with
      | ins p sd =>
          simp only [mStep, hop] at hr
          by_cases hmem : g.ts ∈ sIds (mFold Γ K)
          · rw [if_pos hmem] at hr
            obtain ⟨o, hm, hi, hrec⟩ := ih r hr
            exact ⟨o, List.mem_append_left _ hm, hi, hrec⟩
          · rw [if_neg hmem] at hr
            rcases mem_sInsert.mp hr with hr' | rfl
            · obtain ⟨o, hm, hi, hrec⟩ := ih r hr'
              exact ⟨o, List.mem_append_left _ hm, hi, hrec⟩
            · exact ⟨g, List.mem_append_right _ (by simp),
                by simp [mIsIns, hop], rfl⟩
      | del x =>
          simp only [mStep, hop] at hr
          obtain ⟨o, hm, hi, hrec⟩ := ih r (List.mem_of_mem_filter hr)
          exact ⟨o, List.mem_append_left _ hm, hi, hrec⟩

theorem mView_sub_minted (Γ : OrderedPrefixCode) (K : KnowM) :
    ∀ t ∈ mView Γ K, t ∈ mMintedIds K := by
  intro t ht
  obtain ⟨r, hr, hrt⟩ := List.mem_map.mp ht
  obtain ⟨g, hg, hins, hrec⟩ := m_fold_rec_sub Γ K r hr
  refine List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, hins⟩, ?_⟩
  rw [← hrt, hrec]

/-! ### Successor machinery -/

/-- Keys of all minted elements, dead included. -/
def mKeys (Γ : OrderedPrefixCode) (K : KnowM) : List (ℕ × List ℕ) :=
  (mMintedIds K).map (fun x => (x, mKey Γ K x))

def succCandM (Γ : OrderedPrefixCode) (K : KnowM) (a : ℕ) :
    List (ℕ × List ℕ) :=
  if a = 0 then mKeys Γ K
  else (mKeys Γ K).filter (fun p => keyLt p.2 (mKey Γ K a))

/-- The tombstone-visible successor of `a`: the display-first minted
element after `a` (after everything for `a = 0`, start). -/
def succOfM (Γ : OrderedPrefixCode) (K : KnowM) (a : ℕ) : Option ℕ :=
  ((succCandM Γ K a).foldl maxKey none).map Prod.fst

theorem succCandM_sub {Γ : OrderedPrefixCode} {K : KnowM} {a : ℕ}
    {p : ℕ × List ℕ} (h : p ∈ succCandM Γ K a) : p ∈ mKeys Γ K := by
  unfold succCandM at h
  by_cases h0 : a = 0
  · rwa [if_pos h0] at h
  · rw [if_neg h0] at h
    exact List.mem_of_mem_filter h

theorem mKeys_shape {Γ : OrderedPrefixCode} {K : KnowM}
    {p : ℕ × List ℕ} (h : p ∈ mKeys Γ K) :
    p.1 ∈ mMintedIds K ∧ p.2 = mKey Γ K p.1 := by
  obtain ⟨x, hx, hp⟩ := List.mem_map.mp h
  subst hp
  exact ⟨hx, rfl⟩

/-- The argmax result is a candidate. -/
theorem succOfM_pair {Γ : OrderedPrefixCode} {K : KnowM} {a n : ℕ}
    (h : succOfM Γ K a = some n) :
    (n, mKey Γ K n) ∈ succCandM Γ K a := by
  unfold succOfM at h
  cases hf : (succCandM Γ K a).foldl maxKey none with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some p =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      rcases foldl_maxKey_mem _ none hf with h' | h'
      · exact absurd h' (by simp)
      · have hp2 : p.2 = mKey Γ K p.1 := (mKeys_shape (succCandM_sub h')).2
        have hpe : (p.1, mKey Γ K p.1) = p := by
          rw [← hp2]
        rw [hpe]
        exact h'

theorem succOfM_mem {Γ : OrderedPrefixCode} {K : KnowM} {a n : ℕ}
    (h : succOfM Γ K a = some n) : n ∈ mMintedIds K :=
  (mKeys_shape (succCandM_sub (succOfM_pair h))).1

theorem succOfM_after_anchor {Γ : OrderedPrefixCode} {K : KnowM} {a n : ℕ}
    (h : succOfM Γ K a = some n) (ha : a ≠ 0) :
    keyLt (mKey Γ K n) (mKey Γ K a) = true := by
  have hp := succOfM_pair h
  unfold succCandM at hp
  rw [if_neg ha] at hp
  have := (List.mem_filter.mp hp).2
  simpa using this

/-- The argmax is not beaten by anything it folded over. -/
theorem foldl_maxKey_not_beaten :
    ∀ (l : List (ℕ × List ℕ)) (acc : Option (ℕ × List ℕ))
      {p : ℕ × List ℕ}, l.foldl maxKey acc = some p →
      (∀ q ∈ l, keyLt p.2 q.2 = false) ∧
      (∀ b, acc = some b → keyLt p.2 b.2 = false) := by
  intro l
  induction l with
  | nil =>
      intro acc p h
      have hacc : acc = some p := h
      subst hacc
      refine ⟨fun q hq => absurd hq (by simp), fun b hb => ?_⟩
      injection hb with hb
      rw [hb, keyLt_irrefl]
  | cons q t ih =>
      intro acc p h
      rw [List.foldl_cons] at h
      obtain ⟨ht, hstep⟩ := ih (maxKey acc q) h
      have hq : keyLt p.2 q.2 = false := by
        cases acc with
        | none => exact hstep q rfl
        | some b =>
            by_cases hk : keyLt b.2 q.2 = true
            · exact hstep q (by simp [maxKey, hk])
            · have hb := hstep b (by simp [maxKey, hk])
              by_contra hpq
              rw [Bool.not_eq_false] at hpq
              rcases eq_or_ne b.2 q.2 with heq | hne
              · rw [← heq] at hpq
                rw [hpq] at hb
                exact Bool.noConfusion hb
              · rcases keyLt_total hne with h' | h'
                · exact hk h'
                · rw [keyLt_trans hpq h'] at hb
                  exact Bool.noConfusion hb
      refine ⟨?_, ?_⟩
      · intro q' hq'
        rcases List.mem_cons.mp hq' with rfl | hq''
        · exact hq
        · exact ht q' hq''
      · intro b hb
        subst hb
        by_cases hk : keyLt b.2 q.2 = true
        · by_contra hpb
          rw [Bool.not_eq_false] at hpb
          have htr := keyLt_trans hpb hk
          rw [htr] at hq
          exact Bool.noConfusion hq
        · exact hstep b (by simp [maxKey, hk])

/-- The successor is display-first among the candidates. -/
theorem succOfM_max {Γ : OrderedPrefixCode} {K : KnowM} {a n : ℕ}
    (h : succOfM Γ K a = some n) {y : ℕ}
    (hy : (y, mKey Γ K y) ∈ succCandM Γ K a) :
    keyLt (mKey Γ K n) (mKey Γ K y) = false := by
  unfold succOfM at h
  cases hf : (succCandM Γ K a).foldl maxKey none with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some p =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hpmem : p ∈ succCandM Γ K a := by
        rcases foldl_maxKey_mem _ none hf with h' | h'
        · exact absurd h' (by simp)
        · exact h'
      have h2 : p.2 = mKey Γ K p.1 := (mKeys_shape (succCandM_sub hpmem)).2
      have hnb := (foldl_maxKey_not_beaten _ none hf).1 _ hy
      rw [h2] at hnb
      exact hnb

/-! ### The FugueMax insert rule -/

def isRChildOf (a : ℕ) (g : MRec) : Bool :=
  match g.op with
  | .ins p sd => decide (p = a) && decide (sd = Side.R)
  | .del _ => false

/-- Has `a` ever had a right child (dead nodes included)? -/
def hasRChildM (K : KnowM) (a : ℕ) : Bool := K.any (isRChildOf a)

theorem hasRChildM_iff {K : KnowM} {a : ℕ} :
    hasRChildM K a = true ↔ ∃ g ∈ K, g.op = MOp.ins a Side.R := by
  unfold hasRChildM
  rw [List.any_eq_true]
  constructor
  · rintro ⟨g, hg, hR⟩
    refine ⟨g, hg, ?_⟩
    unfold isRChildOf at hR
    cases hop : g.op with
    | ins p sd =>
        rw [hop] at hR
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hR
        rw [hR.1, hR.2]
    | del x => rw [hop] at hR; simp at hR
  · rintro ⟨g, hg, hop⟩
    exact ⟨g, hg, by simp [isRChildOf, hop]⟩

/-- The right-origin tag: the end tag for `end`, the origin's key
otherwise. -/
def tagK (Γ : OrderedPrefixCode) (K : KnowM) : Option ℕ → List ℕ
  | none => [0]
  | some n => sKey (fmCoordOf Γ (mChainOf K n))

/-- **The FugueMax mint**: Fugue's tree-position rule (right child of the
anchor when it has never had one or there is no successor, else left
child of the successor); R mints carry the successor's key as the
immutable sibling tag. -/
def mGenInsAfter (Γ : OrderedPrefixCode) (K : KnowM) (rep x a : ℕ) : MRec :=
  match succOfM Γ K a, hasRChildM K a with
  | some n, true =>
      { ts := x, rep := rep, op := .ins n Side.L, lo := a, ro := some n,
        chain := mChainOf K n ++ [.L (x - n)] }
  | some n, false =>
      { ts := x, rep := rep, op := .ins a Side.R, lo := a, ro := some n,
        chain := mChainOf K a ++
          [.R (sKey (fmCoordOf Γ (mChainOf K n))) (x - a)] }
  | none, _ =>
      { ts := x, rep := rep, op := .ins a Side.R, lo := a, ro := none,
        chain := mChainOf K a ++ [.R [0] (x - a)] }

/-- Positional intent: the anchor of "insert at index `i` of my view". -/
def mAnchorAt (Γ : OrderedPrefixCode) (K : KnowM) (i : ℕ) : ℕ :=
  if i = 0 then 0 else (mView Γ K).getD (i - 1) 0

def mGenInsAt (Γ : OrderedPrefixCode) (K : KnowM) (rep x i : ℕ) : MRec :=
  mGenInsAfter Γ K rep x (mAnchorAt Γ K i)

def mGenDelAt (Γ : OrderedPrefixCode) (K : KnowM) (rep t i : ℕ) : MRec :=
  { ts := t, rep := rep, op := .del ((mView Γ K).getD i 0),
    lo := 0, ro := none, chain := [] }

/-- Knowledge sync: whole knowledge sets transfer. -/
def syncM (K K' : KnowM) : KnowM := K ++ K'.filter (fun g => decide (g ∉ K))

/-- Reachability under the FugueMax generation policy. -/
inductive MaxReach (Γ : OrderedPrefixCode) : (ℕ → KnowM) → Prop where
  | init : MaxReach Γ (fun _ => [])
  | ins {G : ℕ → KnowM} (r x i : ℕ) :
      MaxReach Γ G → 0 < x →
      (∀ q, ∀ g ∈ G q, g.ts ≠ x) →
      (∀ m ∈ mMintedIds (G r), m < x) →
      MaxReach Γ (Function.update G r (G r ++ [mGenInsAt Γ (G r) r x i]))
  | del {G : ℕ → KnowM} (r t i : ℕ) :
      MaxReach Γ G → 0 < t →
      (∀ q, ∀ g ∈ G q, g.ts ≠ t) →
      MaxReach Γ (Function.update G r (G r ++ [mGenDelAt Γ (G r) r t i]))
  | sync {G : ℕ → KnowM} (r r' : ℕ) :
      MaxReach Γ G →
      MaxReach Γ (Function.update G r (syncM (G r) (G r')))

/-! ### Record-lookup plumbing -/

theorem mMinted_append (K K' : KnowM) :
    mMinted (K ++ K') = mMinted K ++ mMinted K' :=
  List.filter_append ..

theorem mMintedIds_append (K K' : KnowM) :
    mMintedIds (K ++ K') = mMintedIds K ++ mMintedIds K' := by
  simp [mMintedIds, mMinted_append]

theorem mRecOfId_append_left {K : KnowM} {x : ℕ} {g : MRec}
    (h : mRecOfId K x = some g) (K' : KnowM) :
    mRecOfId (K ++ K') x = some g := by
  unfold mRecOfId at h ⊢
  rw [mMinted_append, List.find?_append, h]
  rfl

theorem mRecOfId_append_fresh {K : KnowM} {x : ℕ}
    (hK : ∀ g ∈ K, mIsIns g = true → g.ts ≠ x) {r : MRec}
    (hr : mIsIns r = true) (hrx : r.ts = x) :
    mRecOfId (K ++ [r]) x = some r := by
  unfold mRecOfId
  rw [mMinted_append, List.find?_append]
  have h1 : (mMinted K).find? (fun g => g.ts == x) = none := by
    rw [List.find?_eq_none]
    intro g hg
    have hm := List.mem_filter.mp hg
    simp only [beq_iff_eq]
    exact hK g hm.1 hm.2
  have h2 : mMinted [r] = [r] := by simp [mMinted, hr]
  rw [h1, h2]
  simp [List.find?, hrx]

theorem not_mem_mintedM {K : KnowM} {y : ℕ}
    (h : ∀ g ∈ K, g.ts ≠ y) : y ∉ mMintedIds K := by
  intro hy
  obtain ⟨g, hg, hgy⟩ := List.mem_map.mp hy
  exact h g (List.mem_of_mem_filter hg) hgy

theorem mRecOfId_of_minted {K : KnowM} {p : ℕ} (hp : p ∈ mMintedIds K) :
    ∃ g, mRecOfId K p = some g ∧ g ∈ K ∧ mIsIns g = true ∧ g.ts = p := by
  obtain ⟨g0, hg0, hid⟩ := List.mem_map.mp hp
  have hsome : (mRecOfId K p).isSome := by
    rw [mRecOfId, List.find?_isSome]
    exact ⟨g0, hg0, by simp [hid]⟩
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hsome
  have hmem := List.mem_of_find?_eq_some hg
  have hpg := List.find?_some hg
  refine ⟨g, hg, List.mem_of_mem_filter hmem,
    (List.mem_filter.mp hmem).2, ?_⟩
  simpa using hpg

theorem mChainOf_eq_of_rec {K : KnowM} {x : ℕ} {g : MRec}
    (h : mRecOfId K x = some g) : mChainOf K x = g.chain := by
  unfold mChainOf
  rw [h]
  rfl

theorem mChainOf_zero {K : KnowM} (hpos : ∀ g ∈ K, 1 ≤ g.ts) :
    mChainOf K 0 = [] := by
  unfold mChainOf mRecOfId
  rw [List.find?_eq_none.mpr]
  · rfl
  · intro g hg
    have h1 := hpos g (List.mem_of_mem_filter hg)
    simp only [beq_iff_eq]
    intro h
    rw [h] at h1
    exact absurd h1 (by decide)

/-- Same-id minted records agree across knowledges, so `mChainOf` does. -/
theorem mChainOf_agree {K₁ K₂ : KnowM}
    (h : ∀ g ∈ K₁, ∀ g' ∈ K₂, mIsIns g = true → mIsIns g' = true →
      g.ts = g'.ts → g = g')
    {x : ℕ} (hx₁ : x ∈ mMintedIds K₁) (hx₂ : x ∈ mMintedIds K₂) :
    mChainOf K₁ x = mChainOf K₂ x := by
  obtain ⟨g₁, hf₁, hm₁, hi₁, ht₁⟩ := mRecOfId_of_minted hx₁
  obtain ⟨g₂, hf₂, hm₂, hi₂, ht₂⟩ := mRecOfId_of_minted hx₂
  rw [mChainOf_eq_of_rec hf₁, mChainOf_eq_of_rec hf₂,
    h g₁ hm₁ g₂ hm₂ hi₁ hi₂ (by rw [ht₁, ht₂])]

theorem mem_update_elimM {G : ℕ → KnowM} {r : ℕ} {K : KnowM} {q : ℕ}
    {g : MRec} (hg : g ∈ Function.update G r K q) :
    (q ≠ r ∧ g ∈ G q) ∨ (q = r ∧ g ∈ K) := by
  by_cases hq : q = r
  · subst hq
    rw [Function.update_self] at hg
    exact Or.inr ⟨rfl, hg⟩
  · rw [Function.update_of_ne hq] at hg
    exact Or.inl ⟨hq, hg⟩

theorem mem_syncM {g : MRec} {K K' : KnowM} (h : g ∈ syncM K K') :
    g ∈ K ∨ g ∈ K' := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_of_mem_filter h)

theorem minted_syncM_right {K K' : KnowM} {x : ℕ}
    (h : x ∈ mMintedIds K') : x ∈ mMintedIds (syncM K K') := by
  obtain ⟨g, hg, hx⟩ := List.mem_map.mp h
  have hgK' := List.mem_of_mem_filter hg
  have hins := (List.mem_filter.mp hg).2
  by_cases hK : g ∈ K
  · exact List.mem_map.mpr ⟨g, List.mem_filter.mpr
      ⟨List.mem_append_left _ hK, hins⟩, hx⟩
  · exact List.mem_map.mpr ⟨g, List.mem_filter.mpr
      ⟨List.mem_append_right _ (List.mem_filter.mpr
        ⟨hgK', by simpa using hK⟩), hins⟩, hx⟩

theorem mAnchorAt_cases (Γ : OrderedPrefixCode) (K : KnowM) (i : ℕ) :
    mAnchorAt Γ K i = 0 ∨ mAnchorAt Γ K i ∈ mView Γ K := by
  unfold mAnchorAt
  by_cases h0 : i = 0
  · rw [if_pos h0]; exact Or.inl rfl
  · rw [if_neg h0]
    by_cases hlt : i - 1 < (mView Γ K).length
    · right
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
        Option.getD_some]
      exact List.getElem_mem hlt
    · left
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none
        (Nat.le_of_not_lt hlt)]
      rfl

/-! ## §2  The reachability invariant -/

/-- The R-mint link clause: parent = left origin, chain extends the
parent's by the tagged R entry, and the mint-time geometry fact — the
recorded right origin is NOT an R-descendant of the left origin (the
minter had seen no R-child of the anchor). -/
def LinkR (Γ : OrderedPrefixCode) (K : KnowM) (g : MRec) : Prop :=
  ∀ p, g.op = MOp.ins p Side.R →
    p = g.lo ∧ p < g.ts ∧ (p = 0 ∨ p ∈ mMintedIds K) ∧
    g.chain = mChainOf K p ++ [FMEntry.R (tagK Γ K g.ro) (g.ts - p)] ∧
    ∀ n, g.ro = some n → n ∈ mMintedIds K ∧
      ¬ ∃ t d rest, mChainOf K n = mChainOf K g.lo ++ FMEntry.R t d :: rest

/-- The L-mint link clause: parent = right origin, chain extends the
parent's by an L entry, and the mint-time geometry fact — the parent IS
an R-descendant of the left origin (the successor of an anchor with an
R-child lands in its R-subtree). -/
def LinkL (Γ : OrderedPrefixCode) (K : KnowM) (g : MRec) : Prop :=
  ∀ p, g.op = MOp.ins p Side.L →
    g.ro = some p ∧ p < g.ts ∧ p ∈ mMintedIds K ∧
    g.chain = mChainOf K p ++ [FMEntry.L (g.ts - p)] ∧
    (g.lo = 0 ∨ g.lo ∈ mMintedIds K) ∧
    ∃ t d rest, mChainOf K p = mChainOf K g.lo ++ FMEntry.R t d :: rest

/-- The per-knowledge invariant bundle. -/
structure KInv (Γ : OrderedPrefixCode) (K : KnowM) : Prop where
  pos : ∀ g ∈ K, 1 ≤ g.ts
  uniq : ∀ g ∈ K, ∀ g' ∈ K, mIsIns g = true → mIsIns g' = true →
    g.ts = g'.ts → g = g'
  wf : ∀ g ∈ K, mIsIns g = true →
    PosFMChain g.chain ∧ TagsOK g.chain ∧ (g.chain.map fmδ).sum = g.ts
  linkR : ∀ g ∈ K, LinkR Γ K g
  linkL : ∀ g ∈ K, LinkL Γ K g

/-- The global invariant: per-knowledge bundles plus cross-replica
uniqueness (needed to transport link clauses through sync). -/
structure MInv (Γ : OrderedPrefixCode) (G : ℕ → KnowM) : Prop where
  each : ∀ q, KInv Γ (G q)
  cross : ∀ q q', ∀ g ∈ G q, ∀ g' ∈ G q', mIsIns g = true →
    mIsIns g' = true → g.ts = g'.ts → g = g'

/-! ### Chain facts from the bundle -/

theorem mChainOf_of_mem {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {c : MRec} (hc : c ∈ K) (hins : mIsIns c = true) :
    mChainOf K c.ts = c.chain := by
  have hmem : c.ts ∈ mMintedIds K :=
    List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, hins⟩, rfl⟩
  obtain ⟨g, hfind, hgK, hgins, hgts⟩ := mRecOfId_of_minted hmem
  rw [mChainOf_eq_of_rec hfind, inv.uniq g hgK c hc hgins hins hgts]

theorem mChainOf_wfparts {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {x : ℕ} (hx : x = 0 ∨ x ∈ mMintedIds K) :
    PosFMChain (mChainOf K x) ∧ TagsOK (mChainOf K x) := by
  rcases hx with rfl | hx
  · rw [mChainOf_zero inv.pos]
    exact ⟨fun e he => absurd he (by simp),
      fun e he => absurd he (by simp)⟩
  · obtain ⟨g, hfind, hgK, hgins, hgts⟩ := mRecOfId_of_minted hx
    rw [mChainOf_eq_of_rec hfind]
    obtain ⟨h1, h2, -⟩ := inv.wf g hgK hgins
    exact ⟨h1, h2⟩

theorem mChainOf_sum {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {x : ℕ} (hx : x = 0 ∨ x ∈ mMintedIds K) :
    ((mChainOf K x).map fmδ).sum = x := by
  rcases hx with rfl | hx
  · rw [mChainOf_zero inv.pos]
    rfl
  · obtain ⟨g, hfind, hgK, hgins, hgts⟩ := mRecOfId_of_minted hx
    rw [mChainOf_eq_of_rec hfind, ← hgts]
    exact (inv.wf g hgK hgins).2.2

theorem minted_pos {Γ : OrderedPrefixCode} {K : KnowM} (inv : KInv Γ K)
    {x : ℕ} (hx : x ∈ mMintedIds K) : 1 ≤ x := by
  obtain ⟨g, hfind, hgK, hgins, hgts⟩ := mRecOfId_of_minted hx
  rw [← hgts]
  exact inv.pos g hgK

theorem mChainOf_ne_nil {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {x : ℕ} (hx : x ∈ mMintedIds K) :
    mChainOf K x ≠ [] := by
  intro h
  have hsum := mChainOf_sum inv (Or.inr hx)
  rw [h] at hsum
  have := minted_pos inv hx
  simp at hsum
  omega

/-! ### Link-clause transport -/

theorem tagK_congr {Γ : OrderedPrefixCode} {K K' : KnowM} {ro : Option ℕ}
    (h : ∀ n, ro = some n → mChainOf K' n = mChainOf K n) :
    tagK Γ K' ro = tagK Γ K ro := by
  cases ro with
  | none => rfl
  | some n => simp [tagK, h n rfl]

theorem linkR_transport {Γ : OrderedPrefixCode} {K K' : KnowM} {g : MRec}
    (hL : LinkR Γ K g)
    (hchain : ∀ y, y = 0 ∨ y ∈ mMintedIds K → mChainOf K' y = mChainOf K y)
    (hmem : ∀ y, y ∈ mMintedIds K → y ∈ mMintedIds K') :
    LinkR Γ K' g := by
  intro p hop
  obtain ⟨h1, h2, h3, h4, h5⟩ := hL p hop
  have hlo : g.lo = 0 ∨ g.lo ∈ mMintedIds K := h1 ▸ h3
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · rcases h3 with h | h
    · exact Or.inl h
    · exact Or.inr (hmem p h)
  · rw [hchain p h3, tagK_congr (fun n hn =>
      hchain n (Or.inr (h5 n hn).1))]
    exact h4
  · intro n hn
    obtain ⟨hn1, hn2⟩ := h5 n hn
    refine ⟨hmem n hn1, ?_⟩
    rw [hchain n (Or.inr hn1), hchain g.lo hlo]
    exact hn2

theorem linkL_transport {Γ : OrderedPrefixCode} {K K' : KnowM} {g : MRec}
    (hL : LinkL Γ K g)
    (hchain : ∀ y, y = 0 ∨ y ∈ mMintedIds K → mChainOf K' y = mChainOf K y)
    (hmem : ∀ y, y ∈ mMintedIds K → y ∈ mMintedIds K') :
    LinkL Γ K' g := by
  intro p hop
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL p hop
  refine ⟨h1, h2, hmem p h3, ?_, ?_, ?_⟩
  · rw [hchain p (Or.inr h3)]
    exact h4
  · rcases h5 with h | h
    · exact Or.inl h
    · exact Or.inr (hmem g.lo h)
  · rw [hchain p (Or.inr h3), hchain g.lo h5]
    exact h6

/-! ### The closure walk and the two geometry lemmas -/

theorem prefix_concat_cases {α : Type} {u X : List α} {y : α}
    (h : u <+: X ++ [y]) : u = X ++ [y] ∨ u <+: X := by
  rcases Nat.lt_or_ge u.length (X ++ [y]).length with hlt | hge
  · right
    have hXpre : X <+: X ++ [y] := List.prefix_append _ _
    have hlen : u.length ≤ X.length := by
      rw [List.length_append, List.length_singleton] at hlt
      omega
    exact List.prefix_of_prefix_length_le h hXpre hlen
  · left
    exact List.IsPrefix.eq_of_length h (Nat.le_antisymm h.length_le hge)

/-- Any nonempty prefix (at entry granularity) of a minted chain is
itself a minted chain: knowledge is ancestor-closed. -/
theorem chain_prefix_minted {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) :
    ∀ (N : ℕ) (g : MRec), g ∈ K → mIsIns g = true → g.chain.length ≤ N →
      ∀ pre e, (pre ++ [e]) <+: g.chain →
        ∃ h, h ∈ K ∧ mIsIns h = true ∧ h.chain = pre ++ [e] := by
  intro N
  induction N with
  | zero =>
      intro g hg hins hlen pre e hpre
      exfalso
      have h1 := hpre.length_le
      have h2 : g.chain.length = 0 := Nat.le_antisymm hlen (Nat.zero_le _)
      rw [List.length_append, List.length_singleton, h2] at h1
      omega
  | succ N ih =>
      intro g hg hins hlen pre e hpre
      obtain ⟨p, sd, hop⟩ := mIsIns_shape hins
      have hdecomp : (p = 0 ∨ p ∈ mMintedIds K) ∧
          ∃ e', g.chain = mChainOf K p ++ [e'] := by
        cases sd with
        | R =>
            obtain ⟨-, -, h3, h4, -⟩ := inv.linkR g hg p hop
            exact ⟨h3, _, h4⟩
        | L =>
            obtain ⟨-, -, h3, h4, -, -⟩ := inv.linkL g hg p hop
            exact ⟨Or.inr h3, _, h4⟩
      obtain ⟨hp, e', hchain⟩ := hdecomp
      rw [hchain] at hpre
      rcases prefix_concat_cases hpre with heq | hpre'
      · exact ⟨g, hg, hins, by rw [hchain, heq]⟩
      · have hpne : p ≠ 0 := by
          intro h0
          subst h0
          rw [mChainOf_zero inv.pos] at hpre'
          have := hpre'.length_le
          simp at this
        have hpm : p ∈ mMintedIds K := by
          rcases hp with h | h
          · exact absurd h hpne
          · exact h
        obtain ⟨hrec, hrecfind, hrecK, hrecins, hrects⟩ :=
          mRecOfId_of_minted hpm
        have hchain_p : mChainOf K p = hrec.chain :=
          mChainOf_eq_of_rec hrecfind
        have hlen' : hrec.chain.length ≤ N := by
          have h1 := congrArg List.length hchain
          rw [List.length_append, List.length_singleton, hchain_p] at h1
          omega
        exact ih hrec hrecK hrecins hlen' pre e (hchain_p ▸ hpre')

/-- Every minted chain is R-headed: the root's children are R mints. -/
theorem chain_head_R {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) :
    ∀ (N : ℕ) (g : MRec), g ∈ K → mIsIns g = true → g.chain.length ≤ N →
      ∃ t d rest, g.chain = FMEntry.R t d :: rest := by
  intro N
  induction N with
  | zero =>
      intro g hg hins hlen
      exfalso
      have hsum := (inv.wf g hg hins).2.2
      have hchain_nil : g.chain = [] := List.length_eq_zero_iff.mp
        (Nat.le_antisymm hlen (Nat.zero_le _))
      rw [hchain_nil] at hsum
      have := inv.pos g hg
      simp at hsum
      omega
  | succ N ih =>
      intro g hg hins hlen
      obtain ⟨p, sd, hop⟩ := mIsIns_shape hins
      cases sd with
      | R =>
          obtain ⟨-, -, h3, h4, -⟩ := inv.linkR g hg p hop
          cases hpc : mChainOf K p with
          | nil =>
              refine ⟨tagK Γ K g.ro, g.ts - p, [], ?_⟩
              rw [h4, hpc]
              rfl
          | cons e0 pc' =>
              have hpm : p ∈ mMintedIds K := by
                rcases h3 with h | h
                · exfalso
                  subst h
                  rw [mChainOf_zero inv.pos] at hpc
                  simp at hpc
                · exact h
              obtain ⟨hrec, hrecfind, hrecK, hrecins, hrects⟩ :=
                mRecOfId_of_minted hpm
              have hchain_p : mChainOf K p = hrec.chain :=
                mChainOf_eq_of_rec hrecfind
              have hlen' : hrec.chain.length ≤ N := by
                have h1 := congrArg List.length h4
                rw [List.length_append, List.length_singleton,
                  hchain_p] at h1
                omega
              obtain ⟨t', d', rest', hhead⟩ :=
                ih hrec hrecK hrecins hlen'
              refine ⟨t', d', rest' ++ [FMEntry.R (tagK Γ K g.ro)
                (g.ts - p)], ?_⟩
              rw [h4, hchain_p, hhead]
              rfl
      | L =>
          obtain ⟨-, -, h3, h4, -, -⟩ := inv.linkL g hg p hop
          obtain ⟨hrec, hrecfind, hrecK, hrecins, hrects⟩ :=
            mRecOfId_of_minted h3
          have hchain_p : mChainOf K p = hrec.chain :=
            mChainOf_eq_of_rec hrecfind
          have hlen' : hrec.chain.length ≤ N := by
            have h1 := congrArg List.length h4
            rw [List.length_append, List.length_singleton, hchain_p] at h1
            omega
          obtain ⟨t', d', rest', hhead⟩ := ih hrec hrecK hrecins hlen'
          refine ⟨t', d', rest' ++ [FMEntry.L (g.ts - p)], ?_⟩
          rw [h4, hchain_p, hhead]
          rfl

/-- An R-descendant of `lo` witnesses a (possibly dead) R-child of `lo`
in the same knowledge: the first geometry lemma's engine. -/
theorem hasR_of_R_descendant {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {lo n : ℕ}
    (hlo : lo = 0 ∨ lo ∈ mMintedIds K) (hn : n ∈ mMintedIds K)
    (hdesc : ∃ t d rest, mChainOf K n
      = mChainOf K lo ++ FMEntry.R t d :: rest) :
    hasRChildM K lo = true := by
  obtain ⟨t, d, rest, hd⟩ := hdesc
  obtain ⟨gn, hnfind, hnK, hnins, hnts⟩ := mRecOfId_of_minted hn
  have hnchain : gn.chain = mChainOf K lo ++ FMEntry.R t d :: rest := by
    rw [← mChainOf_eq_of_rec hnfind, hd]
  have hpre : (mChainOf K lo ++ [FMEntry.R t d]) <+: gn.chain := by
    rw [hnchain]
    exact ⟨rest, by simp⟩
  obtain ⟨c, hcK, hcins, hcchain⟩ := chain_prefix_minted inv
    gn.chain.length gn hnK hnins (Nat.le_refl _) _ _ hpre
  obtain ⟨pc, sdc, hcop⟩ := mIsIns_shape hcins
  cases sdc with
  | L =>
      exfalso
      obtain ⟨-, -, -, h4, -, -⟩ := inv.linkL c hcK pc hcop
      rw [hcchain] at h4
      have hinj := List.append_inj' h4 rfl
      injection hinj.2 with h5
      exact FMEntry.noConfusion h5
  | R =>
      obtain ⟨-, -, h3, h4, -⟩ := inv.linkR c hcK pc hcop
      rw [hcchain] at h4
      have hinj := List.append_inj' h4 rfl
      have hpceq : mChainOf K lo = mChainOf K pc := hinj.1
      have hpclo : pc = lo := by
        have hs1 := mChainOf_sum inv h3
        have hs2 := mChainOf_sum inv hlo
        rw [← hpceq] at hs1
        omega
      rw [hasRChildM_iff]
      exact ⟨c, hcK, by rw [hcop, hpclo]⟩

/-- **Geometry, R mint**: when the anchor has never had an R-child, its
successor is not an R-descendant of it. -/
theorem succ_not_R_descendant {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {a n : ℕ}
    (ha : a = 0 ∨ a ∈ mMintedIds K) (hn : n ∈ mMintedIds K)
    (hnoR : hasRChildM K a = false) :
    ¬ ∃ t d rest, mChainOf K n = mChainOf K a ++ FMEntry.R t d :: rest := by
  intro hdesc
  rw [hasR_of_R_descendant inv ha hn hdesc] at hnoR
  exact Bool.noConfusion hnoR

/-- **Geometry, L mint**: when the anchor HAS an R-child, its successor
IS an R-descendant of it — the argmax lands in the R-subtree, by
convexity. -/
theorem succ_R_descendant {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {a n : ℕ}
    (ha : a = 0 ∨ a ∈ mMintedIds K)
    (hR : hasRChildM K a = true)
    (hsucc : succOfM Γ K a = some n) :
    ∃ t d rest, mChainOf K n = mChainOf K a ++ FMEntry.R t d :: rest := by
  have hn : n ∈ mMintedIds K := succOfM_mem hsucc
  -- the R-child witness
  obtain ⟨c, hcK, hcop⟩ := hasRChildM_iff.mp hR
  have hcins : mIsIns c = true := by simp [mIsIns, hcop]
  obtain ⟨-, -, -, h4, -⟩ := inv.linkR c hcK a hcop
  have hcts : c.ts ∈ mMintedIds K :=
    List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hcK, hcins⟩, rfl⟩
  have hcchain : mChainOf K c.ts = c.chain := mChainOf_of_mem inv hcK hcins
  -- wellformedness packages
  have hwa := mChainOf_wfparts inv ha
  have hwn := mChainOf_wfparts inv (Or.inr hn)
  have hwc := mChainOf_wfparts inv (Or.inr hcts)
  -- the R-child displays after the anchor
  have hxa : keyLt (mKey Γ K c.ts) (mKey Γ K a) = true := by
    unfold mKey
    apply fmChainBefore_display Γ hwa.1 (hcchain ▸ hwc.1)
      hwa.2 (hcchain ▸ hwc.2)
    rw [hcchain, h4]
    exact fmChainBefore.extR _ _ _ _
  -- the R-child is a successor candidate
  have hccand : (c.ts, mKey Γ K c.ts) ∈ succCandM Γ K a := by
    unfold succCandM
    by_cases h0 : a = 0
    · rw [if_pos h0]
      exact List.mem_map.mpr ⟨c.ts, hcts, rfl⟩
    · rw [if_neg h0]
      exact List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨c.ts, hcts, rfl⟩, by simpa using hxa⟩
  -- the successor is not beaten by the R-child
  have hnb : keyLt (mKey Γ K n) (mKey Γ K c.ts) = false :=
    succOfM_max hsucc hccand
  rcases ha with rfl | ham
  · -- anchor = start: every minted chain is R-headed
    obtain ⟨gn, hnfind, hnK, hnins, hnts⟩ := mRecOfId_of_minted hn
    obtain ⟨t, d, rest, hhead⟩ := chain_head_R inv gn.chain.length gn
      hnK hnins (Nat.le_refl _)
    refine ⟨t, d, rest, ?_⟩
    rw [mChainOf_zero inv.pos, mChainOf_eq_of_rec hnfind, hhead]
    rfl
  · -- anchor real: keys pin n between the anchor and the R-child
    by_cases hkeq : mKey Γ K n = mKey Γ K c.ts
    · -- equal keys: unique decodability collapses n onto the R-child
      have hceq : mChainOf K n = mChainOf K c.ts := by
        apply fmCoordOf_inj Γ hwn.1 (hwc.1) hwn.2 hwc.2
        have := congrArg (fun l => l) hkeq
        unfold mKey sKey at hkeq
        exact (List.append_inj' hkeq rfl).1
      exact ⟨_, _, [], by rw [hceq, hcchain, h4]⟩
    · have hkn : keyLt (mKey Γ K c.ts) (mKey Γ K n) = true := by
        rcases keyLt_total hkeq with h | h
        · rw [h] at hnb
          exact Bool.noConfusion hnb
        · exact h
      have ha0 : a ≠ 0 := by
        have := minted_pos inv ham
        omega
      have han : keyLt (mKey Γ K n) (mKey Γ K a) = true :=
        succOfM_after_anchor hsucc ha0
      -- chain-level facts via the marker theorem
      have hne_an : mChainOf K a ≠ mChainOf K n := by
        intro h
        unfold mKey at han
        rw [h, keyLt_irrefl] at han
        exact Bool.noConfusion han
      have hne_nc : mChainOf K n ≠ mChainOf K c.ts := by
        intro h
        unfold mKey at hkn
        rw [h, keyLt_irrefl] at hkn
        exact Bool.noConfusion hkn
      have hb_an : fmChainBefore (mChainOf K a) (mChainOf K n) :=
        (fmdisplay_iff_fmChainBefore Γ hwa.1 hwn.1 hwa.2 hwn.2
          hne_an).mp han
      have hb_nc : fmChainBefore (mChainOf K n) (mChainOf K c.ts) :=
        (fmdisplay_iff_fmChainBefore Γ hwn.1 hwc.1 hwn.2 hwc.2
          hne_nc).mp hkn
      obtain ⟨ez, hez⟩ := fm_subtree_convex (mChainOf K a)
        ⟨[], (List.append_nil _).symm⟩
        ⟨[FMEntry.R (tagK Γ K c.ro) (c.ts - a)], by
          rw [hcchain, h4]⟩ hb_an hb_nc
      obtain ⟨t, d, rest, hext⟩ := fm_ext_after_is_R (hez ▸ hb_an)
      exact ⟨t, d, rest, by rw [hez, hext]⟩

/-! ### Stability of chain lookups under knowledge growth -/

theorem mChainOf_append_stable {K : KnowM} {y : ℕ}
    (hy : y = 0 ∨ y ∈ mMintedIds K)
    (hpos : ∀ g ∈ K, 1 ≤ g.ts) {K' : KnowM}
    (hpos' : ∀ g ∈ K', 1 ≤ g.ts) :
    mChainOf (K ++ K') y = mChainOf K y := by
  rcases hy with rfl | hy
  · rw [mChainOf_zero (K := K ++ K') (by
      intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact hpos g h
      · exact hpos' g h), mChainOf_zero hpos]
  · obtain ⟨g, hfind, -, -, -⟩ := mRecOfId_of_minted hy
    rw [mChainOf_eq_of_rec (mRecOfId_append_left hfind K'),
      mChainOf_eq_of_rec hfind]

theorem mMinted_snoc_del {K : KnowM} {g : MRec} (h : mIsIns g = false) :
    mMinted (K ++ [g]) = mMinted K := by
  rw [mMinted_append]
  simp [mMinted, h]

theorem mChainOf_snoc_del {K : KnowM} {g : MRec} (h : mIsIns g = false)
    (y : ℕ) : mChainOf (K ++ [g]) y = mChainOf K y := by
  unfold mChainOf mRecOfId
  rw [mMinted_snoc_del h]

theorem mMintedIds_snoc_del {K : KnowM} {g : MRec}
    (h : mIsIns g = false) : mMintedIds (K ++ [g]) = mMintedIds K := by
  unfold mMintedIds
  rw [mMinted_snoc_del h]

/-! ### Per-step invariant bundles -/

/-- Appending a fresh wellformed insert preserves the bundle. -/
theorem kinv_snoc_ins {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {g : MRec}
    (hts : 1 ≤ g.ts) (hins : mIsIns g = true)
    (hfreshK : ∀ h ∈ K, h.ts ≠ g.ts)
    (hwf : PosFMChain g.chain ∧ TagsOK g.chain ∧
      (g.chain.map fmδ).sum = g.ts)
    (hR : LinkR Γ K g) (hL : LinkL Γ K g) :
    KInv Γ (K ++ [g]) := by
  have hpos' : ∀ h ∈ K ++ [g], 1 ≤ h.ts := by
    intro h hh
    rcases List.mem_append.mp hh with h' | h'
    · exact inv.pos h h'
    · rw [List.mem_singleton] at h'
      subst h'
      exact hts
  have hchain : ∀ y, y = 0 ∨ y ∈ mMintedIds K →
      mChainOf (K ++ [g]) y = mChainOf K y :=
    fun y hy => mChainOf_append_stable hy inv.pos (by
      intro h hh
      rw [List.mem_singleton] at hh
      subst hh
      exact hts)
  have hmem : ∀ y, y ∈ mMintedIds K → y ∈ mMintedIds (K ++ [g]) := by
    intro y hy
    rw [mMintedIds_append]
    exact List.mem_append_left _ hy
  refine ⟨hpos', ?_, ?_, ?_, ?_⟩
  · intro g1 h1 g2 h2 hi1 hi2 hts12
    rcases List.mem_append.mp h1 with h1' | h1' <;>
      rcases List.mem_append.mp h2 with h2' | h2'
    · exact inv.uniq g1 h1' g2 h2' hi1 hi2 hts12
    · rw [List.mem_singleton] at h2'
      subst h2'
      exact absurd hts12 (hfreshK g1 h1')
    · rw [List.mem_singleton] at h1'
      subst h1'
      exact absurd hts12.symm (hfreshK g2 h2')
    · rw [List.mem_singleton] at h1' h2'
      rw [h1', h2']
  · intro g1 h1 hi1
    rcases List.mem_append.mp h1 with h1' | h1'
    · exact inv.wf g1 h1' hi1
    · rw [List.mem_singleton] at h1'
      subst h1'
      exact hwf
  · intro g1 h1
    rcases List.mem_append.mp h1 with h1' | h1'
    · exact linkR_transport (inv.linkR g1 h1') hchain hmem
    · rw [List.mem_singleton] at h1'
      subst h1'
      exact linkR_transport hR hchain hmem
  · intro g1 h1
    rcases List.mem_append.mp h1 with h1' | h1'
    · exact linkL_transport (inv.linkL g1 h1') hchain hmem
    · rw [List.mem_singleton] at h1'
      subst h1'
      exact linkL_transport hL hchain hmem

/-- Appending a delete preserves the bundle. -/
theorem kinv_snoc_del {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {g : MRec} (hts : 1 ≤ g.ts)
    (hnotins : mIsIns g = false) : KInv Γ (K ++ [g]) := by
  have hchain : ∀ y, y = 0 ∨ y ∈ mMintedIds K →
      mChainOf (K ++ [g]) y = mChainOf K y :=
    fun y _ => mChainOf_snoc_del hnotins y
  have hmem : ∀ y, y ∈ mMintedIds K → y ∈ mMintedIds (K ++ [g]) := by
    intro y hy
    rw [mMintedIds_snoc_del hnotins]
    exact hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    rcases List.mem_append.mp hh with h' | h'
    · exact inv.pos h h'
    · rw [List.mem_singleton] at h'
      subst h'
      exact hts
  · intro g1 h1 g2 h2 hi1 hi2 hts12
    have hK : ∀ {gg : MRec}, gg ∈ K ++ [g] → mIsIns gg = true → gg ∈ K := by
      intro gg hgg hi
      rcases List.mem_append.mp hgg with h' | h'
      · exact h'
      · rw [List.mem_singleton] at h'
        subst h'
        rw [hnotins] at hi
        exact Bool.noConfusion hi
    exact inv.uniq g1 (hK h1 hi1) g2 (hK h2 hi2) hi1 hi2 hts12
  · intro g1 h1 hi1
    rcases List.mem_append.mp h1 with h1' | h1'
    · exact inv.wf g1 h1' hi1
    · rw [List.mem_singleton] at h1'
      subst h1'
      rw [hnotins] at hi1
      exact Bool.noConfusion hi1
  · intro g1 h1
    rcases List.mem_append.mp h1 with h1' | h1'
    · exact linkR_transport (inv.linkR g1 h1') hchain hmem
    · rw [List.mem_singleton] at h1'
      intro p hop
      exfalso
      have hins' : mIsIns g1 = true := by
        unfold mIsIns
        rw [hop]
      rw [h1', hnotins] at hins'
      exact Bool.noConfusion hins'
  · intro g1 h1
    rcases List.mem_append.mp h1 with h1' | h1'
    · exact linkL_transport (inv.linkL g1 h1') hchain hmem
    · rw [List.mem_singleton] at h1'
      intro p hop
      exfalso
      have hins' : mIsIns g1 = true := by
        unfold mIsIns
        rw [hop]
      rw [h1', hnotins] at hins'
      exact Bool.noConfusion hins'

/-- Pairwise sync preserves the bundle (cross-uniqueness feeds the
right-side chain agreement). -/
theorem kinv_sync {Γ : OrderedPrefixCode} {G : ℕ → KnowM}
    (inv : MInv Γ G) (r r' : ℕ) : KInv Γ (syncM (G r) (G r')) := by
  have hposU : ∀ g ∈ syncM (G r) (G r'), 1 ≤ g.ts := by
    intro g hg
    rcases mem_syncM hg with h | h
    · exact (inv.each r).pos g h
    · exact (inv.each r').pos g h
  have huniqU : ∀ g ∈ syncM (G r) (G r'), ∀ g' ∈ syncM (G r) (G r'),
      mIsIns g = true → mIsIns g' = true → g.ts = g'.ts → g = g' := by
    intro g hg g' hg' hi hi' hteq
    rcases mem_syncM hg with h | h <;> rcases mem_syncM hg' with h' | h'
    · exact inv.cross r r g h g' h' hi hi' hteq
    · exact inv.cross r r' g h g' h' hi hi' hteq
    · exact inv.cross r' r g h g' h' hi hi' hteq
    · exact inv.cross r' r' g h g' h' hi hi' hteq
  have hchainL : ∀ y, y = 0 ∨ y ∈ mMintedIds (G r) →
      mChainOf (syncM (G r) (G r')) y = mChainOf (G r) y := by
    intro y hy
    exact mChainOf_append_stable hy (inv.each r).pos
      (fun g hg => (inv.each r').pos g (List.mem_of_mem_filter hg))
  have hmemL : ∀ y, y ∈ mMintedIds (G r) →
      y ∈ mMintedIds (syncM (G r) (G r')) := by
    intro y hy
    rw [show syncM (G r) (G r')
      = G r ++ (G r').filter (fun g => decide (g ∉ G r)) from rfl,
      mMintedIds_append]
    exact List.mem_append_left _ hy
  have hchainR : ∀ y, y = 0 ∨ y ∈ mMintedIds (G r') →
      mChainOf (syncM (G r) (G r')) y = mChainOf (G r') y := by
    intro y hy
    rcases hy with rfl | hy
    · rw [mChainOf_zero hposU, mChainOf_zero (inv.each r').pos]
    · exact mChainOf_agree
        (by
          intro g hg g' hg' hi hi' hteq
          rcases mem_syncM hg with h | h
          · exact inv.cross r r' g h g' hg' hi hi' hteq
          · exact inv.cross r' r' g h g' hg' hi hi' hteq)
        (minted_syncM_right hy) hy
  have hmemR : ∀ y, y ∈ mMintedIds (G r') →
      y ∈ mMintedIds (syncM (G r) (G r')) :=
    fun y hy => minted_syncM_right hy
  refine ⟨hposU, huniqU, ?_, ?_, ?_⟩
  · intro g hg hi
    rcases mem_syncM hg with h | h
    · exact (inv.each r).wf g h hi
    · exact (inv.each r').wf g h hi
  · intro g hg
    rcases mem_syncM hg with h | h
    · exact linkR_transport ((inv.each r).linkR g h) hchainL hmemL
    · exact linkR_transport ((inv.each r').linkR g h) hchainR hmemR
  · intro g hg
    rcases mem_syncM hg with h | h
    · exact linkL_transport ((inv.each r).linkL g h) hchainL hmemL
    · exact linkL_transport ((inv.each r').linkL g h) hchainR hmemR

/-! ### The mint's own clauses -/

/-- Branch equations for the mint (packaged so the goals never force deep
`whnf` through the policy functions). -/
theorem mGenInsAfter_none {Γ : OrderedPrefixCode} {K : KnowM}
    {rep x a : ℕ} (hs : succOfM Γ K a = none) :
    mGenInsAfter Γ K rep x a =
      { ts := x, rep := rep, op := .ins a Side.R, lo := a, ro := none,
        chain := mChainOf K a ++ [.R [0] (x - a)] } := by
  unfold mGenInsAfter
  rw [hs]

theorem mGenInsAfter_someTrue {Γ : OrderedPrefixCode} {K : KnowM}
    {rep x a n : ℕ} (hs : succOfM Γ K a = some n)
    (hR : hasRChildM K a = true) :
    mGenInsAfter Γ K rep x a =
      { ts := x, rep := rep, op := .ins n Side.L, lo := a, ro := some n,
        chain := mChainOf K n ++ [.L (x - n)] } := by
  unfold mGenInsAfter
  rw [hs, hR]

theorem mGenInsAfter_someFalse {Γ : OrderedPrefixCode} {K : KnowM}
    {rep x a n : ℕ} (hs : succOfM Γ K a = some n)
    (hR : hasRChildM K a = false) :
    mGenInsAfter Γ K rep x a =
      { ts := x, rep := rep, op := .ins a Side.R, lo := a, ro := some n,
        chain := mChainOf K a ++
          [.R (sKey (fmCoordOf Γ (mChainOf K n))) (x - a)] } := by
  unfold mGenInsAfter
  rw [hs, hR]

/-- The freshly generated insert satisfies everything the bundle demands
of it, over the mint knowledge — including the two geometry facts. -/
theorem mGenInsAfter_props (Γ : OrderedPrefixCode) {K : KnowM}
    (inv : KInv Γ K) (rep : ℕ) {x a : ℕ} (hx : 0 < x)
    (hlam : ∀ m ∈ mMintedIds K, m < x)
    (ha : a = 0 ∨ a ∈ mMintedIds K) :
    (mGenInsAfter Γ K rep x a).ts = x ∧
    mIsIns (mGenInsAfter Γ K rep x a) = true ∧
    (PosFMChain (mGenInsAfter Γ K rep x a).chain ∧
      TagsOK (mGenInsAfter Γ K rep x a).chain ∧
      ((mGenInsAfter Γ K rep x a).chain.map fmδ).sum
        = (mGenInsAfter Γ K rep x a).ts) ∧
    LinkR Γ K (mGenInsAfter Γ K rep x a) ∧
    LinkL Γ K (mGenInsAfter Γ K rep x a) := by
  have halt : a < x := by
    rcases ha with rfl | h
    · exact hx
    · exact hlam a h
  have hwa := mChainOf_wfparts inv ha
  have hsa := mChainOf_sum inv ha
  rcases hs : succOfM Γ K a with _ | n
  · -- no successor: R mint, end tag
    rw [mGenInsAfter_none hs]
    refine ⟨rfl, rfl, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro e he
      rcases List.mem_append.mp he with h | h
      · exact hwa.1 e h
      · rw [List.mem_singleton] at h
        subst h
        show 1 ≤ x - a
        omega
    · intro e he
      rcases List.mem_append.mp he with h | h
      · exact hwa.2 e h
      · rw [List.mem_singleton] at h
        subst h
        exact Or.inl rfl
    · show ((mChainOf K a ++ [FMEntry.R [0] (x - a)]).map fmδ).sum = x
      rw [List.map_append, List.sum_append, hsa]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      show a + (x - a + 0) = x
      omega
    · intro p hop
      injection hop with hp hsd
      subst hp
      exact ⟨rfl, halt, ha, rfl, fun n hn => by simp at hn⟩
    · intro p hop
      injection hop with hp hsd
      exact Side.noConfusion hsd
  · have hnm : n ∈ mMintedIds K := succOfM_mem hs
    have hnlt : n < x := hlam n hnm
    have hnpos : 1 ≤ n := minted_pos inv hnm
    have hwn := mChainOf_wfparts inv (Or.inr hnm)
    have hsn := mChainOf_sum inv (Or.inr hnm)
    cases hR : hasRChildM K a with
    | true =>
        -- L mint of the successor
        rw [mGenInsAfter_someTrue hs hR]
        refine ⟨rfl, rfl, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · intro e he
          rcases List.mem_append.mp he with h | h
          · exact hwn.1 e h
          · rw [List.mem_singleton] at h
            subst h
            show 1 ≤ x - n
            omega
        · intro e he
          rcases List.mem_append.mp he with h | h
          · exact hwn.2 e h
          · rw [List.mem_singleton] at h
            subst h
            exact trivial
        · show ((mChainOf K n ++ [FMEntry.L (x - n)]).map fmδ).sum = x
          rw [List.map_append, List.sum_append, hsn]
          simp only [List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil]
          show n + (x - n + 0) = x
          omega
        · intro p hop
          injection hop with hp hsd
          exact Side.noConfusion hsd
        · intro p hop
          injection hop with hp hsd
          subst hp
          exact ⟨rfl, hnlt, hnm, rfl, ha,
            succ_R_descendant inv ha hR hs⟩
    | false =>
        -- R mint, tagged with the successor's key
        rw [mGenInsAfter_someFalse hs hR]
        refine ⟨rfl, rfl, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · intro e he
          rcases List.mem_append.mp he with h | h
          · exact hwa.1 e h
          · rw [List.mem_singleton] at h
            subst h
            show 1 ≤ x - a
            omega
        · intro e he
          rcases List.mem_append.mp he with h | h
          · exact hwa.2 e h
          · rw [List.mem_singleton] at h
            subst h
            exact tagOK_key Γ hwn.1 hwn.2 (mChainOf_ne_nil inv hnm)
        · show ((mChainOf K a ++
            [FMEntry.R (sKey (fmCoordOf Γ (mChainOf K n))) (x - a)]).map
              fmδ).sum = x
          rw [List.map_append, List.sum_append, hsa]
          simp only [List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil]
          show a + (x - a + 0) = x
          omega
        · intro p hop
          injection hop with hp hsd
          subst hp
          refine ⟨rfl, halt, ha, rfl, ?_⟩
          intro n' hn'
          injection hn' with hn'
          subst hn'
          exact ⟨hnm, succ_not_R_descendant inv ha hnm hR⟩
        · intro p hop
          injection hop with hp hsd
          exact Side.noConfusion hsd

/-! ### The reachability invariant -/

theorem maxReach_inv (Γ : OrderedPrefixCode) {G : ℕ → KnowM}
    (h : MaxReach Γ G) : MInv Γ G := by
  induction h with
  | init =>
      refine ⟨fun q => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro g hg; exact absurd hg (by simp)
      · intro g hg; exact absurd hg (by simp)
      · intro g hg; exact absurd hg (by simp)
      · intro g hg; exact absurd hg (by simp)
      · intro g hg; exact absurd hg (by simp)
      · intro q q' g hg; exact absurd hg (by simp)
  | @ins G r x i hG hx hfresh hlam ih =>
      have ha : mAnchorAt Γ (G r) i = 0 ∨
          mAnchorAt Γ (G r) i ∈ mMintedIds (G r) := by
        rcases mAnchorAt_cases Γ (G r) i with h0 | hv
        · exact Or.inl h0
        · exact Or.inr (mView_sub_minted Γ (G r) _ hv)
      obtain ⟨hts, hins, hwf, hlkR, hlkL⟩ :=
        mGenInsAfter_props Γ (ih.each r) r hx hlam ha
      have hfreshr : ∀ h ∈ G r, h.ts ≠ (mGenInsAt Γ (G r) r x i).ts := by
        intro h hh
        rw [show (mGenInsAt Γ (G r) r x i).ts = x from hts]
        exact hfresh r h hh
      refine ⟨?_, ?_⟩
      · intro q
        by_cases hq : q = r
        · subst hq
          rw [Function.update_self]
          exact kinv_snoc_ins (ih.each q) (by rw [show
              (mGenInsAt Γ (G q) q x i).ts = x from hts]; exact hx)
            hins hfreshr hwf hlkR hlkL
        · rw [Function.update_of_ne hq]
          exact ih.each q
      · have hdec : ∀ {qq : ℕ} {gg : MRec},
            gg ∈ Function.update G r
              (G r ++ [mGenInsAt Γ (G r) r x i]) qq →
            (∃ q₀, gg ∈ G q₀) ∨ gg = mGenInsAt Γ (G r) r x i := by
          intro qq gg hgg
          rcases mem_update_elimM hgg with ⟨-, h'⟩ | ⟨-, h'⟩
          · exact Or.inl ⟨qq, h'⟩
          · rcases List.mem_append.mp h' with h'' | h''
            · exact Or.inl ⟨r, h''⟩
            · rw [List.mem_singleton] at h''
              exact Or.inr h''
        intro q q' g hg g' hg' hi hi' hteq
        rcases hdec hg with ⟨q₁, h1⟩ | rfl <;>
          rcases hdec hg' with ⟨q₂, h2⟩ | rfl
        · exact ih.cross q₁ q₂ g h1 g' h2 hi hi' hteq
        · exact absurd (by rw [hteq]; exact hts) (hfresh q₁ g h1)
        · exact absurd (by rw [← hteq]; exact hts) (hfresh q₂ g' h2)
        · rfl
  | @del G r t i hG ht hfresh ih =>
      have hnotins : mIsIns (mGenDelAt Γ (G r) r t i) = false := rfl
      refine ⟨?_, ?_⟩
      · intro q
        by_cases hq : q = r
        · subst hq
          rw [Function.update_self]
          exact kinv_snoc_del (ih.each q) ht hnotins
        · rw [Function.update_of_ne hq]
          exact ih.each q
      · have hdec : ∀ {qq : ℕ} {gg : MRec},
            gg ∈ Function.update G r
              (G r ++ [mGenDelAt Γ (G r) r t i]) qq →
            mIsIns gg = true → ∃ q₀, gg ∈ G q₀ := by
          intro qq gg hgg hi
          rcases mem_update_elimM hgg with ⟨-, h'⟩ | ⟨-, h'⟩
          · exact ⟨qq, h'⟩
          · rcases List.mem_append.mp h' with h'' | h''
            · exact ⟨r, h''⟩
            · rw [List.mem_singleton] at h''
              subst h''
              rw [hnotins] at hi
              exact Bool.noConfusion hi
        intro q q' g hg g' hg' hi hi' hteq
        obtain ⟨q₁, h1⟩ := hdec hg hi
        obtain ⟨q₂, h2⟩ := hdec hg' hi'
        exact ih.cross q₁ q₂ g h1 g' h2 hi hi' hteq
  | @sync G r r' hG ih =>
      refine ⟨?_, ?_⟩
      · intro q
        by_cases hq : q = r
        · subst hq
          rw [Function.update_self]
          exact kinv_sync ih q r'
        · rw [Function.update_of_ne hq]
          exact ih.each q
      · have hdec : ∀ {qq : ℕ} {gg : MRec},
            gg ∈ Function.update G r (syncM (G r) (G r')) qq →
            ∃ q₀, gg ∈ G q₀ := by
          intro qq gg hgg
          rcases mem_update_elimM hgg with ⟨-, h'⟩ | ⟨-, h'⟩
          · exact ⟨qq, h'⟩
          · rcases mem_syncM h' with h'' | h''
            · exact ⟨r, h''⟩
            · exact ⟨r', h''⟩
        intro q q' g hg g' hg' hi hi' hteq
        obtain ⟨q₁, h1⟩ := hdec hg
        obtain ⟨q₂, h2⟩ := hdec hg'
        exact ih.cross q₁ q₂ g h1 g' h2 hi hi' hteq

#print axioms maxReach_inv

/-! ## §3  The adapted W-K statement (strict reading) -/

def mLoOf (K : KnowM) (x : ℕ) : ℕ := ((mRecOfId K x).map MRec.lo).getD 0

def mRoOf (K : KnowM) (x : ℕ) : Option ℕ :=
  ((mRecOfId K x).map MRec.ro).getD none

/-- The strong-list total order: `x` displays before `y` (tombstones
included). -/
def mBefore (Γ : OrderedPrefixCode) (K : KnowM) (x y : ℕ) : Prop :=
  keyLt (mKey Γ K y) (mKey Γ K x) = true

def mLive (Γ : OrderedPrefixCode) (K : KnowM) (x : ℕ) : Prop :=
  x ∈ mView Γ K

def mConsecutive (Γ : OrderedPrefixCode) (K : KnowM) (x y : ℕ) : Prop :=
  mBefore Γ K x y ∧
    ∀ c, mLive Γ K c → ¬ (mBefore Γ K x c ∧ mBefore Γ K c y)

def mLoDesc (K : KnowM) (c p : ℕ) : Prop := ∃ nn : ℕ, (mLoOf K)^[nn] c = p

/-- Lemma 5's exception at the pair `(A, B)`. -/
def BackwardExceptionM (Γ : OrderedPrefixCode) (K : KnowM)
    (A B : ℕ) : Prop :=
  mLoOf K A ≠ mLoOf K B ∧
  ∃ C ∈ mMintedIds K, mLive Γ K C ∧
    mBefore Γ K (mLoOf K A) C ∧ mBefore Γ K C B ∧
    ¬ mLoDesc K C (mLoOf K A)

/-- Condition (1), forward non-interleaving. -/
def ForwardNIM (Γ : OrderedPrefixCode) (K : KnowM) : Prop :=
  ∀ A ∈ mMintedIds K, ∀ B ∈ mMintedIds K,
    mLive Γ K A → mLive Γ K B → mLoOf K B = A →
    (∀ D ∈ mMintedIds K, mLoOf K D = A → D ≠ B → mBefore Γ K B D) →
    mConsecutive Γ K A B

/-- Condition (2), backward non-interleaving with the exception. -/
def BackwardNIExcM (Γ : OrderedPrefixCode) (K : KnowM) : Prop :=
  ∀ A ∈ mMintedIds K, ∀ B ∈ mMintedIds K,
    mLive Γ K A → mLive Γ K B → mRoOf K A = some B →
    (∀ D ∈ mMintedIds K, mRoOf K D = some B → D ≠ A → mBefore Γ K D A) →
    ¬ BackwardExceptionM Γ K A B →
    mConsecutive Γ K A B

/-- Condition (3), the same-origin tiebreak: lower id first. -/
def SameOriginLowFirstM (Γ : OrderedPrefixCode) (K : KnowM) : Prop :=
  ∀ A ∈ mMintedIds K, ∀ B ∈ mMintedIds K,
    mLive Γ K A → mLive Γ K B →
    mLoOf K A = mLoOf K B → mRoOf K A = mRoOf K B → A < B →
    mBefore Γ K A B

def MaxNonInterleavingM (Γ : OrderedPrefixCode) (K : KnowM) : Prop :=
  ForwardNIM Γ K ∧ BackwardNIExcM Γ K ∧ SameOriginLowFirstM Γ K

/-- **The adapted Theorem-9 statement**: every replica state of every
reachable FugueMax configuration satisfies all three conditions. -/
def FugueMaxMaximallyNonInterleaving (Γ : OrderedPrefixCode) : Prop :=
  ∀ G : ℕ → KnowM, MaxReach Γ G → ∀ r, MaxNonInterleavingM Γ (G r)

/-- Condition (1) over reachability. Stated; Python-clean over 1500
randomized states and every directed case; unproved here (the
display-to-tree-traversal theory, gap G2). -/
def FugueMaxForwardNonInterleaving (Γ : OrderedPrefixCode) : Prop :=
  ∀ G : ℕ → KnowM, MaxReach Γ G → ∀ r, ForwardNIM Γ (G r)

/-- Condition (2) over reachability. Stated; Python-clean; unproved here
(same gap). -/
def FugueMaxBackwardNonInterleaving (Γ : OrderedPrefixCode) : Prop :=
  ∀ G : ℕ → KnowM, MaxReach Γ G → ∀ r, BackwardNIExcM Γ (G r)

/-! ## §4  Condition (3), PROVED: the positive twin -/

/-- Condition (3) from the invariant bundle alone: same recorded origins
force the same mint branch (the two geometry clauses collide otherwise),
and same-branch siblings diverge ascending at the kernel. -/
theorem sameOriginLowFirst_of_KInv {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) : SameOriginLowFirstM Γ K := by
  intro A hA B hB hliveA hliveB hlo hro hAB
  obtain ⟨gA, hfA, hgA, hiA, htA⟩ := mRecOfId_of_minted hA
  obtain ⟨gB, hfB, hgB, hiB, htB⟩ := mRecOfId_of_minted hB
  have hloAB : gA.lo = gB.lo := by
    have h1 : mLoOf K A = gA.lo := by simp [mLoOf, hfA]
    have h2 : mLoOf K B = gB.lo := by simp [mLoOf, hfB]
    rw [h1, h2] at hlo
    exact hlo
  have hroAB : gA.ro = gB.ro := by
    have h1 : mRoOf K A = gA.ro := by simp [mRoOf, hfA]
    have h2 : mRoOf K B = gB.ro := by simp [mRoOf, hfB]
    rw [h1, h2] at hro
    exact hro
  have hkA : mKey Γ K A = sKey (fmCoordOf Γ gA.chain) := by
    unfold mKey
    rw [mChainOf_eq_of_rec hfA]
  have hkB : mKey Γ K B = sKey (fmCoordOf Γ gB.chain) := by
    unfold mKey
    rw [mChainOf_eq_of_rec hfB]
  obtain ⟨hwPA, hwTA, -⟩ := inv.wf gA hgA hiA
  obtain ⟨hwPB, hwTB, -⟩ := inv.wf gB hgB hiB
  obtain ⟨pA, sdA, hopA⟩ := mIsIns_shape hiA
  obtain ⟨pB, sdB, hopB⟩ := mIsIns_shape hiB
  cases sdA with
  | R =>
      cases sdB with
      | R =>
          obtain ⟨e1A, e2A, e3A, e4A, e5A⟩ := inv.linkR gA hgA pA hopA
          obtain ⟨e1B, e2B, e3B, e4B, e5B⟩ := inv.linkR gB hgB pB hopB
          have hp : pB = pA := by rw [e1A, e1B, hloAB]
          have htag : tagK Γ K gB.ro = tagK Γ K gA.ro := by rw [hroAB]
          have hδ : gA.ts - pA < gB.ts - pA := by omega
          have hbef : fmChainBefore gA.chain gB.chain := by
            rw [e4A, e4B, hp, htag]
            exact fmChainBefore.diverge (mChainOf K pA)
              (FMEntry.R (tagK Γ K gA.ro) (gA.ts - pA))
              (FMEntry.R (tagK Γ K gA.ro) (gB.ts - pA)) [] []
              (Or.inr ⟨rfl, hδ⟩)
          have hdisp := fmChainBefore_display Γ hwPA hwPB hwTA hwTB hbef
          show keyLt (mKey Γ K B) (mKey Γ K A) = true
          rw [hkA, hkB]
          exact hdisp
      | L =>
          exfalso
          obtain ⟨-, -, -, -, e5A⟩ := inv.linkR gA hgA pA hopA
          obtain ⟨f1B, -, -, -, -, f6B⟩ := inv.linkL gB hgB pB hopB
          have hgAro : gA.ro = some pB := by rw [hroAB, f1B]
          obtain ⟨-, hneg⟩ := e5A pB hgAro
          rw [hloAB] at hneg
          exact hneg f6B
  | L =>
      cases sdB with
      | R =>
          exfalso
          obtain ⟨f1A, -, -, -, -, f6A⟩ := inv.linkL gA hgA pA hopA
          obtain ⟨-, -, -, -, e5B⟩ := inv.linkR gB hgB pB hopB
          have hgBro : gB.ro = some pA := by rw [← hroAB, f1A]
          obtain ⟨-, hneg⟩ := e5B pA hgBro
          rw [← hloAB] at hneg
          exact hneg f6A
      | L =>
          obtain ⟨f1A, f2A, f3A, f4A, -, -⟩ := inv.linkL gA hgA pA hopA
          obtain ⟨f1B, f2B, f3B, f4B, -, -⟩ := inv.linkL gB hgB pB hopB
          have hp : pB = pA := by
            have h1 : (some pA : Option ℕ) = some pB := by
              rw [← f1A, ← f1B, hroAB]
            injection h1 with h1
            rw [h1]
          have hδ : gA.ts - pA < gB.ts - pA := by omega
          have hbef : fmChainBefore gA.chain gB.chain := by
            rw [f4A, f4B, hp]
            exact fmChainBefore.diverge (mChainOf K pA)
              (FMEntry.L (gA.ts - pA)) (FMEntry.L (gB.ts - pA)) [] [] hδ
          have hdisp := fmChainBefore_display Γ hwPA hwPB hwTA hwTB hbef
          show keyLt (mKey Γ K B) (mKey Γ K A) = true
          rw [hkA, hkB]
          exact hdisp

/-- **The positive twin of the completed arc's first refutation**:
condition (3) of the W-K Definition 4 HOLDS for the FugueMax variant at
every replica of every reachable configuration. -/
theorem fuguemax_same_origin_low_first (Γ : OrderedPrefixCode)
    {G : ℕ → KnowM} (h : MaxReach Γ G) (r : ℕ) :
    SameOriginLowFirstM Γ (G r) :=
  sameOriginLowFirst_of_KInv ((maxReach_inv Γ h).each r)

#print axioms fuguemax_same_origin_low_first

/-- The full Theorem-9 statement reduces to exactly the two stated gaps
plus the proved condition (3). -/
theorem fuguemax_max_noninterleaving_of_gaps {Γ : OrderedPrefixCode}
    (h1 : FugueMaxForwardNonInterleaving Γ)
    (h2 : FugueMaxBackwardNonInterleaving Γ) :
    FugueMaxMaximallyNonInterleaving Γ :=
  fun G hG r =>
    ⟨h1 G hG r, h2 G hG r, fuguemax_same_origin_low_first Γ hG r⟩

#print axioms fuguemax_max_noninterleaving_of_gaps

/-! ## §5  Run contiguity: candidate (a) at the variant -/

/-- Subtrees display as contiguous blocks in any chain-generated FugueMax
fold. -/
theorem fm_fold_subtree_convex (Γ : OrderedPrefixCode) {K : KnowM}
    (chainOf : ℕ → FMChain)
    (hch : ∀ g ∈ K, mIsIns g = true →
      PosFMChain (chainOf g.ts) ∧ TagsOK (chainOf g.ts) ∧
      g.chain = chainOf g.ts)
    {p : FMChain} {x z y : SRec}
    (hx : x ∈ mFold Γ K) (hz : z ∈ mFold Γ K) (hy : y ∈ mFold Γ K)
    (hpx : ∃ ex, chainOf x.1 = p ++ ex) (hpy : ∃ ey, chainOf y.1 = p ++ ey)
    (hzx : keyLt (sKey z.2.2) (sKey x.2.2) = true)
    (hyz : keyLt (sKey y.2.2) (sKey z.2.2) = true) :
    ∃ ez, chainOf z.1 = p ++ ez := by
  obtain ⟨gx, hgx, hix, hrx⟩ := m_fold_rec_sub Γ K x hx
  obtain ⟨gz, hgz, hiz, hrz⟩ := m_fold_rec_sub Γ K z hz
  obtain ⟨gy, hgy, hiy, hry⟩ := m_fold_rec_sub Γ K y hy
  obtain ⟨hPx, hTx, hcx⟩ := hch gx hgx hix
  obtain ⟨hPz, hTz, hcz⟩ := hch gz hgz hiz
  obtain ⟨hPy, hTy, hcy⟩ := hch gy hgy hiy
  have ex1 : x.1 = gx.ts := by rw [hrx]
  have ez1 : z.1 = gz.ts := by rw [hrz]
  have ey1 : y.1 = gy.ts := by rw [hry]
  have ex2 : x.2.2 = fmCoordOf Γ (chainOf x.1) := by
    rw [hrx]
    show fmCoordOf Γ gx.chain = fmCoordOf Γ (chainOf gx.ts)
    rw [hcx]
  have ez2 : z.2.2 = fmCoordOf Γ (chainOf z.1) := by
    rw [hrz]
    show fmCoordOf Γ gz.chain = fmCoordOf Γ (chainOf gz.ts)
    rw [hcz]
  have ey2 : y.2.2 = fmCoordOf Γ (chainOf y.1) := by
    rw [hry]
    show fmCoordOf Γ gy.chain = fmCoordOf Γ (chainOf gy.ts)
    rw [hcy]
  have hPx1 : PosFMChain (chainOf x.1) := ex1 ▸ hPx
  have hPz1 : PosFMChain (chainOf z.1) := ez1 ▸ hPz
  have hPy1 : PosFMChain (chainOf y.1) := ey1 ▸ hPy
  have hTx1 : TagsOK (chainOf x.1) := ex1 ▸ hTx
  have hTz1 : TagsOK (chainOf z.1) := ez1 ▸ hTz
  have hTy1 : TagsOK (chainOf y.1) := ey1 ▸ hTy
  have hnexz : chainOf x.1 ≠ chainOf z.1 := by
    intro he
    rw [ex2, ez2, he, keyLt_irrefl] at hzx
    exact Bool.noConfusion hzx
  have hnezy : chainOf z.1 ≠ chainOf y.1 := by
    intro he
    rw [ez2, ey2, he, keyLt_irrefl] at hyz
    exact Bool.noConfusion hyz
  have hbxz : fmChainBefore (chainOf x.1) (chainOf z.1) :=
    (fmdisplay_iff_fmChainBefore Γ hPx1 hPz1 hTx1 hTz1 hnexz).mp
      (by rw [← ex2, ← ez2]; exact hzx)
  have hbzy : fmChainBefore (chainOf z.1) (chainOf y.1) :=
    (fmdisplay_iff_fmChainBefore Γ hPz1 hPy1 hTz1 hTy1 hnezy).mp
      (by rw [← ez2, ← ey2]; exact hyz)
  exact fm_subtree_convex p hpx hpy hbxz hbzy

#print axioms fm_fold_subtree_convex

/-- A run whose elements chain (each mint extends the previous element's
chain by one entry — what the FugueMax policy generates for forward and
backward runs alike). -/
def RunChainsM (chainOf : ℕ → FMChain) : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      (∃ e, chainOf b = chainOf a ++ [e]) ∧ RunChainsM chainOf (b :: rest)

theorem runChainsM_head_prefix (chainOf : ℕ → FMChain) :
    ∀ (xs : List ℕ) (h : ℕ), RunChainsM chainOf (h :: xs) →
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

/-- **Candidate (a) at the variant**: two runs with prefix-incomparable
head chains never interleave in any chain-generated FugueMax fold. -/
theorem fuguemax_runs_no_interleave (Γ : OrderedPrefixCode) {K : KnowM}
    (chainOf : ℕ → FMChain)
    (hch : ∀ g ∈ K, mIsIns g = true →
      PosFMChain (chainOf g.ts) ∧ TagsOK (chainOf g.ts) ∧
      g.chain = chainOf g.ts)
    {h1 h2 : ℕ} {run1 run2 : List ℕ}
    (hrc1 : RunChainsM chainOf (h1 :: run1))
    (hrc2 : RunChainsM chainOf (h2 :: run2))
    (hpq : ¬ chainOf h1 <+: chainOf h2)
    (hqp : ¬ chainOf h2 <+: chainOf h1)
    {x z y : SRec}
    (hx : x ∈ mFold Γ K) (hz : z ∈ mFold Γ K) (hy : y ∈ mFold Γ K)
    (hxm : x.1 ∈ h1 :: run1) (hym : y.1 ∈ h1 :: run1)
    (hzm : z.1 ∈ h2 :: run2)
    (hzx : keyLt (sKey z.2.2) (sKey x.2.2) = true)
    (hyz : keyLt (sKey y.2.2) (sKey z.2.2) = true) : False := by
  obtain ⟨ex, hex⟩ :=
    runChainsM_head_prefix chainOf run1 h1 hrc1 x.1 hxm
  obtain ⟨ey, hey⟩ :=
    runChainsM_head_prefix chainOf run1 h1 hrc1 y.1 hym
  obtain ⟨ez0, hez0⟩ :=
    runChainsM_head_prefix chainOf run2 h2 hrc2 z.1 hzm
  obtain ⟨ez, hez⟩ := fm_fold_subtree_convex Γ chainOf hch hx hz hy
    ⟨ex, hex.symm⟩ ⟨ey, hey.symm⟩ hzx hyz
  have hzc1 : chainOf h1 <+: chainOf z.1 := ⟨ez, hez.symm⟩
  have hzc2 : chainOf h2 <+: chainOf z.1 := ⟨ez0, hez0⟩
  rcases List.prefix_or_prefix_of_prefix hzc1 hzc2 with h | h
  · exact hpq h
  · exact hqp h

/-- Reachable knowledge is chain-generated in exactly the shape the run
theorems consume. -/
theorem maxReach_chain_gen (Γ : OrderedPrefixCode) {G : ℕ → KnowM}
    (h : MaxReach Γ G) (r : ℕ) :
    ∀ g ∈ G r, mIsIns g = true →
      PosFMChain (mChainOf (G r) g.ts) ∧ TagsOK (mChainOf (G r) g.ts) ∧
      g.chain = mChainOf (G r) g.ts := by
  have inv := (maxReach_inv Γ h).each r
  intro g hg hins
  have hc := mChainOf_of_mem inv hg hins
  obtain ⟨h1, h2, -⟩ := inv.wf g hg hins
  rw [hc]
  exact ⟨h1, h2, rfl⟩

/-- Candidate (a) at any reachable FugueMax configuration. -/
theorem fuguemax_reachable_runs_no_interleave (Γ : OrderedPrefixCode)
    {G : ℕ → KnowM} (hreach : MaxReach Γ G) (r : ℕ)
    {h1 h2 : ℕ} {run1 run2 : List ℕ}
    (hrc1 : RunChainsM (mChainOf (G r)) (h1 :: run1))
    (hrc2 : RunChainsM (mChainOf (G r)) (h2 :: run2))
    (hpq : ¬ mChainOf (G r) h1 <+: mChainOf (G r) h2)
    (hqp : ¬ mChainOf (G r) h2 <+: mChainOf (G r) h1)
    {x z y : SRec}
    (hx : x ∈ mFold Γ (G r)) (hz : z ∈ mFold Γ (G r))
    (hy : y ∈ mFold Γ (G r))
    (hxm : x.1 ∈ h1 :: run1) (hym : y.1 ∈ h1 :: run1)
    (hzm : z.1 ∈ h2 :: run2)
    (hzx : keyLt (sKey z.2.2) (sKey x.2.2) = true)
    (hyz : keyLt (sKey y.2.2) (sKey z.2.2) = true) : False :=
  fuguemax_runs_no_interleave Γ (mChainOf (G r))
    (maxReach_chain_gen Γ hreach r) hrc1 hrc2 hpq hqp hx hz hy
    hxm hym hzm hzx hyz

#print axioms fuguemax_reachable_runs_no_interleave

/-! ## §6  SPOTs (PASS+FAIL, hand-derived, matching fuguemax_check.py) -/

namespace FugueMaxSPOT

def gIns (K : KnowM) (rep x i : ℕ) : KnowM :=
  K ++ [mGenInsAt unaryCode K rep x i]

/-! ### Two concurrent front inserts: the C3 witness flips -/

def kTie : KnowM := syncM (gIns [] 0 1 0) (gIns [] 1 2 0)

/-- PASS: FugueMax ties ascending — the lower id displays first (the
Fugue kernel displayed `[2, 1]` here, its condition-(3) refutation). -/
theorem tie_display : mView unaryCode kTie = [1, 2] := by native_decide

/-- FAIL pin: the recency order is NOT displayed. -/
theorem tie_not_recency : mView unaryCode kTie ≠ [2, 1] := by native_decide

/-! ### L19 backward: the L band is unchanged -/

def kL : KnowM := gIns [] 0 1 0
def kA19 : KnowM := gIns (gIns (gIns kL 0 10 0) 0 30 0) 0 50 0
def kB19 : KnowM := gIns (gIns (gIns kL 1 21 0) 1 41 0) 1 61 0
def k19 : KnowM := syncM kA19 kB19

/-- PASS: both backward runs contiguous, in text order — identical to the
Fugue policy's display (the L band did not change). -/
theorem l19_display :
    mView unaryCode k19 = [50, 30, 10, 61, 41, 21, 1] := by native_decide

/-- FAIL pin: the one-sided fan's interleaving. -/
theorem l19_not_interleaved :
    mView unaryCode k19 ≠ [61, 50, 41, 30, 21, 10, 1] := by native_decide

/-! ### The forward twin: the block ORDER flips to ascending-ID -/

def kAf : KnowM := gIns (gIns (gIns kL 0 10 1) 0 30 2) 0 50 3
def kBf : KnowM := gIns (gIns (gIns kL 1 21 1) 1 41 2) 1 61 3
def kFwd : KnowM := syncM kAf kBf

/-- PASS: blocks contiguous, the LOWER-id head's block first (condition
(3) satisfied where the Fugue kernel violated it). -/
theorem forward_twin_display :
    mView unaryCode kFwd = [1, 10, 30, 50, 21, 41, 61] := by native_decide

/-- FAIL pin: the Fugue kernel's recency block order. -/
theorem forward_twin_not_recency :
    mView unaryCode kFwd ≠ [1, 21, 41, 61, 10, 30, 50] := by native_decide

/-! ### Mixed backward/forward at one position -/

def kAm : KnowM := gIns (gIns (gIns kL 0 10 1) 0 30 1) 0 50 1
def kMix : KnowM := syncM kAm kBf

/-- PASS: both blocks contiguous in text order; A's block first (its head
10 has the lower id). -/
theorem mixed_display :
    mView unaryCode kMix = [1, 50, 30, 10, 21, 41, 61] := by native_decide

/-- FAIL pin: the Fugue kernel's order on the same trace. -/
theorem mixed_not_fugue_order :
    mView unaryCode kMix ≠ [1, 21, 41, 61, 50, 30, 10] := by native_decide

/-! ### Figure 7, both mint orders: the FugueMax-critical traces -/

def kA7 : KnowM := gIns [] 0 3 0
def kB7 : KnowM := gIns [] 1 4 0
def kC7 : KnowM := gIns [] 2 5 0
def k17 : KnowM := gIns (syncM kA7 kC7) 0 6 1
def k27 : KnowM := gIns (syncM kB7 kA7) 1 7 1
def kFig : KnowM := syncM k17 k27

/-- PASS: the Figure-7 execution displays the paper's unique maximally
non-interleaving order A X Y B C. -/
theorem fig7_display : mView unaryCode kFig = [3, 6, 7, 4, 5] := by
  native_decide

/-- FAIL pin: the Fugue kernel's Figure-7 display had Y before X (its
condition-(2) refutation shape). -/
theorem fig7_not_backward_interleaved :
    mView unaryCode kFig ≠ [3, 7, 6, 4, 5] := by native_decide

def k17a : KnowM := gIns (syncM kA7 kC7) 0 7 1
def k27a : KnowM := gIns (syncM kB7 kA7) 1 6 1
def kFigA : KnowM := syncM k17a k27a

/-- PASS: the ADVERSE mint order (Y = 6 minted before X = 7). X still
displays first: the right-origin tag overrides both recency and ID order.
This is the trace on which every plain re-banding of the sided alphabet
fails condition (2) (the Python `mirror` control). -/
theorem fig7_adverse_display :
    mView unaryCode kFigA = [3, 7, 6, 4, 5] := by native_decide

/-- FAIL pin: the ascending-ID (plain-Fugue) order is NOT displayed. -/
theorem fig7_adverse_not_id_order :
    mView unaryCode kFigA ≠ [3, 6, 7, 4, 5] := by native_decide

end FugueMaxSPOT

#print axioms FugueMaxSPOT.tie_display
#print axioms FugueMaxSPOT.fig7_adverse_display

end Sal.ConditionedMRDTs
