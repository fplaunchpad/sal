import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_Fugue
import Sal.MRDTs.RGA_Embed.Sided_Traversal

/-!
# Fugue forward non-interleaving: the condition-(1) discharge

This file discharges the stated def `FugueForwardNonInterleaving` of
`SidedRGA_Fugue.lean` (Weidner-Kleppmann Definition 4 condition (1),
strict reading) at every replica of every `FugueReach`-reachable
configuration, kernel-clean. The proof is the SAME loShape +
first-after-descent argument as the FugueMax discharge, the argmax
argument, the descent, and the discharge never consult the sibling
order, but `SidedRGA_Fugue.lean`'s `GInv` carries no link clauses, so
the entire link layer is built here first, EXTERNALLY (this file adds
invariants over `FugueReach`; it does not touch the Fugue file):

* **§1 The link layer**: `LinkR`/`LinkL` (mint geometry recorded in the
  clauses: parent identity, chain extension by one entry, parent
  mintedness) and `SLC` (the all-L successor shape), bundled as
  `LinkInv`, with the preservation theorem `fugueReach_links` threaded
  through inserts, deletes, and syncs. The per-knowledge working bundle
  `FInv` assembles the Fugue file's `GInv` parts with the link clauses.

* **§2 The geometry**: ancestor closure (`chain_prefix_minted`),
  R-headedness (`chain_head_R`), and the two successor lemmas
  (`succ_R_descendant`, `succ_R_desc_allL`) on the PLAIN sided kernel
  (`Sided_ChainLex`/`Sided_Traversal`; entries are `(Side, δ)`, no
  tags, the FugueMax variant alphabet never appears).

* **§3 loShape, the descent, the discharge**: `loShape_of_inv`,
  `lo_child_before`, `forwardNI_of_inv`, and
  `fugue_forward_ni : FugueForwardNonInterleaving Γ`.

* **§4 SPOTs**, PASS+FAIL shaped, on the Figure-7 and L19 traces of the
  Fugue file (the FAIL pin of the adjacency is the FugueMax rival
  verdict: the recency policy seats 7, not 6, next to 5).

Everything except the final discharge lives in the `FugueFwd`
sub-namespace: the sibling files (`SidedRGA_FugueMax.lean`,
`SidedRGA_NonInterleaving.lean`) define the same-shaped names for the
variant world at the `Sal.ConditionedMRDTs` level, and this file must
coexist with them under the umbrella import.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode keyLt sKey Side SEntry SChain
  PosSChain sidedCoordOf unaryCode schainBefore
  keyLt_irrefl keyLt_asymm keyLt_trans keyLt_total
  sidedCoordOf_inj schainBefore_display sdisplay_iff_schainBefore
  schain_subtree_convex schain_ext_after_is_R)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FugueFwd

/-! ## §1  The link layer -/

/-- Shape of a minted op. -/
theorem gIsIns_shape {g : GRec} (h : sIsIns g.op = true) :
    ∃ e π p sd, g.op.2.2 = SOp.ins e π p sd := by
  cases hop : g.op.2.2 with
  | ins e π p sd => exact ⟨e, π, p, sd, rfl⟩
  | del x =>
      exfalso
      unfold sIsIns at h
      rw [hop] at h
      exact Bool.noConfusion h

/-- L-entries-only chains: the tail shape of a left-origin walk step. -/
def AllL (ls : SChain) : Prop := ∀ e ∈ ls, ∃ d, e = (Side.L, d)

/-- The R-mint link clause: parent = left origin, chain extends the
parent's by one R entry, parent minted (or start). -/
def LinkR (Γ : OrderedPrefixCode) (K : Know) (g : GRec) : Prop :=
  ∀ e π p, g.op.2.2 = SOp.ins e π p Side.R →
    p = g.lo ∧ p < g.op.1 ∧ (p = 0 ∨ p ∈ gMintedIds K) ∧
    g.chain = gChainOf K p ++ [(Side.R, g.op.1 - p)]

/-- The L-mint link clause: parent = right origin (the mint-time
successor), chain extends the parent's by one L entry, parent minted,
left origin minted or start. -/
def LinkL (Γ : OrderedPrefixCode) (K : Know) (g : GRec) : Prop :=
  ∀ e π p, g.op.2.2 = SOp.ins e π p Side.L →
    g.ro = some p ∧ p < g.op.1 ∧ p ∈ gMintedIds K ∧
    g.chain = gChainOf K p ++ [(Side.L, g.op.1 - p)] ∧
    (g.lo = 0 ∨ g.lo ∈ gMintedIds K)

/-- **The strengthened L-mint clause** (the loShape engine): an L mint's
parent extends the recorded left origin by one R entry and L entries
only. -/
def SLC (Γ : OrderedPrefixCode) (K : Know) (g : GRec) : Prop :=
  ∀ e π p, g.op.2.2 = SOp.ins e π p Side.L →
    ∃ d ls, gChainOf K p = gChainOf K g.lo ++ (Side.R, d) :: ls ∧ AllL ls

/-- **The external link invariant** over one knowledge: every record
satisfies all three clauses. Lives outside `GInv` (the Fugue file is not
touched), exactly as `maxReach_inv2` lives outside `MInv`. -/
def LinkInv (Γ : OrderedPrefixCode) (K : Know) : Prop :=
  ∀ g ∈ K, LinkR Γ K g ∧ LinkL Γ K g ∧ SLC Γ K g

/-- The per-knowledge working bundle: the `GInv` parts restricted to one
replica, plus the two link clauses. -/
structure FInv (Γ : OrderedPrefixCode) (K : Know) : Prop where
  pos : ∀ g ∈ K, 1 ≤ g.op.1
  uniq : ∀ g ∈ K, ∀ g' ∈ K, sIsIns g.op = true → sIsIns g'.op = true →
    g.op.1 = g'.op.1 → g = g'
  wf : ∀ g ∈ K, sIsIns g.op = true →
    PosSChain g.chain ∧ (g.chain.map Prod.snd).sum = g.op.1
  linkR : ∀ g ∈ K, LinkR Γ K g
  linkL : ∀ g ∈ K, LinkL Γ K g

/-- Assemble the working bundle from the Fugue file's `GInv` and the
link invariant. -/
theorem fInv_mk {Γ : OrderedPrefixCode} {G : ℕ → Know} (inv : GInv Γ G)
    (q : ℕ) (lk : LinkInv Γ (G q)) : FInv Γ (G q) :=
  ⟨inv.pos q,
   fun g hg g' hg' => inv.uniq q q g hg g' hg',
   fun g hg hins =>
     ⟨(inv.wf q g hg hins).1, (inv.wf q g hg hins).2.1⟩,
   fun g hg => (lk g hg).1,
   fun g hg => (lk g hg).2.1⟩

/-! ### Chain facts from the bundle -/

theorem gChainOf_of_mem {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) {c : GRec} (hc : c ∈ K) (hins : sIsIns c.op = true) :
    gChainOf K c.op.1 = c.chain := by
  have hmem : c.op.1 ∈ gMintedIds K :=
    List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, hins⟩, rfl⟩
  obtain ⟨g, hfind, hgK, hgins, hgts⟩ := gRecOfId_of_minted hmem
  rw [gChainOf_eq_of_rec hfind, inv.uniq g hgK c hc hgins hins hgts]

theorem gChainOf_posOf {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) {x : ℕ} (hx : x = 0 ∨ x ∈ gMintedIds K) :
    PosSChain (gChainOf K x) := by
  rcases hx with rfl | hx
  · rw [gChainOf_zero inv.pos]
    exact fun e he => absurd he (by simp)
  · obtain ⟨g, hfind, hgK, hgins, hgts⟩ := gRecOfId_of_minted hx
    rw [gChainOf_eq_of_rec hfind]
    exact (inv.wf g hgK hgins).1

theorem gChainOf_sum {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) {x : ℕ} (hx : x = 0 ∨ x ∈ gMintedIds K) :
    ((gChainOf K x).map Prod.snd).sum = x := by
  rcases hx with rfl | hx
  · rw [gChainOf_zero inv.pos]
    rfl
  · obtain ⟨g, hfind, hgK, hgins, hgts⟩ := gRecOfId_of_minted hx
    rw [gChainOf_eq_of_rec hfind, ← hgts]
    exact (inv.wf g hgK hgins).2

theorem minted_pos {Γ : OrderedPrefixCode} {K : Know} (inv : FInv Γ K)
    {x : ℕ} (hx : x ∈ gMintedIds K) : 1 ≤ x := by
  obtain ⟨g, hfind, hgK, hgins, hgts⟩ := gRecOfId_of_minted hx
  rw [← hgts]
  exact inv.pos g hgK

theorem gChainOf_ne_nil {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) {x : ℕ} (hx : x ∈ gMintedIds K) :
    gChainOf K x ≠ [] := by
  intro h
  have hsum := gChainOf_sum inv (Or.inr hx)
  rw [h] at hsum
  have hp := minted_pos inv hx
  rw [← hsum] at hp
  exact absurd hp (by decide)

/-- The display bridge, packaged: chain order gives key order. -/
theorem gKey_lt_of_chainBefore {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) {x y : ℕ}
    (hx : x = 0 ∨ x ∈ gMintedIds K) (hy : y = 0 ∨ y ∈ gMintedIds K)
    (hb : schainBefore (gChainOf K x) (gChainOf K y)) :
    keyLt (gKey Γ K y) (gKey Γ K x) = true := by
  unfold gKey
  exact schainBefore_display Γ (gChainOf_posOf inv hx)
    (gChainOf_posOf inv hy) hb

/-- The reverse bridge: key order plus distinct chains gives chain
order. -/
theorem chainBefore_of_gKey_lt {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) {x y : ℕ}
    (hx : x = 0 ∨ x ∈ gMintedIds K) (hy : y = 0 ∨ y ∈ gMintedIds K)
    (hne : gChainOf K x ≠ gChainOf K y)
    (h : keyLt (gKey Γ K y) (gKey Γ K x) = true) :
    schainBefore (gChainOf K x) (gChainOf K y) := by
  unfold gKey at h
  exact (sdisplay_iff_schainBefore Γ (gChainOf_posOf inv hx)
    (gChainOf_posOf inv hy) hne).mp h

/-! ### Link-clause transport under knowledge growth -/

theorem linkR_transport {Γ : OrderedPrefixCode} {K K' : Know} {g : GRec}
    (hL : LinkR Γ K g)
    (hchain : ∀ y, y = 0 ∨ y ∈ gMintedIds K →
      gChainOf K' y = gChainOf K y)
    (hmem : ∀ y, y ∈ gMintedIds K → y ∈ gMintedIds K') :
    LinkR Γ K' g := by
  intro e π p hop
  obtain ⟨h1, h2, h3, h4⟩ := hL e π p hop
  refine ⟨h1, h2, ?_, ?_⟩
  · rcases h3 with h | h
    · exact Or.inl h
    · exact Or.inr (hmem p h)
  · rw [hchain p h3]
    exact h4

theorem linkL_transport {Γ : OrderedPrefixCode} {K K' : Know} {g : GRec}
    (hL : LinkL Γ K g)
    (hchain : ∀ y, y = 0 ∨ y ∈ gMintedIds K →
      gChainOf K' y = gChainOf K y)
    (hmem : ∀ y, y ∈ gMintedIds K → y ∈ gMintedIds K') :
    LinkL Γ K' g := by
  intro e π p hop
  obtain ⟨h1, h2, h3, h4, h5⟩ := hL e π p hop
  refine ⟨h1, h2, hmem p h3, ?_, ?_⟩
  · rw [hchain p (Or.inr h3)]
    exact h4
  · rcases h5 with h | h
    · exact Or.inl h
    · exact Or.inr (hmem g.lo h)

theorem slc_transport {Γ : OrderedPrefixCode} {K K' : Know} {g : GRec}
    (h : SLC Γ K g) (hlk : LinkL Γ K g)
    (hchain : ∀ y, y = 0 ∨ y ∈ gMintedIds K →
      gChainOf K' y = gChainOf K y) :
    SLC Γ K' g := by
  intro e π p hop
  obtain ⟨d, ls, hdec, hall⟩ := h e π p hop
  obtain ⟨-, -, h3, -, h5⟩ := hlk e π p hop
  refine ⟨d, ls, ?_, hall⟩
  rw [hchain p (Or.inr h3), hchain g.lo h5]
  exact hdec

/-! ### Stability of chain lookups under knowledge growth -/

theorem gChainOf_append_stable {K : Know} {y : ℕ}
    (hy : y = 0 ∨ y ∈ gMintedIds K)
    (hpos : ∀ g ∈ K, 1 ≤ g.op.1) {K' : Know}
    (hpos' : ∀ g ∈ K', 1 ≤ g.op.1) :
    gChainOf (K ++ K') y = gChainOf K y := by
  rcases hy with rfl | hy
  · rw [gChainOf_zero (K := K ++ K') (by
      intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact hpos g h
      · exact hpos' g h), gChainOf_zero hpos]
  · obtain ⟨g, hfind, -, -, -⟩ := gRecOfId_of_minted hy
    rw [gChainOf_eq_of_rec (gRecOfId_append_left hfind K'),
      gChainOf_eq_of_rec hfind]

theorem gMinted_snoc_del {K : Know} {g : GRec} (h : sIsIns g.op = false) :
    gMinted (K ++ [g]) = gMinted K := by
  rw [gMinted_append]
  simp [gMinted, h]

theorem gChainOf_snoc_del {K : Know} {g : GRec} (h : sIsIns g.op = false)
    (y : ℕ) : gChainOf (K ++ [g]) y = gChainOf K y := by
  unfold gChainOf gRecOfId
  rw [gMinted_snoc_del h]

theorem gMintedIds_snoc_del {K : Know} {g : GRec}
    (h : sIsIns g.op = false) : gMintedIds (K ++ [g]) = gMintedIds K := by
  unfold gMintedIds
  rw [gMinted_snoc_del h]

/-- Same-id minted records agree across knowledges, so `gChainOf`
does. -/
theorem gChainOf_agree {K₁ K₂ : Know}
    (h : ∀ g ∈ K₁, ∀ g' ∈ K₂, sIsIns g.op = true → sIsIns g'.op = true →
      g.op.1 = g'.op.1 → g = g')
    {x : ℕ} (hx₁ : x ∈ gMintedIds K₁) (hx₂ : x ∈ gMintedIds K₂) :
    gChainOf K₁ x = gChainOf K₂ x := by
  obtain ⟨g₁, hf₁, hm₁, hi₁, ht₁⟩ := gRecOfId_of_minted hx₁
  obtain ⟨g₂, hf₂, hm₂, hi₂, ht₂⟩ := gRecOfId_of_minted hx₂
  rw [gChainOf_eq_of_rec hf₁, gChainOf_eq_of_rec hf₂,
    h g₁ hm₁ g₂ hm₂ hi₁ hi₂ (by rw [ht₁, ht₂])]

theorem minted_syncK_right {K K' : Know} {x : ℕ}
    (h : x ∈ gMintedIds K') : x ∈ gMintedIds (syncK K K') := by
  obtain ⟨g, hg, hx⟩ := List.mem_map.mp h
  have hgK' := List.mem_of_mem_filter hg
  have hins := (List.mem_filter.mp hg).2
  by_cases hK : g ∈ K
  · exact List.mem_map.mpr ⟨g, List.mem_filter.mpr
      ⟨List.mem_append_left _ hK, hins⟩, hx⟩
  · exact List.mem_map.mpr ⟨g, List.mem_filter.mpr
      ⟨List.mem_append_right _ (List.mem_filter.mpr
        ⟨hgK', by simpa using hK⟩), hins⟩, hx⟩

/-! ### Successor machinery: the argmax facts -/

/-- Key-list entries name minted elements and carry their keys (the
record-identifying `uniq` collapses the stored chain onto the lookup). -/
theorem gKeys_shape {Γ : OrderedPrefixCode} {K : Know} (inv : FInv Γ K)
    {p : ℕ × List ℕ} (h : p ∈ gKeys Γ K) :
    p.1 ∈ gMintedIds K ∧ p.2 = gKey Γ K p.1 := by
  obtain ⟨g, hg, hp⟩ := List.mem_map.mp h
  subst hp
  have hins := (List.mem_filter.mp hg).2
  have hmem : g.op.1 ∈ gMintedIds K := List.mem_map.mpr ⟨g, hg, rfl⟩
  refine ⟨hmem, ?_⟩
  show sKey (sidedCoordOf Γ g.chain) = gKey Γ K g.op.1
  unfold gKey
  rw [gChainOf_of_mem inv (List.mem_of_mem_filter hg) hins]

/-- The argmax result is a candidate pair with the looked-up key. -/
theorem succOf_pair {Γ : OrderedPrefixCode} {K : Know} (inv : FInv Γ K)
    {a n : ℕ} (h : succOf Γ K a = some n) :
    (n, gKey Γ K n) ∈ succCand Γ K a := by
  unfold succOf at h
  cases hf : (succCand Γ K a).foldl maxKey none with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some p =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      rcases foldl_maxKey_mem _ none hf with h' | h'
      · exact absurd h' (by simp)
      · have hp2 : p.2 = gKey Γ K p.1 :=
          (gKeys_shape inv (succCand_sub h')).2
        have hpe : (p.1, gKey Γ K p.1) = p := by
          rw [← hp2]
        rw [hpe]
        exact h'

theorem succOf_after_anchor {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) {a n : ℕ}
    (h : succOf Γ K a = some n) (ha : a ≠ 0) :
    keyLt (gKey Γ K n) (gKey Γ K a) = true := by
  have hp := succOf_pair inv h
  unfold succCand at hp
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
theorem succOf_max {Γ : OrderedPrefixCode} {K : Know} (inv : FInv Γ K)
    {a n : ℕ} (h : succOf Γ K a = some n) {y : ℕ}
    (hy : (y, gKey Γ K y) ∈ succCand Γ K a) :
    keyLt (gKey Γ K n) (gKey Γ K y) = false := by
  unfold succOf at h
  cases hf : (succCand Γ K a).foldl maxKey none with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some p =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hpmem : p ∈ succCand Γ K a := by
        rcases foldl_maxKey_mem _ none hf with h' | h'
        · exact absurd h' (by simp)
        · exact h'
      have h2 : p.2 = gKey Γ K p.1 :=
        (gKeys_shape inv (succCand_sub hpmem)).2
      have hnb := (foldl_maxKey_not_beaten _ none hf).1 _ hy
      rw [h2] at hnb
      exact hnb

/-! ## §2  The geometry: closure walk, R-headedness, successor lemmas -/

theorem hasRChild_iff {K : Know} {a : ℕ} :
    hasRChild K a = true ↔
      ∃ g ∈ K, ∃ e π, g.op.2.2 = SOp.ins e π a Side.R := by
  unfold hasRChild
  rw [List.any_eq_true]
  constructor
  · rintro ⟨g, hg, hR⟩
    unfold gAnchorR at hR
    cases hop : g.op.2.2 with
    | ins e π p sd =>
        rw [hop] at hR
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hR
        exact ⟨g, hg, e, π, by rw [hop, hR.1, hR.2]⟩
    | del x =>
        rw [hop] at hR
        exact Bool.noConfusion hR
  · rintro ⟨g, hg, e, π, hop⟩
    refine ⟨g, hg, ?_⟩
    unfold gAnchorR
    rw [hop]
    simp

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
theorem chain_prefix_minted {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) :
    ∀ (N : ℕ) (g : GRec), g ∈ K → sIsIns g.op = true →
      g.chain.length ≤ N →
      ∀ pre e, (pre ++ [e]) <+: g.chain →
        ∃ h, h ∈ K ∧ sIsIns h.op = true ∧ h.chain = pre ++ [e] := by
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
      obtain ⟨e0, π, p, sd, hop⟩ := gIsIns_shape hins
      have hdecomp : (p = 0 ∨ p ∈ gMintedIds K) ∧
          ∃ e', g.chain = gChainOf K p ++ [e'] := by
        cases sd with
        | R =>
            obtain ⟨-, -, h3, h4⟩ := inv.linkR g hg e0 π p hop
            exact ⟨h3, _, h4⟩
        | L =>
            obtain ⟨-, -, h3, h4, -⟩ := inv.linkL g hg e0 π p hop
            exact ⟨Or.inr h3, _, h4⟩
      obtain ⟨hp, e', hchain⟩ := hdecomp
      rw [hchain] at hpre
      rcases prefix_concat_cases hpre with heq | hpre'
      · exact ⟨g, hg, hins, by rw [hchain, heq]⟩
      · have hpne : p ≠ 0 := by
          intro h0
          subst h0
          rw [gChainOf_zero inv.pos] at hpre'
          have := hpre'.length_le
          simp at this
        have hpm : p ∈ gMintedIds K := by
          rcases hp with h | h
          · exact absurd h hpne
          · exact h
        obtain ⟨hrec, hrecfind, hrecK, hrecins, hrects⟩ :=
          gRecOfId_of_minted hpm
        have hchain_p : gChainOf K p = hrec.chain :=
          gChainOf_eq_of_rec hrecfind
        have hlen' : hrec.chain.length ≤ N := by
          have h1 := congrArg List.length hchain
          rw [List.length_append, List.length_singleton, hchain_p] at h1
          omega
        exact ih hrec hrecK hrecins hlen' pre e (hchain_p ▸ hpre')

/-- Every minted chain is R-headed: the root's children are R mints. -/
theorem chain_head_R {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) :
    ∀ (N : ℕ) (g : GRec), g ∈ K → sIsIns g.op = true →
      g.chain.length ≤ N →
      ∃ d rest, g.chain = (Side.R, d) :: rest := by
  intro N
  induction N with
  | zero =>
      intro g hg hins hlen
      exfalso
      have hsum := (inv.wf g hg hins).2
      have hchain_nil : g.chain = [] := List.length_eq_zero_iff.mp
        (Nat.le_antisymm hlen (Nat.zero_le _))
      rw [hchain_nil] at hsum
      have hp := inv.pos g hg
      rw [← hsum] at hp
      exact absurd hp (by decide)
  | succ N ih =>
      intro g hg hins hlen
      obtain ⟨e0, π, p, sd, hop⟩ := gIsIns_shape hins
      cases sd with
      | R =>
          obtain ⟨-, -, h3, h4⟩ := inv.linkR g hg e0 π p hop
          cases hpc : gChainOf K p with
          | nil =>
              refine ⟨g.op.1 - p, [], ?_⟩
              rw [h4, hpc]
              rfl
          | cons ee pc' =>
              have hpm : p ∈ gMintedIds K := by
                rcases h3 with h | h
                · exfalso
                  subst h
                  rw [gChainOf_zero inv.pos] at hpc
                  simp at hpc
                · exact h
              obtain ⟨hrec, hrecfind, hrecK, hrecins, hrects⟩ :=
                gRecOfId_of_minted hpm
              have hchain_p : gChainOf K p = hrec.chain :=
                gChainOf_eq_of_rec hrecfind
              have hlen' : hrec.chain.length ≤ N := by
                have h1 := congrArg List.length h4
                rw [List.length_append, List.length_singleton,
                  hchain_p] at h1
                omega
              obtain ⟨d', rest', hhead⟩ := ih hrec hrecK hrecins hlen'
              refine ⟨d', rest' ++ [(Side.R, g.op.1 - p)], ?_⟩
              rw [h4, hchain_p, hhead]
              rfl
      | L =>
          obtain ⟨-, -, h3, h4, -⟩ := inv.linkL g hg e0 π p hop
          obtain ⟨hrec, hrecfind, hrecK, hrecins, hrects⟩ :=
            gRecOfId_of_minted h3
          have hchain_p : gChainOf K p = hrec.chain :=
            gChainOf_eq_of_rec hrecfind
          have hlen' : hrec.chain.length ≤ N := by
            have h1 := congrArg List.length h4
            rw [List.length_append, List.length_singleton, hchain_p] at h1
            omega
          obtain ⟨d', rest', hhead⟩ := ih hrec hrecK hrecins hlen'
          refine ⟨d', rest' ++ [(Side.L, g.op.1 - p)], ?_⟩
          rw [h4, hchain_p, hhead]
          rfl

/-- An R-descendant of `lo` witnesses a (possibly dead) R-child of `lo`
in the same knowledge. -/
theorem hasR_of_R_descendant {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) {lo n : ℕ}
    (hlo : lo = 0 ∨ lo ∈ gMintedIds K) (hn : n ∈ gMintedIds K)
    (hdesc : ∃ d rest, gChainOf K n
      = gChainOf K lo ++ (Side.R, d) :: rest) :
    hasRChild K lo = true := by
  obtain ⟨d, rest, hd⟩ := hdesc
  obtain ⟨gn, hnfind, hnK, hnins, hnts⟩ := gRecOfId_of_minted hn
  have hnchain : gn.chain = gChainOf K lo ++ (Side.R, d) :: rest := by
    rw [← gChainOf_eq_of_rec hnfind, hd]
  have hpre : (gChainOf K lo ++ [(Side.R, d)]) <+: gn.chain := by
    rw [hnchain]
    exact ⟨rest, by simp⟩
  obtain ⟨c, hcK, hcins, hcchain⟩ := chain_prefix_minted inv
    gn.chain.length gn hnK hnins (Nat.le_refl _) _ _ hpre
  obtain ⟨e0, π, pc, sdc, hcop⟩ := gIsIns_shape hcins
  cases sdc with
  | L =>
      exfalso
      obtain ⟨-, -, -, h4, -⟩ := inv.linkL c hcK e0 π pc hcop
      rw [hcchain] at h4
      have hinj := List.append_inj' h4 rfl
      injection hinj.2 with h5
      have h6 : Side.R = Side.L := congrArg Prod.fst h5
      exact Side.noConfusion h6
  | R =>
      obtain ⟨-, -, h3, h4⟩ := inv.linkR c hcK e0 π pc hcop
      rw [hcchain] at h4
      have hinj := List.append_inj' h4 rfl
      have hpceq : gChainOf K lo = gChainOf K pc := hinj.1
      have hpclo : pc = lo := by
        have hs1 := gChainOf_sum inv h3
        have hs2 := gChainOf_sum inv hlo
        rw [← hpceq] at hs1
        exact hs1.symm.trans hs2
      rw [hasRChild_iff]
      exact ⟨c, hcK, e0, π, by rw [hcop, hpclo]⟩

/-- **Geometry, L mint**: when the anchor HAS an R-child, its successor
IS an R-descendant of it, the argmax lands in the R-subtree, by
convexity. -/
theorem succ_R_descendant {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) {a n : ℕ}
    (ha : a = 0 ∨ a ∈ gMintedIds K)
    (hR : hasRChild K a = true)
    (hsucc : succOf Γ K a = some n) :
    ∃ d rest, gChainOf K n = gChainOf K a ++ (Side.R, d) :: rest := by
  have hn : n ∈ gMintedIds K := succOf_mem hsucc
  obtain ⟨c, hcK, e0, π, hcop⟩ := hasRChild_iff.mp hR
  have hcins : sIsIns c.op = true := by
    unfold sIsIns
    rw [hcop]
  obtain ⟨-, -, -, h4⟩ := inv.linkR c hcK e0 π a hcop
  have hcts : c.op.1 ∈ gMintedIds K :=
    List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hcK, hcins⟩, rfl⟩
  have hcchain : gChainOf K c.op.1 = c.chain :=
    gChainOf_of_mem inv hcK hcins
  have hxa : keyLt (gKey Γ K c.op.1) (gKey Γ K a) = true := by
    apply gKey_lt_of_chainBefore inv ha (Or.inr hcts)
    rw [hcchain, h4]
    exact schainBefore.extR _ _ _
  have hkeys : (c.op.1, gKey Γ K c.op.1) ∈ gKeys Γ K := by
    refine List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hcK, hcins⟩, ?_⟩
    show (c.op.1, sKey (sidedCoordOf Γ c.chain)) = (c.op.1, gKey Γ K c.op.1)
    unfold gKey
    rw [hcchain]
  have hccand : (c.op.1, gKey Γ K c.op.1) ∈ succCand Γ K a := by
    unfold succCand
    by_cases h0 : a = 0
    · rw [if_pos h0]
      exact hkeys
    · rw [if_neg h0]
      exact List.mem_filter.mpr ⟨hkeys, by simpa using hxa⟩
  have hnb : keyLt (gKey Γ K n) (gKey Γ K c.op.1) = false :=
    succOf_max inv hsucc hccand
  rcases ha with rfl | ham
  · -- anchor = start: every minted chain is R-headed
    obtain ⟨gn, hnfind, hnK, hnins, hnts⟩ := gRecOfId_of_minted hn
    obtain ⟨d, rest, hhead⟩ := chain_head_R inv gn.chain.length gn
      hnK hnins (Nat.le_refl _)
    refine ⟨d, rest, ?_⟩
    rw [gChainOf_zero inv.pos, gChainOf_eq_of_rec hnfind, hhead]
    rfl
  · by_cases hkeq : gKey Γ K n = gKey Γ K c.op.1
    · -- equal keys: unique decodability collapses n onto the R-child
      have hceq : gChainOf K n = gChainOf K c.op.1 := by
        apply sidedCoordOf_inj Γ (gChainOf_posOf inv (Or.inr hn))
          (gChainOf_posOf inv (Or.inr hcts))
        unfold gKey sKey at hkeq
        exact (List.append_inj' hkeq rfl).1
      refine ⟨c.op.1 - a, [], ?_⟩
      rw [hceq, hcchain, h4]
    · have hkn : keyLt (gKey Γ K c.op.1) (gKey Γ K n) = true := by
        rcases keyLt_total hkeq with h | h
        · rw [h] at hnb
          exact Bool.noConfusion hnb
        · exact h
      have ha0 : a ≠ 0 := by
        intro h0
        subst h0
        exact absurd (minted_pos inv ham) (by decide)
      have han : keyLt (gKey Γ K n) (gKey Γ K a) = true :=
        succOf_after_anchor inv hsucc ha0
      have hne_an : gChainOf K a ≠ gChainOf K n := by
        intro h
        unfold gKey at han
        rw [h, keyLt_irrefl] at han
        exact Bool.noConfusion han
      have hne_nc : gChainOf K n ≠ gChainOf K c.op.1 := by
        intro h
        unfold gKey at hkn
        rw [h, keyLt_irrefl] at hkn
        exact Bool.noConfusion hkn
      have hb_an : schainBefore (gChainOf K a) (gChainOf K n) :=
        chainBefore_of_gKey_lt inv (Or.inr ham) (Or.inr hn) hne_an han
      have hb_nc : schainBefore (gChainOf K n) (gChainOf K c.op.1) :=
        chainBefore_of_gKey_lt inv (Or.inr hn) (Or.inr hcts) hne_nc hkn
      obtain ⟨ez, hez⟩ := schain_subtree_convex (gChainOf K a)
        ⟨[], (List.append_nil _).symm⟩
        ⟨[(Side.R, c.op.1 - a)], by rw [hcchain, h4]⟩ hb_an hb_nc
      obtain ⟨d, rest, hext⟩ := schain_ext_after_is_R (hez ▸ hb_an)
      exact ⟨d, rest, by rw [hez, hext]⟩

/-- **The all-L successor shape** (the mint-step engine): the successor
of an anchor with an R-child extends the anchor by one R entry and L
entries only, if the rest held an R entry, the node just above it
(minted by ancestor closure) would beat the argmax. -/
theorem succ_R_desc_allL {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) {a n : ℕ}
    (ha : a = 0 ∨ a ∈ gMintedIds K)
    (hR : hasRChild K a = true)
    (hs : succOf Γ K a = some n) :
    ∃ d ls, gChainOf K n = gChainOf K a ++ (Side.R, d) :: ls ∧
      AllL ls := by
  obtain ⟨d, rest, hdec⟩ := succ_R_descendant inv ha hR hs
  refine ⟨d, rest, hdec, ?_⟩
  intro e he
  obtain ⟨sd, d'⟩ := e
  cases sd with
  | L => exact ⟨d', rfl⟩
  | R =>
      exfalso
      obtain ⟨u, v, huv⟩ := List.append_of_mem he
      -- the node just above the offending R entry
      have hm : ∃ pre e0, gChainOf K a ++ (Side.R, d) :: u
          = pre ++ [e0] := by
        rcases List.eq_nil_or_concat u with rfl | ⟨u', lst, rfl⟩
        · exact ⟨gChainOf K a, (Side.R, d), rfl⟩
        · exact ⟨gChainOf K a ++ (Side.R, d) :: u', lst, by simp⟩
      obtain ⟨pre, e0, hpre_eq⟩ := hm
      have hnm : n ∈ gMintedIds K := succOf_mem hs
      obtain ⟨gn, hnfind, hnK, hnins, hnts⟩ := gRecOfId_of_minted hnm
      have hgnchain : gChainOf K n = gn.chain :=
        gChainOf_eq_of_rec hnfind
      have hnfull : gn.chain
          = (gChainOf K a ++ (Side.R, d) :: u) ++ (Side.R, d') :: v := by
        rw [← hgnchain, hdec, huv]
        simp
      have hprefix : (pre ++ [e0]) <+: gn.chain := by
        rw [hnfull, ← hpre_eq]
        exact ⟨(Side.R, d') :: v, rfl⟩
      obtain ⟨h, hhK, hhins, hhchain⟩ := chain_prefix_minted inv
        gn.chain.length gn hnK hnins (Nat.le_refl _) pre e0 hprefix
      have hm_eq : h.chain = gChainOf K a ++ (Side.R, d) :: u := by
        rw [hhchain, ← hpre_eq]
      have hhts : h.op.1 ∈ gMintedIds K :=
        List.mem_map.mpr ⟨h, List.mem_filter.mpr ⟨hhK, hhins⟩, rfl⟩
      have hhchainof : gChainOf K h.op.1 = h.chain :=
        gChainOf_of_mem inv hhK hhins
      -- h displays after a, n displays before h
      have h_after_a : keyLt (gKey Γ K h.op.1) (gKey Γ K a) = true := by
        apply gKey_lt_of_chainBefore inv ha (Or.inr hhts)
        rw [hhchainof, hm_eq]
        exact schainBefore.extR _ _ _
      have h_n_before_h : keyLt (gKey Γ K n) (gKey Γ K h.op.1) = true := by
        apply gKey_lt_of_chainBefore inv (Or.inr hhts) (Or.inr hnm)
        rw [hhchainof, hm_eq, hgnchain, hnfull]
        exact schainBefore.extR _ _ _
      -- h is a successor candidate, so the argmax is not beaten by it
      have hkeys : (h.op.1, gKey Γ K h.op.1) ∈ gKeys Γ K := by
        refine List.mem_map.mpr ⟨h, List.mem_filter.mpr ⟨hhK, hhins⟩, ?_⟩
        show (h.op.1, sKey (sidedCoordOf Γ h.chain))
          = (h.op.1, gKey Γ K h.op.1)
        unfold gKey
        rw [hhchainof]
      have hcand : (h.op.1, gKey Γ K h.op.1) ∈ succCand Γ K a := by
        unfold succCand
        by_cases h0 : a = 0
        · rw [if_pos h0]
          exact hkeys
        · rw [if_neg h0]
          exact List.mem_filter.mpr ⟨hkeys, by simpa using h_after_a⟩
      have hnb := succOf_max inv hs hcand
      rw [h_n_before_h] at hnb
      exact Bool.noConfusion hnb

/-! ### The mint's own clauses -/

theorem fugueChoose_none {Γ : OrderedPrefixCode} {K : Know} {a : ℕ}
    (hs : succOf Γ K a = none) : fugueChoose Γ K a = (Side.R, a) := by
  unfold fugueChoose
  rw [hs]

theorem fugueChoose_someTrue {Γ : OrderedPrefixCode} {K : Know} {a n : ℕ}
    (hs : succOf Γ K a = some n) (hR : hasRChild K a = true) :
    fugueChoose Γ K a = (Side.L, n) := by
  unfold fugueChoose
  rw [hs, hR]
  simp

theorem fugueChoose_someFalse {Γ : OrderedPrefixCode} {K : Know} {a n : ℕ}
    (hs : succOf Γ K a = some n) (hR : hasRChild K a = false) :
    fugueChoose Γ K a = (Side.R, a) := by
  unfold fugueChoose
  rw [hs, hR]
  simp

/-- The branch equation for the mint, packaged so the goals never force
deep `whnf` through the policy functions. -/
theorem genInsAfter_eq {Γ : OrderedPrefixCode} {K : Know} {a : ℕ}
    {sd : Side} {p0 : ℕ} (hc : fugueChoose Γ K a = (sd, p0))
    (rep : Replica) (x : ℕ) :
    genInsAfter Γ K rep x a =
      { op := (x, rep, SOp.ins x (sidedCoordOf Γ (gChainOf K p0)) p0 sd)
        lo := a
        ro := succOf Γ K a
        chain := gChainOf K p0 ++ [(sd, x - p0)] } := by
  unfold genInsAfter
  rw [hc]

/-- The freshly generated insert satisfies every clause of the bundle,
over the mint knowledge, including the all-L successor shape. -/
theorem genInsAfter_props (Γ : OrderedPrefixCode) {K : Know}
    (inv : FInv Γ K) (rep : Replica) {x a : ℕ} (hx : 0 < x)
    (hlam : ∀ m ∈ gMintedIds K, m < x)
    (ha : a = 0 ∨ a ∈ gMintedIds K) :
    (genInsAfter Γ K rep x a).op.1 = x ∧
    sIsIns (genInsAfter Γ K rep x a).op = true ∧
    LinkR Γ K (genInsAfter Γ K rep x a) ∧
    LinkL Γ K (genInsAfter Γ K rep x a) ∧
    SLC Γ K (genInsAfter Γ K rep x a) := by
  have halt : a < x := by
    rcases ha with rfl | h
    · exact hx
    · exact hlam a h
  rcases hs : succOf Γ K a with _ | n
  · -- no successor: R mint of the anchor
    rw [genInsAfter_eq (fugueChoose_none hs) rep x]
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · intro e π p hop
      injection hop with h1 h2 h3 h4
      subst h3
      exact ⟨rfl, halt, ha, rfl⟩
    · intro e π p hop
      injection hop with h1 h2 h3 h4
      exact Side.noConfusion h4
    · intro e π p hop
      injection hop with h1 h2 h3 h4
      exact Side.noConfusion h4
  · have hnm : n ∈ gMintedIds K := succOf_mem hs
    have hnlt : n < x := hlam n hnm
    cases hR : hasRChild K a with
    | true =>
        -- L mint of the successor
        rw [genInsAfter_eq (fugueChoose_someTrue hs hR) rep x]
        refine ⟨rfl, rfl, ?_, ?_, ?_⟩
        · intro e π p hop
          injection hop with h1 h2 h3 h4
          exact Side.noConfusion h4
        · intro e π p hop
          injection hop with h1 h2 h3 h4
          subst h3
          exact ⟨hs, hnlt, hnm, rfl, ha⟩
        · intro e π p hop
          injection hop with h1 h2 h3 h4
          subst h3
          obtain ⟨d, ls, hdec, hall⟩ := succ_R_desc_allL inv ha hR hs
          exact ⟨d, ls, hdec, hall⟩
    | false =>
        -- R mint of the anchor (the successor only feeds `ro`)
        rw [genInsAfter_eq (fugueChoose_someFalse hs hR) rep x]
        refine ⟨rfl, rfl, ?_, ?_, ?_⟩
        · intro e π p hop
          injection hop with h1 h2 h3 h4
          subst h3
          exact ⟨rfl, halt, ha, rfl⟩
        · intro e π p hop
          injection hop with h1 h2 h3 h4
          exact Side.noConfusion h4
        · intro e π p hop
          injection hop with h1 h2 h3 h4
          exact Side.noConfusion h4

/-! ### Per-step preservation -/

/-- Appending a fresh wellformed insert preserves the link bundle. -/
theorem linkInv_snoc_ins {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) (lk : LinkInv Γ K) {g : GRec}
    (hts : 1 ≤ g.op.1)
    (hR : LinkR Γ K g) (hL : LinkL Γ K g) (hS : SLC Γ K g) :
    LinkInv Γ (K ++ [g]) := by
  have hpos1 : ∀ h ∈ [g], 1 ≤ h.op.1 := by
    intro h hh
    rw [List.mem_singleton] at hh
    subst hh
    exact hts
  have hchain : ∀ y, y = 0 ∨ y ∈ gMintedIds K →
      gChainOf (K ++ [g]) y = gChainOf K y :=
    fun y hy => gChainOf_append_stable hy inv.pos hpos1
  have hmem : ∀ y, y ∈ gMintedIds K → y ∈ gMintedIds (K ++ [g]) := by
    intro y hy
    rw [gMintedIds_append]
    exact List.mem_append_left _ hy
  intro g1 hg1
  rcases List.mem_append.mp hg1 with h1 | h1
  · obtain ⟨hr, hl, hs⟩ := lk g1 h1
    exact ⟨linkR_transport hr hchain hmem,
      linkL_transport hl hchain hmem, slc_transport hs hl hchain⟩
  · rw [List.mem_singleton] at h1
    subst h1
    exact ⟨linkR_transport hR hchain hmem,
      linkL_transport hL hchain hmem, slc_transport hS hL hchain⟩

/-- Appending a delete preserves the link bundle (its clauses are
vacuous on the delete record). -/
theorem linkInv_snoc_del {Γ : OrderedPrefixCode} {K : Know}
    (lk : LinkInv Γ K) {g : GRec} (hnotins : sIsIns g.op = false) :
    LinkInv Γ (K ++ [g]) := by
  have hchain : ∀ y, y = 0 ∨ y ∈ gMintedIds K →
      gChainOf (K ++ [g]) y = gChainOf K y :=
    fun y _ => gChainOf_snoc_del hnotins y
  have hmem : ∀ y, y ∈ gMintedIds K → y ∈ gMintedIds (K ++ [g]) := by
    intro y hy
    rw [gMintedIds_snoc_del hnotins]
    exact hy
  intro g1 hg1
  rcases List.mem_append.mp hg1 with h1 | h1
  · obtain ⟨hr, hl, hs⟩ := lk g1 h1
    exact ⟨linkR_transport hr hchain hmem,
      linkL_transport hl hchain hmem, slc_transport hs hl hchain⟩
  · rw [List.mem_singleton] at h1
    subst h1
    have hbad : ∀ {e : ℕ} {π : List ℕ} {p : ℕ} {sd : Side},
        g1.op.2.2 = SOp.ins e π p sd → False := by
      intro e π p sd hop
      have hins : sIsIns g1.op = true := by
        unfold sIsIns
        rw [hop]
      rw [hnotins] at hins
      exact Bool.noConfusion hins
    exact ⟨fun e π p hop => (hbad hop).elim,
      fun e π p hop => (hbad hop).elim,
      fun e π p hop => (hbad hop).elim⟩

/-- Pairwise sync preserves the link bundle (the Fugue file's global
`GInv` supplies the cross-replica uniqueness that the right-side chain
agreement needs). -/
theorem linkInv_sync {Γ : OrderedPrefixCode} {G : ℕ → Know}
    (inv : GInv Γ G) (r r' : ℕ)
    (lkL : LinkInv Γ (G r)) (lkR : LinkInv Γ (G r')) :
    LinkInv Γ (syncK (G r) (G r')) := by
  have hposU : ∀ g ∈ syncK (G r) (G r'), 1 ≤ g.op.1 := by
    intro g hg
    rcases mem_syncK hg with h | h
    · exact inv.pos r g h
    · exact inv.pos r' g h
  have hchainL : ∀ y, y = 0 ∨ y ∈ gMintedIds (G r) →
      gChainOf (syncK (G r) (G r')) y = gChainOf (G r) y := by
    intro y hy
    exact gChainOf_append_stable hy (inv.pos r)
      (fun g hg => inv.pos r' g (List.mem_of_mem_filter hg))
  have hmemL : ∀ y, y ∈ gMintedIds (G r) →
      y ∈ gMintedIds (syncK (G r) (G r')) := by
    intro y hy
    rw [show syncK (G r) (G r')
      = G r ++ (G r').filter (fun g => decide (g ∉ G r)) from rfl,
      gMintedIds_append]
    exact List.mem_append_left _ hy
  have hchainR : ∀ y, y = 0 ∨ y ∈ gMintedIds (G r') →
      gChainOf (syncK (G r) (G r')) y = gChainOf (G r') y := by
    intro y hy
    rcases hy with rfl | hy
    · rw [gChainOf_zero hposU, gChainOf_zero (inv.pos r')]
    · exact gChainOf_agree
        (by
          intro g hg g' hg' hi hi' hteq
          rcases mem_syncK hg with h | h
          · exact inv.uniq r r' g h g' hg' hi hi' hteq
          · exact inv.uniq r' r' g h g' hg' hi hi' hteq)
        (minted_syncK_right hy) hy
  have hmemR : ∀ y, y ∈ gMintedIds (G r') →
      y ∈ gMintedIds (syncK (G r) (G r')) :=
    fun y hy => minted_syncK_right hy
  intro g hg
  rcases mem_syncK hg with h | h
  · obtain ⟨hr, hl, hs⟩ := lkL g h
    exact ⟨linkR_transport hr hchainL hmemL,
      linkL_transport hl hchainL hmemL, slc_transport hs hl hchainL⟩
  · obtain ⟨hr, hl, hs⟩ := lkR g h
    exact ⟨linkR_transport hr hchainR hmemR,
      linkL_transport hl hchainR hmemR, slc_transport hs hl hchainR⟩

/-- **The external link invariant holds at every replica of every
reachable configuration**, threaded through inserts, deletes, and
syncs. -/
theorem fugueReach_links (Γ : OrderedPrefixCode) {G : ℕ → Know}
    (h : FugueReach Γ G) : ∀ q, LinkInv Γ (G q) := by
  induction h with
  | init =>
      intro q g hg
      exact absurd hg (by simp)
  | @ins G r x i hG hx hfresh hlam ih =>
      have ginv := fugueReach_inv Γ hG
      have finv : FInv Γ (G r) := fInv_mk ginv r (ih r)
      have ha : anchorAt Γ (G r) i = 0 ∨
          anchorAt Γ (G r) i ∈ gMintedIds (G r) := by
        rcases anchorAt_cases Γ (G r) i with h0 | hv
        · exact Or.inl h0
        · exact Or.inr (gView_sub_minted Γ (G r) _ hv)
      obtain ⟨hts, hins, hlkR, hlkL, hlkS⟩ :=
        genInsAfter_props Γ finv r hx hlam ha
      intro q
      by_cases hq : q = r
      · subst hq
        rw [Function.update_self]
        exact linkInv_snoc_ins finv (ih q)
          (by rw [show (genInsAt Γ (G q) q x i).op.1 = x from hts]
              exact hx)
          hlkR hlkL hlkS
      · rw [Function.update_of_ne hq]
        exact ih q
  | @del G r t i hG ht hfresh ih =>
      intro q
      by_cases hq : q = r
      · subst hq
        rw [Function.update_self]
        exact linkInv_snoc_del (ih q) rfl
      · rw [Function.update_of_ne hq]
        exact ih q
  | @sync G r r' hG ih =>
      have ginv := fugueReach_inv Γ hG
      intro q
      by_cases hq : q = r
      · subst hq
        rw [Function.update_self]
        exact linkInv_sync ginv q r' (ih q) (ih r')
      · rw [Function.update_of_ne hq]
        exact ih q

#print axioms fugueReach_links

/-! ## §3  loShape, the first-after descent, the discharge -/

theorem gLoOf_eq {K : Know} {x : ℕ} {g : GRec}
    (hfind : gRecOfId K x = some g) : gLoOf K x = g.lo := by
  simp [gLoOf, hfind]

/-- **loShape** (the paper's Lemma 8(a) in chain form): every minted
element's chain is its recorded left origin's chain, one R entry, then L
entries only. -/
theorem loShape_of_inv {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) (inv2 : ∀ g ∈ K, SLC Γ K g)
    {x : ℕ} (hx : x ∈ gMintedIds K) :
    (gLoOf K x = 0 ∨ gLoOf K x ∈ gMintedIds K) ∧
    ∃ d ls, gChainOf K x
        = gChainOf K (gLoOf K x) ++ (Side.R, d) :: ls ∧ AllL ls := by
  obtain ⟨g, hfind, hgK, hgins, hgts⟩ := gRecOfId_of_minted hx
  have hlo := gLoOf_eq hfind
  have hcx : gChainOf K x = g.chain := gChainOf_eq_of_rec hfind
  obtain ⟨e0, π, p, sd, hop⟩ := gIsIns_shape hgins
  cases sd with
  | R =>
      obtain ⟨h1, h2, h3, h4⟩ := inv.linkR g hgK e0 π p hop
      refine ⟨by rw [hlo, ← h1]; exact h3, g.op.1 - p, [], ?_, ?_⟩
      · rw [hcx, h4, hlo, ← h1]
      · intro e he
        exact absurd he (by simp)
  | L =>
      obtain ⟨d, ls, hdec, hall⟩ := inv2 g hgK e0 π p hop
      obtain ⟨h1, h2, h3, h4, h5⟩ := inv.linkL g hgK e0 π p hop
      refine ⟨by rw [hlo]; exact h5,
        d, ls ++ [(Side.L, g.op.1 - p)], ?_, ?_⟩
      · rw [hcx, h4, hdec, hlo]
        simp
      · intro e he
        rcases List.mem_append.mp he with h | h
        · exact hall e h
        · rw [List.mem_singleton] at h
          exact ⟨_, h⟩

/-- **The first-after descent**: any minted `c` sitting R-headedly below
`A` has, on its left-origin walk, a minted element with recorded left
origin exactly `A` displaying no later than `c`. Strong induction on
chain length; the loShape decompositions collide with the all-L tails at
every misalignment. -/
theorem lo_child_before {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) (inv2 : ∀ g ∈ K, SLC Γ K g) :
    ∀ (N c : ℕ), c ∈ gMintedIds K → (gChainOf K c).length ≤ N →
    ∀ A : ℕ, (A = 0 ∨ A ∈ gMintedIds K) →
    (∃ d ext, gChainOf K c = gChainOf K A ++ (Side.R, d) :: ext) →
    ∃ D ∈ gMintedIds K, gLoOf K D = A ∧
      (D = c ∨ keyLt (gKey Γ K c) (gKey Γ K D) = true) := by
  intro N
  induction N with
  | zero =>
      intro c hc hlen A hA hext
      exfalso
      obtain ⟨d, ext, hext⟩ := hext
      have := congrArg List.length hext
      simp at this
      omega
  | succ N ih =>
      intro c hc hlen A hA hext
      obtain ⟨d, ext, hext⟩ := hext
      obtain ⟨hloOr, d', ls', hdec, hall⟩ := loShape_of_inv inv inv2 hc
      have p1 : gChainOf K A <+: gChainOf K c :=
        ⟨(Side.R, d) :: ext, hext.symm⟩
      have p2 : gChainOf K (gLoOf K c) <+: gChainOf K c :=
        ⟨(Side.R, d') :: ls', hdec.symm⟩
      rcases List.prefix_or_prefix_of_prefix p2 p1 with hpre | hpre
      · -- chain(lo c) a prefix of chain(A)
        obtain ⟨u, hu⟩ := hpre
        cases u with
        | nil =>
            rw [List.append_nil] at hu
            have hAeq : gLoOf K c = A := by
              have s1 := gChainOf_sum inv hloOr
              have s2 := gChainOf_sum inv hA
              rw [hu] at s1
              exact s1.symm.trans s2
            exact ⟨c, hc, hAeq, Or.inl rfl⟩
        | cons e u' =>
            -- misalignment: A's R entry lands inside the all-L tail
            exfalso
            have hcc : gChainOf K (gLoOf K c) ++ (Side.R, d') :: ls'
                = gChainOf K (gLoOf K c)
                  ++ (e :: u') ++ (Side.R, d) :: ext := by
              rw [← hdec, hext, ← hu]
            rw [List.append_assoc] at hcc
            have hcc' := List.append_cancel_left hcc
            rw [List.cons_append] at hcc'
            injection hcc' with h1 h2
            have hmem : (Side.R, d) ∈ ls' := by
              rw [h2]
              exact List.mem_append_right _ List.mem_cons_self
            obtain ⟨dd, hL⟩ := hall _ hmem
            have h6 : Side.R = Side.L := congrArg Prod.fst hL
            exact Side.noConfusion h6
      · -- chain(A) a prefix of chain(lo c)
        obtain ⟨v, hv⟩ := hpre
        cases v with
        | nil =>
            rw [List.append_nil] at hv
            have hAeq : gLoOf K c = A := by
              have s1 := gChainOf_sum inv hloOr
              have s2 := gChainOf_sum inv hA
              rw [← hv] at s1
              exact s1.symm.trans s2
            exact ⟨c, hc, hAeq, Or.inl rfl⟩
        | cons e v' =>
            -- chain(lo c) strictly extends chain(A), R-headedly: recurse
            have hcc : gChainOf K A ++ (Side.R, d) :: ext
                = gChainOf K A ++ (e :: v') ++ (Side.R, d') :: ls' := by
              rw [← hext, hdec, ← hv]
            rw [List.append_assoc] at hcc
            have hcc' := List.append_cancel_left hcc
            rw [List.cons_append] at hcc'
            injection hcc' with h1 h2
            have hlomint : gLoOf K c ∈ gMintedIds K := by
              rcases hloOr with h0 | h
              · exfalso
                rw [h0, gChainOf_zero inv.pos] at hv
                have := congrArg List.length hv
                simp at this
              · exact h
            have hlolen : (gChainOf K (gLoOf K c)).length ≤ N := by
              have := congrArg List.length hdec
              simp at this
              omega
            obtain ⟨D, hD, hDlo, hor⟩ := ih (gLoOf K c) hlomint hlolen
              A hA ⟨d, v', by rw [← hv, ← h1]⟩
            -- lo c displays before c
            have hbefore : keyLt (gKey Γ K c) (gKey Γ K (gLoOf K c))
                = true := by
              apply gKey_lt_of_chainBefore inv hloOr (Or.inr hc)
              rw [hdec]
              exact schainBefore.extR _ _ _
            refine ⟨D, hD, hDlo, Or.inr ?_⟩
            rcases hor with rfl | hlt
            · exact hbefore
            · exact keyLt_trans hbefore hlt

/-- **Condition (1) from the invariant bundles**: loShape places B in
A's R-subtree; convexity traps any live in-between element there too;
the descent produces an element with left origin A displaying strictly
before B, against B's minimality. -/
theorem forwardNI_of_inv {Γ : OrderedPrefixCode} {K : Know}
    (inv : FInv Γ K) (inv2 : ∀ g ∈ K, SLC Γ K g) :
    ForwardNI Γ K := by
  intro A hA B hB hliveA hliveB hloB hmin
  obtain ⟨hloOrB, d, ls, hdecB, hallB⟩ := loShape_of_inv inv inv2 hB
  rw [hloB] at hdecB
  have hAB : gBefore Γ K A B := by
    show keyLt (gKey Γ K B) (gKey Γ K A) = true
    apply gKey_lt_of_chainBefore inv (Or.inr hA) (Or.inr hB)
    rw [hdecB]
    exact schainBefore.extR _ _ _
  refine ⟨hAB, ?_⟩
  rintro c hlivec ⟨hAc, hcB⟩
  have hcm : c ∈ gMintedIds K := gView_sub_minted Γ K c hlivec
  -- chain-level order facts
  have hneAc : gChainOf K A ≠ gChainOf K c := by
    intro he
    have hAc' : keyLt (gKey Γ K c) (gKey Γ K A) = true := hAc
    unfold gKey at hAc'
    rw [he, keyLt_irrefl] at hAc'
    exact Bool.noConfusion hAc'
  have hnecB : gChainOf K c ≠ gChainOf K B := by
    intro he
    have hcB' : keyLt (gKey Γ K B) (gKey Γ K c) = true := hcB
    unfold gKey at hcB'
    rw [he, keyLt_irrefl] at hcB'
    exact Bool.noConfusion hcB'
  have hbAc : schainBefore (gChainOf K A) (gChainOf K c) :=
    chainBefore_of_gKey_lt inv (Or.inr hA) (Or.inr hcm) hneAc hAc
  have hbcB : schainBefore (gChainOf K c) (gChainOf K B) :=
    chainBefore_of_gKey_lt inv (Or.inr hcm) (Or.inr hB) hnecB hcB
  -- convexity: c is in A's subtree, R-headedly
  obtain ⟨ec, hec⟩ := schain_subtree_convex (gChainOf K A)
    ⟨[], (List.append_nil _).symm⟩ ⟨(Side.R, d) :: ls, hdecB⟩ hbAc hbcB
  obtain ⟨d', rest', hecR⟩ :=
    schain_ext_after_is_R (p := gChainOf K A) (ext := ec)
      (by rw [← hec]; exact hbAc)
  -- the descent
  obtain ⟨D, hD, hDlo, hor⟩ := lo_child_before inv inv2
    (gChainOf K c).length c hcm (Nat.le_refl _) A (Or.inr hA)
    ⟨d', rest', by rw [hec, hecR]⟩
  -- close the cycle against B's minimality
  have hDB : D ≠ B := by
    rintro rfl
    have h0 : keyLt (gKey Γ K D) (gKey Γ K c) = true := hcB
    rcases hor with heq | hlt
    · rw [heq, keyLt_irrefl] at h0
      exact Bool.noConfusion h0
    · have h1 := keyLt_trans hlt h0
      rw [keyLt_irrefl] at h1
      exact Bool.noConfusion h1
  have hmin' : keyLt (gKey Γ K D) (gKey Γ K B) = true :=
    hmin D hD hDlo hDB
  have hcB' : keyLt (gKey Γ K B) (gKey Γ K c) = true := hcB
  have h1 : keyLt (gKey Γ K D) (gKey Γ K c) = true :=
    keyLt_trans hmin' hcB'
  rcases hor with heq | hlt
  · rw [← heq, keyLt_irrefl] at h1
    exact Bool.noConfusion h1
  · have h2 := keyLt_trans h1 hlt
    rw [keyLt_irrefl] at h2
    exact Bool.noConfusion h2

end FugueFwd

/-- **The stated def is DISCHARGED**: forward non-interleaving
(Weidner-Kleppmann Definition 4 condition (1), strict reading) holds at
every replica of every reachable configuration of the Fugue policy on
the plain sided kernel. -/
theorem fugue_forward_ni (Γ : OrderedPrefixCode) :
    FugueForwardNonInterleaving Γ := by
  intro G hG r
  have lk := FugueFwd.fugueReach_links Γ hG
  exact FugueFwd.forwardNI_of_inv
    (FugueFwd.fInv_mk (fugueReach_inv Γ hG) r (lk r))
    (fun g hg => (lk r g hg).2.2)

#print axioms fugue_forward_ni

/-! ## §4  SPOTs (PASS+FAIL, hand-derived)

The loShape invariant and the condition-(1) adjacency watched concretely
on the Fugue file's own traces: `KFig` (the Figure-7 execution; display
`[5, 7, 6, 4, 3]`) and `FugueSPOT.k19` (the two concurrent backward
runs). Expected values are hand-derived from the chains (7 = R-child of
5 with delta 2, 6 = R-child of 5 with delta 1, 50 = L-descendant of the
start child 1), never `#eval`'d from the implementation. -/

namespace FugueFwdSPOT

/-- Bool form of "R-headed" for concrete chains. -/
def isRHeadB : Sal.EmbedRGA.SChain → Bool
  | (Side.R, _) :: _ => true
  | _ => false

/-- Bool form of `FugueFwd.AllL` for concrete chains. -/
def allLB (ls : Sal.EmbedRGA.SChain) : Bool :=
  ls.all fun e => match e with | (Side.L, _) => true | _ => false

/-- The loShape extension of x over its recorded left origin. -/
def loExt (K : Know) (x : ℕ) : Sal.EmbedRGA.SChain :=
  (gChainOf K x).drop (gChainOf K (gLoOf K x)).length

/-- PASS: on Figure 7, both concurrent inserts after A = 5 record left
origin 5 (X = 6 and Y = 7). -/
theorem fig7_lo_7 : gLoOf KFig 7 = 5 := by native_decide
theorem fig7_lo_6 : gLoOf KFig 6 = 5 := by native_decide

/-- FAIL pin: Y = 7's left origin is NOT its right origin B = 4 (the
`lo` field records the intent anchor, not the mint-time successor). -/
theorem fig7_lo_7_not_ro : gLoOf KFig 7 ≠ 4 := by native_decide

/-- PASS: loShape on Figure 7, entry by entry: 7 extends 5's chain by
one R entry and nothing else; the prefix really is 5's chain. -/
theorem fig7_loshape_7 :
    ((gChainOf KFig 5).isPrefixOf (gChainOf KFig 7)
      && isRHeadB (loExt KFig 7)
      && allLB ((loExt KFig 7).drop 1)) = true := by
  native_decide

/-- PASS: loShape on the L19 backward run: 50 is an L-mint (left origin
start), so its extension over start is one R entry then L entries. -/
theorem l19_loshape_50 :
    (gLoOf FugueSPOT.k19 50 = 0
      ∧ isRHeadB (loExt FugueSPOT.k19 50) = true
      ∧ allLB ((loExt FugueSPOT.k19 50).drop 1) = true) := by
  native_decide

/-- FAIL pin: 50's left origin is NOT its parent 30 (the chain walks up
through L entries; the recorded `lo` is the intent anchor, start). -/
theorem l19_lo_50_not_parent : gLoOf FugueSPOT.k19 50 ≠ 30 := by
  native_decide

/-- FAIL pin: the extension of 50 is NOT all-R (its tail is L entries;
the walk-up rule has something to strip). -/
theorem l19_ext_50_not_allR :
    ¬ ((loExt FugueSPOT.k19 50).all
        (fun e => isRHeadB [e]) = true) := by native_decide

/-- PASS: the condition-(1) adjacency on Figure 7: A = 5 and its
display-first left-origin child B = 7 (the recency policy's pick) are
consecutive in the view. -/
theorem fig7_forward_adjacent :
    (gView unaryCode KFig).take 2 = [5, 7] := by native_decide

/-- FAIL pin: the FugueMax rival verdict, 6 seated next to 5, is NOT
what the recency policy displays. -/
theorem fig7_not_fuguemax_adjacent :
    (gView unaryCode KFig).take 2 ≠ [5, 6] := by native_decide

end FugueFwdSPOT

#print axioms FugueFwdSPOT.fig7_loshape_7
#print axioms FugueFwdSPOT.fig7_forward_adjacent

end Sal.ConditionedMRDTs
