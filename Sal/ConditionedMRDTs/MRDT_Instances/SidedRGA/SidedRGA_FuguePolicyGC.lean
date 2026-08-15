import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_Fugue_ForwardNI

/-!
# Fugue mint-policy collection: live state is insufficient

The runtime migration needs a collectable issuer summary for Fugue's
generation-time `fugueChoose`. This file pins the first design boundary:
projecting knowledge to the live sided-RGA fold loses information needed by a
later mint.

The two worlds below have the same live state. One world has only the live
anchor `1`. The other minted its right child `2` and then deleted it. Fugue
chooses `(R, 1)` after the anchor in the first world, but the tombstone-visible
policy tree makes it choose `(L, 2)` in the second.
-/

namespace Sal.ConditionedMRDTs.FuguePolicyGC

open Sal.EmbedRGA (Side SChain unaryCode schainBefore keyLt keyLt_irrefl
  sKey sidedCoordOf)
open Sal.ConditionedMRDTs

abbrev Γ := unaryCode

/-- World A: one live anchor. -/
def onlyAnchor : Know := FugueSPOT.gIns [] 0 1 0

/-- World B before deletion: the anchor and its right child. -/
def withRightChild : Know := FugueSPOT.gIns onlyAnchor 0 2 1

/-- World B after deleting the right child at visible index 1. -/
def deadRightChild : Know :=
  withRightChild ++ [genDelAt Γ withRightChild 0 3 1]

/-- PASS: deletion makes the live sided-RGA states identical. -/
theorem live_projection_equal :
    gFold Γ onlyAnchor = gFold Γ deadRightChild := by native_decide

/-- PASS: the simpler world chooses a new right child of the anchor. -/
theorem choose_without_dead_child :
    fugueChoose Γ onlyAnchor 1 = (Side.R, 1) := by native_decide

/-- PASS: the dead right child remains the tombstone-visible successor, so
the same user intent chooses a left child of that dead node. -/
theorem choose_with_dead_child :
    fugueChoose Γ deadRightChild 1 = (Side.L, 2) := by native_decide

/-- FAIL companion for live-state sufficiency: equal live folds do not imply
equal Fugue mint decisions. -/
theorem live_projection_does_not_determine_choose :
    gFold Γ onlyAnchor = gFold Γ deadRightChild ∧
    fugueChoose Γ onlyAnchor 1 ≠ fugueChoose Γ deadRightChild 1 := by
  exact ⟨live_projection_equal, by native_decide⟩

/-! ## A sufficient but unbounded summary

Delete records do not affect `fugueChoose`. Keeping every insert record is
therefore sufficient, but it retains one policy record per inserted element.
The counterexample above shows that filtering this summary to live inserts is
not sufficient.
-/

/-- Drop delete events but retain every minted insert and its chain/origins. -/
def fullMintSummary (K : Know) : Know := gMinted K

theorem gMinted_idem (K : Know) :
    gMinted (gMinted K) = gMinted K := by
  simp only [gMinted, List.filter_filter]
  apply List.filter_congr
  intro g hg
  simp

theorem gRecOfId_fullMintSummary (K : Know) (x : ℕ) :
    gRecOfId (fullMintSummary K) x = gRecOfId K x := by
  simp [gRecOfId, fullMintSummary, gMinted_idem]

theorem gChainOf_fullMintSummary (K : Know) (x : ℕ) :
    gChainOf (fullMintSummary K) x = gChainOf K x := by
  simp [gChainOf, gRecOfId_fullMintSummary]

theorem gKeys_fullMintSummary (K : Know) :
    gKeys Γ (fullMintSummary K) = gKeys Γ K := by
  simp [gKeys, fullMintSummary, gMinted_idem]

theorem hasRChild_fullMintSummary (K : Know) (a : ℕ) :
    hasRChild (fullMintSummary K) a = hasRChild K a := by
  induction K with
  | nil => rfl
  | cons g K ih =>
      rcases g with ⟨⟨t, r, op⟩, lo, ro, chain⟩
      cases op with
      | ins x p sd side =>
          change (gAnchorR a ⟨(t, r, SOp.ins x p sd side), lo, ro, chain⟩ ||
              hasRChild (fullMintSummary K) a) =
            (gAnchorR a ⟨(t, r, SOp.ins x p sd side), lo, ro, chain⟩ ||
              hasRChild K a)
          rw [ih]
      | del x =>
          change hasRChild (fullMintSummary K) a =
            (false || hasRChild K a)
          simpa using ih

theorem succOf_fullMintSummary (K : Know) (a : ℕ) :
    succOf Γ (fullMintSummary K) a = succOf Γ K a := by
  simp [succOf, succCand, gKeys_fullMintSummary, gChainOf_fullMintSummary,
    gKey]

/-- Machine-checked upper bound: all minted inserts, without delete events,
preserve every future Fugue choice. This summary is not bounded. -/
theorem fullMintSummary_preserves_choose (K : Know) (a : ℕ) :
    fugueChoose Γ (fullMintSummary K) a = fugueChoose Γ K a := by
  simp [fugueChoose, succOf_fullMintSummary, hasRChild_fullMintSummary]

/-! ## The finite information consumed at one live gap

The policy does not consume the whole tree when minting at a particular live
anchor.  It consumes the anchor chain, one monotone bit, and at most one
successor id and chain.  `LiveGap` makes that boundary explicit.  A runtime
may keep one such record for start and for every live anchor, sharing the
chains between records.
-/

structure LiveGap where
  anchorChain : SChain
  hasR : Bool
  succ : Option ℕ
  succChain : Option SChain

@[ext] theorem LiveGap.ext {g h : LiveGap}
    (hanchor : g.anchorChain = h.anchorChain)
    (hR : g.hasR = h.hasR) (hsucc : g.succ = h.succ)
    (hchain : g.succChain = h.succChain) : g = h := by
  cases g
  cases h
  simp_all

def liveGapOf (K : Know) (a : ℕ) : LiveGap where
  anchorChain := gChainOf K a
  hasR := hasRChild K a
  succ := succOf Γ K a
  succChain := (succOf Γ K a).map (gChainOf K)

def liveGapChoose (g : LiveGap) (a : ℕ) : Side × ℕ :=
  match g.succ with
  | some n => if g.hasR then (Side.L, n) else (Side.R, a)
  | none => (Side.R, a)

def liveGapParentChain (g : LiveGap) : SChain :=
  match g.succ with
  | some _ => if g.hasR then g.succChain.getD [] else g.anchorChain
  | none => g.anchorChain

/-- The per-gap summary makes exactly the same side/parent decision as the
full tombstone-visible Fugue policy tree. -/
theorem liveGapChoose_exact (K : Know) (a : ℕ) :
    liveGapChoose (liveGapOf K a) a = fugueChoose Γ K a := by
  rfl

/-- It also retains exactly the parent chain needed to mint the coordinate.
This is the complete generation-time observation used by `genInsAfter`. -/
theorem liveGapParentChain_exact (K : Know) (a : ℕ) :
    liveGapParentChain (liveGapOf K a) =
      gChainOf K (fugueChoose Γ K a).2 := by
  simp only [liveGapParentChain, liveGapOf, fugueChoose]
  cases hsucc : succOf Γ K a with
  | none => simp [hsucc]
  | some n =>
      cases hr : hasRChild K a <;> simp [hsucc, hr]

/-! Delete transitions are already fully congruent. A delete changes the live
fold but contributes no policy information, so every surviving gap fact is
literally unchanged. -/

def policyDelete (t : Emulation.Timestamp) (rep : Emulation.Replica)
    (x : ℕ) : GRec where
  op := (t, rep, SOp.del x)
  lo := 0
  ro := none
  chain := []

theorem fullMintSummary_append_delete (K : Know) (t : Emulation.Timestamp)
    (rep : Emulation.Replica) (x : ℕ) :
    fullMintSummary (K ++ [policyDelete t rep x]) = fullMintSummary K := by
  simp [fullMintSummary, gMinted, policyDelete, sIsIns]

/-- Exact delete-transition congruence for every anchor retained by the
collector. Removing the deleted anchor's own map entry is therefore the only
runtime action required. -/
theorem liveGapOf_append_delete (K : Know) (t : Emulation.Timestamp)
    (rep : Emulation.Replica) (x a : ℕ) :
    liveGapOf (K ++ [policyDelete t rep x]) a = liveGapOf K a := by
  have hs := fullMintSummary_append_delete K t rep x
  have hc : ∀ y, gChainOf (K ++ [policyDelete t rep x]) y = gChainOf K y := by
    intro y
    rw [← gChainOf_fullMintSummary (K ++ [policyDelete t rep x]) y,
      hs, gChainOf_fullMintSummary]
  have hr : hasRChild (K ++ [policyDelete t rep x]) a = hasRChild K a := by
    rw [← hasRChild_fullMintSummary (K ++ [policyDelete t rep x]) a,
      hs, hasRChild_fullMintSummary]
  have hn : succOf Γ (K ++ [policyDelete t rep x]) a = succOf Γ K a := by
    rw [← succOf_fullMintSummary (K ++ [policyDelete t rep x]) a,
      hs, succOf_fullMintSummary]
  have hcfun : gChainOf (K ++ [policyDelete t rep x]) = gChainOf K :=
    funext hc
  simp [liveGapOf, hc, hr, hn, hcfun]

/-! ## The successor argmax is immediate in chain order

The strengthened reachable-state invariant and argmax machinery are proved in
`SidedRGA_Fugue_ForwardNI`.  The theorem below packages exactly the bridge the
incremental collector needs for a non-root live anchor: `succOf` lies after the
anchor, and no other minted chain lies strictly between them.
-/

theorem succOf_schain_immediate {K : Know} (inv : FugueFwd.FInv Γ K)
    {a n : ℕ} (ha : a ∈ gMintedIds K) (hs : succOf Γ K a = some n) :
    schainBefore (gChainOf K a) (gChainOf K n) ∧
      ∀ y, y ∈ gMintedIds K →
        schainBefore (gChainOf K a) (gChainOf K y) →
        ¬schainBefore (gChainOf K y) (gChainOf K n) := by
  have ha0 : a ≠ 0 := by
    intro h
    subst h
    exact absurd (FugueFwd.minted_pos inv ha) (by decide)
  have han := FugueFwd.succOf_after_anchor inv hs ha0
  have hn : n ∈ gMintedIds K := succOf_mem hs
  have hne : gChainOf K a ≠ gChainOf K n := by
    intro h
    unfold gKey at han
    rw [h, keyLt_irrefl] at han
    exact Bool.noConfusion han
  refine ⟨FugueFwd.chainBefore_of_gKey_lt inv (Or.inr ha) (Or.inr hn)
    hne han, ?_⟩
  intro y hy hay hyn
  obtain ⟨g, hfind, hgK, hgins, hgid⟩ := gRecOfId_of_minted hy
  have hgy : gChainOf K y = g.chain := gChainOf_eq_of_rec hfind
  have hkeys : (y, gKey Γ K y) ∈ gKeys Γ K := by
    refine List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hgK, hgins⟩, ?_⟩
    apply Prod.ext
    · exact hgid
    · unfold gKey
      rw [hgy]
  have hayKey := FugueFwd.gKey_lt_of_chainBefore inv (Or.inr ha)
    (Or.inr hy) hay
  have hcand : (y, gKey Γ K y) ∈ succCand Γ K a := by
    unfold succCand
    rw [if_neg ha0]
    exact List.mem_filter.mpr ⟨hkeys, by simpa using hayKey⟩
  have hmax := FugueFwd.succOf_max inv hs hcand
  have hynKey := FugueFwd.gKey_lt_of_chainBefore inv (Or.inr hy)
    (Or.inr hn) hyn
  rw [hynKey] at hmax
  exact Bool.noConfusion hmax

/-- Root/start companion to `succOf_schain_immediate`. Reachable minted
chains are R-headed, so the empty root chain precedes the argmax result. -/
theorem succOf_start_schain_immediate {K : Know} (inv : FugueFwd.FInv Γ K)
    {n : ℕ} (hs : succOf Γ K 0 = some n) :
    schainBefore (gChainOf K 0) (gChainOf K n) ∧
      ∀ y, y ∈ gMintedIds K →
        schainBefore (gChainOf K 0) (gChainOf K y) →
        ¬schainBefore (gChainOf K y) (gChainOf K n) := by
  have hn : n ∈ gMintedIds K := succOf_mem hs
  obtain ⟨gn, hnfind, hnK, hnins, _⟩ := gRecOfId_of_minted hn
  obtain ⟨d, rest, hhead⟩ := FugueFwd.chain_head_R inv gn.chain.length gn
    hnK hnins (Nat.le_refl _)
  have hroot : schainBefore (gChainOf K 0) (gChainOf K n) := by
    rw [gChainOf_zero inv.pos, gChainOf_eq_of_rec hnfind, hhead]
    exact schainBefore.extR [] d rest
  refine ⟨hroot, ?_⟩
  intro y hy _ hyn
  obtain ⟨g, hfind, hgK, hgins, hgid⟩ := gRecOfId_of_minted hy
  have hgy : gChainOf K y = g.chain := gChainOf_eq_of_rec hfind
  have hkeys : (y, gKey Γ K y) ∈ gKeys Γ K := by
    refine List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hgK, hgins⟩, ?_⟩
    apply Prod.ext
    · exact hgid
    · unfold gKey
      rw [hgy]
  have hcand : (y, gKey Γ K y) ∈ succCand Γ K 0 := by
    simp [succCand, hkeys]
  have hmax := FugueFwd.succOf_max inv hs hcand
  have hynKey := FugueFwd.gKey_lt_of_chainBefore inv (Or.inr hy)
    (Or.inr hn) hyn
  rw [hynKey] at hmax
  exact Bool.noConfusion hmax

/-! ## Insert-transition equations independent of successor argmax

Two fields can be discharged without the remaining post-insert argmax proof:
the mint's chain is found exactly under its fresh id, and the intent anchor's
monotone `hasR` bit is true after every Fugue insert (either it was already
true and the mint is L, or the mint creates its first R child).
-/

theorem gChainOf_append_gen_new (K : Know) (rep : Emulation.Replica)
    {x a : ℕ} (hfresh : ∀ g ∈ K, sIsIns g.op = true → g.op.1 ≠ x) :
    gChainOf (K ++ [genInsAfter Γ K rep x a]) x =
      (genInsAfter Γ K rep x a).chain := by
  apply gChainOf_eq_of_rec
  exact gRecOfId_append_fresh hfresh rfl rfl

theorem hasRChild_append_gen_anchor (K : Know) (rep : Emulation.Replica)
    (x a : ℕ) :
    hasRChild (K ++ [genInsAfter Γ K rep x a]) a = true := by
  rw [hasRChild_append]
  cases hs : succOf Γ K a with
  | none =>
      have hc : fugueChoose Γ K a = (Side.R, a) :=
        FugueFwd.fugueChoose_none hs
      simp [hasRChild, gAnchorR, genInsAfter, hc]
  | some n =>
      cases hr : hasRChild K a with
      | true => simp [hr]
      | false =>
          have hc : fugueChoose Γ K a = (Side.R, a) :=
            FugueFwd.fugueChoose_someFalse hs hr
          simp [hr, hasRChild, gAnchorR, genInsAfter, hc]

/-! ### Generic argmax insertion

This lemma removes list-fold mechanics from the geometric proof. If the new
successor candidate is appended and beats the old argmax whenever one exists,
the new `succOf` is exactly its id.
-/

theorem succOf_of_append_beating_candidate {K K' : Know} {a x : ℕ}
    {kx : List ℕ}
    (hcand : succCand Γ K' a = succCand Γ K a ++ [(x, kx)])
    (hbeats : ∀ p, (succCand Γ K a).foldl maxKey none = some p →
      keyLt p.2 kx = true) :
    succOf Γ K' a = some x := by
  unfold succOf
  rw [hcand, List.foldl_append]
  cases hold : (succCand Γ K a).foldl maxKey none with
  | none => simp [maxKey]
  | some p => simp [maxKey, hbeats p hold]

theorem gKeys_append_gen (K : Know) (rep : Emulation.Replica) (x a : ℕ) :
    gKeys Γ (K ++ [genInsAfter Γ K rep x a]) =
      gKeys Γ K ++ [(x,
        sKey (sidedCoordOf Γ (genInsAfter Γ K rep x a).chain))] := by
  simp [gKeys, gMinted_append, gMinted, genInsAfter, sIsIns]

theorem succCand_append_of_gKeys {K K' : Know} {a x : ℕ} {kx : List ℕ}
    (hkeys : gKeys Γ K' = gKeys Γ K ++ [(x, kx)])
    (hanchor : gKey Γ K' a = gKey Γ K a)
    (hafter : a ≠ 0 → keyLt kx (gKey Γ K a) = true) :
    succCand Γ K' a = succCand Γ K a ++ [(x, kx)] := by
  unfold succCand
  by_cases h0 : a = 0
  · simp [h0, hkeys]
  · rw [if_neg h0, if_neg h0, hkeys, List.filter_append, hanchor]
    simp [hafter h0]

theorem gKey_append_gen_old {K : Know} (inv : FugueFwd.FInv Γ K)
    (rep : Emulation.Replica) {x a y : ℕ} (hx : 0 < x)
    (hy : y = 0 ∨ y ∈ gMintedIds K) :
    gKey Γ (K ++ [genInsAfter Γ K rep x a]) y = gKey Γ K y := by
  unfold gKey
  rw [FugueFwd.gChainOf_append_stable hy inv.pos]
  intro g hg
  rw [List.mem_singleton] at hg
  subst g
  simpa using hx

/-- The exact anchor-successor equation, reduced to its two geometric facts:
the fresh chain is after the anchor and beats the previous candidate argmax.
All knowledge-list and fold bookkeeping is discharged here. -/
theorem succOf_append_gen_anchor_of_geometry {K : Know}
    (inv : FugueFwd.FInv Γ K) (rep : Emulation.Replica) {x a : ℕ}
    (hx : 0 < x) (ha : a = 0 ∨ a ∈ gMintedIds K)
    (hafter : a ≠ 0 →
      keyLt (sKey (sidedCoordOf Γ (genInsAfter Γ K rep x a).chain))
        (gKey Γ K a) = true)
    (hbeats : ∀ p, (succCand Γ K a).foldl maxKey none = some p →
      keyLt p.2
        (sKey (sidedCoordOf Γ (genInsAfter Γ K rep x a).chain)) = true) :
    succOf Γ (K ++ [genInsAfter Γ K rep x a]) a = some x := by
  apply succOf_of_append_beating_candidate
  · apply succCand_append_of_gKeys (gKeys_append_gen K rep x a)
      (gKey_append_gen_old inv rep hx ha)
    exact hafter
  · exact hbeats

theorem succOf_append_gen_anchor_of_between {K : Know}
    (inv : FugueFwd.FInv Γ K) (rep : Emulation.Replica) {x a : ℕ}
    (hx : 0 < x)
    (ha : a = 0 ∨ a ∈ gMintedIds K)
    (hnewPos : Sal.EmbedRGA.PosSChain (genInsAfter Γ K rep x a).chain)
    (hanchor : schainBefore (gChainOf K a)
      (genInsAfter Γ K rep x a).chain)
    (hold : ∀ n, succOf Γ K a = some n →
      schainBefore (genInsAfter Γ K rep x a).chain (gChainOf K n)) :
    succOf Γ (K ++ [genInsAfter Γ K rep x a]) a = some x := by
  apply succOf_append_gen_anchor_of_geometry inv rep hx ha
  · intro _
    exact Sal.EmbedRGA.schainBefore_display Γ
      (FugueFwd.gChainOf_posOf inv ha) hnewPos hanchor
  · intro p hp
    have hs : succOf Γ K a = some p.1 := by
      unfold succOf
      rw [hp]
      rfl
    have hpmem : p ∈ succCand Γ K a := by
      rcases foldl_maxKey_mem _ none hp with h | h
      · exact absurd h (by simp)
      · exact h
    have hpkey : p.2 = gKey Γ K p.1 :=
      (FugueFwd.gKeys_shape inv (succCand_sub hpmem)).2
    have hpminted : p.1 ∈ gMintedIds K := succOf_mem hs
    rw [hpkey]
    unfold gKey
    exact Sal.EmbedRGA.schainBefore_display Γ hnewPos
      (FugueFwd.gChainOf_posOf inv (Or.inr hpminted)) (hold p.1 hs)

/-- Fresh monotone ids make the generated final chain entry positive. -/
theorem genInsAfter_pos {K : Know} (inv : FugueFwd.FInv Γ K)
    (rep : Emulation.Replica) {x a : ℕ} (hx : 0 < x)
    (hlam : ∀ m ∈ gMintedIds K, m < x)
    (ha : a = 0 ∨ a ∈ gMintedIds K) :
    Sal.EmbedRGA.PosSChain (genInsAfter Γ K rep x a).chain := by
  have hp : (fugueChoose Γ K a).2 = 0 ∨
      (fugueChoose Γ K a).2 ∈ gMintedIds K := by
    rcases fugueChoose_parent_or Γ K a with h | h
    · rw [h]
      exact ha
    · exact Or.inr (succOf_mem h)
  have hpx : (fugueChoose Γ K a).2 < x := by
    rcases hp with h | h
    · rw [h]
      exact hx
    · exact hlam _ h
  rw [genInsAfter_chain]
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact FugueFwd.gChainOf_posOf inv hp e h
  · rw [List.mem_singleton] at h
    subst e
    exact Nat.sub_pos_of_lt hpx

/-- The generated Fugue chain lies strictly inside the anchor's current gap:
after the anchor and before its old successor, when one exists. -/
theorem genInsAfter_between {K : Know} (inv : FugueFwd.FInv Γ K)
    (rep : Emulation.Replica) {x a : ℕ} (hx : 0 < x)
    (hlam : ∀ m ∈ gMintedIds K, m < x)
    (ha : a = 0 ∨ a ∈ gMintedIds K) :
    schainBefore (gChainOf K a) (genInsAfter Γ K rep x a).chain ∧
      ∀ n, succOf Γ K a = some n →
        schainBefore (genInsAfter Γ K rep x a).chain (gChainOf K n) := by
  rcases hs : succOf Γ K a with _ | n
  · have hc := FugueFwd.fugueChoose_none hs
    constructor
    · rw [genInsAfter_chain, hc]
      exact schainBefore.extR _ _ []
    · intro n hn
      cases hn
  · cases hr : hasRChild K a with
    | true =>
        have hc := FugueFwd.fugueChoose_someTrue hs hr
        obtain ⟨d, ls, hnchain, _⟩ :=
          FugueFwd.succ_R_desc_allL inv ha hr hs
        constructor
        · rw [genInsAfter_chain, hc, hnchain]
          rw [List.append_assoc]
          exact schainBefore.extR _ d (ls ++ [(Side.L, x - n)])
        · intro n' hn'
          injection hn' with h
          subst n'
          rw [genInsAfter_chain, hc]
          exact schainBefore.extL _ _ []
    | false =>
        have hc := FugueFwd.fugueChoose_someFalse hs hr
        have hbefore : schainBefore (gChainOf K a) (gChainOf K n) := by
          rcases ha with h0 | ham
          · subst a
            exact (succOf_start_schain_immediate inv hs).1
          · exact (succOf_schain_immediate inv ham hs).1
        constructor
        · rw [genInsAfter_chain, hc]
          exact schainBefore.extR _ _ []
        · intro n' hn'
          injection hn' with h
          subst n'
          rw [genInsAfter_chain, hc]
          apply schainBefore_snoc_newest hbefore
          intro d rest hdecomp
          have hnmem : n ∈ gMintedIds K := succOf_mem hs
          have hsumN := FugueFwd.gChainOf_sum inv (Or.inr hnmem)
          have hsumA := FugueFwd.gChainOf_sum inv ha
          rw [hdecomp, List.map_append, List.sum_append] at hsumN
          simp at hsumN
          have hnx : n < x := hlam n hnmem
          omega

/-- **Exact anchor insert equation.** A fresh monotone Fugue mint becomes the
tombstone-visible successor of its intent anchor. -/
theorem succOf_append_gen_anchor {K : Know} (inv : FugueFwd.FInv Γ K)
    (rep : Emulation.Replica) {x a : ℕ} (hx : 0 < x)
    (hlam : ∀ m ∈ gMintedIds K, m < x)
    (ha : a = 0 ∨ a ∈ gMintedIds K) :
    succOf Γ (K ++ [genInsAfter Γ K rep x a]) a = some x := by
  obtain ⟨hanchor, hold⟩ := genInsAfter_between inv rep hx hlam ha
  exact succOf_append_gen_anchor_of_between inv rep hx ha
    (genInsAfter_pos inv rep hx hlam ha) hanchor hold

/-! ## The fresh anchor inherits the old gap

The second successor equation is definitionally reduced to candidate-set
equality. The lemmas here discharge lookup and fold plumbing; the remaining
order obligation is to show that the old elements after `a` are exactly the
post-state elements after `x`.
-/

theorem gKey_append_gen_new (K : Know) (rep : Emulation.Replica)
    {x a : ℕ} (hfresh : ∀ g ∈ K, sIsIns g.op = true → g.op.1 ≠ x) :
    gKey Γ (K ++ [genInsAfter Γ K rep x a]) x =
      sKey (sidedCoordOf Γ (genInsAfter Γ K rep x a).chain) := by
  unfold gKey
  rw [gChainOf_append_gen_new K rep hfresh]

theorem succOf_congr_candidates {K K' : Know} {a a' : ℕ}
    (h : succCand Γ K a = succCand Γ K' a') :
    succOf Γ K a = succOf Γ K' a' := by
  unfold succOf
  rw [h]

theorem succOf_append_gen_new_of_candidates (K : Know)
    (rep : Emulation.Replica) {x a : ℕ}
    (hcand : succCand Γ (K ++ [genInsAfter Γ K rep x a]) x =
      succCand Γ K a) :
    succOf Γ (K ++ [genInsAfter Γ K rep x a]) x = succOf Γ K a :=
  succOf_congr_candidates hcand

theorem foldl_maxKey_from_some (l : List (ℕ × List ℕ))
    (p : ℕ × List ℕ) : ∃ q, l.foldl maxKey (some p) = some q := by
  induction l generalizing p with
  | nil => exact ⟨p, rfl⟩
  | cons b l ih =>
      rw [List.foldl_cons]
      cases h : keyLt p.2 b.2
      · rw [maxKey, h]
        exact ih p
      · rw [maxKey, h]
        exact ih b

theorem foldl_maxKey_of_nonempty {l : List (ℕ × List ℕ)} (h : l ≠ []) :
    ∃ p, l.foldl maxKey none = some p := by
  cases l with
  | nil => exact absurd rfl h
  | cons b l =>
      rw [List.foldl_cons]
      simpa [maxKey] using foldl_maxKey_from_some l b

/-- Every old candidate after `a` remains after the freshly inserted `x`.
This is the forward half of candidate-set equality. -/
theorem genInsAfter_before_old_candidate {K : Know}
    (inv : FugueFwd.FInv Γ K) (rep : Emulation.Replica) {x a : ℕ}
    (hx : 0 < x) (hlam : ∀ m ∈ gMintedIds K, m < x)
    (ha : a = 0 ∨ a ∈ gMintedIds K) {p : ℕ × List ℕ}
    (hp : p ∈ succCand Γ K a) :
    keyLt p.2
      (sKey (sidedCoordOf Γ (genInsAfter Γ K rep x a).chain)) = true := by
  rcases hs : succOf Γ K a with _ | n
  · unfold succOf at hs
    have hne : succCand Γ K a ≠ [] := by
      intro hnil
      rw [hnil] at hp
      exact absurd hp (by simp)
    obtain ⟨q, hq⟩ := foldl_maxKey_of_nonempty hne
    rw [hq] at hs
    exact absurd hs (by simp)
  · have hnmem : n ∈ gMintedIds K := succOf_mem hs
    have hnewn := (genInsAfter_between inv rep hx hlam ha).2 n hs
    have hnewnKey : keyLt (gKey Γ K n)
        (sKey (sidedCoordOf Γ (genInsAfter Γ K rep x a).chain)) = true := by
      unfold gKey
      exact Sal.EmbedRGA.schainBefore_display Γ
        (genInsAfter_pos inv rep hx hlam ha)
        (FugueFwd.gChainOf_posOf inv (Or.inr hnmem)) hnewn
    have hshape := FugueFwd.gKeys_shape inv (succCand_sub hp)
    have hp' : (p.1, gKey Γ K p.1) ∈ succCand Γ K a := by
      have heq : (p.1, gKey Γ K p.1) = p := by
        apply Prod.ext
        · rfl
        · exact hshape.2.symm
      rw [heq]
      exact hp
    have hmax := FugueFwd.succOf_max inv hs hp'
    by_cases hid : p.1 = n
    · rw [hshape.2, hid]
      exact hnewnKey
    · have hpne : gKey Γ K p.1 ≠ gKey Γ K n := by
        intro heq
        have hcoord : sidedCoordOf Γ (gChainOf K p.1) =
            sidedCoordOf Γ (gChainOf K n) := by
          unfold gKey sKey at heq
          exact (List.append_inj' heq rfl).1
        have hchain : gChainOf K p.1 = gChainOf K n :=
          Sal.EmbedRGA.sidedCoordOf_inj Γ
            (FugueFwd.gChainOf_posOf inv (Or.inr hshape.1))
            (FugueFwd.gChainOf_posOf inv (Or.inr hnmem)) hcoord
        have hs1 := FugueFwd.gChainOf_sum inv (Or.inr hshape.1)
        have hs2 := FugueFwd.gChainOf_sum inv (Or.inr hnmem)
        exact hid (hs1.symm.trans (hchain ▸ hs2))
      rcases Sal.EmbedRGA.keyLt_total hpne with hpn | hnp
      · rw [hshape.2]
        exact Sal.EmbedRGA.keyLt_trans hpn hnewnKey
      · rw [hnp] at hmax
        exact Bool.noConfusion hmax

/-- The post-state candidates after fresh `x` are exactly the pre-state
candidates after its intent anchor `a`. -/
theorem succCand_append_gen_new {K : Know} (inv : FugueFwd.FInv Γ K)
    (rep : Emulation.Replica) {x a : ℕ} (hx : 0 < x)
    (hlam : ∀ m ∈ gMintedIds K, m < x)
    (ha : a = 0 ∨ a ∈ gMintedIds K) :
    succCand Γ (K ++ [genInsAfter Γ K rep x a]) x = succCand Γ K a := by
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hfresh : ∀ g ∈ K, sIsIns g.op = true → g.op.1 ≠ x := by
    intro g hg hins
    have hm : g.op.1 ∈ gMintedIds K :=
      List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, hins⟩, rfl⟩
    exact Nat.ne_of_lt (hlam _ hm)
  have hkey := gKey_append_gen_new (K := K) (a := a) rep hfresh
  unfold succCand
  rw [if_neg hx0, gKeys_append_gen, hkey, List.filter_append]
  have hdrop : List.filter (fun p : ℕ × List ℕ => keyLt p.2
      (sKey (sidedCoordOf Γ (genInsAfter Γ K rep x a).chain)))
      [(x, sKey (sidedCoordOf Γ (genInsAfter Γ K rep x a).chain))] = [] := by
    simp [keyLt_irrefl]
  rw [hdrop, List.append_nil]
  by_cases h0 : a = 0
  · rw [if_pos h0]
    apply List.filter_eq_self.mpr
    intro p hp
    apply genInsAfter_before_old_candidate inv rep hx hlam ha
    simpa [succCand, h0] using hp
  · rw [if_neg h0]
    apply List.filter_congr
    intro p hp
    have holdToNew : keyLt p.2 (gKey Γ K a) = true →
        keyLt p.2
          (sKey (sidedCoordOf Γ (genInsAfter Γ K rep x a).chain)) = true := by
      intro h
      apply genInsAfter_before_old_candidate inv rep hx hlam ha
      unfold succCand
      rw [if_neg h0]
      exact List.mem_filter.mpr ⟨hp, h⟩
    have hanchorKey : keyLt
        (sKey (sidedCoordOf Γ (genInsAfter Γ K rep x a).chain))
        (gKey Γ K a) = true := by
      unfold gKey
      exact Sal.EmbedRGA.schainBefore_display Γ
        (FugueFwd.gChainOf_posOf inv ha)
        (genInsAfter_pos inv rep hx hlam ha)
        (genInsAfter_between inv rep hx hlam ha).1
    have hnewToOld : keyLt p.2
        (sKey (sidedCoordOf Γ (genInsAfter Γ K rep x a).chain)) = true →
        keyLt p.2 (gKey Γ K a) = true := by
      intro h
      exact Sal.EmbedRGA.keyLt_trans h hanchorKey
    cases hn : keyLt p.2
        (sKey (sidedCoordOf Γ (genInsAfter Γ K rep x a).chain)) <;>
      cases ho : keyLt p.2 (gKey Γ K a)
    · rfl
    · exact absurd (holdToNew ho) (by simp [hn])
    · exact absurd (hnewToOld hn) (by simp [ho])
    · rfl

/-- **Exact inherited-successor equation.** -/
theorem succOf_append_gen_new {K : Know} (inv : FugueFwd.FInv Γ K)
    (rep : Emulation.Replica) {x a : ℕ} (hx : 0 < x)
    (hlam : ∀ m ∈ gMintedIds K, m < x)
    (ha : a = 0 ∨ a ∈ gMintedIds K) :
    succOf Γ (K ++ [genInsAfter Γ K rep x a]) x = succOf Γ K a :=
  succOf_append_gen_new_of_candidates K rep
    (succCand_append_gen_new inv rep hx hlam ha)

/-! ## Merge congruence

Policy knowledge merges by set union (`syncK`). We first expose its exact
membership and monotone-bit equations; successor argmax composition follows.
-/

theorem mem_syncK_iff {K K' : Know} {g : GRec} :
    g ∈ syncK K K' ↔ g ∈ K ∨ g ∈ K' := by
  constructor
  · intro h
    unfold syncK at h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_of_mem_filter h)
  · intro h
    unfold syncK
    rcases h with h | h
    · exact List.mem_append_left _ h
    · by_cases hk : g ∈ K
      · exact List.mem_append_left _ hk
      · exact List.mem_append_right _ (List.mem_filter.mpr ⟨h, by simp [hk]⟩)

theorem hasRChild_syncK (K K' : Know) (a : ℕ) :
    hasRChild (syncK K K') a =
      (hasRChild K a || hasRChild K' a) := by
  cases hK : hasRChild K a <;> cases hK' : hasRChild K' a
  · apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨g, hg, e, π, hop⟩ := FugueFwd.hasRChild_iff.mp h
    rcases mem_syncK_iff.mp hg with hg | hg
    · exact Bool.noConfusion (hK ▸ FugueFwd.hasRChild_iff.mpr ⟨g, hg, e, π, hop⟩)
    · exact Bool.noConfusion (hK' ▸ FugueFwd.hasRChild_iff.mpr ⟨g, hg, e, π, hop⟩)
  · apply FugueFwd.hasRChild_iff.mpr
    obtain ⟨g, hg, e, π, hop⟩ := FugueFwd.hasRChild_iff.mp hK'
    exact ⟨g, mem_syncK_iff.mpr (Or.inr hg), e, π, hop⟩
  · apply FugueFwd.hasRChild_iff.mpr
    obtain ⟨g, hg, e, π, hop⟩ := FugueFwd.hasRChild_iff.mp hK
    exact ⟨g, mem_syncK_iff.mpr (Or.inl hg), e, π, hop⟩
  · apply FugueFwd.hasRChild_iff.mpr
    obtain ⟨g, hg, e, π, hop⟩ := FugueFwd.hasRChild_iff.mp hK
    exact ⟨g, mem_syncK_iff.mpr (Or.inl hg), e, π, hop⟩

/-- A well-formed retained successor witness: id plus the chain used to order
it. `liveGapOf` always produces either both fields or neither. -/
def liveGapSucc (g : LiveGap) : Option (ℕ × SChain) :=
  match g.succ, g.succChain with
  | some n, some c => some (n, c)
  | _, _ => none

def maxGapSucc : Option (ℕ × SChain) → Option (ℕ × SChain) →
    Option (ℕ × SChain)
  | none, q => q
  | p, none => p
  | some p, some q =>
      if keyLt (sKey (sidedCoordOf Γ p.2))
          (sKey (sidedCoordOf Γ q.2)) = true
      then some q else some p

def liveGapWithSucc (base : LiveGap) : Option (ℕ × SChain) → LiveGap
  | none => { base with succ := none, succChain := none }
  | some p => { base with succ := some p.1, succChain := some p.2 }

theorem liveGapWithSucc_hasR (base : LiveGap) (p : Option (ℕ × SChain)) :
    (liveGapWithSucc base p).hasR = base.hasR := by cases p <;> rfl

/-- Runtime merge for one retained live gap. Anchor chains are globally
immutable, so either branch may supply the base chain. -/
def mergeLiveGap (l r : LiveGap) : LiveGap :=
  liveGapWithSucc { l with hasR := l.hasR || r.hasR }
    (maxGapSucc (liveGapSucc l) (liveGapSucc r))

theorem liveGapSucc_of (K : Know) (a : ℕ) :
    liveGapSucc (liveGapOf K a) =
      (succOf Γ K a).map (fun n => (n, gChainOf K n)) := by
  simp [liveGapSucc, liveGapOf]
  cases succOf Γ K a <;> rfl

theorem mergeLiveGap_hasR (K K' : Know) (a : ℕ) :
    (mergeLiveGap (liveGapOf K a) (liveGapOf K' a)).hasR =
      (liveGapOf (syncK K K') a).hasR := by
  rw [mergeLiveGap, liveGapWithSucc_hasR]
  exact (hasRChild_syncK K K' a).symm

theorem maxGapSucc_none_left (p : Option (ℕ × SChain)) :
    maxGapSucc none p = p := rfl

theorem maxGapSucc_none_right (p : Option (ℕ × SChain)) :
    maxGapSucc p none = p := by cases p <;> rfl

theorem liveGapSucc_mergeLiveGap (l r : LiveGap) :
    liveGapSucc (mergeLiveGap l r) =
      maxGapSucc (liveGapSucc l) (liveGapSucc r) := by
  unfold mergeLiveGap
  cases h : maxGapSucc (liveGapSucc l) (liveGapSucc r) with
  | none => simp [liveGapWithSucc, liveGapSucc, h]
  | some p =>
      obtain ⟨n, c⟩ := p
      simp [liveGapWithSucc, liveGapSucc, h]

/-- The sole remaining semantic merge law: union's immediate successor is
the display-earlier of the two branch immediate successors. -/
def MergeSuccLaw (K K' : Know) (a : ℕ) : Prop :=
  liveGapSucc (liveGapOf (syncK K K') a) =
    maxGapSucc (liveGapSucc (liveGapOf K a))
      (liveGapSucc (liveGapOf K' a))

theorem liveGapWithSucc_liveGapOf (K : Know) (a : ℕ) :
    liveGapWithSucc (liveGapOf K a) (liveGapSucc (liveGapOf K a)) =
      liveGapOf K a := by
  rw [liveGapSucc_of]
  cases h : succOf Γ K a <;> simp [liveGapWithSucc, liveGapOf, h]

/-- Full compact merge congruence follows from immutable anchor-chain
agreement plus `MergeSuccLaw`; `hasR` agreement is already unconditional. -/
theorem mergeLiveGap_exact_of_succLaw (K K' : Know) (a : ℕ)
    (hanchor : gChainOf K a = gChainOf (syncK K K') a)
    (hsucc : MergeSuccLaw K K' a) :
    mergeLiveGap (liveGapOf K a) (liveGapOf K' a) =
      liveGapOf (syncK K K') a := by
  unfold mergeLiveGap
  rw [← hsucc]
  cases hp : liveGapSucc (liveGapOf (syncK K K') a) with
  | none =>
      have hself := liveGapWithSucc_liveGapOf (syncK K K') a
      rw [hp] at hself
      simp only [liveGapWithSucc] at hself ⊢
      apply LiveGap.ext
      · exact hanchor
      · exact (hasRChild_syncK K K' a).symm
      · change none = (liveGapOf (syncK K K') a).succ
        exact congrArg LiveGap.succ hself
      · change none = (liveGapOf (syncK K K') a).succChain
        exact congrArg LiveGap.succChain hself
  | some p =>
      obtain ⟨n, c⟩ := p
      have hself := liveGapWithSucc_liveGapOf (syncK K K') a
      rw [hp] at hself
      simp only [liveGapWithSucc] at hself ⊢
      apply LiveGap.ext
      · exact hanchor
      · exact (hasRChild_syncK K K' a).symm
      · change some n = (liveGapOf (syncK K K') a).succ
        exact congrArg LiveGap.succ hself
      · change some c = (liveGapOf (syncK K K') a).succChain
        exact congrArg LiveGap.succChain hself

/-! ## Stable deletion is still continuation-observable

Assume every replica has observed `deadRightChild`; the deletion is therefore
stable. Two replicas then concurrently insert ids `5` and `4` after anchor `1`.
Without policy collection, both inserts are L children of dead `2`, and the
mirrored L band displays the older id first. If collection replaces the common
knowledge with `onlyAnchor`, both become R children of `1`, and the R band
displays the newer id first. The merged reads differ.
-/

def fullA : Know :=
  deadRightChild ++ [genInsAfter Γ deadRightChild 0 5 1]

def fullB : Know :=
  deadRightChild ++ [genInsAfter Γ deadRightChild 1 4 1]

def fullMerged : Know := syncK fullA fullB

def collectedA : Know :=
  onlyAnchor ++ [genInsAfter Γ onlyAnchor 0 5 1]

def collectedB : Know :=
  onlyAnchor ++ [genInsAfter Γ onlyAnchor 1 4 1]

def collectedMerged : Know := syncK collectedA collectedB

/-- PASS: the uncollected policy tree orders the concurrent L siblings oldest
first. -/
theorem uncollected_continuation_view :
    gView Γ fullMerged = [1, 4, 5] := by native_decide

/-- FAIL companion: forgetting the stable dead child changes both operations
to R children and reverses the concurrent pair. -/
theorem collected_continuation_view :
    gView Γ collectedMerged = [1, 5, 4] := by native_decide

/-- Checked counterexample: stable dead-leaf erasure is not
continuation-equivalent under the unchanged Fugue policy. -/
theorem stable_dead_leaf_collection_changes_future_read :
    gView Γ fullMerged ≠ gView Γ collectedMerged := by native_decide

#print axioms live_projection_equal
#print axioms choose_without_dead_child
#print axioms choose_with_dead_child
#print axioms live_projection_does_not_determine_choose
#print axioms fullMintSummary_preserves_choose
#print axioms liveGapChoose_exact
#print axioms liveGapParentChain_exact
#print axioms liveGapOf_append_delete
#print axioms succOf_schain_immediate
#print axioms succOf_start_schain_immediate
#print axioms gChainOf_append_gen_new
#print axioms hasRChild_append_gen_anchor
#print axioms succOf_of_append_beating_candidate
#print axioms gKeys_append_gen
#print axioms succCand_append_of_gKeys
#print axioms gKey_append_gen_old
#print axioms succOf_append_gen_anchor_of_geometry
#print axioms succOf_append_gen_anchor_of_between
#print axioms genInsAfter_pos
#print axioms genInsAfter_between
#print axioms succOf_append_gen_anchor
#print axioms gKey_append_gen_new
#print axioms succOf_append_gen_new_of_candidates
#print axioms genInsAfter_before_old_candidate
#print axioms succCand_append_gen_new
#print axioms succOf_append_gen_new
#print axioms hasRChild_syncK
#print axioms mergeLiveGap_hasR
#print axioms liveGapSucc_mergeLiveGap
#print axioms mergeLiveGap_exact_of_succLaw
#print axioms stable_dead_leaf_collection_changes_future_read

end Sal.ConditionedMRDTs.FuguePolicyGC
