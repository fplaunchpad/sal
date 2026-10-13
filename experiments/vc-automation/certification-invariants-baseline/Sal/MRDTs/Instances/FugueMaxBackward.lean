import Sal.MRDTs.Instances.FugueMaxNonInterleaving

/-!
# FugueMax backward non-interleaving: the condition-(2) discharge

This file discharges the stated def `FugueMaxBackwardNonInterleaving`
(Weidner-Kleppmann Definition 4 condition (2) with the Lemma-5 exception,
strict reading, the minted-witness quantification of §9.7.2) at
every replica of every `MaxReach`-reachable configuration, kernel-clean,
and with it the full adapted Theorem 9
(`fuguemax_maximally_noninterleaving`).

* **§1 Display and record plumbing**: totality/transitivity of the
  strong-list order from the marker theorem, the convexity trap, record
  lookups.

* **§2 Record-shape inversion** (§9.7.8 item 3): a minted element whose
  chain extends `P`'s by one entry is a mint at `P` on that entry's side.

* **§3 The `RBk` bundle** (§9.7.3): the three mint-time clauses (R0),
  (RSA), (RSuccL), (RSuccR) on R-mint records, their mint-step proofs
  (the paper's causal-minimality exclusions as stable existential
  witnesses), transport, and `maxReach_inv3` (structured like `SLC` +
  `maxReach_inv2`; `MInv`/`KInv`/`LinkR` are used unmodified, since
  folding the clauses in would reopen the proved bundle).

* **§4 The loDesc-to-prefix lemma**: the only fact about `mLoDesc` the
  discharge needs.

* **§5 The discharge**: the beta1 lemma (stated over MINTED in-betweens
  so the beta0 ladder can call it), the L case, the R-case witness
  function (alpha / beta1 / beta0-direct / beta0-ladder), and
  `fuguemax_backward_ni : FugueMaxBackwardNonInterleaving Γ`.

* **§6 SPOTs** (PASS+FAIL, hand-derived from §9.7.2/9.7.5/9.7.7): the
  four delete variants, Figure 7 both mint orders + delete 4, the beta0
  direct and ladder constructions + delete 2, with the witness values
  pinned.

* **§7 The capstone**: `fuguemax_maximally_noninterleaving`, full
  adapted W-K Theorem 9, via `fuguemax_theorem9_of_backward`.
-/

namespace Sal.MRDTs.Instances.SidedEmbedRGA

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode keyLt sKey unaryCode Side
  keyLt_irrefl keyLt_asymm keyLt_trans keyLt_total
  FMEntry FMChain fmδ PosFMChain TagOK fmTagOK TagsOK
  fmCoordOf fmChainBefore fmChainBefore_display
  fmdisplay_iff_fmChainBefore fm_subtree_convex fm_ext_after_is_R
  fm_ext_before_is_L fm_R_sibling_inv tagOK_key fmCoordOf_inj)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## §1  Display and record plumbing -/

theorem mBefore_ne {Γ : OrderedPrefixCode} {K : KnowM} {x y : ℕ}
    (h : mBefore Γ K x y) : x ≠ y := by
  rintro rfl
  have h' : keyLt (mKey Γ K x) (mKey Γ K x) = true := h
  rw [keyLt_irrefl] at h'
  exact Bool.noConfusion h'

theorem mBefore_trans {Γ : OrderedPrefixCode} {K : KnowM} {x y z : ℕ}
    (h1 : mBefore Γ K x y) (h2 : mBefore Γ K y z) : mBefore Γ K x z :=
  keyLt_trans h2 h1

theorem mBefore_asymm {Γ : OrderedPrefixCode} {K : KnowM} {x y : ℕ}
    (h : mBefore Γ K x y) : ¬ mBefore Γ K y x := by
  intro h'
  have := keyLt_trans h h'
  rw [keyLt_irrefl] at this
  exact Bool.noConfusion this

/-- Equal strong-list keys collapse ids: unique decodability plus the
telescoping sums. -/
theorem mKey_inj {Γ : OrderedPrefixCode} {K : KnowM} (inv : KInv Γ K)
    {x y : ℕ} (hx : x = 0 ∨ x ∈ mMintedIds K)
    (hy : y = 0 ∨ y ∈ mMintedIds K)
    (h : mKey Γ K x = mKey Γ K y) : x = y := by
  have hwx := mChainOf_wfparts inv hx
  have hwy := mChainOf_wfparts inv hy
  have hch : mChainOf K x = mChainOf K y := by
    apply fmCoordOf_inj Γ hwx.1 hwy.1 hwx.2 hwy.2
    unfold mKey sKey at h
    exact (List.append_inj' h rfl).1
  have s1 := mChainOf_sum inv hx
  have s2 := mChainOf_sum inv hy
  rw [hch] at s1
  omega

theorem mBefore_total {Γ : OrderedPrefixCode} {K : KnowM} (inv : KInv Γ K)
    {x y : ℕ} (hx : x = 0 ∨ x ∈ mMintedIds K)
    (hy : y = 0 ∨ y ∈ mMintedIds K) (hne : x ≠ y) :
    mBefore Γ K x y ∨ mBefore Γ K y x := by
  have hk : mKey Γ K x ≠ mKey Γ K y := fun h => hne (mKey_inj inv hx hy h)
  rcases keyLt_total hk with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem mBefore_of_chainBefore {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {x y : ℕ} (hx : x = 0 ∨ x ∈ mMintedIds K)
    (hy : y = 0 ∨ y ∈ mMintedIds K)
    (h : fmChainBefore (mChainOf K x) (mChainOf K y)) : mBefore Γ K x y := by
  have hwx := mChainOf_wfparts inv hx
  have hwy := mChainOf_wfparts inv hy
  exact fmChainBefore_display Γ hwx.1 hwy.1 hwx.2 hwy.2 h

theorem chainBefore_of_mBefore {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {x y : ℕ} (hx : x = 0 ∨ x ∈ mMintedIds K)
    (hy : y = 0 ∨ y ∈ mMintedIds K) (h : mBefore Γ K x y) :
    fmChainBefore (mChainOf K x) (mChainOf K y) := by
  have hwx := mChainOf_wfparts inv hx
  have hwy := mChainOf_wfparts inv hy
  have hne : mChainOf K x ≠ mChainOf K y := by
    intro he
    have h' : keyLt (mKey Γ K y) (mKey Γ K x) = true := h
    unfold mKey at h'
    rw [he, keyLt_irrefl] at h'
    exact Bool.noConfusion h'
  exact (fmdisplay_iff_fmChainBefore Γ hwx.1 hwy.1 hwx.2 hwy.2 hne).mp h

/-- **The convexity trap**: an element displayed between two members of a
subtree is in the subtree. -/
theorem mTrap {Γ : OrderedPrefixCode} {K : KnowM} (inv : KInv Γ K)
    {p : FMChain} {x z y : ℕ}
    (hx : x = 0 ∨ x ∈ mMintedIds K) (hz : z = 0 ∨ z ∈ mMintedIds K)
    (hy : y = 0 ∨ y ∈ mMintedIds K)
    (hpx : p <+: mChainOf K x) (hpy : p <+: mChainOf K y)
    (hxz : mBefore Γ K x z) (hzy : mBefore Γ K z y) :
    p <+: mChainOf K z := by
  obtain ⟨ex, hex⟩ := hpx
  obtain ⟨ey, hey⟩ := hpy
  obtain ⟨ez, hez⟩ := fm_subtree_convex p ⟨ex, hex.symm⟩ ⟨ey, hey.symm⟩
    (chainBefore_of_mBefore inv hx hz hxz)
    (chainBefore_of_mBefore inv hz hy hzy)
  exact ⟨ez, hez.symm⟩

theorem minted_of_recOfId {K : KnowM} {x : ℕ} {g : MRec}
    (h : mRecOfId K x = some g) :
    x ∈ mMintedIds K ∧ g ∈ K ∧ mIsIns g = true ∧ g.ts = x := by
  have hmem := List.mem_of_find?_eq_some h
  have hts : g.ts = x := by simpa using List.find?_some h
  exact ⟨List.mem_map.mpr ⟨g, hmem, hts⟩,
    List.mem_of_mem_filter hmem, (List.mem_filter.mp hmem).2, hts⟩

/-- The lookup of a member's own id returns that member (uniqueness). -/
theorem mRecOfId_of_mem {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {g : MRec} (hg : g ∈ K) (hins : mIsIns g = true) :
    mRecOfId K g.ts = some g := by
  have hmem : g.ts ∈ mMintedIds K :=
    List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, hins⟩, rfl⟩
  obtain ⟨g', hf, hg'K, hg'ins, hg'ts⟩ := mRecOfId_of_minted hmem
  rw [hf, inv.uniq g' hg'K g hg hg'ins hins hg'ts]

theorem mRecOfId_zero {K : KnowM} (hpos : ∀ g ∈ K, 1 ≤ g.ts) :
    mRecOfId K 0 = none := by
  unfold mRecOfId
  rw [List.find?_eq_none]
  intro g hg
  have := hpos g (List.mem_of_mem_filter hg)
  simp only [beq_iff_eq]
  omega

theorem mLoOf_zero {K : KnowM} (hpos : ∀ g ∈ K, 1 ≤ g.ts) :
    mLoOf K 0 = 0 := by
  unfold mLoOf
  rw [mRecOfId_zero hpos]
  rfl

theorem mRoOf_eq {K : KnowM} {x : ℕ} {g : MRec}
    (h : mRecOfId K x = some g) : mRoOf K x = g.ro := by
  simp [mRoOf, h]

/-- Same-id minted records agree across knowledges, so lookups do. -/
theorem mRecOfId_agree {K₁ K₂ : KnowM}
    (h : ∀ g ∈ K₁, ∀ g' ∈ K₂, mIsIns g = true → mIsIns g' = true →
      g.ts = g'.ts → g = g')
    {x : ℕ} (hx₁ : x ∈ mMintedIds K₁) (hx₂ : x ∈ mMintedIds K₂) :
    mRecOfId K₁ x = mRecOfId K₂ x := by
  obtain ⟨g₁, hf₁, hm₁, hi₁, ht₁⟩ := mRecOfId_of_minted hx₁
  obtain ⟨g₂, hf₂, hm₂, hi₂, ht₂⟩ := mRecOfId_of_minted hx₂
  rw [hf₁, hf₂, h g₁ hm₁ g₂ hm₂ hi₁ hi₂ (by rw [ht₁, ht₂])]

theorem mKey_congr {Γ : OrderedPrefixCode} {K K' : KnowM} {y : ℕ}
    (h : mChainOf K' y = mChainOf K y) : mKey Γ K' y = mKey Γ K y := by
  unfold mKey
  rw [h]

/-! ## §2  Record-shape inversion (§9.7.8 item 3) -/

/-- **R side**: a minted element whose chain extends `P`'s by one R entry
is an R mint anchored at `P`, and the entry's tag is the tag of its
recorded right origin. -/
theorem rec_shape_R {Γ : OrderedPrefixCode} {K : KnowM} (inv : KInv Γ K)
    {x P : ℕ} {t : List ℕ} {d : ℕ}
    (hx : x ∈ mMintedIds K) (hP : P = 0 ∨ P ∈ mMintedIds K)
    (hch : mChainOf K x = mChainOf K P ++ [FMEntry.R t d]) :
    ∃ g, mRecOfId K x = some g ∧ g ∈ K ∧ g.ts = x ∧
      g.op = MOp.ins P Side.R ∧ g.lo = P ∧ t = tagK Γ K g.ro := by
  obtain ⟨g, hf, hgK, hgins, hgts⟩ := mRecOfId_of_minted hx
  have hcx : mChainOf K x = g.chain := mChainOf_eq_of_rec hf
  obtain ⟨p, sd, hop⟩ := mIsIns_shape hgins
  cases sd with
  | L =>
      exfalso
      obtain ⟨-, -, -, h4, -, -⟩ := inv.linkL g hgK p hop
      have h4' : mChainOf K P ++ [FMEntry.R t d]
          = mChainOf K p ++ [FMEntry.L (g.ts - p)] := by
        rw [← hch, hcx, h4]
      have hinj := List.append_inj' h4' rfl
      injection hinj.2 with h5
      exact FMEntry.noConfusion h5
  | R =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := inv.linkR g hgK p hop
      have h4' : mChainOf K P ++ [FMEntry.R t d]
          = mChainOf K p ++ [FMEntry.R (tagK Γ K g.ro) (g.ts - p)] := by
        rw [← hch, hcx, h4]
      have hinj := List.append_inj' h4' rfl
      have hpP : p = P := by
        have s1 := mChainOf_sum inv h3
        have s2 := mChainOf_sum inv hP
        rw [← hinj.1] at s1
        omega
      have h6 := hinj.2
      injection h6 with h7
      injection h7 with h8 h9
      exact ⟨g, hf, hgK, hgts, by rw [hop, hpP], by rw [← h1, hpP], h8⟩

/-- **L side**: a minted element whose chain extends `P`'s by one L entry
is an L mint with parent `P`, hence records `P` as its right origin. -/
theorem rec_shape_L {Γ : OrderedPrefixCode} {K : KnowM} (inv : KInv Γ K)
    {x P : ℕ} {d : ℕ}
    (hx : x ∈ mMintedIds K) (hP : P = 0 ∨ P ∈ mMintedIds K)
    (hch : mChainOf K x = mChainOf K P ++ [FMEntry.L d]) :
    ∃ g, mRecOfId K x = some g ∧ g ∈ K ∧ g.ts = x ∧
      g.op = MOp.ins P Side.L ∧ g.ro = some P := by
  obtain ⟨g, hf, hgK, hgins, hgts⟩ := mRecOfId_of_minted hx
  have hcx : mChainOf K x = g.chain := mChainOf_eq_of_rec hf
  obtain ⟨p, sd, hop⟩ := mIsIns_shape hgins
  cases sd with
  | R =>
      exfalso
      obtain ⟨-, -, -, h4, -⟩ := inv.linkR g hgK p hop
      have h4' : mChainOf K P ++ [FMEntry.L d]
          = mChainOf K p ++ [FMEntry.R (tagK Γ K g.ro) (g.ts - p)] := by
        rw [← hch, hcx, h4]
      have hinj := List.append_inj' h4' rfl
      injection hinj.2 with h5
      exact FMEntry.noConfusion h5
  | L =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := inv.linkL g hgK p hop
      have h4' : mChainOf K P ++ [FMEntry.L d]
          = mChainOf K p ++ [FMEntry.L (g.ts - p)] := by
        rw [← hch, hcx, h4]
      have hinj := List.append_inj' h4' rfl
      have hpP : p = P := by
        have s1 := mChainOf_sum inv (Or.inr h3)
        have s2 := mChainOf_sum inv hP
        rw [← hinj.1] at s1
        omega
      exact ⟨g, hf, hgK, hgts, by rw [hop, hpP], by rw [h1, hpP]⟩

/-! ## §3  The `RBk` bundle (§9.7.3) -/

/-- **The three backward mint-time clauses** on R-mint records (per-record
predicate over `(K, g)`, the shape of `SLC`):

* **(R0)** a root-anchored R mint recorded no successor;
* **(RSA)** a recorded successor displays after the anchor;
* **(RSuccL)** under an L-minted anchor with parent `P`, the recorded
  successor is `P` itself or lies in the subtree of a LATER L-sibling
  `s` of the anchor (the stable witness for the paper's third causal
  exclusion);
* **(RSuccR)** under an R-minted anchor with recorded successor `m`, the
  recorded successor displays no later than `m`. -/
def RBk (Γ : OrderedPrefixCode) (K : KnowM) (g : MRec) : Prop :=
  ∀ a, g.op = MOp.ins a Side.R →
    (a = 0 → g.ro = none) ∧
    (∀ n, g.ro = some n → mBefore Γ K a n) ∧
    (∀ ga P, mRecOfId K a = some ga → ga.op = MOp.ins P Side.L →
      ∃ n, g.ro = some n ∧
        (n = P ∨ ∃ s ds, s ∈ mMintedIds K ∧
          mChainOf K s = mChainOf K P ++ [FMEntry.L ds] ∧
          mBefore Γ K a s ∧ mChainOf K s <+: mChainOf K n)) ∧
    (∀ ga P m, mRecOfId K a = some ga → ga.op = MOp.ins P Side.R →
      ga.ro = some m →
      ∃ n, g.ro = some n ∧ (n = m ∨ mBefore Γ K n m))

/-- A nonempty candidate fold produces a successor. -/
theorem foldl_maxKey_isSome :
    ∀ (l : List (ℕ × List ℕ)) (acc : Option (ℕ × List ℕ)),
      (acc.isSome = true ∨ l ≠ []) → (l.foldl maxKey acc).isSome = true := by
  intro l
  induction l with
  | nil =>
      intro acc h
      rcases h with h | h
      · exact h
      · exact absurd rfl h
  | cons q tl ih =>
      intro acc h
      rw [List.foldl_cons]
      apply ih
      left
      cases acc with
      | none => simp [maxKey]
      | some b =>
          by_cases hk : keyLt b.2 q.2 = true <;> simp [maxKey, hk]

theorem succOfM_isSome_of_cand {Γ : OrderedPrefixCode} {K : KnowM}
    {a y : ℕ} (hy : (y, mKey Γ K y) ∈ succCandM Γ K a) :
    ∃ n, succOfM Γ K a = some n := by
  unfold succOfM
  have h := foldl_maxKey_isSome (succCandM Γ K a) none
    (Or.inr (List.ne_nil_of_mem hy))
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
  exact ⟨p.1, by rw [hp]; rfl⟩

/-- Any minted element after `a` is a successor candidate of `a`. -/
theorem cand_of_after {Γ : OrderedPrefixCode} {K : KnowM} {a y : ℕ}
    (hy : y ∈ mMintedIds K) (hafter : a = 0 ∨ mBefore Γ K a y) :
    (y, mKey Γ K y) ∈ succCandM Γ K a := by
  unfold succCandM
  rcases hafter with rfl | h
  · rw [if_pos rfl]
    exact List.mem_map.mpr ⟨y, hy, rfl⟩
  · by_cases h0 : a = 0
    · rw [if_pos h0]
      exact List.mem_map.mpr ⟨y, hy, rfl⟩
    · rw [if_neg h0]
      exact List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨y, hy, rfl⟩, by simpa using h⟩

/-- A knowledge whose root has a successor already has a minted R-child
of the root: the (R0) engine (§9.7.3). -/
theorem succ_zero_hasR {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {n : ℕ} (hs : succOfM Γ K 0 = some n) :
    hasRChildM K 0 = true := by
  have hn := succOfM_mem hs
  obtain ⟨gn, hnf, hnK, hnins, hnts⟩ := mRecOfId_of_minted hn
  obtain ⟨t, d, rest, hhead⟩ := chain_head_R inv gn.chain.length gn
    hnK hnins (Nat.le_refl _)
  have hpre : ([] ++ [FMEntry.R t d]) <+: gn.chain := by
    rw [hhead]
    exact ⟨rest, rfl⟩
  obtain ⟨h, hhK, hhins, hhchain⟩ := chain_prefix_minted inv
    gn.chain.length gn hnK hnins (Nat.le_refl _) [] (FMEntry.R t d) hpre
  have hhts : h.ts ∈ mMintedIds K :=
    List.mem_map.mpr ⟨h, List.mem_filter.mpr ⟨hhK, hhins⟩, rfl⟩
  have hch : mChainOf K h.ts = mChainOf K 0 ++ [FMEntry.R t d] := by
    rw [mChainOf_of_mem inv hhK hhins, hhchain, mChainOf_zero inv.pos]
  obtain ⟨g', -, hg'K, -, hg'op, -, -⟩ :=
    rec_shape_R inv hhts (Or.inl rfl) hch
  rw [hasRChildM_iff]
  exact ⟨g', hg'K, hg'op⟩

/-- **Step 0** (§9.7.4): an R-mint record's recorded successor displays
after the record's own node and is not in the anchor's subtree (an
R-headed trap would contradict the `LinkR` geometry clause). -/
theorem rmint_ro_after {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {g : MRec} (hg : g ∈ K) (hrbk : RBk Γ K g)
    {a n : ℕ} (hop : g.op = MOp.ins a Side.R) (hro : g.ro = some n) :
    mBefore Γ K g.ts n ∧ ¬ mChainOf K a <+: mChainOf K n := by
  have hgins : mIsIns g = true := by simp [mIsIns, hop]
  obtain ⟨h1, h2, h3, h4, h5⟩ := inv.linkR g hg a hop
  obtain ⟨hnm, hnodesc⟩ := h5 n hro
  have hgts : g.ts ∈ mMintedIds K :=
    List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, hgins⟩, rfl⟩
  have hgchain : mChainOf K g.ts = g.chain := mChainOf_of_mem inv hg hgins
  have hRSA := (hrbk a hop).2.1 n hro
  -- n is not in the anchor's subtree
  have hnsub : ¬ mChainOf K a <+: mChainOf K n := by
    intro hsub
    obtain ⟨ext, hext⟩ := hsub
    have hb : fmChainBefore (mChainOf K a) (mChainOf K a ++ ext) := by
      rw [hext]
      exact chainBefore_of_mBefore inv h3 (Or.inr hnm) hRSA
    obtain ⟨t', d', rest', hR⟩ := fm_ext_after_is_R hb
    exact hnodesc ⟨t', d', rest', by rw [← hext, hR, h1]⟩
  refine ⟨?_, hnsub⟩
  -- the node itself displays before its recorded successor
  by_contra hnb
  have hne : n ≠ g.ts := by
    rintro rfl
    exact hnsub ⟨[FMEntry.R (tagK Γ K g.ro) (g.ts - a)], by
      rw [hgchain, h4]⟩
  rcases mBefore_total inv (Or.inr hnm) (Or.inr hgts) hne with h | h
  · -- n before g.ts: a < n < g.ts traps n in the anchor's subtree
    exact hnsub (mTrap inv h3 (Or.inr hnm) (Or.inr hgts)
      (List.prefix_refl _) ⟨[FMEntry.R (tagK Γ K g.ro) (g.ts - a)], by
        rw [hgchain, h4]⟩ hRSA h)
  · exact hnb h

/-- **The mint-step proofs** (§9.7.3): the freshly generated insert
satisfies the three backward clauses over the mint knowledge. (R0),
(RSA), (RSuccR) are cheap; (RSuccL) is the `succ_R_desc_allL`-grade
argument: the argmax against the candidate parent, two convexity traps,
and ancestor closure. The paper's causal-minimality exclusions surface
here as stable existential witnesses over `K` alone. -/
theorem mGenInsAfter_rbk {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (inv3 : ∀ g ∈ K, RBk Γ K g) (rep : ℕ) {x a₀ : ℕ}
    (ha : a₀ = 0 ∨ a₀ ∈ mMintedIds K) :
    RBk Γ K (mGenInsAfter Γ K rep x a₀) := by
  rcases hs : succOfM Γ K a₀ with _ | n
  · -- no successor recorded: R mint, ro = none
    rw [mGenInsAfter_none hs]
    intro a hop
    injection hop with hpa hsd
    subst hpa
    refine ⟨fun _ => rfl, fun n hro => absurd hro (by simp), ?_, ?_⟩
    · -- (RSuccL): an L-minted anchor's parent is a candidate, so the
      -- successor could not have been none
      intro ga P hf hgaop
      exfalso
      obtain ⟨haminted, hgaK, hgains, hgats⟩ := minted_of_recOfId hf
      obtain ⟨l1, l2, l3, l4, l5, l6⟩ := inv.linkL ga hgaK P hgaop
      have hcha : mChainOf K a₀ = mChainOf K P ++ [FMEntry.L (ga.ts - P)] := by
        rw [mChainOf_eq_of_rec hf, l4]
      have haP : mBefore Γ K a₀ P :=
        mBefore_of_chainBefore inv (Or.inr haminted) (Or.inr l3)
          (by rw [hcha]; exact fmChainBefore.extL _ _ [])
      obtain ⟨n', hn'⟩ := succOfM_isSome_of_cand
        (cand_of_after l3 (Or.inr haP))
      rw [hs] at hn'
      exact absurd hn' (by simp)
    · -- (RSuccR): an R-minted anchor's recorded successor is a candidate
      intro ga P m hf hgaop hgaro
      exfalso
      obtain ⟨haminted, hgaK, hgains, hgats⟩ := minted_of_recOfId hf
      have hstep0 := rmint_ro_after inv hgaK (inv3 ga hgaK) hgaop hgaro
      have ham : mBefore Γ K a₀ m := by
        rw [← hgats]
        exact hstep0.1
      have hm : m ∈ mMintedIds K :=
        ((inv.linkR ga hgaK P hgaop).2.2.2.2 m hgaro).1
      obtain ⟨n', hn'⟩ := succOfM_isSome_of_cand
        (cand_of_after hm (Or.inr ham))
      rw [hs] at hn'
      exact absurd hn' (by simp)
  · cases hR : hasRChildM K a₀ with
    | true =>
        -- L mint: every backward clause is vacuous
        rw [mGenInsAfter_someTrue hs hR]
        intro a hop
        injection hop with hpa hsd
        exact Side.noConfusion hsd
    | false =>
        -- R mint, ro = some n
        rw [mGenInsAfter_someFalse hs hR]
        intro a hop
        injection hop with hpa hsd
        subst hpa
        have hn : n ∈ mMintedIds K := succOfM_mem hs
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- (R0): a root anchor with a successor has a minted R-child
          intro h0
          exfalso
          rw [h0] at hs hR
          rw [succ_zero_hasR inv hs] at hR
          exact Bool.noConfusion hR
        · -- (RSA)
          intro n' hro'
          injection hro' with hnn
          subst hnn
          have h0 : a₀ ≠ 0 := by
            intro h0
            rw [h0] at hs hR
            rw [succ_zero_hasR inv hs] at hR
            exact Bool.noConfusion hR
          exact succOfM_after_anchor hs h0
        · -- (RSuccL), the hard point
          intro ga P hf hgaop
          obtain ⟨haminted, hgaK, hgains, hgats⟩ := minted_of_recOfId hf
          obtain ⟨l1, l2, l3, l4, l5, l6⟩ := inv.linkL ga hgaK P hgaop
          have hcha : mChainOf K a₀
              = mChainOf K P ++ [FMEntry.L (ga.ts - P)] := by
            rw [mChainOf_eq_of_rec hf, l4]
          have haP : mBefore Γ K a₀ P :=
            mBefore_of_chainBefore inv (Or.inr haminted) (Or.inr l3)
              (by rw [hcha]; exact fmChainBefore.extL _ _ [])
          refine ⟨n, rfl, ?_⟩
          by_cases hnP : n = P
          · exact Or.inl hnP
          right
          -- the argmax against the candidate parent: n displays before P
          have hPn : mBefore Γ K n P := by
            have hnb := succOfM_max hs (cand_of_after l3 (Or.inr haP))
            rcases mBefore_total inv (Or.inr hn) (Or.inr l3) hnP with h | h
            · exact h
            · exfalso
              rw [h] at hnb
              exact Bool.noConfusion hnb
          have h0 : a₀ ≠ 0 := by
            have := minted_pos inv haminted
            omega
          have han : mBefore Γ K a₀ n := succOfM_after_anchor hs h0
          -- first trap: a₀ < n < P puts n in Subtree(P)
          have hsubP : mChainOf K P <+: mChainOf K n :=
            mTrap inv (Or.inr haminted) (Or.inr hn) (Or.inr l3)
              ⟨[FMEntry.L (ga.ts - P)], hcha.symm⟩ (List.prefix_refl _)
              han hPn
          obtain ⟨ext, hext⟩ := hsubP
          -- n before P: the extension is L-headed
          have hbnP : fmChainBefore (mChainOf K P ++ ext)
              (mChainOf K P) := by
            rw [hext]
            exact chainBefore_of_mBefore inv (Or.inr hn) (Or.inr l3) hPn
          obtain ⟨ds, rest, hLh⟩ := fm_ext_before_is_L hbnP
          -- the L-child of P on n's path: the stable witness
          obtain ⟨gn, hnf, hnK, hnins, hnts⟩ := mRecOfId_of_minted hn
          have hgnchain : mChainOf K n = gn.chain := mChainOf_eq_of_rec hnf
          have hpre : (mChainOf K P ++ [FMEntry.L ds]) <+: gn.chain := by
            rw [← hgnchain, ← hext, hLh]
            exact ⟨rest, by simp⟩
          obtain ⟨hS, hSK, hSins, hSchain⟩ := chain_prefix_minted inv
            gn.chain.length gn hnK hnins (Nat.le_refl _) _ _ hpre
          have hSts : hS.ts ∈ mMintedIds K :=
            List.mem_map.mpr ⟨hS, List.mem_filter.mpr ⟨hSK, hSins⟩, rfl⟩
          have hSch : mChainOf K hS.ts
              = mChainOf K P ++ [FMEntry.L ds] := by
            rw [mChainOf_of_mem inv hSK hSins, hSchain]
          have hSn : mChainOf K hS.ts <+: mChainOf K n := by
            rw [hSch, ← hext, hLh]
            exact ⟨rest, by simp⟩
          -- s ≠ a₀: else n would exhibit a minted R-child of a₀
          have hSne : hS.ts ≠ a₀ := by
            rintro heq
            have hsub : mChainOf K a₀ <+: mChainOf K n := by
              rw [← heq]
              exact hSn
            obtain ⟨e2, he2⟩ := hsub
            have hb2 : fmChainBefore (mChainOf K a₀)
                (mChainOf K a₀ ++ e2) := by
              rw [he2]
              exact chainBefore_of_mBefore inv (Or.inr haminted)
                (Or.inr hn) han
            obtain ⟨t2, d2, r2, hR2⟩ := fm_ext_after_is_R hb2
            have hhas : hasRChildM K a₀ = true :=
              hasR_of_R_descendant inv (Or.inr haminted) hn
                ⟨t2, d2, r2, by rw [← he2, hR2]⟩
            rw [hhas] at hR
            exact Bool.noConfusion hR
          -- a₀ < s: the second trap plus the length collapse
          have haS : mBefore Γ K a₀ hS.ts := by
            rcases mBefore_total inv (Or.inr haminted) (Or.inr hSts)
              (Ne.symm hSne) with h | h
            · exact h
            · exfalso
              have htr := mTrap inv (Or.inr hSts) (Or.inr haminted)
                (Or.inr hn) (List.prefix_refl _) hSn h han
              have hlen : (mChainOf K hS.ts).length
                  = (mChainOf K a₀).length := by
                rw [hSch, hcha]
                simp
              have hcheq : mChainOf K hS.ts = mChainOf K a₀ :=
                List.IsPrefix.eq_of_length htr hlen
              have s1 := mChainOf_sum inv (Or.inr hSts)
              have s2 := mChainOf_sum inv (Or.inr haminted)
              rw [hcheq] at s1
              exact hSne (by omega)
          exact ⟨hS.ts, ds, hSts, hSch, haS, hSn⟩
        · -- (RSuccR)
          intro ga P m hf hgaop hgaro
          obtain ⟨haminted, hgaK, hgains, hgats⟩ := minted_of_recOfId hf
          have hstep0 := rmint_ro_after inv hgaK (inv3 ga hgaK) hgaop hgaro
          have ham : mBefore Γ K a₀ m := by
            rw [← hgats]
            exact hstep0.1
          have hm : m ∈ mMintedIds K :=
            ((inv.linkR ga hgaK P hgaop).2.2.2.2 m hgaro).1
          refine ⟨n, rfl, ?_⟩
          by_cases hnm : n = m
          · exact Or.inl hnm
          · right
            have hnb := succOfM_max hs (cand_of_after hm (Or.inr ham))
            rcases mBefore_total inv (Or.inr (succOfM_mem hs)) (Or.inr hm)
              hnm with h | h
            · exact h
            · exfalso
              rw [h] at hnb
              exact Bool.noConfusion hnb

/-- Transport under knowledge growth: every clause ingredient, records,
chains, keys, display comparisons, prefixes, is about ids minted in the
old knowledge, so lookups and keys are stable. -/
theorem rbk_transport {Γ : OrderedPrefixCode} {K K' : KnowM} {g : MRec}
    (h : RBk Γ K g) (inv : KInv Γ K) (hlkR : LinkR Γ K g)
    (hpos' : ∀ r ∈ K', 1 ≤ r.ts)
    (hchain : ∀ y, y = 0 ∨ y ∈ mMintedIds K →
      mChainOf K' y = mChainOf K y)
    (hmem : ∀ y, y ∈ mMintedIds K → y ∈ mMintedIds K')
    (hrec : ∀ y, y ∈ mMintedIds K → mRecOfId K' y = mRecOfId K y) :
    RBk Γ K' g := by
  intro a hop
  obtain ⟨hR0, hRSA, hRSL, hRSR⟩ := h a hop
  obtain ⟨e1, e2, e3, e4, e5⟩ := hlkR a hop
  have hbef : ∀ {u v : ℕ}, (u = 0 ∨ u ∈ mMintedIds K) →
      (v = 0 ∨ v ∈ mMintedIds K) → mBefore Γ K u v → mBefore Γ K' u v := by
    intro u v hu hv huv
    show keyLt (mKey Γ K' v) (mKey Γ K' u) = true
    rw [mKey_congr (hchain v hv), mKey_congr (hchain u hu)]
    exact huv
  refine ⟨hR0, ?_, ?_, ?_⟩
  · intro n hro
    exact hbef e3 (Or.inr (e5 n hro).1) (hRSA n hro)
  · -- (RSuccL)
    intro ga P hf hgaop
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [mRecOfId_zero hpos'] at hf
      exact absurd hf (by simp)
    have ham : a ∈ mMintedIds K := by
      rcases e3 with h0 | h0
      · exact absurd h0 ha0
      · exact h0
    rw [hrec a ham] at hf
    obtain ⟨n, hro, hcase⟩ := hRSL ga P hf hgaop
    refine ⟨n, hro, ?_⟩
    have hnm : n ∈ mMintedIds K := (e5 n hro).1
    rcases hcase with heq | ⟨s, ds, hsm, hsch, hsaf, hspre⟩
    · exact Or.inl heq
    · obtain ⟨hgaKm, hgaK, hgains, hgats⟩ := minted_of_recOfId hf
      obtain ⟨-, -, l3, -, -, -⟩ := inv.linkL ga hgaK P hgaop
      refine Or.inr ⟨s, ds, hmem s hsm, ?_,
        hbef e3 (Or.inr hsm) hsaf, ?_⟩
      · rw [hchain s (Or.inr hsm), hchain P (Or.inr l3)]
        exact hsch
      · rw [hchain s (Or.inr hsm), hchain n (Or.inr hnm)]
        exact hspre
  · -- (RSuccR)
    intro ga P m hf hgaop hgaro
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [mRecOfId_zero hpos'] at hf
      exact absurd hf (by simp)
    have ham : a ∈ mMintedIds K := by
      rcases e3 with h0 | h0
      · exact absurd h0 ha0
      · exact h0
    rw [hrec a ham] at hf
    obtain ⟨n, hro, hcase⟩ := hRSR ga P m hf hgaop hgaro
    refine ⟨n, hro, ?_⟩
    rcases hcase with heq | hbe
    · exact Or.inl heq
    · obtain ⟨hgaKm, hgaK, hgains, hgats⟩ := minted_of_recOfId hf
      have hm : m ∈ mMintedIds K :=
        ((inv.linkR ga hgaK P hgaop).2.2.2.2 m hgaro).1
      exact Or.inr (hbef (Or.inr (e5 n hro).1) (Or.inr hm) hbe)

/-- **The supplementary reachability invariant** (§9.7.6): every record
of every reachable knowledge satisfies the backward bundle. Structured
exactly like `maxReach_inv2`; the fresh mint is `mGenInsAfter_rbk`. -/
theorem maxReach_inv3 (Γ : OrderedPrefixCode) {G : ℕ → KnowM}
    (h : MaxReach Γ G) : ∀ q, ∀ g ∈ G q, RBk Γ (G q) g := by
  induction h with
  | init =>
      intro q g hg
      exact absurd hg (by simp)
  | @ins G r x i hG hx hfresh hlam ih =>
      have inv := maxReach_inv Γ hG
      have ha : mAnchorAt Γ (G r) i = 0 ∨
          mAnchorAt Γ (G r) i ∈ mMintedIds (G r) := by
        rcases mAnchorAt_cases Γ (G r) i with h0 | hv
        · exact Or.inl h0
        · exact Or.inr (mView_sub_minted Γ (G r) _ hv)
      obtain ⟨hts, hins, -, hlkR, -⟩ :=
        mGenInsAfter_props Γ (inv.each r) r hx hlam ha
      have hposU : ∀ h ∈ G r ++ [mGenInsAt Γ (G r) r x i], 1 ≤ h.ts := by
        intro h hh
        rcases List.mem_append.mp hh with h' | h'
        · exact (inv.each r).pos h h'
        · rw [List.mem_singleton] at h'
          subst h'
          rw [show (mGenInsAt Γ (G r) r x i).ts = x from hts]
          exact hx
      have hchain : ∀ y, y = 0 ∨ y ∈ mMintedIds (G r) →
          mChainOf (G r ++ [mGenInsAt Γ (G r) r x i]) y
            = mChainOf (G r) y :=
        fun y hy => mChainOf_append_stable hy (inv.each r).pos
          (fun h hh => hposU h (List.mem_append_right _ hh))
      have hmemU : ∀ y, y ∈ mMintedIds (G r) →
          y ∈ mMintedIds (G r ++ [mGenInsAt Γ (G r) r x i]) := by
        intro y hy
        rw [mMintedIds_append]
        exact List.mem_append_left _ hy
      have hrecU : ∀ y, y ∈ mMintedIds (G r) →
          mRecOfId (G r ++ [mGenInsAt Γ (G r) r x i]) y
            = mRecOfId (G r) y := by
        intro y hy
        obtain ⟨gy, hfy, -, -, -⟩ := mRecOfId_of_minted hy
        rw [mRecOfId_append_left hfy, hfy]
      intro q g hg
      rcases mem_update_elimM hg with ⟨hq, hg'⟩ | ⟨hq, hg'⟩
      · rw [Function.update_of_ne hq]
        exact ih q g hg'
      · subst hq
        rw [Function.update_self]
        rcases List.mem_append.mp hg' with hgr | hgnew
        · exact rbk_transport (ih q g hgr) (inv.each q)
            ((inv.each q).linkR g hgr) hposU hchain hmemU hrecU
        · rw [List.mem_singleton] at hgnew
          subst hgnew
          exact rbk_transport (mGenInsAfter_rbk (inv.each q) (ih q) q ha)
            (inv.each q) hlkR hposU hchain hmemU hrecU
  | @del G r t i hG ht hfresh ih =>
      have inv := maxReach_inv Γ hG
      have hposU : ∀ h ∈ G r ++ [mGenDelAt Γ (G r) r t i], 1 ≤ h.ts := by
        intro h hh
        rcases List.mem_append.mp hh with h' | h'
        · exact (inv.each r).pos h h'
        · rw [List.mem_singleton] at h'
          subst h'
          exact ht
      have hchain : ∀ y, y = 0 ∨ y ∈ mMintedIds (G r) →
          mChainOf (G r ++ [mGenDelAt Γ (G r) r t i]) y
            = mChainOf (G r) y :=
        fun y _ => mChainOf_snoc_del rfl y
      have hmemU : ∀ y, y ∈ mMintedIds (G r) →
          y ∈ mMintedIds (G r ++ [mGenDelAt Γ (G r) r t i]) := by
        intro y hy
        rw [mMintedIds_append]
        exact List.mem_append_left _ hy
      have hrecU : ∀ y, y ∈ mMintedIds (G r) →
          mRecOfId (G r ++ [mGenDelAt Γ (G r) r t i]) y
            = mRecOfId (G r) y := by
        intro y hy
        obtain ⟨gy, hfy, -, -, -⟩ := mRecOfId_of_minted hy
        rw [mRecOfId_append_left hfy, hfy]
      intro q g hg
      rcases mem_update_elimM hg with ⟨hq, hg'⟩ | ⟨hq, hg'⟩
      · rw [Function.update_of_ne hq]
        exact ih q g hg'
      · subst hq
        rw [Function.update_self]
        rcases List.mem_append.mp hg' with hgr | hgnew
        · exact rbk_transport (ih q g hgr) (inv.each q)
            ((inv.each q).linkR g hgr) hposU hchain hmemU hrecU
        · rw [List.mem_singleton] at hgnew
          subst hgnew
          intro p hop
          exfalso
          simp [mGenDelAt] at hop
  | @sync G r r' hG ih =>
      have inv := maxReach_inv Γ hG
      have hposU : ∀ g ∈ syncM (G r) (G r'), 1 ≤ g.ts := by
        intro g hg
        rcases mem_syncM hg with h | h
        · exact (inv.each r).pos g h
        · exact (inv.each r').pos g h
      have hchainL : ∀ y, y = 0 ∨ y ∈ mMintedIds (G r) →
          mChainOf (syncM (G r) (G r')) y = mChainOf (G r) y := by
        intro y hy
        exact mChainOf_append_stable hy (inv.each r).pos
          (fun g hg => (inv.each r').pos g (List.mem_of_mem_filter hg))
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
      have hmemL : ∀ y, y ∈ mMintedIds (G r) →
          y ∈ mMintedIds (syncM (G r) (G r')) := by
        intro y hy
        rw [show syncM (G r) (G r')
          = G r ++ (G r').filter (fun g => decide (g ∉ G r)) from rfl,
          mMintedIds_append]
        exact List.mem_append_left _ hy
      have hmemR : ∀ y, y ∈ mMintedIds (G r') →
          y ∈ mMintedIds (syncM (G r) (G r')) :=
        fun y hy => minted_syncM_right hy
      have hrecL : ∀ y, y ∈ mMintedIds (G r) →
          mRecOfId (syncM (G r) (G r')) y = mRecOfId (G r) y := by
        intro y hy
        obtain ⟨gy, hfy, -, -, -⟩ := mRecOfId_of_minted hy
        rw [show syncM (G r) (G r')
          = G r ++ (G r').filter (fun g => decide (g ∉ G r)) from rfl,
          mRecOfId_append_left hfy, hfy]
      have hrecR : ∀ y, y ∈ mMintedIds (G r') →
          mRecOfId (syncM (G r) (G r')) y = mRecOfId (G r') y := by
        intro y hy
        exact mRecOfId_agree
          (by
            intro g hg g' hg' hi hi' hteq
            rcases mem_syncM hg with h | h
            · exact inv.cross r r' g h g' hg' hi hi' hteq
            · exact inv.cross r' r' g h g' hg' hi hi' hteq)
          (minted_syncM_right hy) hy
      intro q g hg
      rcases mem_update_elimM hg with ⟨hq, hg'⟩ | ⟨hq, hg'⟩
      · rw [Function.update_of_ne hq]
        exact ih q g hg'
      · subst hq
        rw [Function.update_self]
        rcases mem_syncM hg' with hgr | hgr'
        · exact rbk_transport (ih q g hgr) (inv.each q)
            ((inv.each q).linkR g hgr) hposU hchainL hmemL hrecL
        · exact rbk_transport (ih r' g hgr') (inv.each r')
            ((inv.each r').linkR g hgr') hposU hchainR hmemR hrecR

#print axioms maxReach_inv3

/-! ## §4  The loDesc-to-prefix lemma -/

theorem mLoOf_iterate_zero {K : KnowM} (hpos : ∀ g ∈ K, 1 ≤ g.ts) :
    ∀ nn : ℕ, (mLoOf K)^[nn] 0 = 0 := by
  intro nn
  induction nn with
  | zero => rfl
  | succ n ihn => rw [Function.iterate_succ_apply, mLoOf_zero hpos, ihn]

/-- **loDesc to prefix** (§9.7.8 item 5): a left-origin-walk ancestor's
chain is a chain prefix, the only fact about `mLoDesc` the discharge
needs (loShape makes every walk step strip an R-then-all-L block). -/
theorem loDesc_prefix {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (inv2 : ∀ g ∈ K, SLC Γ K g) :
    ∀ (nn c p : ℕ), c ∈ mMintedIds K → (mLoOf K)^[nn] c = p →
      mChainOf K p <+: mChainOf K c := by
  intro nn
  induction nn with
  | zero =>
      intro c p hc hit
      rw [Function.iterate_zero_apply] at hit
      subst hit
      exact List.prefix_refl _
  | succ n ihn =>
      intro c p hc hit
      rw [Function.iterate_succ_apply] at hit
      obtain ⟨hloOr, t, d, ls, hdec, hall⟩ := loShape_of_inv inv inv2 hc
      rcases hloOr with h0 | hm
      · rw [h0, mLoOf_iterate_zero inv.pos] at hit
        subst hit
        rw [mChainOf_zero inv.pos]
        exact List.nil_prefix
      · exact List.IsPrefix.trans (ihn (mLoOf K c) p hm hit)
          ⟨FMEntry.R t d :: ls, hdec.symm⟩

theorem not_loDesc_of_not_prefix {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (inv2 : ∀ g ∈ K, SLC Γ K g)
    {c p : ℕ} (hc : c ∈ mMintedIds K)
    (hnp : ¬ mChainOf K p <+: mChainOf K c) : ¬ mLoDesc K c p := by
  rintro ⟨nn, hit⟩
  exact hnp (loDesc_prefix inv inv2 nn c p hc hit)

/-! ## §5  The discharge -/

/-- A minted element's key is never the end tag (it ends in the marker). -/
theorem mKey_ne_end {Γ : OrderedPrefixCode} {K : KnowM} {x : ℕ} :
    mKey Γ K x ≠ [0] := by
  unfold mKey sKey
  cases hc : fmCoordOf Γ (mChainOf K x) with
  | nil =>
      intro h
      rw [List.nil_append] at h
      injection h with h1 h2
      omega
  | cons y ys =>
      intro h
      rw [List.cons_append] at h
      injection h with h1 h2
      exact absurd h2 (by simp)

/-- The end tag is lexicographically below every minted key: real keys
have a nonzero head (§9.7.5, the beta1 tie analysis). -/
theorem keyLt_key_end_false {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {x : ℕ} (hx : x ∈ mMintedIds K) :
    keyLt (mKey Γ K x) [0] = false := by
  have hw := mChainOf_wfparts inv (Or.inr hx)
  have ht := tagOK_key Γ hw.1 hw.2 (mChainOf_ne_nil inv hx)
  rcases ht with h0 | ⟨hd, c, heq, hne0, -, -, -⟩
  · exact absurd h0 mKey_ne_end
  · show keyLt (mKey Γ K x) [0] = false
    rw [show mKey Γ K x = (hd :: c) ++ [3] from heq, List.cons_append]
    simp [keyLt, Nat.pos_of_ne_zero hne0]

/-- **The beta1 witness** (§9.7.5): an R-sibling `E ≠ A` of `A` under the
anchor, holding a minted in-between `c` of `(A, B)` in its subtree,
records as right origin an element strictly between the anchor and `B`
that escapes the anchor's subtree. Stated over MINTED in-betweens (`c`'s
liveness is nowhere used), so the beta0 ladder can call it with `n_D` in
place of `c`. -/
theorem beta1_witness {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (inv3 : ∀ g ∈ K, RBk Γ K g)
    {A B a : ℕ} {gA : MRec} (hfA : mRecOfId K A = some gA)
    (hopA : gA.op = MOp.ins a Side.R) (hroA : gA.ro = some B)
    (hlast : ∀ D ∈ mMintedIds K, mRoOf K D = some B → D ≠ A →
      mBefore Γ K D A)
    {E : ℕ} {tE : List ℕ} {dE : ℕ} (hEm : E ∈ mMintedIds K)
    (hchE : mChainOf K E = mChainOf K a ++ [FMEntry.R tE dE])
    (hEA : E ≠ A)
    {c : ℕ} (hcm : c ∈ mMintedIds K)
    (hEc : mChainOf K E <+: mChainOf K c)
    (hAc : mBefore Γ K A c) (hcB : mBefore Γ K c B) :
    ∃ C ∈ mMintedIds K, mBefore Γ K a C ∧ mBefore Γ K C B ∧
      ¬ mChainOf K a <+: mChainOf K C := by
  obtain ⟨hAm, hgAK, hgAins, hgAts⟩ := minted_of_recOfId hfA
  obtain ⟨r1, r2, r3, r4, r5⟩ := inv.linkR gA hgAK a hopA
  have hBm : B ∈ mMintedIds K := (r5 B hroA).1
  have hchA : mChainOf K A = mChainOf K a ++
      [FMEntry.R (tagK Γ K gA.ro) (gA.ts - a)] := by
    rw [mChainOf_eq_of_rec hfA, r4]
  -- A displays before E (else the trap collapses E onto A)
  have hAE : mBefore Γ K A E := by
    rcases mBefore_total inv (Or.inr hAm) (Or.inr hEm) (Ne.symm hEA)
      with h | h
    · exact h
    · exfalso
      have htr := mTrap inv (Or.inr hEm) (Or.inr hAm) (Or.inr hcm)
        (List.prefix_refl _) hEc h hAc
      have hlen : (mChainOf K E).length = (mChainOf K A).length := by
        rw [hchE, hchA]
        simp
      have hcheq := List.IsPrefix.eq_of_length htr hlen
      have s1 := mChainOf_sum inv (Or.inr hEm)
      have s2 := mChainOf_sum inv (Or.inr hAm)
      rw [hcheq] at s1
      exact hEA (by omega)
  -- E's record: an R mint at the anchor, tag = tag of its origin
  obtain ⟨gE, hfE, hgEK, hgEts, hgEop, hgElo, hgEtag⟩ :=
    rec_shape_R inv hEm r3 hchE
  obtain ⟨q1, q2, q3, q4, q5⟩ := inv.linkR gE hgEK a hgEop
  -- sibling divergence: A before E reads off the entry order
  have hchainAE : fmChainBefore
      (mChainOf K a ++ [FMEntry.R (tagK Γ K gA.ro) (gA.ts - a)])
      (mChainOf K a ++ FMEntry.R tE dE :: []) := by
    rw [← hchA, ← hchE]
    exact chainBefore_of_mBefore inv (Or.inr hAm) (Or.inr hEm) hAE
  have hdivg := fm_R_sibling_inv hchainAE
  have hEntry : keyLt (tagK Γ K gA.ro) tE = true ∨
      (tagK Γ K gA.ro = tE ∧ gA.ts - a < dE) := by
    rcases hdivg with h | ⟨ht, hd⟩
    · exact h
    · exfalso
      have hcheq : mChainOf K E = mChainOf K A := by
        rw [hchE, hchA, ht, hd]
      have s1 := mChainOf_sum inv (Or.inr hEm)
      have s2 := mChainOf_sum inv (Or.inr hAm)
      rw [hcheq] at s1
      exact hEA (by omega)
  have htagA : tagK Γ K gA.ro = mKey Γ K B := by rw [hroA]; rfl
  -- the end tag is ruled out
  rcases hroE : gE.ro with _ | nE
  · exfalso
    rw [hroE] at hgEtag
    have htE0 : tE = [0] := by rw [hgEtag]; rfl
    rcases hEntry with h | ⟨ht, -⟩
    · rw [htagA, htE0, keyLt_key_end_false inv hBm] at h
      exact Bool.noConfusion h
    · rw [htagA, htE0] at ht
      exact mKey_ne_end ht
  · rw [hroE] at hgEtag
    have hgEtag' : tE = mKey Γ K nE := by rw [hgEtag]; rfl
    have hnEm : nE ∈ mMintedIds K := (q5 nE hroE).1
    rcases hEntry with hkey | ⟨ht, -⟩
    · -- strict: C := ro(E), before B, after a, outside the subtree
      have hnEB : mBefore Γ K nE B := by
        show keyLt (mKey Γ K B) (mKey Γ K nE) = true
        rw [← htagA, ← hgEtag']
        exact hkey
      have hanE : mBefore Γ K a nE := ((inv3 gE hgEK) a hgEop).2.1 nE hroE
      have hnEnot : ¬ mChainOf K a <+: mChainOf K nE := by
        intro hsub
        obtain ⟨ext, hext⟩ := hsub
        have hb : fmChainBefore (mChainOf K a) (mChainOf K a ++ ext) := by
          rw [hext]
          exact chainBefore_of_mBefore inv r3 (Or.inr hnEm) hanE
        obtain ⟨t2, d2, r2', hR2⟩ := fm_ext_after_is_R hb
        exact (q5 nE hroE).2 ⟨t2, d2, r2', by
          rw [hgElo, ← hR2]
          exact hext.symm⟩
      exact ⟨nE, hnEm, hanE, hnEB, hnEnot⟩
    · -- tie: ro(E) = B makes E a LAST violation
      exfalso
      rw [htagA, hgEtag'] at ht
      have hBn : B = nE := mKey_inj inv (Or.inr hBm) (Or.inr hnEm) ht
      have hroE' : mRoOf K E = some B := by
        rw [mRoOf_eq hfE, hroE, hBn]
      exact mBefore_asymm hAE (hlast E hEm hroE' hEA)

/-- **Condition (2) from the invariant bundles** (§9.7.4/9.7.5): the L
case is consecutive outright (any live in-between manufactures a LAST
violation through (RSuccL)); the R case exhibits the state-definable
exception witness (alpha / beta1 / beta0-direct / beta0-ladder) at any
live in-between, so a premise pair that is refused the exception has no
live in-between at all. -/
theorem backwardNIM_of_inv {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (inv2 : ∀ g ∈ K, SLC Γ K g)
    (inv3 : ∀ g ∈ K, RBk Γ K g) :
    BackwardNIExcM Γ K := by
  intro A hA B hB hliveA hliveB hro hlast hnexc
  obtain ⟨gA, hfA, hgAK, hgAins, hgAts⟩ := mRecOfId_of_minted hA
  have hroA : gA.ro = some B := by
    rw [← mRoOf_eq hfA]
    exact hro
  obtain ⟨p, sd, hopA⟩ := mIsIns_shape hgAins
  cases sd with
  | L =>
      -- ===== the L case: consecutive outright =====
      obtain ⟨l1, l2, l3, l4, l5, l6⟩ := inv.linkL gA hgAK p hopA
      have hpB : B = p := by
        rw [hroA] at l1
        injection l1
      subst hpB
      have hchA : mChainOf K A = mChainOf K B ++ [FMEntry.L (gA.ts - B)] := by
        rw [mChainOf_eq_of_rec hfA, l4]
      have hAB : mBefore Γ K A B :=
        mBefore_of_chainBefore inv (Or.inr hA) (Or.inr l3)
          (by rw [hchA]; exact fmChainBefore.extL _ _ [])
      refine ⟨hAB, ?_⟩
      rintro c hlivec ⟨hAc, hcB⟩
      have hcm : c ∈ mMintedIds K := mView_sub_minted Γ K c hlivec
      -- c is trapped in Subtree(B), before B: its extension is L-headed
      have hsubB : mChainOf K B <+: mChainOf K c :=
        mTrap inv (Or.inr hA) (Or.inr hcm) (Or.inr l3)
          ⟨[FMEntry.L (gA.ts - B)], hchA.symm⟩ (List.prefix_refl _) hAc hcB
      obtain ⟨ext, hext⟩ := hsubB
      have hbcB : fmChainBefore (mChainOf K B ++ ext) (mChainOf K B) := by
        rw [hext]
        exact chainBefore_of_mBefore inv (Or.inr hcm) (Or.inr l3) hcB
      obtain ⟨ds, rest, hLh⟩ := fm_ext_before_is_L hbcB
      -- S := the L-child of B on c's path
      obtain ⟨gc, hcf, hcK, hcins, hcts⟩ := mRecOfId_of_minted hcm
      have hgcchain : mChainOf K c = gc.chain := mChainOf_eq_of_rec hcf
      have hpreS : (mChainOf K B ++ [FMEntry.L ds]) <+: gc.chain := by
        rw [← hgcchain, ← hext, hLh]
        exact ⟨rest, by simp⟩
      obtain ⟨hS, hSK, hSins, hSchain⟩ := chain_prefix_minted inv
        gc.chain.length gc hcK hcins (Nat.le_refl _) _ _ hpreS
      have hSts : hS.ts ∈ mMintedIds K :=
        List.mem_map.mpr ⟨hS, List.mem_filter.mpr ⟨hSK, hSins⟩, rfl⟩
      have hSch : mChainOf K hS.ts = mChainOf K B ++ [FMEntry.L ds] := by
        rw [mChainOf_of_mem inv hSK hSins, hSchain]
      have hSc : mChainOf K hS.ts <+: mChainOf K c := by
        rw [hSch, ← hext, hLh]
        exact ⟨rest, by simp⟩
      obtain ⟨gS, hfS, hgSK, hgSts, hgSop, hgSro⟩ :=
        rec_shape_L inv hSts (Or.inr l3) hSch
      have hroS : mRoOf K hS.ts = some B := by
        rw [mRoOf_eq hfS, hgSro]
      -- S collapses onto A
      have hSA : hS.ts = A := by
        by_contra hne
        rcases mBefore_total inv (Or.inr hSts) (Or.inr hA) hne with h | h
        · have htr := mTrap inv (Or.inr hSts) (Or.inr hA) (Or.inr hcm)
            (List.prefix_refl _) hSc h hAc
          have hlen : (mChainOf K hS.ts).length
              = (mChainOf K A).length := by
            rw [hSch, hchA]
            simp
          have hcheq := List.IsPrefix.eq_of_length htr hlen
          have s1 := mChainOf_sum inv (Or.inr hSts)
          have s2 := mChainOf_sum inv (Or.inr hA)
          rw [hcheq] at s1
          exact hne (by omega)
        · exact mBefore_asymm h (hlast hS.ts hSts hroS hne)
      -- c sits R-headedly below A: D := the R-child of A on c's path
      rw [hSA] at hSc
      obtain ⟨ext2, hext2⟩ := hSc
      have hbAc : fmChainBefore (mChainOf K A) (mChainOf K A ++ ext2) := by
        rw [hext2]
        exact chainBefore_of_mBefore inv (Or.inr hA) (Or.inr hcm) hAc
      obtain ⟨tD, dD, restD, hRD⟩ := fm_ext_after_is_R hbAc
      have hpreD : (mChainOf K A ++ [FMEntry.R tD dD]) <+: gc.chain := by
        rw [← hgcchain, ← hext2, hRD]
        exact ⟨restD, by simp⟩
      obtain ⟨hD, hDK, hDins, hDchain⟩ := chain_prefix_minted inv
        gc.chain.length gc hcK hcins (Nat.le_refl _) _ _ hpreD
      have hDts : hD.ts ∈ mMintedIds K :=
        List.mem_map.mpr ⟨hD, List.mem_filter.mpr ⟨hDK, hDins⟩, rfl⟩
      have hDch : mChainOf K hD.ts = mChainOf K A ++ [FMEntry.R tD dD] := by
        rw [mChainOf_of_mem inv hDK hDins, hDchain]
      obtain ⟨gD, hfD, hgDK, hgDts, hgDop, hgDlo, hgDtag⟩ :=
        rec_shape_R inv hDts (Or.inr hA) hDch
      have hAD : mBefore Γ K A hD.ts :=
        mBefore_of_chainBefore inv (Or.inr hA) (Or.inr hDts)
          (by rw [hDch]; exact fmChainBefore.extR _ _ _ [])
      -- consume (RSuccL) at D: both outcomes are LAST violations
      obtain ⟨n, hron, hcase⟩ :=
        ((inv3 gD hgDK) A hgDop).2.2.1 gA B hfA hopA
      rcases hcase with heq | ⟨s, ds', hsm, hsch, hsaf, hspre⟩
      · have hroD : mRoOf K hD.ts = some B := by
          rw [mRoOf_eq hfD, hron, heq]
        have hDA : hD.ts ≠ A := (mBefore_ne hAD).symm
        exact mBefore_asymm hAD (hlast hD.ts hDts hroD hDA)
      · obtain ⟨gs, hfs, hgsK, hgsts, hgsop, hgsro⟩ :=
          rec_shape_L inv hsm (Or.inr l3) hsch
        have hros : mRoOf K s = some B := by
          rw [mRoOf_eq hfs, hgsro]
        have hsA : s ≠ A := (mBefore_ne hsaf).symm
        exact mBefore_asymm hsaf (hlast s hsm hros hsA)
  | R =>
      -- ===== the R case: the exception witness =====
      obtain ⟨r1, r2, r3, r4, r5⟩ := inv.linkR gA hgAK p hopA
      have hstep0 := rmint_ro_after inv hgAK (inv3 gA hgAK) hopA hroA
      have hAB : mBefore Γ K A B := by
        rw [← hgAts]
        exact hstep0.1
      refine ⟨hAB, ?_⟩
      rintro c hlivec ⟨hAc, hcB⟩
      apply hnexc
      have hcm : c ∈ mMintedIds K := mView_sub_minted Γ K c hlivec
      have hBm : B ∈ mMintedIds K := (r5 B hroA).1
      have hloA : mLoOf K A = p := by
        rw [mLoOf_eq hfA, ← r1]
      have hchA : mChainOf K A = mChainOf K p ++
          [FMEntry.R (tagK Γ K gA.ro) (gA.ts - p)] := by
        rw [mChainOf_eq_of_rec hfA, r4]
      have hpA : mBefore Γ K p A :=
        mBefore_of_chainBefore inv r3 (Or.inr hA)
          (by rw [hchA]; exact fmChainBefore.extR _ _ _ [])
      -- the dichotomy: distinct left origins, for free
      have hlodif : mLoOf K A ≠ mLoOf K B := by
        rw [hloA]
        intro heq
        obtain ⟨-, t', d', ls', hdecB, -⟩ := loShape_of_inv inv inv2 hB
        rw [← heq] at hdecB
        exact hstep0.2 ⟨FMEntry.R t' d' :: ls', hdecB.symm⟩
      refine ⟨hlodif, ?_⟩
      rw [hloA]
      -- the witness function, §9.7.5
      by_cases hsub : mChainOf K p <+: mChainOf K c
      · -- c is in the anchor's subtree: E := the R-child of p on c's path
        obtain ⟨ext, hext⟩ := hsub
        have hbc : fmChainBefore (mChainOf K p) (mChainOf K p ++ ext) := by
          rw [hext]
          exact chainBefore_of_mBefore inv r3 (Or.inr hcm)
            (mBefore_trans hpA hAc)
        obtain ⟨tE, dE, restE, hRE⟩ := fm_ext_after_is_R hbc
        obtain ⟨gc, hcf, hcK, hcins, hcts⟩ := mRecOfId_of_minted hcm
        have hgcchain : mChainOf K c = gc.chain := mChainOf_eq_of_rec hcf
        have hpreE : (mChainOf K p ++ [FMEntry.R tE dE]) <+: gc.chain := by
          rw [← hgcchain, ← hext, hRE]
          exact ⟨restE, by simp⟩
        obtain ⟨hE, hEK, hEins, hEchain⟩ := chain_prefix_minted inv
          gc.chain.length gc hcK hcins (Nat.le_refl _) _ _ hpreE
        have hEts : hE.ts ∈ mMintedIds K :=
          List.mem_map.mpr ⟨hE, List.mem_filter.mpr ⟨hEK, hEins⟩, rfl⟩
        have hEch : mChainOf K hE.ts
            = mChainOf K p ++ [FMEntry.R tE dE] := by
          rw [mChainOf_of_mem inv hEK hEins, hEchain]
        have hEc : mChainOf K hE.ts <+: mChainOf K c := by
          rw [hEch, ← hext, hRE]
          exact ⟨restE, by simp⟩
        by_cases hEA : hE.ts = A
        · -- ===== beta0: descend once through D =====
          rw [hEA] at hEc
          obtain ⟨ext2, hext2⟩ := hEc
          have hbAc2 : fmChainBefore (mChainOf K A)
              (mChainOf K A ++ ext2) := by
            rw [hext2]
            exact chainBefore_of_mBefore inv (Or.inr hA) (Or.inr hcm) hAc
          obtain ⟨tD, dD, restD, hRD⟩ := fm_ext_after_is_R hbAc2
          have hpreD : (mChainOf K A ++ [FMEntry.R tD dD]) <+: gc.chain := by
            rw [← hgcchain, ← hext2, hRD]
            exact ⟨restD, by simp⟩
          obtain ⟨hD, hDK, hDins, hDchain⟩ := chain_prefix_minted inv
            gc.chain.length gc hcK hcins (Nat.le_refl _) _ _ hpreD
          have hDts : hD.ts ∈ mMintedIds K :=
            List.mem_map.mpr ⟨hD, List.mem_filter.mpr ⟨hDK, hDins⟩, rfl⟩
          have hDch : mChainOf K hD.ts
              = mChainOf K A ++ [FMEntry.R tD dD] := by
            rw [mChainOf_of_mem inv hDK hDins, hDchain]
          obtain ⟨gD, hfD, hgDK, hgDts, hgDop, hgDlo, hgDtag⟩ :=
            rec_shape_R inv hDts (Or.inr hA) hDch
          have hAD : mBefore Γ K A hD.ts :=
            mBefore_of_chainBefore inv (Or.inr hA) (Or.inr hDts)
              (by rw [hDch]; exact fmChainBefore.extR _ _ _ [])
          -- consume (RSuccR) at D over the R-minted anchor A
          obtain ⟨nD, hronD, hcaseD⟩ :=
            ((inv3 gD hgDK) A hgDop).2.2.2 gA p B hfA hopA hroA
          have hnDB : mBefore Γ K nD B := by
            rcases hcaseD with heq | h
            · exfalso
              have hroD : mRoOf K hD.ts = some B := by
                rw [mRoOf_eq hfD, hronD, heq]
              have hDA : hD.ts ≠ A := (mBefore_ne hAD).symm
              exact mBefore_asymm hAD (hlast hD.ts hDts hroD hDA)
            · exact h
          obtain ⟨w1, w2, w3, w4, w5⟩ := inv.linkR gD hgDK A hgDop
          have hnDm : nD ∈ mMintedIds K := (w5 nD hronD).1
          have hAnD : mBefore Γ K A nD :=
            ((inv3 gD hgDK) A hgDop).2.1 nD hronD
          have hpnD : mBefore Γ K p nD := mBefore_trans hpA hAnD
          by_cases hsub2 : mChainOf K p <+: mChainOf K nD
          · -- ===== beta0-ladder: re-aim through E' =====
            obtain ⟨ext3, hext3⟩ := hsub2
            have hbn : fmChainBefore (mChainOf K p)
                (mChainOf K p ++ ext3) := by
              rw [hext3]
              exact chainBefore_of_mBefore inv r3 (Or.inr hnDm) hpnD
            obtain ⟨tE', dE', restE', hRE'⟩ := fm_ext_after_is_R hbn
            obtain ⟨gn, hnf, hnK, hnins, hnts⟩ := mRecOfId_of_minted hnDm
            have hgnchain : mChainOf K nD = gn.chain :=
              mChainOf_eq_of_rec hnf
            have hpreE' : (mChainOf K p ++ [FMEntry.R tE' dE'])
                <+: gn.chain := by
              rw [← hgnchain, ← hext3, hRE']
              exact ⟨restE', by simp⟩
            obtain ⟨hE', hE'K, hE'ins, hE'chain⟩ := chain_prefix_minted inv
              gn.chain.length gn hnK hnins (Nat.le_refl _) _ _ hpreE'
            have hE'ts : hE'.ts ∈ mMintedIds K :=
              List.mem_map.mpr ⟨hE', List.mem_filter.mpr ⟨hE'K, hE'ins⟩,
                rfl⟩
            have hE'ch : mChainOf K hE'.ts
                = mChainOf K p ++ [FMEntry.R tE' dE'] := by
              rw [mChainOf_of_mem inv hE'K hE'ins, hE'chain]
            have hE'nD : mChainOf K hE'.ts <+: mChainOf K nD := by
              rw [hE'ch, ← hext3, hRE']
              exact ⟨restE', by simp⟩
            have hE'A : hE'.ts ≠ A := by
              rintro heq
              rw [heq] at hE'nD
              obtain ⟨ext4, hext4⟩ := hE'nD
              have hb4 : fmChainBefore (mChainOf K A)
                  (mChainOf K A ++ ext4) := by
                rw [hext4]
                exact chainBefore_of_mBefore inv (Or.inr hA)
                  (Or.inr hnDm) hAnD
              obtain ⟨t4, d4, r4', hR4⟩ := fm_ext_after_is_R hb4
              exact (w5 nD hronD).2 ⟨t4, d4, r4', by
                rw [hgDlo, ← hR4]
                exact hext4.symm⟩
            obtain ⟨C, hCm, hpC, hCB, hCnot⟩ := beta1_witness inv inv3
              hfA hopA hroA hlast hE'ts hE'ch hE'A hnDm hE'nD hAnD hnDB
            exact ⟨C, hCm, hpC, hCB,
              not_loDesc_of_not_prefix inv inv2 hCm hCnot⟩
          · -- ===== beta0-direct: C := the recorded origin of D =====
            exact ⟨nD, hnDm, hpnD, hnDB,
              not_loDesc_of_not_prefix inv inv2 hnDm hsub2⟩
        · -- ===== beta1: E is a genuine sibling =====
          obtain ⟨C, hCm, hpC, hCB, hCnot⟩ := beta1_witness inv inv3
            hfA hopA hroA hlast hEts hEch hEA hcm hEc hAc hcB
          exact ⟨C, hCm, hpC, hCB,
            not_loDesc_of_not_prefix inv inv2 hCm hCnot⟩
      · -- ===== alpha: C := c itself =====
        exact ⟨c, hcm, mBefore_trans hpA hAc, hcB,
          not_loDesc_of_not_prefix inv inv2 hcm hsub⟩

/-- **The condition-(2) gap of Theorem 9 is DISCHARGED**: backward
non-interleaving with the (corrected, minted-witness) Lemma-5 exception
holds at every replica of every reachable FugueMax configuration. -/
theorem fuguemax_backward_ni (Γ : OrderedPrefixCode) :
    FugueMaxBackwardNonInterleaving Γ := by
  intro G hG r
  exact backwardNIM_of_inv ((maxReach_inv Γ hG).each r)
    (maxReach_inv2 Γ hG r) (maxReach_inv3 Γ hG r)

#print axioms fuguemax_backward_ni

/-! ## §6  SPOTs (PASS+FAIL, hand-derived from §9.7.2/9.7.5/9.7.7)

The four delete variants, witness values pinned. All expected values
are hand-derived, never taken from the implementation under test. -/

namespace BackwardSPOT

def gDel (K : KnowM) (rep t i : ℕ) : KnowM :=
  K ++ [mGenDelAt unaryCode K rep t i]

/-! ### Figure 7 + delete 4 (§9.7.2, the live-reading countermodel) -/

/-- Figure 7 (display `[3,6,7,4,5]`) with B = 4 deleted (index 3). -/
def kFigD : KnowM := gDel FugueMaxSPOT.kFig 0 99 3

/-- PASS: the visible document after the delete. -/
theorem fig7_del_display : mView unaryCode kFigD = [3, 6, 7, 5] := by
  native_decide

/-- FAIL pin: the delete is not a no-op. -/
theorem fig7_del_not_noop : mView unaryCode kFigD ≠ [3, 6, 7, 4, 5] := by
  native_decide

/-- PASS: the condition-(2) premise pair (A, B) = (6, 5) with distinct
left origins (the exception's first conjunct, concretely). -/
theorem fig7_del_pair :
    (mRoOf kFigD 6 = some 5 ∧ mLoOf kFigD 6 = 3 ∧ mLoOf kFigD 5 = 0) := by
  native_decide

/-- PASS: **the dead witness**: C = 4 is minted but not visible, sits
strictly between lo(6) = 3 and B = 5 in the strong order, and its
left-origin walk starts at 0 (not at 3: no descent). -/
theorem fig7_del_witness :
    (4 ∈ mMintedIds kFigD ∧ 4 ∉ mView unaryCode kFigD ∧
      keyLt (mKey unaryCode kFigD 4) (mKey unaryCode kFigD 3) = true ∧
      keyLt (mKey unaryCode kFigD 5) (mKey unaryCode kFigD 4) = true ∧
      mLoOf kFigD 4 = 0) := by
  native_decide

/-- FAIL pin (the §9.7.2 refutation content): the pair (6, 5) is NOT
consecutive, 7 is a LIVE in-between, and every live strict in-between
(6 and 7) is a left-origin child of 3, so no LIVE witness exists. -/
theorem fig7_del_no_live_witness :
    (7 ∈ mView unaryCode kFigD ∧
      keyLt (mKey unaryCode kFigD 7) (mKey unaryCode kFigD 6) = true ∧
      keyLt (mKey unaryCode kFigD 5) (mKey unaryCode kFigD 7) = true ∧
      mLoOf kFigD 6 = 3 ∧ mLoOf kFigD 7 = 3) := by
  native_decide

/-! ### Figure 7, ADVERSE mint order + delete 4 -/

/-- The adverse mint order (display `[3,7,6,4,5]`) with 4 deleted. -/
def kFigAD : KnowM := gDel FugueMaxSPOT.kFigA 1 98 3

/-- PASS: the visible document; the premise pair is (7, 5) here. -/
theorem fig7a_del_display : mView unaryCode kFigAD = [3, 7, 6, 5] := by
  native_decide

/-- PASS: the pair and the same dead witness 4. -/
theorem fig7a_del_pair_witness :
    (mRoOf kFigAD 7 = some 5 ∧ mLoOf kFigAD 7 = 3 ∧
      4 ∈ mMintedIds kFigAD ∧ 4 ∉ mView unaryCode kFigAD ∧
      keyLt (mKey unaryCode kFigAD 4) (mKey unaryCode kFigAD 3) = true ∧
      keyLt (mKey unaryCode kFigAD 5) (mKey unaryCode kFigAD 4) = true) := by
  native_decide

/-- FAIL pin: the delete is not a no-op. -/
theorem fig7a_del_not_noop :
    mView unaryCode kFigAD ≠ [3, 7, 6, 4, 5] := by native_decide

/-! ### The beta0-direct construction + delete 2 (§9.7.5) -/

def b1 : KnowM := FugueMaxSPOT.gIns [] 0 1 0
def b2 : KnowM := FugueMaxSPOT.gIns [] 1 2 0
def b3 : KnowM := FugueMaxSPOT.gIns [] 2 3 0

/-- 4 = R-child of 1 minted in view {1, 3}: ro(4) = 3. -/
def bA : KnowM := FugueMaxSPOT.gIns (syncM b1 b3) 0 4 1

/-- 5 = R-child of 4 minted in view {1, 3, 4, 2}: ro(5) = 2, which
escapes Subtree(1) directly. -/
def bDir : KnowM := FugueMaxSPOT.gIns (syncM bA b2) 0 5 2

def bDirD : KnowM := gDel bDir 0 99 3

/-- PASS: the direct construction's display. -/
theorem bdir_display : mView unaryCode bDir = [1, 4, 5, 2, 3] := by
  native_decide

/-- PASS: the beta0-direct route, pinned record by record: the premise
pair (4, 3); D = 5 anchored at 4; D's recorded origin 2 = the witness,
whose walk starts at 0 (outside Subtree(1)). -/
theorem bdir_route :
    (mRoOf bDir 4 = some 3 ∧ mLoOf bDir 4 = 1 ∧ mRoOf bDir 5 = some 2 ∧
      mLoOf bDir 5 = 4 ∧ mLoOf bDir 2 = 0) := by
  native_decide

/-- FAIL pin: D's recorded origin is NOT B, the argmax escaped strictly
past it (kills the tempting `ro(D) = B` reading, which would be a LAST
violation, not a witness). -/
theorem bdir_ro5_not_B : mRoOf bDir 5 ≠ some 3 := by native_decide

/-- PASS: after deleting 2 the witness is dead but still minted, still
strictly between lo(4) = 1 and B = 3. -/
theorem bdir_del_witness :
    (mView unaryCode bDirD = [1, 4, 5, 3] ∧ 2 ∈ mMintedIds bDirD ∧
      2 ∉ mView unaryCode bDirD ∧
      keyLt (mKey unaryCode bDirD 2) (mKey unaryCode bDirD 1) = true ∧
      keyLt (mKey unaryCode bDirD 3) (mKey unaryCode bDirD 2) = true) := by
  native_decide

/-- FAIL pin: the delete is not a no-op. -/
theorem bdir_del_not_noop : mView unaryCode bDirD ≠ [1, 4, 5, 2, 3] := by
  native_decide

/-! ### The beta0-ladder construction + delete 2 (§9.7.5) -/

/-- 6 = R-child of 1 minted in view {1, 2}: ro(6) = 2. -/
def bL6 : KnowM := FugueMaxSPOT.gIns (syncM b1 b2) 0 6 1

/-- 7 = R-child of 4 minted in view {1, 3, 4, 2, 6}: ro(7) = 6, which
lands INSIDE Subtree(1), the ladder must re-aim through E' = 6. -/
def bLad : KnowM := FugueMaxSPOT.gIns (syncM bA bL6) 0 7 2

def bLadD : KnowM := gDel bLad 0 99 4

/-- PASS: the ladder construction's display. -/
theorem blad_display : mView unaryCode bLad = [1, 4, 7, 6, 2, 3] := by
  native_decide

/-- PASS: the beta0-ladder route: n_D = ro(7) = 6 sits inside Subtree(1)
(lo(6) = 1), and the re-aim through E' = 6 returns C = ro(6) = 2, which
escapes (lo(2) = 0). -/
theorem blad_route :
    (mRoOf bLad 4 = some 3 ∧ mRoOf bLad 7 = some 6 ∧ mLoOf bLad 6 = 1 ∧
      mRoOf bLad 6 = some 2 ∧ mLoOf bLad 2 = 0) := by
  native_decide

/-- FAIL pin: the first hop does NOT escape, lo(n_D) is 1, not 0: the
ladder is genuinely two steps (kills the `beta0-direct always suffices`
reading). -/
theorem blad_first_hop_not_escape : mLoOf bLad 6 ≠ 0 := by native_decide

/-- PASS: after deleting 2 the ladder's witness is dead but minted,
strictly between lo(4) = 1 and B = 3. -/
theorem blad_del_witness :
    (mView unaryCode bLadD = [1, 4, 7, 6, 3] ∧ 2 ∈ mMintedIds bLadD ∧
      2 ∉ mView unaryCode bLadD ∧
      keyLt (mKey unaryCode bLadD 2) (mKey unaryCode bLadD 1) = true ∧
      keyLt (mKey unaryCode bLadD 3) (mKey unaryCode bLadD 2) = true) := by
  native_decide

/-- FAIL pin: the delete is not a no-op. -/
theorem blad_del_not_noop :
    mView unaryCode bLadD ≠ [1, 4, 7, 6, 2, 3] := by native_decide

end BackwardSPOT

#print axioms BackwardSPOT.fig7_del_witness
#print axioms BackwardSPOT.blad_route

/-! ## §7  The capstone: full adapted W-K Theorem 9 -/

/-- **FugueMax is maximally non-interleaving** (Weidner-Kleppmann
arXiv:2305.00583v3 Theorem 9, adapted statement over `MaxReach`, strict
reading, the minted-witness Lemma-5 exception): forward
non-interleaving, backward non-interleaving with exceptions, and the
same-origin low-first tiebreak all hold at every replica of every
reachable FugueMax configuration. Conditions (1) and (3) are
`fuguemax_forward_ni` and `fuguemax_same_origin_low_first`; condition
(2) is this file's `fuguemax_backward_ni`. -/
theorem fuguemax_maximally_noninterleaving (Γ : OrderedPrefixCode) :
    FugueMaxMaximallyNonInterleaving Γ :=
  fuguemax_theorem9_of_backward (fuguemax_backward_ni Γ)

#print axioms fuguemax_maximally_noninterleaving

end Sal.MRDTs.Instances.SidedEmbedRGA
