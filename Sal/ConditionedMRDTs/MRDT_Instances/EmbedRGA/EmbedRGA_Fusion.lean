import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_MultiEpoch

/-!
# Spine fusion — iteration two of the embed GC (#97)

The v1 compaction (`compactEliasDelta`, drop dead ranges + rank-renumber)
recovers 1.1x–1.8x on real traces; the residual cost is **spine depth**: a
typing run mints a delta-1 chain, and after edits the interior of that chain is
dead-but-kept (kept only because a live descendant hangs off its tail — the
`[9]` node of the CompactEliasDelta SPOT). Every dead level still costs a
codeword. **Fusion** removes the dead levels themselves.

**The map** (recoding note, Addendum 2 + errata). A *fusible spine* is a
maximal chain of dead unary nodes `d₁, …, d_k` (`k ≥ 2`, errata 1) below the
cut, each with exactly one child branch (counting in-flight), no in-flight op
anchored at any `d_i`, and no declared in-flight coordinate ending at one
(errata 3). Write `Q = P ++ [d₁, …, d_k]` for the whole dead spine chain and
`Q' = P ++ [d₁]` for its head. Fusion collapses the spine to its head:

    fuseChain Q Q' c = if Q <+: c then Q' ++ c.drop |Q| else c

i.e. every coordinate *through* the spine (`Q <+: c`) keeps its parent block
`P`, keeps the head codeword `d₁` (this is the **head group codeword**: post
rank-renumber the head delta *is* its ordinal, errata 2), and drops the dead
interior `d₂…d_k`; everything else is unchanged. Composition with the v1
rank-renumber (`StablePrefixMap.comp`) is the full iteration-two map.

**Why order survives (the H2 argument), three comparison classes.**
`fuseChain_chainBefore` proves `chainBefore` is preserved; H2 (`ord`) then
follows through `chainBefore_display` and totality, exactly as
`remapChain_keyLt` does for the rank pass. The three classes are the three
cases of the proof:

* **class 1 — both through the spine** (`Q <+: a`, `Q <+: b`): the common block
  `Q` is replaced wholesale by `Q'` on both, so the divergence in the shared
  tail is untouched (`chainBefore_append_left_iff`);
* **class 2 — block vs the head's siblings** (one through, one not): the verdict
  is decided at the head level `Q'`, which fusion keeps verbatim (the block
  inherits `d₁`'s rank), so replacing the interior below `Q'` cannot move it
  (`chainBefore_prefix_indep`);
* **class 3 — the sentinel corner is vacuous**: dead spine interior nodes carry
  no records, so no coordinate ends inside `Q` (`hthru`: on the domain, passing
  `Q'` forces passing all of `Q`), and no anchor-vs-extension comparison is
  lost.

Kernel-clean; the SPOT pins a deep-dead-spine directed case (reads and
coordinate-length drop) with the order-breaking reparent as the FAIL companion.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode PosChain coordOf coordOf_append key keyLt
  keyLt_irrefl keyLt_asymm chainBefore chainBefore_cons chainBefore_total
  chainBefore_display eliasDeltaCode unaryCode)

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §1 `chainBefore` inversion and prefix-stability lemmas

The fusion order argument is entirely about how `chainBefore` (the birth-tree
display order on chains) behaves when a common block is replaced or a shared
prefix is extended. Everything is derived from one inversion lemma. -/

/-- Inversion of `chainBefore` into its two verdict shapes (ancestor / newer
sibling). Re-proved locally so the file is self-contained. -/
theorem chainBefore_inv {u v : List ℕ} (h : chainBefore u v) :
    (∃ ext, ext ≠ [] ∧ v = u ++ ext) ∨
    (∃ p d e c1 c2, e < d ∧ u = p ++ d :: c1 ∧ v = p ++ e :: c2) := by
  cases h with
  | ancestor ch ext hne => exact Or.inl ⟨ext, hne, rfl⟩
  | newer p d e c1 c2 hlt => exact Or.inr ⟨p, d, e, c1, c2, hlt, rfl, rfl⟩

/-- No chain precedes the empty chain (the empty coordinate is the root, first
in display order). -/
theorem not_chainBefore_nil (l : List ℕ) : ¬ chainBefore l [] := by
  intro h
  rcases chainBefore_inv h with ⟨ext, hne, hext⟩ | ⟨p, d, e, c1, c2, _, _, hv⟩
  · exact hne (List.append_eq_nil_iff.mp hext.symm).2
  · simp at hv

/-- Stripping a common head preserves the chain order. -/
theorem chainBefore_cons_inv {x : ℕ} {a b : List ℕ}
    (h : chainBefore (x :: a) (x :: b)) : chainBefore a b := by
  rcases chainBefore_inv h with ⟨ext, hne, hext⟩ | ⟨p, d, e, c1, c2, hlt, hu, hv⟩
  · have hb : b = a ++ ext := by simpa using hext
    subst hb
    exact chainBefore.ancestor a ext hne
  · cases p with
    | nil =>
        simp only [List.nil_append] at hu hv
        injection hu with hxd _
        injection hv with hxe _
        omega
    | cons y p' =>
        simp only [List.cons_append] at hu hv
        injection hu with _ ha
        injection hv with _ hb
        subst ha; subst hb
        exact chainBefore.newer p' d e c1 c2 hlt

/-- With distinct heads the verdict is decided by the head comparison alone:
the newer (larger) head precedes. -/
theorem chainBefore_head_ne {c cy : ℕ} {X Y : List ℕ} (hne : c ≠ cy) :
    chainBefore (c :: X) (cy :: Y) ↔ cy < c := by
  constructor
  · intro h
    rcases chainBefore_inv h with ⟨ext, _, hext⟩ | ⟨p, d, e, c1, c2, hlt, hu, hv⟩
    · exfalso; apply hne; injection hext with h1 _; exact h1.symm
    · cases p with
      | nil =>
          simp only [List.nil_append] at hu hv
          injection hu with hcd _
          injection hv with hce _
          omega
      | cons z p' =>
          simp only [List.cons_append] at hu hv
          injection hu with hcz _
          injection hv with hcyz _
          exact absurd (hcz.trans hcyz.symm) hne
  · intro h
    exact chainBefore.newer [] c cy X Y h

/-- A common block prepended to both sides is invisible to the display order. -/
theorem chainBefore_append_left_iff (u r r' : List ℕ) :
    chainBefore (u ++ r) (u ++ r') ↔ chainBefore r r' := by
  induction u with
  | nil => simp
  | cons x xs ih =>
      constructor
      · intro h
        rw [List.cons_append, List.cons_append] at h
        exact ih.mp (chainBefore_cons_inv h)
      · intro h
        rw [List.cons_append, List.cons_append]
        exact chainBefore_cons x (ih.mpr h)

/-- **Prefix stability (classes 2/3).** If `x` and `x'` share a prefix `w`
that `y` does *not* extend, then the display verdict of either against `y` is
the same: the divergence lies strictly inside `w`, where `x` and `x'` agree.
Both argument positions, by one induction on `w`. -/
theorem chainBefore_prefix_indep :
    ∀ (w x x' y : List ℕ), w <+: x → w <+: x' → ¬ (w <+: y) →
      (chainBefore x y ↔ chainBefore x' y) ∧ (chainBefore y x ↔ chainBefore y x')
  | [], _, _, _, _, _, hy => absurd List.nil_prefix hy
  | c :: w', x, x', y, hx, hx', hy => by
      obtain ⟨tx, rfl⟩ := hx
      obtain ⟨tx', rfl⟩ := hx'
      cases y with
      | nil =>
          refine ⟨⟨fun h => absurd h (not_chainBefore_nil _),
                   fun h => absurd h (not_chainBefore_nil _)⟩, ?_⟩
          exact ⟨fun _ => chainBefore.ancestor [] _ (by simp),
                 fun _ => chainBefore.ancestor [] _ (by simp)⟩
      | cons cy y' =>
          by_cases hcc : c = cy
          · subst hcc
            have hy' : ¬ (w' <+: y') :=
              fun hp => hy (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
            obtain ⟨ihL, ihR⟩ := chainBefore_prefix_indep w' (w' ++ tx)
              (w' ++ tx') y' (List.prefix_append _ _) (List.prefix_append _ _) hy'
            refine ⟨⟨fun h => chainBefore_cons c (ihL.mp (chainBefore_cons_inv h)),
                     fun h => chainBefore_cons c (ihL.mpr (chainBefore_cons_inv h))⟩,
                    ⟨fun h => chainBefore_cons c (ihR.mp (chainBefore_cons_inv h)),
                     fun h => chainBefore_cons c (ihR.mpr (chainBefore_cons_inv h))⟩⟩
          · refine ⟨⟨fun h => (chainBefore_head_ne hcc).mpr ((chainBefore_head_ne hcc).mp h),
                     fun h => (chainBefore_head_ne hcc).mpr ((chainBefore_head_ne hcc).mp h)⟩,
                    ⟨fun h => (chainBefore_head_ne (Ne.symm hcc)).mpr
                        ((chainBefore_head_ne (Ne.symm hcc)).mp h),
                     fun h => (chainBefore_head_ne (Ne.symm hcc)).mpr
                        ((chainBefore_head_ne (Ne.symm hcc)).mp h)⟩⟩

/-! ## §2 The fusion chain map and its order preservation

`fuseChain Q Q'` collapses the dead spine chain `Q` to its head `Q'` (`Q' <+: Q`)
on every chain passing through it, and is the identity elsewhere. The domain
hypothesis `hthru` is the geometric content of "a fusible spine has exactly one
child branch and no interior records": on the coordinates at hand, reaching the
head `Q'` forces passing the whole spine `Q`. -/

/-- The fusion chain map: keep the head `Q'`, drop the dead interior of `Q`. -/
def fuseChain (Q Q' : List ℕ) (c : List ℕ) : List ℕ :=
  if Q.isPrefixOf c then Q' ++ c.drop Q.length else c

/-- Fusion preserves positivity: the head `Q'` (a prefix of the positive `Q`)
and the surviving tail are positive. -/
theorem fuseChain_pos {Q Q' : List ℕ} (hQ' : Q' <+: Q) (hQpos : PosChain Q)
    {ch : List ℕ} (hch : PosChain ch) : PosChain (fuseChain Q Q' ch) := by
  simp only [fuseChain]
  by_cases hQc : Q.isPrefixOf ch
  · rw [if_pos hQc]
    intro d hd
    rw [List.mem_append] at hd
    rcases hd with hdQ' | hdr
    · obtain ⟨w, hw⟩ := hQ'
      exact hQpos d (hw ▸ List.mem_append_left _ hdQ')
    · exact hch d (List.mem_of_mem_drop hdr)
  · rw [if_neg hQc]; exact hch

/-- **The order-preservation core (the three-class H2 argument).** On the
domain, fusion preserves the birth-tree display order `chainBefore`. -/
theorem fuseChain_chainBefore {Q Q' : List ℕ} {𝒟 : List ℕ → Prop}
    (hQ' : Q' <+: Q) (hthru : ∀ c, 𝒟 c → Q' <+: c → Q <+: c)
    {a b : List ℕ} (ha : 𝒟 a) (hb : 𝒟 b) (hab : chainBefore a b) :
    chainBefore (fuseChain Q Q' a) (fuseChain Q Q' b) := by
  simp only [fuseChain]
  by_cases hQa : Q.isPrefixOf a
  · by_cases hQb : Q.isPrefixOf b
    · -- class 1: both through — replace the common block wholesale
      rw [if_pos hQa, if_pos hQb]
      obtain ⟨ra, hra⟩ := List.isPrefixOf_iff_prefix.mp hQa
      obtain ⟨rb, hrb⟩ := List.isPrefixOf_iff_prefix.mp hQb
      have hda : a.drop Q.length = ra := by rw [← hra, List.drop_left]
      have hdb : b.drop Q.length = rb := by rw [← hrb, List.drop_left]
      rw [hda, hdb]
      rw [← hra, ← hrb] at hab
      exact (chainBefore_append_left_iff Q' ra rb).mpr
        ((chainBefore_append_left_iff Q ra rb).mp hab)
    · -- class 2: a through, b not — verdict decided at the head Q'
      rw [if_pos hQa, if_neg hQb]
      obtain ⟨ra, hra⟩ := List.isPrefixOf_iff_prefix.mp hQa
      have hda : a.drop Q.length = ra := by rw [← hra, List.drop_left]
      rw [hda]
      have hnQ'b : ¬ Q' <+: b := fun hp =>
        hQb (List.isPrefixOf_iff_prefix.mpr (hthru b hb hp))
      have hQ'a : Q' <+: a := hQ'.trans (List.isPrefixOf_iff_prefix.mp hQa)
      obtain ⟨ihL, _⟩ := chainBefore_prefix_indep Q' a (Q' ++ ra) b
        hQ'a (List.prefix_append _ _) hnQ'b
      exact ihL.mp hab
  · by_cases hQb : Q.isPrefixOf b
    · -- class 2 (mirror): b through, a not
      rw [if_neg hQa, if_pos hQb]
      obtain ⟨rb, hrb⟩ := List.isPrefixOf_iff_prefix.mp hQb
      have hdb : b.drop Q.length = rb := by rw [← hrb, List.drop_left]
      rw [hdb]
      have hnQ'a : ¬ Q' <+: a := fun hp =>
        hQa (List.isPrefixOf_iff_prefix.mpr (hthru a ha hp))
      have hQ'b : Q' <+: b := hQ'.trans (List.isPrefixOf_iff_prefix.mp hQb)
      obtain ⟨_, ihR⟩ := chainBefore_prefix_indep Q' b (Q' ++ rb) a
        hQ'b (List.prefix_append _ _) hnQ'a
      exact ihR.mp hab
    · -- neither through: identity
      rw [if_neg hQa, if_neg hQb]
      exact hab

/-! ## §3 The induced bit-string map, aligned to `fuseChain` on coordinates -/

/-- The fusion re-map on coordinates: rewrite the dead spine's codeword block
`coordOf Q` to `coordOf Q'`, keeping the tail bit-for-bit. Total on all bit
strings. -/
def fuseBits (Γ : OrderedPrefixCode) (Q Q' : List ℕ) (c : List Bool) : List Bool :=
  if (coordOf Γ Q).isPrefixOf c
  then coordOf Γ Q' ++ c.drop (coordOf Γ Q).length
  else c

/-- **Master alignment**: on any positive chain's coordinate the bit-string
fusion *is* the chain fusion — the spine boundary lands on a codeword boundary
(prefix-freedom, `coordOf_prefix_align`) and the tail is copied verbatim. No
domain hypothesis. -/
theorem fuseBits_coordOf (Γ : OrderedPrefixCode) {Q Q' : List ℕ}
    (hQpos : PosChain Q) {ch : List ℕ} (hch : PosChain ch) :
    fuseBits Γ Q Q' (coordOf Γ ch) = coordOf Γ (fuseChain Q Q' ch) := by
  simp only [fuseBits, fuseChain]
  by_cases hQc : Q.isPrefixOf ch
  · have hpc : Q <+: ch := List.isPrefixOf_iff_prefix.mp hQc
    have hcoordpre : coordOf Γ Q <+: coordOf Γ ch := coordOf_prefix_of_prefix Γ hpc
    rw [if_pos (List.isPrefixOf_iff_prefix.mpr hcoordpre), if_pos hQc]
    obtain ⟨r, hr⟩ := hpc
    rw [← hr]
    simp only [coordOf_append, List.drop_left]
  · have hnpc : ¬ Q <+: ch := fun hp => hQc (List.isPrefixOf_iff_prefix.mpr hp)
    have hncoord : ¬ coordOf Γ Q <+: coordOf Γ ch :=
      fun hp => hnpc (coordOf_prefix_align Γ hQpos hch hp)
    rw [if_neg (fun h => hncoord (List.isPrefixOf_iff_prefix.mp h)), if_neg hQc]

/-! ## §4 The fusion bundle: H3 by construction, H2 by §2/§3, H1 derived -/

/-- A prefix of `chA ++ [δ]` is either a prefix of `chA` or the whole thing. -/
theorem prefix_snoc_cases {Q chA : List ℕ} {δ : ℕ}
    (h : Q <+: chA ++ [δ]) : Q <+: chA ∨ Q = chA ++ [δ] := by
  rcases Nat.lt_or_ge Q.length (chA ++ [δ]).length with hlt | hge
  · left
    have hle : Q.length ≤ chA.length := by
      simp only [List.length_append, List.length_singleton] at hlt; omega
    exact List.prefix_of_prefix_length_le h (List.prefix_append chA [δ]) hle
  · right
    obtain ⟨w, hw⟩ := h
    have hwnil : w = [] := by
      have hl := congrArg List.length hw
      rw [List.length_append] at hl
      exact List.eq_nil_of_length_eq_zero (by omega)
    rw [hwnil, List.append_nil] at hw
    exact hw

/-- The fusion mint domain: one fresh positive delta on an at-hand anchor chain,
the minted node distinct from the spine (a genuine beyond-cut node, never the
dead spine tail — the class-3 vacuity, `errata 3`). -/
def fuseMintAt (Γ : OrderedPrefixCode) (Q : List ℕ) (𝒟 : List ℕ → Prop)
    (π : List Bool) (δ : ℕ) : Prop :=
  1 ≤ δ ∧ ∃ chA, π = coordOf Γ chA ∧ PosChain chA ∧ 𝒟 (chA ++ [δ]) ∧ chA ++ [δ] ≠ Q

theorem fuseDom_chain {Γ : OrderedPrefixCode} {Q : List ℕ} {𝒟 : List ℕ → Prop}
    {c : List Bool}
    (h : compactRest Γ 𝒟 c ∨ ∃ π δ, fuseMintAt Γ Q 𝒟 π δ ∧ c = π ++ Γ.enc δ) :
    ∃ ch, 𝒟 ch ∧ c = coordOf Γ ch := by
  rcases h with ⟨ch, hch, rfl⟩ | ⟨π, δ, ⟨_, chA, rfl, _, hD, -⟩, rfl⟩
  · exact ⟨ch, hch, rfl⟩
  · exact ⟨chA ++ [δ], hD, by rw [coordOf_append]; simp [coordOf]⟩

/-- **The fusion compaction bundle.** Collapsing a fusible dead spine `Q` to its
head `Q'` (`Q' <+: Q`) induces a `StablePrefixMap` through the coordinate fusion
`fuseBits`. H3 (`ext`) holds by construction (the re-map rewrites the stable
spine prefix wholesale and never touches a beyond-cut minted delta); H2 (`ord`)
is `fuseChain_chainBefore` composed through the chain-lex theorem; H1 is derived
by the bundle. -/
def fuseSPM (Γ : OrderedPrefixCode) (Q Q' : List ℕ) (𝒟 : List ℕ → Prop)
    (hQpos : PosChain Q) (hQ' : Q' <+: Q)
    (hDpos : ∀ ch, 𝒟 ch → PosChain ch)
    (hthru : ∀ c, 𝒟 c → Q' <+: c → Q <+: c) :
    StablePrefixMap Γ where
  f := fuseBits Γ Q Q'
  Rest := compactRest Γ 𝒟
  MintAt := fuseMintAt Γ Q 𝒟
  ext := by
    rintro π δ ⟨hδ, chA, rfl, hposA, hD, hne⟩
    have hposm : PosChain (chA ++ [δ]) := hDpos _ hD
    have hcoord : coordOf Γ chA ++ Γ.enc δ = coordOf Γ (chA ++ [δ]) := by
      rw [coordOf_append]; simp [coordOf]
    rw [hcoord, fuseBits_coordOf Γ hQpos hposm, fuseBits_coordOf Γ hQpos hposA]
    have hfc : fuseChain Q Q' (chA ++ [δ]) = fuseChain Q Q' chA ++ [δ] := by
      simp only [fuseChain]
      by_cases hQa : Q.isPrefixOf chA
      · have hd : Q.isPrefixOf (chA ++ [δ]) := by
          rw [List.isPrefixOf_iff_prefix] at hQa ⊢
          exact hQa.trans (List.prefix_append _ _)
        rw [if_pos hQa, if_pos hd]
        have hlen : Q.length ≤ chA.length :=
          (List.isPrefixOf_iff_prefix.mp hQa).length_le
        rw [List.drop_append_of_le_length hlen, ← List.append_assoc]
      · have hnd : ¬ Q.isPrefixOf (chA ++ [δ]) := by
          rw [List.isPrefixOf_iff_prefix]
          intro hp
          rcases prefix_snoc_cases hp with h1 | h2
          · exact hQa (List.isPrefixOf_iff_prefix.mpr h1)
          · exact hne h2.symm
        rw [if_neg hQa, if_neg hnd]
    rw [hfc, coordOf_append]; simp [coordOf]
  ord := by
    intro c c' hc hc'
    obtain ⟨ch, hch, rfl⟩ := fuseDom_chain hc
    obtain ⟨ch', hch', rfl⟩ := fuseDom_chain hc'
    rw [fuseBits_coordOf Γ hQpos (hDpos _ hch),
        fuseBits_coordOf Γ hQpos (hDpos _ hch')]
    by_cases heq : ch = ch'
    · subst heq; rw [keyLt_irrefl, keyLt_irrefl]
    · have hpos := hDpos ch hch
      have hpos' := hDpos ch' hch'
      have hfpos : PosChain (fuseChain Q Q' ch) := fuseChain_pos hQ' hQpos hpos
      have hfpos' : PosChain (fuseChain Q Q' ch') := fuseChain_pos hQ' hQpos hpos'
      rcases chainBefore_total heq with hb | hb
      · rw [keyLt_asymm (chainBefore_display Γ hpos hpos' hb),
            keyLt_asymm (chainBefore_display Γ hfpos hfpos'
              (fuseChain_chainBefore hQ' hthru hch hch' hb))]
      · rw [chainBefore_display Γ hpos' hpos hb,
            chainBefore_display Γ hfpos' hfpos
              (fuseChain_chainBefore hQ' hthru hch' hch hb)]

/-! ## §5 The reads headlines: fusion alone, and fusion after the rank pass

Both are direct re-invocations of the re-coding cluster's T2
(`eRecode_reads_identical`) on the fusion bundle and on its composite with the
v1 rank-renumber pass. -/

/-- **Fusion preserves every read.** Folding a beyond-cut continuation (its
mints translated) over the fused cut state reads exactly as the uncompacted
run: dropping the dead spine levels is invisible. -/
theorem fuse_reads_identical {Γ : OrderedPrefixCode} {Q Q' : List ℕ}
    {𝒟 : List ℕ → Prop} (hQpos : PosChain Q) (hQ' : Q' <+: Q)
    (hDpos : ∀ ch, 𝒟 ch → PosChain ch)
    (hthru : ∀ c, 𝒟 c → Q' <+: c → Q <+: c)
    (s : EState α) (τ : List (Op (EOp α)))
    (hs : ∀ x ∈ s, (fuseSPM Γ Q Q' 𝒟 hQpos hQ' hDpos hthru).Dom x.2.2)
    (hτ : ∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a →
      (fuseSPM Γ Q Q' 𝒟 hQpos hQ' hDpos hthru).MintAt π (o.1 - a)) :
    (E Γ α).query (applySeq (E Γ α).toCRDTSig
        (eRemapSt (fuseBits Γ Q Q') s)
        (τ.map (eRemapOp (fuseBits Γ Q Q')))) ()
      = (E Γ α).query (applySeq (E Γ α).toCRDTSig s τ) () :=
  eRecode_reads_identical (fuseSPM Γ Q Q' 𝒟 hQpos hQ' hDpos hthru) s τ hs hτ

/-- **The iteration-two headline (composed): rank-renumber, then fusion,
preserves every read.** `F` is the v1 rank-renumber pass (`compactRanked`),
`fuseSPM …` the fusion, composed at their shared surviving domain
`(Rest', MintAt')` via `StablePrefixMap.comp` (the between-pass compatibility
`h` is what the settled-cut protocol supplies). The two-pass coordinate
translation is `fuseBits ∘ F.f`, and the reads of any beyond-cut continuation
survive both passes. -/
theorem compactThenFuse_reads {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    {Q Q' : List ℕ} {𝒟 : List ℕ → Prop} (hQpos : PosChain Q) (hQ' : Q' <+: Q)
    (hDpos : ∀ ch, 𝒟 ch → PosChain ch)
    (hthru : ∀ c, 𝒟 c → Q' <+: c → Q <+: c)
    (Rest' : List Bool → Prop) (MintAt' : List Bool → ℕ → Prop)
    (h : CompatOn F (fuseSPM Γ Q Q' 𝒟 hQpos hQ' hDpos hthru) Rest' MintAt')
    (s : EState α) (τ : List (Op (EOp α)))
    (hs : ∀ x ∈ s,
      (F.comp (fuseSPM Γ Q Q' 𝒟 hQpos hQ' hDpos hthru) Rest' MintAt' h).Dom x.2.2)
    (hτ : ∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ), o.2.2 = EOp.ins e π a →
      (F.comp (fuseSPM Γ Q Q' 𝒟 hQpos hQ' hDpos hthru) Rest' MintAt' h).MintAt π
        (o.1 - a)) :
    (E Γ α).query (applySeq (E Γ α).toCRDTSig
        (eRemapSt (fuseBits Γ Q Q' ∘ F.f) s)
        (τ.map (eRemapOp (fuseBits Γ Q Q' ∘ F.f)))) ()
      = (E Γ α).query (applySeq (E Γ α).toCRDTSig s τ) () :=
  eRecode_reads_identical
    (F.comp (fuseSPM Γ Q Q' 𝒟 hQpos hQ' hDpos hthru) Rest' MintAt' h) s τ hs hτ

/-! ## §6 Axiom audit -/

#print axioms fuseChain_chainBefore
#print axioms fuseBits_coordOf
#print axioms fuseSPM
#print axioms fuse_reads_identical
#print axioms compactThenFuse_reads

/-! ## §7 SPOT — a deep dead spine, hand-derived (PASS + FAIL shaped)

Unary code (`enc d = 1^d 0`), hand-computed. Cut state: a live root sibling
`y` (id 20, payload 200, chain `[2]`) and a live record `x` (id 10, payload
100) hanging off a **3-level dead spine** `[1,1,1]` — chain `[1,1,1,2]`, so `x`
carries two dead interior codewords. `Q = [1,1,1]`, `Q' = [1]`. Fusion keeps
the head `[1]` and drops the two dead interiors: `x`'s coordinate collapses
`[1,1,1,2] ↦ [1,2]`. Beyond the cut: insert `z` (id 13, payload 300) under `x`
(delta 3). Hand-derived display order both sides: `y, x, z` (`y`'s root delta 2
beats `x`'s root delta 1; `x` is `z`'s ancestor) → payloads `[200, 100, 300]`.
Hand-summed coordinate weight `25 → 17`.

FAIL companion `badFuse`: reparents the dead spine to a *different* root delta
(`[1,1,1] ↦ [3]`, so `x ↦ [3,2]`), jumping `x` over the sibling `y`. It is a
prefix rewrite (H3-shaped) but **order-breaking** (H2 fails): the display
comparator between `x` and `y` flips, and the read changes — pinning H2
(`fuseChain_chainBefore`) as the load-bearing hypothesis. -/

namespace FusionSPOT

/-- Cut state, pre-sorted display order `[y, x]`: `y` root delta 2 (newer)
before `x`'s deep-spine subtree. -/
def sCut : EState ℕ :=
  [(20, 200, coordOf unaryCode [2]), (10, 100, coordOf unaryCode [1, 1, 1, 2])]

/-- The good fusion map: `Q = [1,1,1]` (3-level dead spine) collapses to its
head `Q' = [1]`. -/
def gfuse : List Bool → List Bool := fuseBits unaryCode [1, 1, 1] [1]

/-- **The fusion drops two dead levels, at the codeword boundary**: `x`'s
coordinate `[1,1,1,2]` (9 bits) collapses to `[1,2]` (5 bits); the sibling
`[2]` is untouched. -/
theorem fuse_concrete :
    gfuse (coordOf unaryCode [1, 1, 1, 2]) = coordOf unaryCode [1, 2] ∧
    gfuse (coordOf unaryCode [2]) = coordOf unaryCode [2] := by native_decide

/-- Beyond the cut: `z` (id 13, payload 300) anchored under `x` (id 10),
delta 3. -/
def postOps : List (Op (EOp ℕ)) :=
  [(13, 0, .ins 300 (coordOf unaryCode [1, 1, 1, 2]) 10)]

def finalO : EState ℕ := applySeq (E unaryCode).toCRDTSig sCut postOps

def finalR : EState ℕ :=
  applySeq (E unaryCode).toCRDTSig (eRemapSt gfuse sCut) (postOps.map (eRemapOp gfuse))

/-- **PASS**: fusion is invisible — both reads are the hand-derived
`[200, 100, 300]` (`y` newest root sibling, then `x`, then its child `z`).
Not empty, not the raw id list. -/
theorem reads_identical :
    SPOT.readE finalR = [200, 100, 300] ∧ SPOT.readE finalO = [200, 100, 300] := by
  native_decide

/-- **PASS**: the fusion genuinely compresses under the unary code:
`17 < 25` bits, hand-summed (`x`: 9→5 dropping two dead codewords, `z`: 13→9,
`y`: 3→3). -/
theorem size_reduced :
    SPOT.coordWeight finalR = 17 ∧ SPOT.coordWeight finalO = 25 := by native_decide

/-- Degenerate-behavior pin: the read equality is NOT the identity map echoing
the state — the fused state differs record for record. -/
theorem fusion_not_identity :
    eRemapSt gfuse sCut ≠ sCut ∧ finalR ≠ finalO := by native_decide

/-- The order-breaking rival: reparent the dead spine to root delta 3. -/
def badFuse (c : List Bool) : List Bool :=
  if (coordOf unaryCode [1, 1, 1]).isPrefixOf c
  then coordOf unaryCode [3] ++ c.drop (coordOf unaryCode [1, 1, 1]).length
  else c

def finalB : EState ℕ :=
  applySeq (E unaryCode).toCRDTSig (eRemapSt badFuse sCut) (postOps.map (eRemapOp badFuse))

/-- **FAIL companion (H2 is load-bearing)**: `badFuse` FLIPS the display
comparator between `x` and its sibling `y` (`x ↦ [3,2]` now beats `[2]`),
whereas the good fusion `gfuse` preserves it. The comparator is exactly what
the read sorts by, so the FAIL read genuinely changes. -/
theorem badfuse_flips_comparator :
    keyLt (key (badFuse (coordOf unaryCode [1, 1, 1, 2])))
        (key (badFuse (coordOf unaryCode [2])))
      ≠ keyLt (key (coordOf unaryCode [1, 1, 1, 2])) (key (coordOf unaryCode [2])) ∧
    keyLt (key (gfuse (coordOf unaryCode [1, 1, 1, 2])))
        (key (gfuse (coordOf unaryCode [2])))
      = keyLt (key (coordOf unaryCode [1, 1, 1, 2])) (key (coordOf unaryCode [2])) := by
  native_decide

/-- **FAIL companion (read level)**: the order-breaking reparent changes the
read away from the fusion-invariant `[200, 100, 300]`. -/
theorem badfuse_changes_read : SPOT.readE finalB ≠ SPOT.readE finalO := by native_decide

#print axioms fuse_concrete
#print axioms reads_identical
#print axioms size_reduced
#print axioms fusion_not_identity
#print axioms badfuse_flips_comparator
#print axioms badfuse_changes_read

end FusionSPOT

end Sal.ConditionedMRDTs
