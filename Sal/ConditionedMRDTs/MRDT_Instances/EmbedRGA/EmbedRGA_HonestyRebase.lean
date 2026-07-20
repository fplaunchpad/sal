import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_CompatChain
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_Fusion

/-!
# Honesty rebasing: the coded anchored forest invariant `I` (#97 (⋆))

This file discharges the single remaining obligation across the embed-GC
compaction stack: the `(⋆)` re-based-honesty lemma isolated in
`EmbedRGA_AnchorsFactor.lean` (single-epoch `AnchorsFactorBeyond`) and
`EmbedRGA_CompatChain.lean` (multi-epoch `restG`/`mintG`). Design and Python
validation: `whiteboard/honesty-rebasing-note.md` (+ §7 findings),
`whiteboard/litmus/honesty_rebasing_check.py`.

**The strategy.** Stop demanding a re-coded configuration be *natively* honest
(`EHonest.chain_gen` fails on renumbered/fused coordinates). Instead track the
structural invariant `eAnchored_exists` actually consumes: the **coded anchored
forest** `I` over the LIVE coordinate set, each live coordinate decodes as a
nonempty positive birth chain (a code-word SEQUENCE, well founded to the
sentinel `[]`), with distinct live coordinates distinct. `I` is history-free: a
property of the coordinate SET, not the operation history. We prove
`EHonest ⟹ I` (S1) and `StablePrefixMap` (rank-renumber / fusion / their
composition) preserves `I` (S2, the load-bearing lemma), so honesty **rebases**
across epochs: `I(C₁)` from `EHonest` for epoch 1, `I(F₁.C₁)` by S2 thereafter.
Then `I` supplies exactly the chain structure the epoch boundary needs (S3/S4),
closing `CompatChain`'s `restG`/`mintG` from `I(F₁.C₁)`.

It is **not circular**: `I` is established from `EHonest` for the first epoch
(S1) and PRESERVED by the map (S2). It never asks a re-coded configuration to be
natively `EHonest`, which it is not. "honest modulo the order-embedding" is
precisely: carry `I`, not `EHonest`, across epochs.

**Erratum applied (note §7.1).** Condition 1 reads "`w` is a nonempty decodable
code-word SEQUENCE" (one word per intervening dead level), NOT a single word.
`CodedAnchoredForest.decode` therefore decodes each live coordinate to a whole
positive chain; the nearest-live-ancestor factorization (`caf_ancestor_factor`)
splits it by prefix-freeness alone (`coordOf_inj`), no dead-head-key field
needed (note §7.2).
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode PosChain coordOf coordOf_inj coordOf_append
  key keyLt keyLt_irrefl key_inj enc_ne_nil)

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §1  The invariant `I` and its coordinate scraps -/

/-- **`I(C)`, the coded anchored forest invariant**, over a configuration's LIVE
coordinate set `L` (the coordinates of the live records). History-free:
* `nodup`, distinct live coordinates are distinct (note condition 3);
* `decode`, every live coordinate is the coordinate of a *nonempty positive
  birth chain*: a decodable code-word SEQUENCE, well founded to the sentinel
  `[]` (note conditions 1+2, with the §7.1 sequence reading).

This is exactly what `eAnchored_exists` returns, stated intrinsically over the
coordinate set instead of over the operation history, the whole point being
that a re-coded configuration has no honest history but still carries `I`. -/
structure CodedAnchoredForest (Γ : OrderedPrefixCode) (L : List (List Bool)) :
    Prop where
  nodup : L.Nodup
  decode : ∀ c ∈ L, ∃ ch : List ℕ, ch ≠ [] ∧ PosChain ch ∧ c = coordOf Γ ch

/-- A nonempty positive chain has a nonempty coordinate (its first codeword is
nonempty). -/
theorem coordOf_ne_nil {Γ : OrderedPrefixCode} {ch : List ℕ}
    (hne : ch ≠ []) (hpos : PosChain ch) : coordOf Γ ch ≠ [] := by
  cases ch with
  | nil => exact absurd rfl hne
  | cons d ds =>
      simp only [coordOf]
      intro h
      exact enc_ne_nil Γ (hpos d List.mem_cons_self)
        (List.append_eq_nil_iff.mp h).1

/-- A strictly-sorted embed state has NODUP coordinates: distinct keys force
distinct coordinates (`key` injective, `keyLt` irreflexive). This is the
`nodup` half of `I` for a native fold. -/
theorem coords_nodup_of_esorted {s : EState α} (hs : ESorted s) :
    (s.map (fun r => r.2.2)).Nodup := by
  have hp : (s.map (fun r => r.2.2)).Pairwise
      (fun c c' => keyLt (key c') (key c) = true) := List.pairwise_map.mpr hs
  refine hp.imp ?_
  intro c c' h hcc
  rw [hcc, keyLt_irrefl] at h
  exact Bool.noConfusion h

/-! ## §2  S1, a native honest configuration satisfies `I`

`ehonest_implies_I`: the live coordinate set of any well-formed fold of a
disciplined (honest) configuration satisfies `I`. The anchor certificate
`eAnchored_exists` gives each live insert's coordinate as `coordOf (chainOf id)`,
positive and nonempty (a live insert's id is nonzero, `eGen_no_zero_ins`, so its
chain sum is positive, so the chain is nonempty); `nodup` is sortedness. -/
theorem ehonest_implies_I {Γ : OrderedPrefixCode} {C : Configuration (E Γ α)}
    (hGen : GenHonest (E Γ α) eApplicable C)
    (hEnum : CausalPastEnumerable (E Γ α) C)
    {ρ : List (Op (EOp α))} (hwf : EWf Γ ρ)
    (hsub : ∀ o ∈ ρ, o ∈ C.events) :
    CodedAnchoredForest Γ ((eFold Γ ρ).map (fun r => r.2.2)) := by
  obtain ⟨chainOf, hA⟩ := eAnchored_exists hGen hEnum
  refine ⟨coords_nodup_of_esorted (e_fold_sorted Γ hwf), ?_⟩
  intro c hc
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  obtain ⟨o, hoρ, hoi, hrec⟩ := e_fold_rec_sub Γ ρ r hr
  have hoev : o ∈ C.events := hsub o hoρ
  refine ⟨chainOf o.1, ?_, hA.pos o hoev hoi, ?_⟩
  · -- nonempty: the chain sums to the nonzero id
    intro hnil
    have hsum := hA.sum o hoev hoi
    rw [hnil, List.sum_nil] at hsum
    exact eGen_no_zero_ins hGen hEnum o hoev hoi hsum.symm
  · -- the coordinate IS the chain's coordinate
    rw [hrec]
    exact hA.coord o hoev hoi

#print axioms ehonest_implies_I

/-! ## §2½  The forest reconstructed from `I` (note conditions 1–3 explicit)

`I` carries only decodability + distinctness; the note's nearest-live-ancestor
FOREST is reconstructed from the coordinate set (as `check_I` does). Here we
expose it: condition 1 (`caf_ancestor_factor`: every coded ancestor splits off a
nonempty decodable code-word sequence), condition 2 (`caf_ancestor_shorter`: the
ancestor chain is strictly shorter, so iterating reaches the sentinel `[]`), and
condition 3 (`caf_chain_inj`: distinct live coordinates have distinct chains).
No dead-head keys (note §7.2): the split is by prefix-freeness alone. -/

/-- **Condition 1 (the factorization).** For a coded ancestor `a` of `c` (its
chain a proper prefix), `c = a ++ w'` with `w'` the coordinate of a *nonempty
positive chain*, a code-word SEQUENCE the anchor walk re-splits by unique
decodability. The `w`-chain is a subchain of `c`'s, hence positive; nonempty
because `a ≠ c`. -/
theorem caf_ancestor_factor {Γ : OrderedPrefixCode}
    {c a : List Bool} {chc cha : List ℕ}
    (hposc : PosChain chc) (hcc : c = coordOf Γ chc) (hca : a = coordOf Γ cha)
    (hpre : cha <+: chc) (hproper : a ≠ c) :
    ∃ w : List ℕ, w ≠ [] ∧ PosChain w ∧ c = a ++ coordOf Γ w := by
  obtain ⟨w, hw⟩ := hpre
  have hwpos : PosChain w := fun d hd => hposc d (hw ▸ List.mem_append_right _ hd)
  refine ⟨w, ?_, hwpos, ?_⟩
  · intro hwnil
    rw [hwnil, List.append_nil] at hw
    apply hproper
    rw [hca, hw]
    exact hcc.symm
  · rw [hcc, ← hw, coordOf_append, ← hca]

/-- **Condition 2 (well-foundedness).** A coded ancestor's chain is strictly
shorter, so iterating the nearest-live-ancestor reaches the sentinel `[]`. -/
theorem caf_ancestor_shorter {Γ : OrderedPrefixCode}
    {c a : List Bool} {chc cha : List ℕ}
    (hcc : c = coordOf Γ chc) (hca : a = coordOf Γ cha)
    (hpre : cha <+: chc) (hproper : a ≠ c) : cha.length < chc.length := by
  obtain ⟨w, hw⟩ := hpre
  have hwne : w ≠ [] := by
    intro hwnil
    rw [hwnil, List.append_nil] at hw
    exact hproper (by rw [hca, hw]; exact hcc.symm)
  have hlen := congrArg List.length hw
  rw [List.length_append] at hlen
  have hwpos : 0 < w.length := List.length_pos_of_ne_nil hwne
  omega

/-- **Condition 3 (distinctness).** Distinct live coordinates decode to distinct
chains, the forest is a genuine tree, no two live nodes collide (unique
decodability, `coordOf_inj`). -/
theorem caf_chain_inj {Γ : OrderedPrefixCode} {c c' : List Bool}
    {ch ch' : List ℕ} (hcc : c = coordOf Γ ch) (hcc' : c' = coordOf Γ ch')
    (hne : c ≠ c') : ch ≠ ch' := by
  intro heq
  exact hne (by rw [hcc, hcc', heq])

#print axioms caf_ancestor_factor

/-! ## §3  Chain-aligned maps and S2, `StablePrefixMap` preserves `I`

The abstract `StablePrefixMap` guarantees only H2 (order) / H3 (ext), which do
*not* keep a coordinate decodable. What the compaction maps additionally do,
and what preserves `I`, is send `coordOf`-coordinates to `coordOf`-coordinates
through a chain-level map `φ`: `F.f (coordOf ch) = coordOf (φ ch)`, with `φ`
positive and nonempty-preserving. `ChainAligned` isolates that; both concrete
producers (rank-renumber `compactSPM`, fusion `fuseSPM`) and their composition
`StablePrefixMap.comp` satisfy it. -/

/-- **`F` is chain-aligned via `φ`**: on positive-chain coordinates the
bit-string map is the chain map `φ` (`align`), `φ` preserves positivity (`pos`)
and nonemptiness (`ne`). This is `fStab_coordOf` / `fuseBits_coordOf` abstracted:
the stable/unstable split lands on a codeword boundary and the tail is
verbatim. -/
structure ChainAligned (Γ : OrderedPrefixCode) (F : StablePrefixMap Γ)
    (φ : List ℕ → List ℕ) : Prop where
  align : ∀ ch, PosChain ch → F.f (coordOf Γ ch) = coordOf Γ (φ ch)
  pos : ∀ ch, PosChain ch → PosChain (φ ch)
  ne : ∀ ch, PosChain ch → ch ≠ [] → φ ch ≠ []

/-- **Rank-renumber is chain-aligned** (`φ = remapChain r`): `fStab_coordOf`
gives `align`, `remapFrom_pos` gives `pos`, and length preservation gives `ne`.
-/
theorem chainAligned_compactSPM (Γ : OrderedPrefixCode) (keep : List (List ℕ))
    (r : List ℕ → ℕ → ℕ) (𝒟 : List ℕ → Prop)
    (hKpos : ∀ k ∈ keep, PosChain k) (hDpos : ∀ ch, 𝒟 ch → PosChain ch)
    (hrPos : ∀ p d, 1 ≤ d → 1 ≤ r p d)
    (hrOff : ∀ p d, (p ++ [d]) ∉ keep → r p d = d)
    (hiso : ∀ p d e, Occ 𝒟 p d → Occ 𝒟 p e → d < e → r p d < r p e) :
    ChainAligned Γ (compactSPM Γ keep r 𝒟 hKpos hDpos hrPos hrOff hiso)
      (remapChain r) where
  align := fun ch hch => fStab_coordOf Γ hKpos hrOff hch
  pos := fun ch hch => remapFrom_pos hrPos ch [] hch
  ne := fun ch _ hne h => hne (by
    have hl : (remapChain r ch).length = ch.length := remapFrom_length r ch []
    rw [h, List.length_nil] at hl
    exact List.eq_nil_of_length_eq_zero hl.symm)

/-- **Fusion is chain-aligned** (`φ = fuseChain Q Q'`; the load-bearing case):
`fuseBits_coordOf` gives `align`, `fuseChain_pos` gives `pos`. A fused live
coordinate stays nonempty because the surviving head `Q'` is nonempty (`hQ'ne`):
a fused tail is a nonempty code-word SEQUENCE (note §7.2, R1). -/
theorem chainAligned_fuseSPM (Γ : OrderedPrefixCode) (Q Q' : List ℕ)
    (𝒟 : List ℕ → Prop) (hQpos : PosChain Q) (hQ' : Q' <+: Q)
    (hDpos : ∀ ch, 𝒟 ch → PosChain ch)
    (hthru : ∀ c, 𝒟 c → Q' <+: c → Q <+: c) (hQ'ne : Q' ≠ []) :
    ChainAligned Γ (fuseSPM Γ Q Q' 𝒟 hQpos hQ' hDpos hthru) (fuseChain Q Q') where
  align := fun ch hch => fuseBits_coordOf Γ hQpos hch
  pos := fun ch hch => fuseChain_pos hQ' hQpos hch
  ne := fun ch _ hne h => by
    simp only [fuseChain] at h
    split at h
    · exact hQ'ne (List.append_eq_nil_iff.mp h).1
    · exact hne h

/-- **Composition preserves chain-alignment** (`φ = ψ ∘ φ`): the composite of two
chain-aligned maps is chain-aligned, so `I` is preserved along a whole
`CompatChain` of epochs by induction (via `chainAligned_comp` iterated). -/
theorem chainAligned_comp {Γ : OrderedPrefixCode} {F G : StablePrefixMap Γ}
    {φ ψ : List ℕ → List ℕ} (hF : ChainAligned Γ F φ) (hG : ChainAligned Γ G ψ)
    (Rest' : List Bool → Prop) (MintAt' : List Bool → ℕ → Prop)
    (h : CompatOn F G Rest' MintAt') :
    ChainAligned Γ (F.comp G Rest' MintAt' h) (ψ ∘ φ) where
  align := fun ch hch => by
    simp only [StablePrefixMap.comp_f, Function.comp_apply,
      hF.align ch hch, hG.align (φ ch) (hF.pos ch hch)]
  pos := fun ch hch => hG.pos (φ ch) (hF.pos ch hch)
  ne := fun ch hch hne => hG.ne (φ ch) (hF.pos ch hch) (hF.ne ch hch hne)

/-- **S2, the load-bearing lemma: `StablePrefixMap` preserves `I`.** For a
chain-aligned `F` whose domain covers the live coordinates, `I(L)` implies
`I(F.f '' L)`: each `F`-image `coordOf (φ ch)` is again a nonempty positive
chain's coordinate (via `ChainAligned`), and distinctness survives because `F` is
injective on its domain (H1, `StablePrefixMap.injOn`). Honesty rebases: no
re-derivation of `EHonest` on the re-coded set. -/
theorem stablePrefixMap_preserves_I {Γ : OrderedPrefixCode}
    (F : StablePrefixMap Γ) {φ : List ℕ → List ℕ} (hCA : ChainAligned Γ F φ)
    {L : List (List Bool)} (hI : CodedAnchoredForest Γ L)
    (hdom : ∀ c ∈ L, F.Dom c) :
    CodedAnchoredForest Γ (L.map F.f) := by
  refine ⟨?_, ?_⟩
  · exact hI.nodup.map_on
      (fun x hx y hy hfxy => F.injOn (hdom x hx) (hdom y hy) hfxy)
  · intro c hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    obtain ⟨ch, hne, hpos, rfl⟩ := hI.decode c0 hc0
    exact ⟨φ ch, hCA.ne ch hpos hne, hCA.pos ch hpos, hCA.align ch hpos⟩

#print axioms stablePrefixMap_preserves_I

/-! ## §4  S3/S4, discharging `(⋆)` at the epoch boundary from `I`

`I` supplies exactly the chain structure the epoch boundary consumes. S3 (the
definitional bridge): `I` certifies each live coordinate is `coordOf` of a
positive chain, the "at hand" coverage a next-epoch compaction's domain needs
(`I_implies_atHand`). S4: build epoch 2's map over the **rebased image domain**
(the `φ₁`-images of epoch-1's chains) and discharge `CompatChain`'s `restG` /
`mintG` from chain-alignment, closing `(⋆)` at the multi-epoch boundary. -/

/-- **S3, the definitional bridge.** `I` is exactly the "at hand" certificate a
next-epoch compaction consumes: every live coordinate is the coordinate of a
positive birth chain. This is `eAnchored_exists`'s output read off the coordinate
set, anchor = nearest coded ancestor (`caf_ancestor_factor`), no honesty. -/
theorem I_implies_atHand {Γ : OrderedPrefixCode} {L : List (List Bool)}
    (hI : CodedAnchoredForest Γ L) :
    ∀ c ∈ L, ∃ ch, PosChain ch ∧ c = coordOf Γ ch :=
  fun c hc => (hI.decode c hc).imp (fun _ h => ⟨h.2.1, h.2.2⟩)

/-- **The snoc-commute.** For a beyond-cut mint on anchor chain `chA` with fresh
delta `d`, the chain map `φ` commutes with the append: `φ (chA ++ [d]) =
φ chA ++ [d]`. Derived purely from `F.ext` (H3) + chain-alignment + unique
decodability, the minted delta rides through untouched (note §2). -/
theorem chainAligned_snoc {Γ : OrderedPrefixCode} {F : StablePrefixMap Γ}
    {φ : List ℕ → List ℕ} (hCA : ChainAligned Γ F φ) {chA : List ℕ} {d : ℕ}
    (hposA : PosChain chA) (hd : 1 ≤ d)
    (hmint : F.MintAt (coordOf Γ chA) d) : φ (chA ++ [d]) = φ chA ++ [d] := by
  have hposd : PosChain (chA ++ [d]) := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hposA x h
    · rw [List.mem_singleton.mp h]; exact hd
  have hposφd : PosChain (φ chA ++ [d]) := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hCA.pos chA hposA x h
    · rw [List.mem_singleton.mp h]; exact hd
  have hext := F.ext hmint
  have hcd : coordOf Γ chA ++ Γ.enc d = coordOf Γ (chA ++ [d]) := by
    rw [coordOf_append]; simp [coordOf]
  have hrd : coordOf Γ (φ chA) ++ Γ.enc d = coordOf Γ (φ chA ++ [d]) := by
    rw [coordOf_append]; simp [coordOf]
  rw [hcd, hCA.align (chA ++ [d]) hposd, hCA.align chA hposA, hrd] at hext
  exact coordOf_inj Γ (hCA.pos (chA ++ [d]) hposd) hposφd hext

/-- **The rebased epoch-2 domain** (note §4): the `φ₁`-images of epoch-1's
at-hand chains. Building epoch 2 over THIS domain is what "honest modulo the
embedding" means, the domain is carried by `I`, not re-derived from a fresh
honesty assumption at epoch 2. -/
def rebasedDom (𝒟₁ : List ℕ → Prop) (φ₁ : List ℕ → List ℕ) (ch' : List ℕ) : Prop :=
  ∃ ch, 𝒟₁ ch ∧ ch' = φ₁ ch

/-- **The rebased epoch-2 map**: the (identity-renumber) `StablePrefixMap` over
the rebased image domain. A genuine, valid second-epoch map whose domain is the
`I`-carried image of epoch 1, no epoch-2 honesty assumption. -/
def rebaseSPM (Γ : OrderedPrefixCode) (𝒟₁ : List ℕ → Prop) (φ₁ : List ℕ → List ℕ)
    (hφpos : ∀ ch, 𝒟₁ ch → PosChain (φ₁ ch)) : StablePrefixMap Γ :=
  compactSPM Γ [] (fun _ d => d) (rebasedDom 𝒟₁ φ₁)
    (fun k hk => absurd hk (List.not_mem_nil))
    (fun _ h => by obtain ⟨c0, hc0, rfl⟩ := h; exact hφpos c0 hc0)
    (fun _ _ hd => hd)
    (fun _ _ _ => rfl)
    (fun _ _ _ _ _ h => h)

/-- **S4, multi-epoch: `(⋆)` discharged.** From epoch 1's chain-aligned map `F₁`
(whose `Rest`/`MintAt` have the compaction shape, `hRestShape`/`hMintShape`,
true of `compactSPM` and `fuseSPM`), the epoch-boundary obligations
`CompatOn`'s `restG`/`mintG` are met by epoch 2 = `rebaseSPM` over the image
domain: a survivor's `F₁`-image is at hand for epoch 2 by chain-alignment
(`restG`), and a beyond-cut mint's `F₁`-image is an epoch-2 mint by the
snoc-commute (`mintG`). This is the residue the `CompatChain` note isolated,
closed from `I`, no epoch-2 honesty assumption. -/
theorem twoEpoch_compatOn_of_I {Γ : OrderedPrefixCode} (F₁ : StablePrefixMap Γ)
    {φ₁ : List ℕ → List ℕ} (hCA₁ : ChainAligned Γ F₁ φ₁)
    (𝒟₁ : List ℕ → Prop) (h𝒟pos : ∀ ch, 𝒟₁ ch → PosChain ch)
    (hRestShape : ∀ c, F₁.Rest c → ∃ ch, 𝒟₁ ch ∧ c = coordOf Γ ch)
    (hMintShape : ∀ π d, F₁.MintAt π d →
        ∃ chA, 𝒟₁ (chA ++ [d]) ∧ PosChain chA ∧ π = coordOf Γ chA ∧ 1 ≤ d) :
    CompatOn F₁ (rebaseSPM Γ 𝒟₁ φ₁ (fun ch h => hCA₁.pos ch (h𝒟pos ch h)))
      F₁.Rest F₁.MintAt :=
  compatOn_two_epoch F₁ _ F₁.Rest F₁.MintAt
    (fun _ hc => Or.inl hc)
    (fun c hc => by
      obtain ⟨ch, h𝒟, rfl⟩ := hRestShape c hc
      rw [hCA₁.align ch (h𝒟pos ch h𝒟)]
      exact Or.inl ⟨φ₁ ch, ⟨ch, h𝒟, rfl⟩, rfl⟩)
    (fun _ _ hm => hm)
    (fun π d hm => by
      obtain ⟨chA, h𝒟d, hposA, rfl, hd⟩ := hMintShape π d hm
      rw [hCA₁.align chA hposA]
      refine ⟨hd, φ₁ chA, rfl, hCA₁.pos chA hposA, ⟨chA ++ [d], h𝒟d, ?_⟩,
        List.not_mem_nil⟩
      exact (chainAligned_snoc hCA₁ hposA hd hm).symm)

#print axioms twoEpoch_compatOn_of_I

/-- **The payoff, `I` rebases across two epochs (multi-epoch native).** With
both epochs' maps chain-aligned and the domain coverage `I` supplies, `I`
survives BOTH compactions: `I(C₁) ⟹ I(F₁.C₁) ⟹ I(F₂.F₁.C₁)`. Composed with
`twoEpoch_compatOn_of_I` (the boundary is compatible), the second epoch operates
on the `I`-carried rebased domain, not by transport through the first. -/
theorem I_preserved_two_epoch {Γ : OrderedPrefixCode} (F₁ F₂ : StablePrefixMap Γ)
    {φ₁ φ₂ : List ℕ → List ℕ} (hCA₁ : ChainAligned Γ F₁ φ₁)
    (hCA₂ : ChainAligned Γ F₂ φ₂) {L : List (List Bool)}
    (hI : CodedAnchoredForest Γ L) (hdom₁ : ∀ c ∈ L, F₁.Dom c)
    (hdom₂ : ∀ c ∈ L.map F₁.f, F₂.Dom c) :
    CodedAnchoredForest Γ ((L.map F₁.f).map F₂.f) :=
  stablePrefixMap_preserves_I F₂ hCA₂
    (stablePrefixMap_preserves_I F₁ hCA₁ hI hdom₁) hdom₂

#print axioms I_preserved_two_epoch

/-! ## §5  SPOT, `I` on a concrete honest forest, preserved through a
renumber+fuse epoch (PASS + FAIL shaped)

Unary code (`enc d = 1^d 0`). Live forest at the cut (the FusionSPOT geometry):
a root sibling `y` (chain `[2]`) and a deep node `x` (chain `[1,1,1,2]`, hanging
off a 3-level DEAD spine `[1,1,1]`). `I` holds. The fusion `Q=[1,1,1] ↦ Q'=[1]`
collapses `x`'s two dead interior codewords (`[1,1,1,2] ↦ [1,2]`); `I` survives.
FAIL companion: a pseudo-map that collapses the two distinct live coordinates to
one breaks `I` (the R2 collision negative control, a non-injective, hence
non-order-preserving, map). -/

namespace RebaseSPOT

open Sal.EmbedRGA (unaryCode)

/-- The live coordinate set at the cut: root sibling `[2]`, deep node
`[1,1,1,2]` (two dead interior codewords baked in). -/
abbrev Ls : List (List Bool) :=
  [coordOf unaryCode [2], coordOf unaryCode [1, 1, 1, 2]]

/-- The at-hand chains: exactly the two live chains. -/
abbrev 𝒟s : List ℕ → Prop := fun ch => ch = [2] ∨ ch = [1, 1, 1, 2]

theorem hQpos : PosChain [1, 1, 1] := by intro d hd; simp at hd; omega
theorem hQ' : ([1] : List ℕ) <+: [1, 1, 1] := by decide
theorem hDpos : ∀ ch, 𝒟s ch → PosChain ch := by
  rintro ch (rfl | rfl) <;> (intro d hd; simp at hd; omega)
theorem hthru : ∀ c, 𝒟s c → ([1] : List ℕ) <+: c → ([1, 1, 1] : List ℕ) <+: c := by
  rintro c (rfl | rfl) h
  · exact absurd h (by decide)
  · decide

/-- The concrete fusion map (a genuine `StablePrefixMap`). -/
def Fs : StablePrefixMap unaryCode := fuseSPM unaryCode [1, 1, 1] [1] 𝒟s hQpos hQ' hDpos hthru

/-- **PASS**: `I` holds on the honest cut forest. Not vacuous: two distinct live
coordinates, each decoding to a nonempty positive chain. -/
theorem I_pass : CodedAnchoredForest unaryCode Ls := by
  refine ⟨by native_decide, ?_⟩
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ⟨[2], by decide, by intro d hd; simp at hd; omega, rfl⟩
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨[1, 1, 1, 2], by decide, by intro d hd; simp at hd; omega, rfl⟩
    · exact absurd hc List.not_mem_nil

theorem hdoms : ∀ c ∈ Ls, Fs.Dom c := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact Or.inl ⟨[2], Or.inl rfl, rfl⟩
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl ⟨[1, 1, 1, 2], Or.inr rfl, rfl⟩
    · exact absurd hc List.not_mem_nil

/-- **PASS**: `I` is preserved through the renumber+fuse epoch, the fired
`stablePrefixMap_preserves_I` on the concrete fusion. -/
theorem I_preserved : CodedAnchoredForest unaryCode (Ls.map Fs.f) :=
  stablePrefixMap_preserves_I Fs
    (chainAligned_fuseSPM unaryCode [1, 1, 1] [1] 𝒟s hQpos hQ' hDpos hthru
      (by decide)) I_pass hdoms

/-- The fused coordinate set, hand-derived: `x`'s two dead interiors dropped
(`[1,1,1,2] ↦ [1,2]`), `y` untouched. Pins the map is NOT the identity (the
first coord differs) and NOT a projection (`y` survives). -/
theorem fused_coords :
    Ls.map Fs.f = [coordOf unaryCode [2], coordOf unaryCode [1, 2]] := by
  native_decide

/-- **FAIL companion**: a non-order-preserving pseudo-map collapsing the two
distinct live coordinates to one breaks `I`, the fused set is not `nodup` (R2
collision). Rules out the degenerate "any map preserves `I`". -/
theorem I_pseudomap_fail :
    ¬ CodedAnchoredForest unaryCode (Ls.map (fun _ => coordOf unaryCode [1])) :=
  fun hI => absurd hI.nodup (by native_decide)

#print axioms I_pass
#print axioms I_preserved
#print axioms fused_coords
#print axioms I_pseudomap_fail

end RebaseSPOT

end Sal.ConditionedMRDTs
