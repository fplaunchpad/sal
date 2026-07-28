import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_AnchorsFactor
import Sal.MRDTs.RGA_Embed.Embed_Code_EliasDelta

/-!
# `compactEliasDelta` — the concrete verified compaction

The compaction for the embed RGA, as a `StablePrefixMap` producer:

* **(a) DROP dead ranges** — `ePruneKeep`: a stable chain is carried forward
  iff it has a live descendant in the stable tree or a known in-flight
  coordinate passes through it; everything else is dropped, and its sibling
  rank is reclaimed.
* **(b) RANK-RENUMBER** — `rED`: in each sibling group with **no known
  in-flight child delta** (`skipAt = false`), the surviving deltas are
  renumbered to `1..k` order-isomorphically (`rankIn`) and re-encoded with
  the same ordered prefix code; groups *with* in-flight children are skipped
  this epoch. Spine fusion for such groups is a separate construction
  (`EmbedRGA_Fusion.lean`).

Soundness: H2 (`ord`) is `remapChain_keyLt` — per-group order-isomorphism
composed through the chain-lex theorem (`chainBefore_display`, where the
code's monotonicity lives); the rank map is an order-isomorphism against
surviving kids and is dominated by Lamport-fresh future deltas (`rED_iso`);
H3 (`ext`) holds by construction (the re-map rewrites the stable chain
prefix wholesale and never touches the minted delta codeword); H1 is derived
by the bundle. The headline (`compactRanked_settled_reads`,
`compactEliasDelta_settled_reads`) discharges everything at a `SettledAtOn`
cut of a disciplined honest configuration: freshness comes from
`Configuration.causal_mono` (the Lamport clause) through
`settledAt_dichotomy`.

**Addressing (runtime-twin erratum honored):** the cut-side inputs `tree`,
`live`, `inflight` are lists of *chains* (coordinate-addressed data), never
event ids resolved through prefix sums; id arithmetic appears only inside
the epoch-zero honest configuration. Scope: the **single-epoch** statement —
one compaction at a settled cut of an honest configuration.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode PosChain coordOf coordOf_append
  coordOf_inj key keyLt keyLt_irrefl keyLt_asymm chainBefore chainBefore_total
  chainBefore_display enc_ne_nil eliasDeltaCode)

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §1 Chain-prefix alignment: bit prefixes of coordinates ARE chain
prefixes (prefix-freedom decodes the cut point onto a codeword boundary) -/

theorem coordOf_prefix_align (Γ : OrderedPrefixCode) :
    ∀ {ch1 ch2 : List ℕ}, PosChain ch1 → PosChain ch2 →
      coordOf Γ ch1 <+: coordOf Γ ch2 → ch1 <+: ch2
  | [], _, _, _, _ => List.nil_prefix
  | d :: ds, [], h1, _, h => by
      exfalso
      have hnil : coordOf Γ (d :: ds) = [] := List.prefix_nil.mp h
      simp only [coordOf] at hnil
      cases henc : Γ.enc d with
      | nil => exact enc_ne_nil Γ (h1 d List.mem_cons_self) henc
      | cons b bs => rw [henc] at hnil; simp at hnil
  | d :: ds, e :: es, h1, h2, h => by
      simp only [coordOf] at h
      have hd1 : 1 ≤ d := h1 d List.mem_cons_self
      have he1 : 1 ≤ e := h2 e List.mem_cons_self
      have hde : d = e := by
        by_contra hne
        have p1 : Γ.enc d <+: Γ.enc e ++ coordOf Γ es :=
          List.IsPrefix.trans (List.prefix_append _ _) h
        have p2 : Γ.enc e <+: Γ.enc e ++ coordOf Γ es := List.prefix_append _ _
        rcases Nat.le_total (Γ.enc d).length (Γ.enc e).length with hle | hle
        · exact Γ.prefixFree hd1 he1 hne
            (List.prefix_of_prefix_length_le p1 p2 hle)
        · exact Γ.prefixFree he1 hd1 (Ne.symm hne)
            (List.prefix_of_prefix_length_le p2 p1 hle)
      subst hde
      have htail : coordOf Γ ds <+: coordOf Γ es := by
        obtain ⟨w, hw⟩ := h
        rw [List.append_assoc] at hw
        exact ⟨w, List.append_cancel_left hw⟩
      exact List.cons_prefix_cons.mpr ⟨rfl,
        coordOf_prefix_align Γ
          (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
          (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) htail⟩

theorem coordOf_prefix_of_prefix (Γ : OrderedPrefixCode) {ch1 ch2 : List ℕ}
    (h : ch1 <+: ch2) : coordOf Γ ch1 <+: coordOf Γ ch2 := by
  obtain ⟨u, hu⟩ := h
  exact ⟨coordOf Γ u, by rw [← coordOf_append, hu]⟩

theorem prefix_snoc_cons (p : List ℕ) (d : ℕ) (c : List ℕ) :
    (p ++ [d]) <+: (p ++ d :: c) := by
  have h := List.prefix_append (p ++ [d]) c
  rwa [List.append_assoc, List.singleton_append] at h

/-! ## §2 The chain re-map: per-position renumbering keyed on the (old)
parent prefix -/

/-- Re-map a chain suffix, the accumulator carrying the original parent
prefix: position `i`'s delta `d` under parent `p` becomes `r p d`. -/
def remapFrom (r : List ℕ → ℕ → ℕ) : List ℕ → List ℕ → List ℕ
  | _, [] => []
  | p, d :: ds => r p d :: remapFrom r (p ++ [d]) ds

/-- The whole-chain re-map. -/
def remapChain (r : List ℕ → ℕ → ℕ) (ch : List ℕ) : List ℕ :=
  remapFrom r [] ch

theorem remapFrom_cons (r : List ℕ → ℕ → ℕ) (p : List ℕ) (d : ℕ)
    (ds : List ℕ) :
    remapFrom r p (d :: ds) = r p d :: remapFrom r (p ++ [d]) ds := rfl

theorem remapFrom_length (r : List ℕ → ℕ → ℕ) :
    ∀ (ds p : List ℕ), (remapFrom r p ds).length = ds.length
  | [], _ => rfl
  | d :: ds, p => by
      rw [remapFrom_cons, List.length_cons, List.length_cons,
        remapFrom_length r ds]

theorem remapFrom_append (r : List ℕ → ℕ → ℕ) :
    ∀ (u p v : List ℕ),
      remapFrom r p (u ++ v) = remapFrom r p u ++ remapFrom r (p ++ u) v
  | [], p, v => by simp [remapFrom]
  | d :: u', p, v => by
      simp only [List.cons_append, remapFrom_cons]
      rw [remapFrom_append r u' (p ++ [d]) v]
      simp [List.append_assoc]

theorem remapFrom_pos {r : List ℕ → ℕ → ℕ}
    (hr : ∀ p d, 1 ≤ d → 1 ≤ r p d) :
    ∀ (ds p : List ℕ), PosChain ds → PosChain (remapFrom r p ds)
  | [], _, _ => fun x hx => absurd hx (List.not_mem_nil)
  | d :: ds, p, h => by
      intro x hx
      rw [remapFrom_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hr p d (h d List.mem_cons_self)
      · exact remapFrom_pos hr ds (p ++ [d])
          (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx'

/-- Off the kept tree the re-map is the identity, position for position. -/
theorem remapFrom_id {keep : List (List ℕ)} {r : List ℕ → ℕ → ℕ}
    (hrOff : ∀ p d, (p ++ [d]) ∉ keep → r p d = d) :
    ∀ (u p : List ℕ),
      (∀ q e, (q ++ [e]) <+: u → (p ++ q ++ [e]) ∉ keep) →
      remapFrom r p u = u
  | [], _, _ => rfl
  | x :: xs, p, h => by
      rw [remapFrom_cons]
      have hx : r p x = x := by
        apply hrOff
        have := h [] x (by simp)
        simpa using this
      have htail := remapFrom_id hrOff xs (p ++ [x]) (fun q e hqe => by
        have h2 := h (x :: q) e (by
          rw [show (x :: q) ++ [e] = x :: (q ++ [e]) from rfl]
          exact List.cons_prefix_cons.mpr ⟨rfl, hqe⟩)
        simpa [List.append_assoc] using h2)
      rw [hx, htail]

/-! ## §3 H2, generically: an order-isomorphic per-group renumbering
preserves the display comparator (through the chain-lex theorem — this is
where the code's monotonicity is consumed) -/

/-- `(p, d)` occurs in the domain: some at-hand chain passes through the
node `p ++ [d]`. -/
def Occ (𝒟 : List ℕ → Prop) (p : List ℕ) (d : ℕ) : Prop :=
  ∃ ch, 𝒟 ch ∧ (p ++ [d]) <+: ch

theorem remapChain_chainBefore {r : List ℕ → ℕ → ℕ} {𝒟 : List ℕ → Prop}
    (hiso : ∀ p d e, Occ 𝒟 p d → Occ 𝒟 p e → d < e → r p d < r p e)
    {ch ch' : List ℕ} (h : 𝒟 ch) (h' : 𝒟 ch') (hb : chainBefore ch ch') :
    chainBefore (remapChain r ch) (remapChain r ch') := by
  cases hb with
  | ancestor ch0 ext hne =>
      rw [remapChain, remapChain, remapFrom_append]
      refine chainBefore.ancestor _ _ (fun hnil => hne ?_)
      have hlen := congrArg List.length hnil
      rw [remapFrom_length] at hlen
      exact List.eq_nil_of_length_eq_zero hlen
  | newer p0 d e c1 c2 hlt =>
      have hoccd : Occ 𝒟 p0 d := ⟨p0 ++ d :: c1, h, prefix_snoc_cons p0 d c1⟩
      have hocce : Occ 𝒟 p0 e := ⟨p0 ++ e :: c2, h', prefix_snoc_cons p0 e c2⟩
      have hred : r p0 e < r p0 d := hiso p0 e d hocce hoccd hlt
      have e1 : remapChain r (p0 ++ d :: c1)
          = remapFrom r [] p0 ++ r p0 d :: remapFrom r (p0 ++ [d]) c1 := by
        rw [remapChain, show p0 ++ d :: c1 = (p0 ++ [d]) ++ c1 from by simp,
          remapFrom_append, remapFrom_append]
        simp [remapFrom, List.append_assoc]
      have e2 : remapChain r (p0 ++ e :: c2)
          = remapFrom r [] p0 ++ r p0 e :: remapFrom r (p0 ++ [e]) c2 := by
        rw [remapChain, show p0 ++ e :: c2 = (p0 ++ [e]) ++ c2 from by simp,
          remapFrom_append, remapFrom_append]
        simp [remapFrom, List.append_assoc]
      rw [e1, e2]
      exact chainBefore.newer _ _ _ _ _ hred

/-- **H2, the generic soundness theorem**: an order-isomorphic (on occurring
sibling pairs), positivity-preserving chain re-map preserves the fold's key
comparator, as a Boolean equation (both directions). -/
theorem remapChain_keyLt (Γ : OrderedPrefixCode) {r : List ℕ → ℕ → ℕ}
    {𝒟 : List ℕ → Prop} (hDpos : ∀ ch, 𝒟 ch → PosChain ch)
    (hrPos : ∀ p d, 1 ≤ d → 1 ≤ r p d)
    (hiso : ∀ p d e, Occ 𝒟 p d → Occ 𝒟 p e → d < e → r p d < r p e)
    {ch ch' : List ℕ} (h : 𝒟 ch) (h' : 𝒟 ch') :
    keyLt (key (coordOf Γ (remapChain r ch)))
        (key (coordOf Γ (remapChain r ch')))
      = keyLt (key (coordOf Γ ch)) (key (coordOf Γ ch')) := by
  by_cases heq : ch = ch'
  · subst heq
    rw [keyLt_irrefl, keyLt_irrefl]
  · have hpos := hDpos ch h
    have hpos' := hDpos ch' h'
    have hrp : PosChain (remapChain r ch) := remapFrom_pos hrPos ch [] hpos
    have hrp' : PosChain (remapChain r ch') := remapFrom_pos hrPos ch' [] hpos'
    rcases chainBefore_total heq with hb | hb
    · have h1 := chainBefore_display Γ hpos hpos' hb
      have h2 := chainBefore_display Γ hrp hrp'
        (remapChain_chainBefore hiso h h' hb)
      rw [keyLt_asymm h1, keyLt_asymm h2]
    · have h1 := chainBefore_display Γ hpos' hpos hb
      have h2 := chainBefore_display Γ hrp' hrp
        (remapChain_chainBefore hiso h' h hb)
      rw [h1, h2]

/-! ## §4 The induced bit-string translation: longest kept stable prefix
rewritten wholesale, tail verbatim -/

/-- The longest kept chain whose coordinate prefixes `c` (`[]` if none). -/
def stabChain (Γ : OrderedPrefixCode) : List (List ℕ) → List Bool → List ℕ
  | [], _ => []
  | k :: ks, c =>
      if (coordOf Γ k).isPrefixOf c ∧ (stabChain Γ ks c).length < k.length
      then k else stabChain Γ ks c

theorem stabChain_spec (Γ : OrderedPrefixCode) :
    ∀ (K : List (List ℕ)) (c : List Bool),
      stabChain Γ K c = [] ∨
        (stabChain Γ K c ∈ K ∧ coordOf Γ (stabChain Γ K c) <+: c)
  | [], _ => Or.inl rfl
  | k :: ks, c => by
      simp only [stabChain]
      by_cases h : (coordOf Γ k).isPrefixOf c
          ∧ (stabChain Γ ks c).length < k.length
      · rw [if_pos h]
        exact Or.inr ⟨List.mem_cons_self, List.isPrefixOf_iff_prefix.mp h.1⟩
      · rw [if_neg h]
        rcases stabChain_spec Γ ks c with h' | ⟨hm, hp⟩
        · exact Or.inl h'
        · exact Or.inr ⟨List.mem_cons_of_mem _ hm, hp⟩

theorem stabChain_max (Γ : OrderedPrefixCode) :
    ∀ (K : List (List ℕ)) (c : List Bool) (k : List ℕ), k ∈ K →
      coordOf Γ k <+: c → k.length ≤ (stabChain Γ K c).length
  | [], _, _, hk, _ => absurd hk (List.not_mem_nil)
  | k0 :: ks, c, k, hk, hp => by
      simp only [stabChain]
      by_cases h : (coordOf Γ k0).isPrefixOf c
          ∧ (stabChain Γ ks c).length < k0.length
      · rw [if_pos h]
        rcases List.mem_cons.mp hk with rfl | hk'
        · exact Nat.le_refl _
        · exact Nat.le_trans (stabChain_max Γ ks c k hk' hp) (Nat.le_of_lt h.2)
      · rw [if_neg h]
        rcases List.mem_cons.mp hk with rfl | hk'
        · rcases Nat.lt_or_ge (stabChain Γ ks c).length k.length with hlt | hge
          · exact absurd ⟨List.isPrefixOf_iff_prefix.mpr hp, hlt⟩ h
          · exact hge
        · exact stabChain_max Γ ks c k hk' hp

/-- **The lazy translation, concretely**: rewrite the longest kept stable
prefix through the chain re-map, keep the tail bit-for-bit. Total and
computable on all bit strings. -/
def fStab (Γ : OrderedPrefixCode) (r : List ℕ → ℕ → ℕ)
    (keep : List (List ℕ)) (c : List Bool) : List Bool :=
  coordOf Γ (remapChain r (stabChain Γ keep c))
    ++ c.drop (coordOf Γ (stabChain Γ keep c)).length

/-- **The master alignment lemma**: on any positive chain's coordinate the
bit-string translation IS the chain re-map — the stable/unstable split lands
on a codeword boundary and the tail is off the kept tree, where `r` is the
identity. No domain hypothesis: this holds for every positive chain. -/
theorem fStab_coordOf (Γ : OrderedPrefixCode) {r : List ℕ → ℕ → ℕ}
    {keep : List (List ℕ)} (hKpos : ∀ k ∈ keep, PosChain k)
    (hrOff : ∀ p d, (p ++ [d]) ∉ keep → r p d = d)
    {ch : List ℕ} (hch : PosChain ch) :
    fStab Γ r keep (coordOf Γ ch) = coordOf Γ (remapChain r ch) := by
  rcases stabChain_spec Γ keep (coordOf Γ ch) with hnil | ⟨hmem, hpre⟩
  · have hid : remapChain r ch = ch := by
      apply remapFrom_id hrOff
      intro q e hqe hin
      have hin' : (q ++ [e]) ∈ keep := by simpa using hin
      have hmax := stabChain_max Γ keep (coordOf Γ ch) _ hin'
        (coordOf_prefix_of_prefix Γ hqe)
      rw [hnil] at hmax
      simp at hmax
    rw [fStab, hnil, hid]
    simp [remapChain, remapFrom, coordOf]
  · have hspos : PosChain (stabChain Γ keep (coordOf Γ ch)) := hKpos _ hmem
    have hsch : stabChain Γ keep (coordOf Γ ch) <+: ch :=
      coordOf_prefix_align Γ hspos hch hpre
    set st := stabChain Γ keep (coordOf Γ ch) with hst
    obtain ⟨u, hu⟩ := hsch
    have htail : remapFrom r st u = u := by
      apply remapFrom_id hrOff
      intro q e hqe hin
      have hpre2 : ((st ++ q) ++ [e]) <+: ch := by
        obtain ⟨w, hw⟩ := hqe
        refine ⟨w, ?_⟩
        rw [← hu, List.append_assoc, List.append_assoc]
        congr 1
        rw [← List.append_assoc]
        exact hw
      have hmax := stabChain_max Γ keep (coordOf Γ ch) _ hin
        (coordOf_prefix_of_prefix Γ hpre2)
      rw [← hst] at hmax
      simp only [List.length_append, List.length_singleton] at hmax
      omega
    rw [fStab, ← hst, ← hu, coordOf_append, List.drop_left]
    simp only [remapChain, remapFrom_append, List.nil_append, htail,
      coordOf_append]

/-! ## §5 The bundle producer: H3 by construction, H2 by §3, H1 derived -/

/-- The at-rest domain: coordinates of at-hand chains. -/
def compactRest (Γ : OrderedPrefixCode) (𝒟 : List ℕ → Prop)
    (c : List Bool) : Prop :=
  ∃ ch, 𝒟 ch ∧ c = coordOf Γ ch

/-- The mint domain: one fresh positive delta on an at-hand anchor chain,
the minted node off the kept tree (it is a new-epoch node). -/
def compactMintAt (Γ : OrderedPrefixCode) (keep : List (List ℕ))
    (𝒟 : List ℕ → Prop) (π : List Bool) (δ : ℕ) : Prop :=
  1 ≤ δ ∧ ∃ chA, π = coordOf Γ chA ∧ PosChain chA ∧ 𝒟 (chA ++ [δ]) ∧
    (chA ++ [δ]) ∉ keep

theorem compactDom_chain {Γ : OrderedPrefixCode} {keep : List (List ℕ)}
    {𝒟 : List ℕ → Prop} {c : List Bool}
    (h : compactRest Γ 𝒟 c ∨
      ∃ π δ, compactMintAt Γ keep 𝒟 π δ ∧ c = π ++ Γ.enc δ) :
    ∃ ch, 𝒟 ch ∧ c = coordOf Γ ch := by
  rcases h with ⟨ch, hch, rfl⟩ | ⟨π, δ, ⟨hδ, chA, rfl, hpos, hD, -⟩, rfl⟩
  · exact ⟨ch, hch, rfl⟩
  · exact ⟨chA ++ [δ], hD, by rw [coordOf_append]; simp [coordOf]⟩

/-- **The generic compaction bundle**: any renumbering that is positive,
identity off the kept tree, and order-isomorphic on occurring sibling pairs
induces a `StablePrefixMap` through the longest-kept-prefix translation. -/
def compactSPM (Γ : OrderedPrefixCode) (keep : List (List ℕ))
    (r : List ℕ → ℕ → ℕ) (𝒟 : List ℕ → Prop)
    (hKpos : ∀ k ∈ keep, PosChain k)
    (hDpos : ∀ ch, 𝒟 ch → PosChain ch)
    (hrPos : ∀ p d, 1 ≤ d → 1 ≤ r p d)
    (hrOff : ∀ p d, (p ++ [d]) ∉ keep → r p d = d)
    (hiso : ∀ p d e, Occ 𝒟 p d → Occ 𝒟 p e → d < e → r p d < r p e) :
    StablePrefixMap Γ where
  f := fStab Γ r keep
  Rest := compactRest Γ 𝒟
  MintAt := compactMintAt Γ keep 𝒟
  ext := by
    rintro π δ ⟨hδ, chA, rfl, hpos, hD, hnk⟩
    have hposm : PosChain (chA ++ [δ]) := hDpos _ hD
    have hcoord : coordOf Γ chA ++ Γ.enc δ = coordOf Γ (chA ++ [δ]) := by
      rw [coordOf_append]
      simp [coordOf]
    have hrm : remapChain r (chA ++ [δ]) = remapChain r chA ++ [δ] := by
      simp only [remapChain]
      rw [remapFrom_append, List.nil_append, remapFrom_cons,
        hrOff chA δ hnk]
      rfl
    rw [hcoord, fStab_coordOf Γ hKpos hrOff hposm,
      fStab_coordOf Γ hKpos hrOff hpos, hrm, coordOf_append]
    congr 1
    simp [coordOf]
  ord := by
    intro c c' h h'
    obtain ⟨ch, hch, rfl⟩ := compactDom_chain h
    obtain ⟨ch', hch', rfl⟩ := compactDom_chain h'
    rw [fStab_coordOf Γ hKpos hrOff (hDpos _ hch),
      fStab_coordOf Γ hKpos hrOff (hDpos _ hch')]
    exact remapChain_keyLt Γ hDpos hrPos hiso hch hch'

/-! ## §6 The concrete renumbering: drop dead ranges, rank-renumber
in-flight-free sibling groups -/

/-- The child deltas of `p` recorded in a chain list. -/
def kidsOf (K : List (List ℕ)) (p : List ℕ) : List ℕ :=
  K.filterMap (fun k => if k.dropLast = p then k.getLast? else none)

theorem mem_kidsOf {K : List (List ℕ)} {p : List ℕ} {d : ℕ} :
    d ∈ kidsOf K p ↔ (p ++ [d]) ∈ K := by
  simp only [kidsOf, List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, hsome⟩
    by_cases hdp : k.dropLast = p
    · rw [if_pos hdp] at hsome
      obtain ⟨l', rfl⟩ := List.getLast?_eq_some_iff.mp hsome
      rw [List.dropLast_concat] at hdp
      exact hdp ▸ hk
    · rw [if_neg hdp] at hsome
      exact absurd hsome (by simp)
  · intro hk
    exact ⟨p ++ [d], hk, by rw [if_pos (List.dropLast_concat), List.getLast?_concat]⟩

/-- The 1-based rank of `d` among the (deduplicated) deltas of a group. -/
def rankIn (ds : List ℕ) (d : ℕ) : ℕ :=
  (ds.dedup.filter (fun e => e ≤ d)).length

/-- Rank is strictly monotone against recorded deltas. -/
theorem rankIn_lt_rankIn {ds : List ℕ} {d e : ℕ} (hde : d < e)
    (he : e ∈ ds) : rankIn ds d < rankIn ds e := by
  have hsub : List.Sublist (ds.dedup.filter (fun a => a ≤ d))
      (ds.dedup.filter (fun a => a ≤ e)) := by
    apply List.monotone_filter_right
    intro a ha
    simp only [decide_eq_true_eq] at ha ⊢
    omega
  have hmem : e ∈ ds.dedup.filter (fun a => a ≤ e) :=
    List.mem_filter.mpr ⟨List.mem_dedup.mpr he, by simp⟩
  have hnmem : e ∉ ds.dedup.filter (fun a => a ≤ d) := by
    intro hmem'
    have := (List.mem_filter.mp hmem').2
    simp only [decide_eq_true_eq] at this
    omega
  refine Nat.lt_of_le_of_ne hsub.length_le (fun heq => ?_)
  have heql := hsub.eq_of_length heq
  rw [← heql] at hmem
  exact hnmem hmem

/-- A duplicate-free list of integers in `[1, d]` has at most `d` members. -/
theorem nodup_length_le_of_bounded :
    ∀ (d : ℕ) (l : List ℕ), l.Nodup → (∀ x ∈ l, 1 ≤ x ∧ x ≤ d) →
      l.length ≤ d
  | 0, [], _, _ => Nat.le_refl _
  | 0, x :: xs, _, hb => by
      obtain ⟨h1, h2⟩ := hb x List.mem_cons_self
      omega
  | d + 1, l, hnd, hb => by
      by_cases hmem : (d + 1) ∈ l
      · have hlen := List.length_erase_of_mem hmem
        have hle := nodup_length_le_of_bounded d (l.erase (d + 1))
          (hnd.erase _) (fun x hx => by
            have hx' := (hnd.mem_erase_iff).mp hx
            obtain ⟨h1, h2⟩ := hb x hx'.2
            have := hx'.1
            omega)
        have hpos : 1 ≤ l.length := by
          cases l with
          | nil => exact absurd hmem (List.not_mem_nil)
          | cons y ys => simp
        omega
      · have hle := nodup_length_le_of_bounded d l hnd (fun x hx => by
          obtain ⟨h1, h2⟩ := hb x hx
          rcases Nat.lt_or_ge x (d + 1) with h | h
          · omega
          · exact absurd (Nat.le_antisymm h2 h ▸ hx) hmem)
        omega

/-- Rank never exceeds the delta it renumbers (distinct positives below `d`
number at most `d`) — the freshness-domination half of H2. -/
theorem rankIn_le_self {ds : List ℕ} (hpos : ∀ x ∈ ds, 1 ≤ x) (d : ℕ) :
    rankIn ds d ≤ d := by
  apply nodup_length_le_of_bounded d _ ((List.nodup_dedup ds).filter _)
  intro x hx
  obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
  simp only [decide_eq_true_eq] at hx2
  exact ⟨hpos x (List.mem_dedup.mp hx1), hx2⟩

/-- Group `p` has a known in-flight child delta. -/
def skipAt (inflight : List (List ℕ)) (p : List ℕ) : Bool :=
  !(kidsOf inflight p).isEmpty

theorem skipAt_eq_false {inflight : List (List ℕ)} {p : List ℕ} :
    skipAt inflight p = false ↔ ∀ d, (p ++ [d]) ∉ inflight := by
  constructor
  · intro h d hd
    have hmem : d ∈ kidsOf inflight p := mem_kidsOf.mpr hd
    have : kidsOf inflight p ≠ [] := List.ne_nil_of_mem hmem
    simp only [skipAt, Bool.not_eq_false', List.isEmpty_iff] at h
    exact this h
  · intro h
    simp only [skipAt, Bool.not_eq_false', List.isEmpty_iff]
    cases hk : kidsOf inflight p with
    | nil => rfl
    | cons x xs =>
        have hx : x ∈ kidsOf inflight p := by
          rw [hk]
          exact List.mem_cons_self
        exact absurd (mem_kidsOf.mp hx) (h x)

/-- **(a) DROP dead ranges**: carry a stable chain forward iff it has a live
descendant in the tree or a known in-flight coordinate passes through it. -/
def ePruneKeep (tree : List (List ℕ)) (live : List ℕ → Bool)
    (inflight : List (List ℕ)) : List (List ℕ) :=
  tree.filter (fun k =>
    tree.any (fun k' => k.isPrefixOf k' && live k') ||
    inflight.any (fun q => k.isPrefixOf q))

theorem mem_ePruneKeep {tree : List (List ℕ)} {live : List ℕ → Bool}
    {inflight : List (List ℕ)} {k : List ℕ} :
    k ∈ ePruneKeep tree live inflight ↔
      k ∈ tree ∧ ((∃ k' ∈ tree, k <+: k' ∧ live k' = true) ∨
        ∃ q ∈ inflight, k <+: q) := by
  simp [ePruneKeep, List.mem_filter, List.any_eq_true,
    List.isPrefixOf_iff_prefix, Bool.and_eq_true, Bool.or_eq_true]

theorem ePruneKeep_subset {tree : List (List ℕ)} {live : List ℕ → Bool}
    {inflight : List (List ℕ)} :
    ∀ k ∈ ePruneKeep tree live inflight, k ∈ tree :=
  fun _ hk => (mem_ePruneKeep.mp hk).1

theorem ePruneKeep_prefix {tree : List (List ℕ)} {live : List ℕ → Bool}
    {inflight : List (List ℕ)} {k1 k2 : List ℕ}
    (h12 : k1 <+: k2) (h2 : k2 ∈ ePruneKeep tree live inflight)
    (h1 : k1 ∈ tree) : k1 ∈ ePruneKeep tree live inflight := by
  rcases mem_ePruneKeep.mp h2 with ⟨-, ⟨k', hk', hp, hl⟩ | ⟨q, hq, hp⟩⟩
  · exact mem_ePruneKeep.mpr ⟨h1, Or.inl ⟨k', hk', h12.trans hp, hl⟩⟩
  · exact mem_ePruneKeep.mpr ⟨h1, Or.inr ⟨q, hq, h12.trans hp⟩⟩

/-- **(b) RANK-RENUMBER**: dense ranks in kept, in-flight-free sibling
groups; identity everywhere else (off-tree nodes, and groups with known
in-flight children, which are skipped). -/
def rED (keep : List (List ℕ)) (inflight : List (List ℕ))
    (p : List ℕ) (d : ℕ) : ℕ :=
  if (p ++ [d]) ∈ keep ∧ skipAt inflight p = false
  then rankIn (kidsOf keep p) d else d

theorem rED_off {keep inflight : List (List ℕ)} :
    ∀ p d, (p ++ [d]) ∉ keep → rED keep inflight p d = d := by
  intro p d h
  rw [rED, if_neg (fun hc => h hc.1)]

theorem rED_pos {keep inflight : List (List ℕ)} :
    ∀ p d, 1 ≤ d → 1 ≤ rED keep inflight p d := by
  intro p d hd
  rw [rED]
  split
  · next hc =>
      have hdk : d ∈ kidsOf keep p := mem_kidsOf.mpr hc.1
      have hmem : d ∈ (kidsOf keep p).dedup.filter (fun a => a ≤ d) :=
        List.mem_filter.mpr ⟨List.mem_dedup.mpr hdk, by simp⟩
      exact Nat.pos_of_ne_zero (fun h0 =>
        List.ne_nil_of_mem hmem (List.eq_nil_of_length_eq_zero h0))
  · exact hd

/-- **The stage-2 soundness theorem for the concrete renumbering** (per-group
order-isomorphism + Lamport freshness): if every occurring delta at an
unskipped group is a surviving kid or fresh (dominates every kid), `rED` is
strictly monotone on occurring sibling pairs — H2's hypothesis. -/
theorem rED_iso {keep inflight : List (List ℕ)} {𝒟 : List ℕ → Prop}
    (hKpos : ∀ k ∈ keep, PosChain k)
    (hocc : ∀ p d, Occ 𝒟 p d → skipAt inflight p = false →
      (p ++ [d]) ∈ keep ∨ ∀ e, (p ++ [e]) ∈ keep → e < d) :
    ∀ p d e, Occ 𝒟 p d → Occ 𝒟 p e → d < e →
      rED keep inflight p d < rED keep inflight p e := by
  intro p d e hd he hde
  by_cases hskip : skipAt inflight p = false
  · have hkids_pos : ∀ x ∈ kidsOf keep p, 1 ≤ x := by
      intro x hx
      exact hKpos _ (mem_kidsOf.mp hx) x
        (List.mem_append_right _ List.mem_cons_self)
    rcases hocc p d hd hskip with hkd | hfd
    · rcases hocc p e he hskip with hke | hfe
      · rw [rED, if_pos ⟨hkd, hskip⟩, rED, if_pos ⟨hke, hskip⟩]
        exact rankIn_lt_rankIn hde (mem_kidsOf.mpr hke)
      · have h1 : rED keep inflight p d = rankIn (kidsOf keep p) d := by
          rw [rED, if_pos ⟨hkd, hskip⟩]
        have h2 : rED keep inflight p e = e :=
          rED_off p e (fun hc => absurd (hfe e hc) (Nat.lt_irrefl e))
        rw [h1, h2]
        exact Nat.lt_of_le_of_lt (rankIn_le_self hkids_pos d) hde
    · rcases hocc p e he hskip with hke | hfe
      · exact absurd (hfd e hke) (Nat.lt_asymm hde)
      · rw [rED_off p d (fun hc => absurd (hfd d hc) (Nat.lt_irrefl d)),
          rED_off p e (fun hc => absurd (hfe e hc) (Nat.lt_irrefl e))]
        exact hde
  · rw [rED, if_neg (fun hc => hskip hc.2), rED, if_neg (fun hc => hskip hc.2)]
    exact hde

/-- The ranked compaction at any ordered prefix code, packaged as a
`StablePrefixMap`. -/
def compactRanked (Γ : OrderedPrefixCode) (tree : List (List ℕ))
    (live : List ℕ → Bool) (inflight : List (List ℕ)) (𝒟 : List ℕ → Prop)
    (htpos : ∀ k ∈ tree, PosChain k)
    (hDpos : ∀ ch, 𝒟 ch → PosChain ch)
    (hocc : ∀ p d, Occ 𝒟 p d → skipAt inflight p = false →
      (p ++ [d]) ∈ ePruneKeep tree live inflight ∨
      ∀ e, (p ++ [e]) ∈ ePruneKeep tree live inflight → e < d) :
    StablePrefixMap Γ :=
  compactSPM Γ (ePruneKeep tree live inflight)
    (rED (ePruneKeep tree live inflight) inflight) 𝒟
    (fun k hk => htpos k (ePruneKeep_subset k hk))
    hDpos
    (rED_pos)
    (rED_off)
    (rED_iso (fun k hk => htpos k (ePruneKeep_subset k hk)) hocc)

/-- **`compactEliasDelta`** — the concrete verified compaction: drop dead
ranges, rank-renumber in-flight-free sibling groups, re-encode with the
flipped Elias-δ code. -/
abbrev compactEliasDelta (tree : List (List ℕ)) (live : List ℕ → Bool)
    (inflight : List (List ℕ)) (𝒟 : List ℕ → Prop)
    (htpos : ∀ k ∈ tree, PosChain k)
    (hDpos : ∀ ch, 𝒟 ch → PosChain ch)
    (hocc : ∀ p d, Occ 𝒟 p d → skipAt inflight p = false →
      (p ++ [d]) ∈ ePruneKeep tree live inflight ∨
      ∀ e, (p ++ [e]) ∈ ePruneKeep tree live inflight → e < d) :
    StablePrefixMap eliasDeltaCode :=
  compactRanked eliasDeltaCode tree live inflight 𝒟 htpos hDpos hocc

/-- The at-hand chains of a settled cut: chains of cut-live settled inserts,
of known in-flight inserts, and of new-epoch (beyond-`Ev`) inserts — the
domain over which the compaction must preserve order. -/
def EAtHand (Γ : OrderedPrefixCode) (C : Configuration (E Γ α))
    (S Ev : Set (Op (EOp α))) (inflight : List (List ℕ))
    (chainOf : ℕ → List ℕ) (ch : List ℕ) : Prop :=
  ∃ o, o ∈ C.events ∧ eIsIns o = true ∧ chainOf o.1 = ch ∧
    ((o ∈ S ∧ ∀ dl ∈ Ev, dl.2.2 ≠ EOp.del o.1) ∨
      chainOf o.1 ∈ inflight ∨ o ∉ Ev)

/-! ## §7 The headline: at a settled cut of a disciplined honest
configuration, the ranked compaction preserves every read

Data adequacy (`hTree`/`hTreeS`/`hLive`/`hInflight`) is the protocol half's
obligation (recoding note §6), stated **coordinate-addressed** (chains
matched through `coordOf`, never ids). Everything else is proved: the
kids-or-fresh trichotomy classifies every occurrence by its realizer's
epoch — settled (kept, via anchor-liveness), in-flight (skipped), or beyond
(Lamport-fresh via `causal_mono` + `settledAt_dichotomy`). -/

theorem compactRanked_settled_reads {Γ : OrderedPrefixCode}
    {C : Configuration (E Γ α)} (hReach : EReach Γ C)
    (hGen : GenHonest (E Γ α) eApplicable C)
    (hEnum : CausalPastEnumerable (E Γ α) C)
    {v : Version} {s : EState α} {Ev S : Set (Op (EOp α))}
    (hv : C.ver v = some (s, Ev)) (hsettled : SettledAtOn C Ev S)
    (tree : List (List ℕ)) (live : List ℕ → Bool) (inflight : List (List ℕ))
    (htpos : ∀ k ∈ tree, PosChain k)
    (hTree : ∀ o, o ∈ C.events → eIsIns o = true → o ∈ S →
      ∃ k ∈ tree, coordOf Γ k = eCoord Γ o)
    (hTreeS : ∀ k ∈ tree, ∃ o, o ∈ S ∧ o ∈ C.events ∧ eIsIns o = true ∧
      coordOf Γ k = eCoord Γ o)
    (hLive : ∀ k ∈ tree, ∀ o, o ∈ C.events → o ∈ S → eIsIns o = true →
      coordOf Γ k = eCoord Γ o → (∀ dl ∈ S, dl.2.2 ≠ EOp.del o.1) →
      live k = true)
    (hInflight : ∀ o, o ∈ C.events → eIsIns o = true → o ∈ Ev → o ∉ S →
      ∃ q ∈ inflight, PosChain q ∧ coordOf Γ q = eCoord Γ o) :
    ∃ F : StablePrefixMap Γ,
      F.f = fStab Γ (rED (ePruneKeep tree live inflight) inflight)
        (ePruneKeep tree live inflight) ∧
      ∀ τ : List (Op (EOp α)), (∀ o ∈ τ, o ∈ C.events ∧ o ∉ Ev) →
        applySeq (E Γ α).toCRDTSig (eRemapSt F.f s) (τ.map (eRemapOp F.f))
            = eRemapSt F.f (applySeq (E Γ α).toCRDTSig s τ) ∧
          (E Γ α).query
              (applySeq (E Γ α).toCRDTSig (eRemapSt F.f s)
                (τ.map (eRemapOp F.f))) ()
            = (E Γ α).query (applySeq (E Γ α).toCRDTSig s τ) () := by
  classical
  obtain ⟨chainOf, hA⟩ := eAnchored_exists hGen hEnum
  have hHon : EHonest Γ C := eHonest_of_genHonest C hEnum hGen
  have hGood := e_goodConfig3 hReach
  have hEvSub : ∀ a ∈ Ev, a ∈ C.events :=
    fun a ha => hGood.ver_events_sub v s Ev hv a ha
  have hSsub : ∀ a ∈ S, a ∈ C.events := fun a ha => hEvSub a (hsettled.sub ha)
  have hirr : ∀ a : Op (EOp α), ¬ C.vis a a :=
    fun a ha => absurd (C.causal_mono ha) (Nat.lt_irrefl a.1)
  -- the chain of an event is pinned by its coordinate
  have hchain_eq : ∀ o, o ∈ C.events → eIsIns o = true → ∀ k, PosChain k →
      coordOf Γ k = eCoord Γ o → chainOf o.1 = k := by
    intro o ho hi k hk hck
    apply coordOf_inj Γ (hA.pos o ho hi) hk
    rw [← hA.coord o ho hi]
    exact hck.symm
  have hsum_node : ∀ a, a ∈ C.events → eIsIns a = true →
      ∀ p d, chainOf a.1 = p ++ [d] → a.1 = p.sum + d := by
    intro a ha hi p d hch
    have h1 := hA.sum a ha hi
    rw [hch] at h1
    simp only [List.sum_append, List.sum_cons, List.sum_nil,
      Nat.add_zero] at h1
    exact h1.symm
  have hids_eq : ∀ a b, a ∈ C.events → b ∈ C.events → eIsIns a = true →
      eIsIns b = true → chainOf a.1 = chainOf b.1 → a = b := by
    intro a b ha hb hai hbi hch
    apply (Configuration.core C).ts_unique ha hb
    have h1 := hA.sum a ha hai
    have h2 := hA.sum b hb hbi
    rw [hch] at h1
    exact h1.symm.trans h2
  set keep := ePruneKeep tree live inflight with hkeep
  -- the at-hand chain domain
  have hDpos : ∀ ch, EAtHand Γ C S Ev inflight chainOf ch → PosChain ch := by
    rintro ch ⟨o, ho, hi, rfl, -⟩
    exact hA.pos o ho hi
  have htree_of : ∀ a, a ∈ C.events → a ∈ S → eIsIns a = true →
      chainOf a.1 ∈ tree := by
    intro a haev haS hai
    obtain ⟨kt, hktm, hktc⟩ := hTree a haev hai haS
    rw [hchain_eq a haev hai kt (htpos kt hktm) hktc]
    exact hktm
  have hlive_of : ∀ a k, a ∈ C.events → a ∈ S → eIsIns a = true →
      chainOf a.1 = k → (∀ dl ∈ S, dl.2.2 ≠ EOp.del a.1) →
      k ∈ keep := by
    intro a k haev haS hai hak hnoSdel
    have hktree : k ∈ tree := hak ▸ htree_of a haev haS hai
    have hlv : live k = true := hLive k hktree a haev haS hai
      (by rw [← hak]; exact (hA.coord a haev hai).symm) hnoSdel
    exact mem_ePruneKeep.mpr ⟨hktree, Or.inl ⟨k, hktree, List.prefix_refl k, hlv⟩⟩
  -- the kept lemma: settled-realized nodes on at-hand chains survive pruning
  have hKept : ∀ (u ch : List ℕ), EAtHand Γ C S Ev inflight chainOf ch →
      ∀ k, ch = k ++ u → k ≠ [] →
      (∃ a, a ∈ C.events ∧ a ∈ S ∧ eIsIns a = true ∧ chainOf a.1 = k) →
      k ∈ keep := by
    intro u
    induction u with
    | nil =>
        rintro ch ⟨o, ho, hi, hcho, hcase⟩ k hch hkne ⟨a, haev, haS, hai, hak⟩
        rw [List.append_nil] at hch
        rw [hch] at hcho
        have hoa : o = a := hids_eq o a ho haev hi hai (by rw [hcho, hak])
        subst hoa
        rcases hcase with ⟨-, hcut⟩ | hinfl | hnotEv
        · exact hlive_of o k ho haS hi hak
            (fun dl hdl => hcut dl (hsettled.sub hdl))
        · rw [hak] at hinfl
          exact mem_ePruneKeep.mpr ⟨hak ▸ htree_of o ho haS hi,
            Or.inr ⟨k, hinfl, List.prefix_refl k⟩⟩
        · exact absurd (hsettled.sub haS) hnotEv
    | cons x u' ih =>
        rintro ch hD k hch hkne ⟨a, haev, haS, hai, hak⟩
        have hwit := hD
        obtain ⟨o, ho, hi, hcho, -⟩ := hwit
        have hpre : (k ++ [x]) <+: chainOf o.1 := by
          rw [hcho, hch]
          exact prefix_snoc_cons k x u'
        obtain ⟨b, hbev, hbi, hbk⟩ := hA.realize o ho hi k x hpre
        by_cases hbS : b ∈ S
        · have hk' : (k ++ [x]) ∈ keep := ih ch hD (k ++ [x])
            (by rw [hch]; simp) (by simp) ⟨b, hbev, hbS, hbi, hbk⟩
          exact ePruneKeep_prefix ⟨[x], rfl⟩ hk'
            (hak ▸ htree_of a haev haS hai)
        · by_cases hbEv : b ∈ Ev
          · obtain ⟨q, hqm, hqpos, hqc⟩ := hInflight b hbev hbi hbEv hbS
            have hqk : chainOf b.1 = q := hchain_eq b hbev hbi q hqpos hqc
            exact mem_ePruneKeep.mpr ⟨hak ▸ htree_of a haev haS hai,
              Or.inr ⟨q, hqm, by rw [← hqk, hbk]; exact ⟨[x], rfl⟩⟩⟩
          · -- b beyond the cut: its anchor is k's settled record, live in S
            obtain ⟨eb, πb, db, hop⟩ : ∃ eb πb db, b.2.2 = EOp.ins eb πb db := by
              obtain ⟨tb, rb, opb⟩ := b
              cases opb with
              | del y => simp [eIsIns] at hbi
              | ins eb πb db => exact ⟨eb, πb, db, rfl⟩
            obtain ⟨-, -, hchb⟩ := hA.anchored b hbev eb πb db hop
            have hcomb : k ++ [x] = chainOf db ++ [b.1 - db] :=
              hbk.symm.trans hchb
            have hdbk : chainOf db = k := by
              have h := congrArg List.dropLast hcomb
              rw [List.dropLast_concat, List.dropLast_concat] at h
              exact h.symm
            have hdb0 : db ≠ 0 := by
              intro h0
              rw [h0, hA.root] at hdbk
              exact hkne hdbk.symm
            obtain ⟨⟨a', ha'ev, ha'i, ha'1, -⟩, hblive⟩ :=
              hA.anchor_event b hbev eb πb db hop hdb0
            have ha'a : a' = a := hids_eq a' a ha'ev haev ha'i hai
              (by rw [ha'1, hdbk, hak])
            have hdba : db = a.1 := by rw [← ha'1, ha'a]
            refine hlive_of a k haev haS hai hak ?_
            intro dl hdl
            have hdlvis : C.vis dl b :=
              settledAt_dichotomy hsettled b hbev hbEv dl hdl
            have := hblive dl (hSsub dl hdl) hdlvis
            rwa [hdba] at this
  -- kids-or-fresh: the occurrence trichotomy
  have hocc : ∀ p d, Occ (EAtHand Γ C S Ev inflight chainOf) p d →
      skipAt inflight p = false →
      (p ++ [d]) ∈ keep ∨ ∀ e, (p ++ [e]) ∈ keep → e < d := by
    rintro p d ⟨ch, hD, hpre⟩ hskip
    have hwit := hD
    obtain ⟨o, ho, hi, hcho, -⟩ := hwit
    obtain ⟨b, hbev, hbi, hbk⟩ := hA.realize o ho hi p d
      (by rw [hcho]; exact hpre)
    by_cases hbS : b ∈ S
    · left
      obtain ⟨u, hu⟩ := hpre
      exact hKept u ch hD (p ++ [d]) hu.symm (by simp)
        ⟨b, hbev, hbS, hbi, hbk⟩
    · by_cases hbEv : b ∈ Ev
      · obtain ⟨q, hqm, hqpos, hqc⟩ := hInflight b hbev hbi hbEv hbS
        have : (p ++ [d]) ∈ inflight := by
          rw [← hbk, hchain_eq b hbev hbi q hqpos hqc]
          exact hqm
        exact absurd this (skipAt_eq_false.mp hskip d)
      · right
        intro e hke
        have hkt : (p ++ [e]) ∈ tree := ePruneKeep_subset _ hke
        obtain ⟨oe, hoeS, hoeev, hoei, hoec⟩ := hTreeS _ hkt
        have hoek : chainOf oe.1 = p ++ [e] :=
          hchain_eq oe hoeev hoei _ (htpos _ hkt) hoec
        have hlt := C.causal_mono
          (settledAt_dichotomy hsettled b hbev hbEv oe hoeS)
        rw [hsum_node oe hoeev hoei p e hoek,
          hsum_node b hbev hbi p d hbk] at hlt
        exact Nat.lt_of_add_lt_add_left hlt
  -- the bundle
  set F : StablePrefixMap Γ := compactRanked Γ tree live inflight
    (EAtHand Γ C S Ev inflight chainOf) htpos hDpos hocc with hFdef
  -- the canonical chain-aligned mints land in the bundle's MintAt
  have hMint : ∀ π δ, ChainMintBeyond Γ C S chainOf π δ →
      compactMintAt Γ keep (EAtHand Γ C S Ev inflight chainOf) π δ := by
    rintro π δ ⟨hδ, chA, hπ, hposA, o, ho, hi, hvisS, hcho⟩
    have hoS : o ∉ S := fun hoS => hirr o (hvisS o hoS)
    refine ⟨hδ, chA, hπ, hposA, ⟨o, ho, hi, hcho, ?_⟩, ?_⟩
    · by_cases hoEv : o ∈ Ev
      · obtain ⟨q, hqm, hqpos, hqc⟩ := hInflight o ho hi hoEv hoS
        exact Or.inr (Or.inl (by
          rw [hchain_eq o ho hi q hqpos hqc]; exact hqm))
      · exact Or.inr (Or.inr hoEv)
    · intro hk
      have hkt : (chA ++ [δ]) ∈ tree := ePruneKeep_subset _ hk
      obtain ⟨oe, hoeS, hoeev, hoei, hoec⟩ := hTreeS _ hkt
      have hoek : chainOf oe.1 = chA ++ [δ] :=
        hchain_eq oe hoeev hoei _ (htpos _ hkt) hoec
      have hooe : o = oe :=
        hids_eq o oe ho hoeev hi hoei (hcho.trans hoek.symm)
      exact hoS (hooe ▸ hoeS)
  have hAF : AnchorsFactorBeyond Γ F C S :=
    anchorsFactorBeyond_of_anchored hA F S hMint
  -- the cut state's coordinates are at rest (survival = never deleted in Ev)
  obtain ⟨ρ, hperm, hresp, happ⟩ := hGood.canonical v s Ev hv
  have hin : ∀ a ∈ Ev, a ∈ (Configuration.core C).events := by
    intro a ha
    rw [core_events]
    exact hEvSub a ha
  have hcl : ∀ a b, (Configuration.core C).vis a b →
      ¬ (E Γ α).toCRDTSig.commutes a b → b ∈ Ev → a ∈ Ev :=
    fun a b hvis _ hb => hGood.ver_causal v s Ev hv a b hvis hb
  have hwf := e_wf_of_enum (eHonest_core hHon) hin hcl hperm hresp
  have hrest : ∀ x ∈ s, F.Dom x.2.2 := by
    intro x hx
    rw [← happ] at hx
    obtain ⟨⟨o, hoρ, hoi, hrec⟩, hnd⟩ := (e_fold_mem Γ hwf x).mp hx
    have hoEv : o ∈ Ev := (hperm.2 o).mp hoρ
    have hoev : o ∈ C.events := hEvSub o hoEv
    have hx22 : x.2.2 = eCoord Γ o := by rw [hrec]; rfl
    have hx1 : x.1 = o.1 := by rw [hrec]; rfl
    refine Or.inl ⟨chainOf o.1, ⟨o, hoev, hoi, rfl, ?_⟩, by
      rw [hx22]; exact hA.coord o hoev hoi⟩
    by_cases hoS : o ∈ S
    · refine Or.inl ⟨hoS, fun dl hdl hddl => hnd ?_⟩
      rw [hx1]
      exact mem_eDels.mpr ⟨dl, (hperm.2 dl).mpr hdl, hddl⟩
    · obtain ⟨q, hqm, hqpos, hqc⟩ := hInflight o hoev hoi hoEv hoS
      exact Or.inr (Or.inl (by
        rw [hchain_eq o hoev hoi q hqpos hqc]; exact hqm))
  exact ⟨F, rfl, fun τ hτ =>
    eRecode_settled_bridge F hv hsettled hAF hrest τ hτ⟩

/-- **The composed headline, at the Elias-δ code**: at a `SettledAtOn`
cut of a disciplined honest configuration, the compaction — drop dead
ranges, rank-renumber in-flight-free sibling groups, re-encode with the
flipped Elias-δ code — preserves the fold and every read of every beyond-cut
continuation. Pure instantiation of `compactRanked_settled_reads`. -/
theorem compactEliasDelta_settled_reads
    {C : Configuration (E eliasDeltaCode α)}
    (hReach : EReach eliasDeltaCode C)
    (hGen : GenHonest (E eliasDeltaCode α) eApplicable C)
    (hEnum : CausalPastEnumerable (E eliasDeltaCode α) C)
    {v : Version} {s : EState α} {Ev S : Set (Op (EOp α))}
    (hv : C.ver v = some (s, Ev)) (hsettled : SettledAtOn C Ev S)
    (tree : List (List ℕ)) (live : List ℕ → Bool) (inflight : List (List ℕ))
    (htpos : ∀ k ∈ tree, PosChain k)
    (hTree : ∀ o, o ∈ C.events → eIsIns o = true → o ∈ S →
      ∃ k ∈ tree, coordOf eliasDeltaCode k = eCoord eliasDeltaCode o)
    (hTreeS : ∀ k ∈ tree, ∃ o, o ∈ S ∧ o ∈ C.events ∧ eIsIns o = true ∧
      coordOf eliasDeltaCode k = eCoord eliasDeltaCode o)
    (hLive : ∀ k ∈ tree, ∀ o, o ∈ C.events → o ∈ S → eIsIns o = true →
      coordOf eliasDeltaCode k = eCoord eliasDeltaCode o →
      (∀ dl ∈ S, dl.2.2 ≠ EOp.del o.1) → live k = true)
    (hInflight : ∀ o, o ∈ C.events → eIsIns o = true → o ∈ Ev → o ∉ S →
      ∃ q ∈ inflight, PosChain q ∧
        coordOf eliasDeltaCode q = eCoord eliasDeltaCode o) :
    ∃ F : StablePrefixMap eliasDeltaCode,
      F.f = fStab eliasDeltaCode
          (rED (ePruneKeep tree live inflight) inflight)
          (ePruneKeep tree live inflight) ∧
      ∀ τ : List (Op (EOp α)), (∀ o ∈ τ, o ∈ C.events ∧ o ∉ Ev) →
        applySeq (E eliasDeltaCode α).toCRDTSig
            (eRemapSt F.f s) (τ.map (eRemapOp F.f))
            = eRemapSt F.f (applySeq (E eliasDeltaCode α).toCRDTSig s τ) ∧
          (E eliasDeltaCode α).query
              (applySeq (E eliasDeltaCode α).toCRDTSig
                (eRemapSt F.f s) (τ.map (eRemapOp F.f))) ()
            = (E eliasDeltaCode α).query
                (applySeq (E eliasDeltaCode α).toCRDTSig s τ) () :=
  compactRanked_settled_reads hReach hGen hEnum hv hsettled tree live
    inflight htpos hTree hTreeS hLive hInflight

/-! ## §8 Axiom audit -/

#print axioms remapChain_keyLt
#print axioms rED_iso
#print axioms compactRanked_settled_reads
#print axioms compactEliasDelta_settled_reads

/-! ## §9 SPOT — the worked compaction, hand-derived (PASS + FAIL)

**PASS**: a delete-heavy epoch-0 history at the Elias-δ code (six inserts,
four deletes). Root group `{1,2,3,4,9}`, survivor `4`; `9` dead but kept (its
child `[9,5]` is live). `ePruneKeep` drops `[1],[2],[3]`; `rED` renumbers the
root group `4↦1, 9↦2` and the `[9]` group `5↦1`. Beyond the cut: a child of
the survivor (δ=6), a fresh root mint (δ=21 — Lamport-fresh, dominating both
renumbered ordinals), and a delete. Reads pinned equal (`[108, 106, 107]`,
hand-derived: root deltas 21 > 9/2 dominate, ancestor before descendant);
coordinate weight pinned 40 → 24 bits (hand-summed: 13+18+9 vs 5+10+9).

**FAIL companion**: same cut, but an epoch-0 in-flight root insert (chain
`[6]`) is still undelivered. The *unguarded* dense renumbering (`rED` fed an
empty in-flight list — the tempting degenerate) maps `9↦2` under the
in-flight `6`, and the read flips to `[110, 106, 104]`: the late op jumps the
compacted survivor. The *guarded* construction (`skipAt` sees `[6]`) skips
the root group (`4,9` frozen), still renumbers the in-flight-free `[9]` group
(`5↦1`, 13→9 bits), and the read stays pinned `[106, 110, 104]`. -/

namespace CompactSPOT

open Sal.EmbedRGA (dEnc)

/-- Epoch 0, delete-heavy: chains `[1] [2] [3] [4] [9] [9,5]`; deletes kill
`1, 2, 3, 9`. Survivors: `104` (chain `[4]`), `106` (chain `[9,5]`). -/
def preOps : List (Op (EOp ℕ)) :=
  [ (1, 0, .ins 101 [] 0)
  , (2, 0, .ins 102 [] 0)
  , (3, 0, .ins 103 [] 0)
  , (4, 0, .ins 104 [] 0)
  , (9, 0, .ins 105 [] 0)
  , (14, 0, .ins 106 (dEnc 9) 9)
  , (15, 0, .del 1)
  , (16, 0, .del 2)
  , (17, 0, .del 3)
  , (18, 0, .del 9) ]

def sCut : EState ℕ := eFold eliasDeltaCode preOps

/-- The cut state, hand-derived: two survivors, the deep one carrying its
dead ancestor's 8-bit codeword. -/
theorem cut_state : sCut = [(14, 106, dEnc 9 ++ dEnc 5), (4, 104, dEnc 4)] := by
  native_decide

def tree0 : List (List ℕ) := [[1], [2], [3], [4], [9], [9, 5]]
def live0 : List ℕ → Bool := fun k => decide (k = [4] ∨ k = [9, 5])
def keep0 : List (List ℕ) := ePruneKeep tree0 live0 []

/-- **(a) DROP pinned**: the dead ranges `[1],[2],[3]` are dropped; dead `[9]`
is kept (live descendant). NOT the whole tree, NOT only the live leaves. -/
theorem keep_drops_dead : keep0 = [[4], [9], [9, 5]] ∧ keep0 ≠ tree0 := by
  native_decide

/-- The translation: rank-renumber + Elias-δ re-encode below `keep0`. -/
def gcf : List Bool → List Bool := fStab eliasDeltaCode (rED keep0 []) keep0

/-- **(b) RENUMBER pinned at codeword level**: `4 ↦ 1` (5 bits → 1),
`[9,5] ↦ [2,1]` (13 bits → 5). -/
theorem remap_concrete :
    gcf (dEnc 4) = dEnc 1 ∧ gcf (dEnc 9 ++ dEnc 5) = dEnc 2 ++ dEnc 1 := by
  native_decide

/-- Beyond the cut: a child of the deep survivor (δ = 6), a fresh root mint
(δ = 21), a delete of the shallow survivor. -/
def postOps : List (Op (EOp ℕ)) :=
  [ (20, 0, .ins 107 (dEnc 9 ++ dEnc 5) 14)
  , (21, 0, .ins 108 [] 0)
  , (22, 0, .del 4) ]

def finalO : EState ℕ := applySeq (E eliasDeltaCode).toCRDTSig sCut postOps

def finalR : EState ℕ :=
  applySeq (E eliasDeltaCode).toCRDTSig (eRemapSt gcf sCut)
    (postOps.map (eRemapOp gcf))

/-- PASS: compaction is invisible — both reads are the hand-derived
`[108, 106, 107]` (21 first, then the `9`-subtree, ancestor before child). -/
theorem reads_identical :
    SPOT.readE finalR = [108, 106, 107] ∧
    SPOT.readE finalO = [108, 106, 107] := by native_decide

/-- PASS: the compaction genuinely compresses under the Elias-δ code:
24 < 40 bits, hand-summed (`106`: 13→5, `107`: 18→10, `108`: 9→9). -/
theorem size_reduced :
    SPOT.coordWeight finalR = 24 ∧ SPOT.coordWeight finalO = 40 := by
  native_decide

/-- Degenerate-behavior pin: the read equality is NOT the identity map
echoing the state — the compacted state differs record-for-record. -/
theorem compaction_not_identity :
    eRemapSt gcf sCut ≠ sCut ∧ finalR ≠ finalO := by native_decide

/-! ### The FAIL companion: an in-flight sibling -/

/-- The in-flight epoch-0 op: a root insert (chain `[6]`), minted before the
cut, not yet delivered. -/
def flightOp : Op (EOp ℕ) := (6, 0, .ins 110 [] 0)

def inflight1 : List (List ℕ) := [[6]]

def keepF : List (List ℕ) := ePruneKeep tree0 live0 inflight1

/-- The guard, pinned: the root group has a known in-flight child ⟹ skipped;
the `[9]` group has none ⟹ renumbered. -/
theorem skip_guard :
    skipAt inflight1 [] = true ∧ skipAt inflight1 [9] = false := by
  native_decide

/-- Guarded map (skips the root group). -/
def gcfG : List Bool → List Bool :=
  fStab eliasDeltaCode (rED keepF inflight1) keepF

/-- UNGUARDED dense renumbering — the tempting degenerate: renumber every
kept group, ignoring the in-flight sibling. -/
def gcfU : List Bool → List Bool := fStab eliasDeltaCode (rED keepF []) keepF

def finalOF : EState ℕ := applySeq (E eliasDeltaCode).toCRDTSig sCut [flightOp]

def finalG : EState ℕ :=
  applySeq (E eliasDeltaCode).toCRDTSig (eRemapSt gcfG sCut)
    [eRemapOp gcfG flightOp]

def finalU : EState ℕ :=
  applySeq (E eliasDeltaCode).toCRDTSig (eRemapSt gcfU sCut)
    [eRemapOp gcfU flightOp]

/-- FAIL: unguarded dense renumbering FLIPS the pinned order — `9 ↦ 2` slides
the compacted survivor under the in-flight `6`, and the late op jumps from
the middle to the front. -/
theorem unguarded_flips_order :
    SPOT.readE finalOF = [106, 110, 104] ∧
    SPOT.readE finalU = [110, 106, 104] ∧
    SPOT.readE finalU ≠ SPOT.readE finalOF := by native_decide

/-- PASS: the guarded construction skips exactly that group and the read
stays pinned — while the in-flight-free `[9]` group still compresses
(23 → 19 bits: `106` sheds 4 bits of dead-delta codeword). -/
theorem guarded_skips_group :
    SPOT.readE finalG = [106, 110, 104] ∧
    SPOT.coordWeight finalG = 19 ∧ SPOT.coordWeight finalOF = 23 := by
  native_decide

#print axioms cut_state
#print axioms keep_drops_dead
#print axioms remap_concrete
#print axioms reads_identical
#print axioms size_reduced
#print axioms compaction_not_identity
#print axioms skip_guard
#print axioms unguarded_flips_order
#print axioms guarded_skips_group

end CompactSPOT

end Sal.ConditionedMRDTs
