import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_CompactEliasDelta

/-!
# Multi-epoch composition for the embed GC

The single-epoch story is closed: at a `SettledAtOn` cut of a disciplined
honest configuration, one compaction (`compactEliasDelta_settled_reads`)
preserves the fold and every read of every beyond-cut continuation. But the
re-coded configuration is **not** a native honest configuration (compacted
coordinates are no longer birth-chain telescopes), so a *second* epoch cannot
re-invoke the single-epoch theorem on it. This file supplies the composed
statement: arbitrarily many settled-cut compactions preserve reads, by a
statement that re-invokes at every epoch.

**Composition closure carried.** The semantic residue of one
compaction is a `StablePrefixMap`; the semantic residue of *n* compactions is
their composition, and the composition of two `StablePrefixMap`s is again one.
H2 (`ord`) composes because order-isomorphisms compose; H3 (`ext`/`MintAt`)
composes at the boundary — an epoch-1 mint `(π, d)`, once epoch-1-remapped,
is an epoch-2 mint `(F₁.f π, d)` (the delta codeword is never touched by any
map); H1 (injectivity) is derived per the bundle.

**The one subtlety that makes it non-trivial.** Naive composition
*on the full first-epoch domain* is unsound whenever epoch 2 reclaims the rank
of a record that died between the two epochs: the dead coordinate and the
reclaimed live coordinate collide under `F₂.f ∘ F₁.f`, so `ord`/`injOn` fail.
`comp` therefore carries the composite's *own* at-hand domain `(Rest', MintAt')`
— the coordinates surviving to epoch 2, coordinate-addressed, never id-addressed
(the runtime twin's erratum: after epoch one, renumbered coordinates no longer
telescope to event ids; §7 SPOT `id_addressing_breaks` pins this as a kernel
fact). `CompatOn` states the four boundary conditions, and everything downstream
(`ord`, `ext`, `injOn`) transports.

Contents:
* §1 `CompatOn` / `comp` — the domain-restricted binary composition closure;
  `Compat` / `comp_simple` — the full-domain special case (no reclaim).
* §2 remap plumbing (`eRemapSt_comp`, `eRemapOp_comp`, `applySeq` domain
  preservation).
* §3 `twoEpoch_reads` — compact, continue (settling), compact again, continue
  (lagging): reads pinned, re-invoking T1 at each epoch.
* §4 `chainComp` / `multiEpoch_settled_reads` — the n-epoch headline over a
  list of maps.
* §5 `rED_le_self` — the future-mint-freshness-post-epoch lemma (renumbering
  never grows a delta, so freshness/domination survives every epoch).
* §7 SPOTs (PASS: a directed two-epoch scenario, reads pinned throughout;
  FAIL: id-addressing breaks after epoch one, and the dead-rank collision).
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode keyLt key keyLt_total keyLt_irrefl key_inj
  coordOf coordOf_append PosChain)

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §1  The composition closure -/

/-- **The boundary conditions for composing two stable-prefix maps.** `F` is
the earlier epoch's map, `G` the later; `(Rest', MintAt')` is the *composite*'s
own at-hand domain — the coordinates surviving to `G`'s epoch. The four clauses
say those coordinates are at hand for `F` (so `F`'s `ord`/`ext` apply) and, once
`F`-remapped, at hand for `G` (so `G`'s apply). Restricting to the surviving
domain is exactly what avoids the dead-rank collision (file header). -/
structure CompatOn {Γ : OrderedPrefixCode} (F G : StablePrefixMap Γ)
    (Rest' : List Bool → Prop) (MintAt' : List Bool → ℕ → Prop) : Prop where
  restF : ∀ c, Rest' c → F.Dom c
  restG : ∀ c, Rest' c → G.Dom (F.f c)
  mintF : ∀ π d, MintAt' π d → F.MintAt π d
  mintG : ∀ π d, MintAt' π d → G.MintAt (F.f π) d

namespace CompatOn

variable {Γ : OrderedPrefixCode} {F G : StablePrefixMap Γ}
  {Rest' : List Bool → Prop} {MintAt' : List Bool → ℕ → Prop}

/-- A composite-domain coordinate is at hand for the earlier map. -/
theorem domF (h : CompatOn F G Rest' MintAt') {c : List Bool}
    (hc : Rest' c ∨ ∃ π d, MintAt' π d ∧ c = π ++ Γ.enc d) : F.Dom c := by
  rcases hc with hr | ⟨π, d, hm, rfl⟩
  · exact h.restF c hr
  · exact Or.inr ⟨π, d, h.mintF π d hm, rfl⟩

/-- A composite-domain coordinate, once earlier-remapped, is at hand for the
later map. -/
theorem domG (h : CompatOn F G Rest' MintAt') {c : List Bool}
    (hc : Rest' c ∨ ∃ π d, MintAt' π d ∧ c = π ++ Γ.enc d) : G.Dom (F.f c) := by
  rcases hc with hr | ⟨π, d, hm, rfl⟩
  · exact h.restG c hr
  · rw [F.ext (h.mintF π d hm)]
    exact Or.inr ⟨F.f π, d, h.mintG π d hm, rfl⟩

end CompatOn

/-- **The composition closure**: the composite `G.f ∘ F.f` of two stable-prefix
maps, carrying the surviving domain `(Rest', MintAt')`, is again a stable-prefix
map. H3 (`ext`) chains through both maps' `ext`; H2 (`ord`) chains through both
maps' order-isos; H1 (`injOn`) is derived by the bundle. -/
def StablePrefixMap.comp {Γ : OrderedPrefixCode} (F G : StablePrefixMap Γ)
    (Rest' : List Bool → Prop) (MintAt' : List Bool → ℕ → Prop)
    (h : CompatOn F G Rest' MintAt') : StablePrefixMap Γ where
  f := G.f ∘ F.f
  Rest := Rest'
  MintAt := MintAt'
  ext := by
    intro π d hm
    show G.f (F.f (π ++ Γ.enc d)) = G.f (F.f π) ++ Γ.enc d
    rw [F.ext (h.mintF π d hm), G.ext (h.mintG π d hm)]
  ord := by
    intro c c' hc hc'
    show keyLt (key (G.f (F.f c))) (key (G.f (F.f c'))) = keyLt (key c) (key c')
    rw [G.ord' (h.domG hc) (h.domG hc'), F.ord' (h.domF hc) (h.domF hc')]

@[simp] theorem StablePrefixMap.comp_f {Γ : OrderedPrefixCode}
    (F G : StablePrefixMap Γ) (Rest' MintAt') (h : CompatOn F G Rest' MintAt') :
    (F.comp G Rest' MintAt' h).f = G.f ∘ F.f := rfl

/-- **The full-domain special case** (no reclaim): when the composite may keep
`F`'s entire domain — every `F`-at-hand coordinate is still `G`-at-hand after
remapping, and every `F`-mint is still a `G`-mint — the boundary conditions
collapse to two clauses on `F.Dom`/`F.MintAt`. Sound exactly when epoch 2
reclaims nothing that epoch 1 saw (e.g. back-to-back compactions with no
between-epoch deaths). -/
def Compat {Γ : OrderedPrefixCode} (F G : StablePrefixMap Γ) : Prop :=
  (∀ c, F.Dom c → G.Dom (F.f c)) ∧ (∀ π d, F.MintAt π d → G.MintAt (F.f π) d)

/-- The full-domain compatibility is the `CompatOn` instance at `F`'s domain. -/
theorem CompatOn.of_compat {Γ : OrderedPrefixCode} {F G : StablePrefixMap Γ}
    (h : Compat F G) : CompatOn F G F.Rest F.MintAt where
  restF := fun _ hc => Or.inl hc
  restG := fun c hc => h.1 c (Or.inl hc)
  mintF := fun _ _ hm => hm
  mintG := fun π d hm => h.2 π d hm

/-! ## §2  Remap plumbing: composition on states/ops, domain preservation -/

/-- The record re-map is functorial. -/
theorem eRemapRec_comp (g f : List Bool → List Bool) (r : ERec α) :
    eRemapRec (g ∘ f) r = eRemapRec g (eRemapRec f r) := rfl

/-- **The state re-map fuses**: two successive compactions of a state at rest
are the compaction by the composed map. This is the state-side of "n epochs =
one composite". -/
theorem eRemapSt_comp (g f : List Bool → List Bool) (s : EState α) :
    eRemapSt (g ∘ f) s = eRemapSt g (eRemapSt f s) := by
  unfold eRemapSt
  rw [List.map_map]
  apply List.map_congr_left
  intro r _
  rfl

/-- **The op re-map fuses**: translating a lagging op through both epochs'
maps is translating it through the composite. -/
theorem eRemapOp_comp (g f : List Bool → List Bool) (o : Op (EOp α)) :
    eRemapOp (g ∘ f) o = eRemapOp g (eRemapOp f o) := by
  obtain ⟨t, r, op⟩ := o
  cases op <;> rfl

/-- One update preserves "coordinates at hand": the output records are input
records (already at hand) or the op's own mint (at hand by the mint clause). -/
theorem eUpdate_dom_pres {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    (s : EState α) (o : Op (EOp α))
    (hs : ∀ x ∈ s, F.Dom x.2.2)
    (ho : ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a)) :
    ∀ x ∈ eUpdate Γ s o, F.Dom x.2.2 := by
  intro x hx
  obtain ⟨t, rr, op⟩ := o
  cases op with
  | del y => exact hs x (List.mem_of_mem_filter hx)
  | ins e π a =>
      rcases mem_eUpdate_cases hx with h | h
      · exact hs x h
      · rw [h]
        exact Or.inr ⟨π, t - a, ho e π a rfl, rfl⟩

/-- **A whole continuation preserves "coordinates at hand"**: after applying a
settling continuation whose mints land at hand, every record of the resulting
state is at hand. This is the domain-tracking that lets the *next* epoch's
compaction cover the settled state. -/
theorem applySeq_dom_pres {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ) :
    ∀ (τ : List (Op (EOp α))) (s : EState α),
    (∀ x ∈ s, F.Dom x.2.2) →
    (∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a)) →
    ∀ x ∈ (show EState α from applySeq (E Γ α).toCRDTSig s τ), F.Dom x.2.2
  | [], s, hs, _ => hs
  | o :: τ', s, hs, hτ => by
      show ∀ x ∈ (show EState α from applySeq (E Γ α).toCRDTSig (eUpdate Γ s o) τ'),
        F.Dom x.2.2
      exact applySeq_dom_pres F τ' (eUpdate Γ s o)
        (eUpdate_dom_pres F s o hs (fun e π a h => hτ o List.mem_cons_self e π a h))
        (fun o' ho' => hτ o' (List.mem_cons_of_mem _ ho'))

/-! ## §3  The two-epoch headline: compact, continue, compact, continue

This is the staged form that re-invokes T1 at *each* epoch. The between-epoch
continuation `τ₁` settles into the state (its mints land at hand); the epoch-2
compaction then covers that settled state (`hs2`, the settledness of the second
cut — representation-independent, `SettledAtOn` is stated on event sets); the
lagging continuation `τ₂` is still in epoch-0 code and is translated through
*both* maps (`eRemapOp` of the composite). Reads are pinned to the uncompacted
run at the end. -/
theorem twoEpoch_reads {Γ : OrderedPrefixCode} (F₁ F₂ : StablePrefixMap Γ)
    (Rest' : List Bool → Prop) (MintAt' : List Bool → ℕ → Prop)
    (h : CompatOn F₁ F₂ Rest' MintAt')
    (s : EState α) (τ₁ τ₂ : List (Op (EOp α)))
    (hs : ∀ x ∈ s, F₁.Dom x.2.2)
    (hτ₁ : ∀ o ∈ τ₁, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F₁.MintAt π (o.1 - a))
    (hs2 : ∀ x ∈ (show EState α from applySeq (E Γ α).toCRDTSig s τ₁),
      (F₁.comp F₂ Rest' MintAt' h).Dom x.2.2)
    (hτ₂ : ∀ o ∈ τ₂, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → (F₁.comp F₂ Rest' MintAt' h).MintAt π (o.1 - a)) :
    (E Γ α).query
        (applySeq (E Γ α).toCRDTSig
          (eRemapSt F₂.f
            (applySeq (E Γ α).toCRDTSig (eRemapSt F₁.f s)
              (τ₁.map (eRemapOp F₁.f))))
          (τ₂.map (eRemapOp (F₁.comp F₂ Rest' MintAt' h).f))) ()
      = (E Γ α).query
          (applySeq (E Γ α).toCRDTSig
            (applySeq (E Γ α).toCRDTSig s τ₁) τ₂) () := by
  set G := F₁.comp F₂ Rest' MintAt' h with hG
  rw [eRecode_applySeq F₁ τ₁ s hs hτ₁]
  rw [show eRemapSt F₂.f (eRemapSt F₁.f (applySeq (E Γ α).toCRDTSig s τ₁))
        = eRemapSt G.f (applySeq (E Γ α).toCRDTSig s τ₁) from by
      rw [hG, StablePrefixMap.comp_f, eRemapSt_comp]]
  exact eRecode_reads_identical G _ τ₂ hs2 hτ₂

/-! ## §4  The n-epoch headline: a list of maps composes to one

A `CompatChain` is the full-domain chain (no between-epoch reclaim, e.g. a tower
of back-to-back compactions at successively finer settled cuts). `compFun` is
the accumulated coordinate translation, `chainSPM` bundles it as a single
`StablePrefixMap` proved by induction over the list — *this is where the
composition re-invokes at every epoch*. The headline then folds and reads
identically for the whole tower in one shot, because the composite is a genuine
stable-prefix map and every single-epoch theorem (T1/T2) applies to it verbatim. -/

/-- Full-domain consecutive compatibility along a list of epoch maps. -/
def CompatChain {Γ : OrderedPrefixCode} : List (StablePrefixMap Γ) → Prop
  | [] => True
  | [_] => True
  | F :: G :: rest => Compat F G ∧ CompatChain (G :: rest)

/-- The accumulated coordinate translation: apply the earliest map first. -/
def compFun {Γ : OrderedPrefixCode} :
    List (StablePrefixMap Γ) → (List Bool → List Bool)
  | [] => id
  | F :: Fs => compFun Fs ∘ F.f

/-- The mint domain to relativize to: the first (earliest) map's. -/
def headMintAt {Γ : OrderedPrefixCode} :
    List (StablePrefixMap Γ) → List Bool → ℕ → Prop
  | [] => fun _ _ => True
  | F :: _ => fun π d => F.MintAt π d

/-- The at-rest domain to relativize to: the first (earliest) map's. -/
def headDom {Γ : OrderedPrefixCode} : List (StablePrefixMap Γ) → List Bool → Prop
  | [] => fun _ => True
  | F :: _ => fun c => F.Dom c

/-- H3 composes along the whole chain: the accumulated translation commutes
with a beyond-cut extension whose mint is at hand for the earliest map. -/
theorem compFun_ext {Γ : OrderedPrefixCode} :
    ∀ (Fs : List (StablePrefixMap Γ)), CompatChain Fs →
    ∀ (π : List Bool) (d : ℕ), headMintAt Fs π d →
      compFun Fs (π ++ Γ.enc d) = compFun Fs π ++ Γ.enc d
  | [], _, _, _, _ => rfl
  | [F], _, _, _, hm => F.ext hm
  | F :: G :: rest, h, π, d, hm => by
      show compFun (G :: rest) (F.f (π ++ Γ.enc d))
        = compFun (G :: rest) (F.f π) ++ Γ.enc d
      rw [F.ext hm]
      exact compFun_ext (G :: rest) h.2 (F.f π) d (h.1.2 π d hm)

/-- H2 composes along the whole chain: the accumulated translation preserves
the display comparator on at-hand coordinates (order-isos compose). -/
theorem compFun_ord {Γ : OrderedPrefixCode} :
    ∀ (Fs : List (StablePrefixMap Γ)), CompatChain Fs →
    ∀ (c c' : List Bool), headDom Fs c → headDom Fs c' →
      keyLt (key (compFun Fs c)) (key (compFun Fs c')) = keyLt (key c) (key c')
  | [], _, _, _, _, _ => rfl
  | [F], _, _, _, hc, hc' => F.ord' hc hc'
  | F :: G :: rest, h, c, c', hc, hc' => by
      show keyLt (key (compFun (G :: rest) (F.f c)))
          (key (compFun (G :: rest) (F.f c'))) = keyLt (key c) (key c')
      rw [compFun_ord (G :: rest) h.2 (F.f c) (F.f c')
            (h.1.1 c hc) (h.1.1 c' hc'), F.ord' hc hc']

/-- **The n-fold composition closure**: a `CompatChain` of stable-prefix maps
composes to a single stable-prefix map, the accumulated translation carrying the
earliest map's domain. -/
def chainSPM {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    (Fs : List (StablePrefixMap Γ)) (h : CompatChain (F :: Fs)) :
    StablePrefixMap Γ where
  f := compFun (F :: Fs)
  Rest := F.Rest
  MintAt := F.MintAt
  ext := fun {π d} hm => compFun_ext (F :: Fs) h π d hm
  ord := fun {c c'} hc hc' => compFun_ord (F :: Fs) h c c' hc hc'

@[simp] theorem chainSPM_f {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    (Fs : List (StablePrefixMap Γ)) (h : CompatChain (F :: Fs)) :
    (chainSPM F Fs h).f = compFun (F :: Fs) := rfl

/-- **The n-epoch fold congruence.** Folding the (composite-)translated
continuation over the (composite-)re-mapped cut state is the composite re-map
of the untranslated fold — for a tower of arbitrarily many compactions. -/
theorem multiEpoch_applySeq {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    (Fs : List (StablePrefixMap Γ)) (h : CompatChain (F :: Fs))
    (s : EState α) (τ : List (Op (EOp α)))
    (hrest : ∀ x ∈ s, F.Dom x.2.2)
    (hτ : ∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a)) :
    applySeq (E Γ α).toCRDTSig (eRemapSt (chainSPM F Fs h).f s)
        (τ.map (eRemapOp (chainSPM F Fs h).f))
      = eRemapSt (chainSPM F Fs h).f (applySeq (E Γ α).toCRDTSig s τ) :=
  eRecode_applySeq (chainSPM F Fs h) τ s hrest hτ

/-- **THE n-EPOCH HEADLINE.** After arbitrarily many settled-cut compactions
(composed into the single `chainSPM`), any beyond-all-cuts continuation — its
lagging ops translated through every epoch's map — reads exactly as the
uncompacted run. Compression stays invisible across the whole tower of epochs.
Kernel-clean; a direct re-invocation of T2 on the composite (which the n-fold
closure proves is a genuine stable-prefix map). -/
theorem multiEpoch_settled_reads {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    (Fs : List (StablePrefixMap Γ)) (h : CompatChain (F :: Fs))
    (s : EState α) (τ : List (Op (EOp α)))
    (hrest : ∀ x ∈ s, F.Dom x.2.2)
    (hτ : ∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a)) :
    (E Γ α).query (applySeq (E Γ α).toCRDTSig (eRemapSt (chainSPM F Fs h).f s)
        (τ.map (eRemapOp (chainSPM F Fs h).f))) ()
      = (E Γ α).query (applySeq (E Γ α).toCRDTSig s τ) () :=
  eRecode_reads_identical (chainSPM F Fs h) s τ hrest hτ

/-! ## §5  Future-mint freshness survives every epoch

The order-iso side of the composition closure: `compactRanked`'s `rED_iso` needs, at each
unskipped group, that every occurring delta is a surviving kid or *fresh*
(dominates every kid). The renumbering `rED` never grows a delta, so this
domination is invariant under composition: a delta fresh against epoch-`k`'s
ordinals was fresh against epoch-`(k-1)`'s, all the way down to the original
timestamp differences. Ordinals are bounded by their delta (a rank counts at
most `d` distinct positives `≤ d`), hence by the record count, hence by the
maximum stamp — so a Lamport-fresh future mint dominates every stored ordinal
regardless of the epoch's coordinate meaning. -/

/-- **Renumbering never grows a delta.** `rED` maps a kept sibling delta to its
rank (`≤` itself, `rankIn_le_self`) and leaves everything else fixed. -/
theorem rED_le_self {keep inflight : List (List ℕ)}
    (hKpos : ∀ k ∈ keep, PosChain k) (p : List ℕ) (d : ℕ) :
    rED keep inflight p d ≤ d := by
  rw [rED]
  split
  · exact rankIn_le_self (fun x hx =>
      hKpos _ (mem_kidsOf.mp hx) x (List.mem_append_right _ List.mem_cons_self)) d
  · exact Nat.le_refl d

/-- **The future-mint-freshness-post-epoch lemma.** A delta `d` that dominates
every kept sibling's *original* delta still dominates every kept sibling's
*renumbered ordinal* — so the kids-or-fresh domination that the next epoch's
`rED_iso` consumes is preserved, on epoch-`k` coordinates, without inspecting
whether the stored deltas mean timestamp differences or ranks. -/
theorem rED_fresh_dominates {keep inflight : List (List ℕ)}
    (hKpos : ∀ k ∈ keep, PosChain k) {p : List ℕ} {d e : ℕ}
    (hfresh : ∀ k, (p ++ [k]) ∈ keep → k < d) (he : (p ++ [e]) ∈ keep) :
    rED keep inflight p e < d :=
  Nat.lt_of_le_of_lt (rED_le_self hKpos p e) (hfresh e he)

/-! ## §6  Axiom audit -/

#print axioms StablePrefixMap.comp
#print axioms twoEpoch_reads
#print axioms chainSPM
#print axioms multiEpoch_applySeq
#print axioms multiEpoch_settled_reads
#print axioms rED_le_self
#print axioms rED_fresh_dominates

/-! ## §7  SPOT — a directed two-epoch scenario (PASS + FAIL shaped)

Unary code, hand-computed. **Epoch 0**: one live record, id 2 delta 2, payload
20, coordinate `enc 2`. **Epoch 1** (`gc1`): renumber the root group `{2} ↦ {1}`
(`enc 2 ↦ enc 1`). **Between epochs** (`tau1`, settling): a lagging root insert
`z` (id 5 delta 5, payload 50) arrives in epoch-0 code; it settles as a record.
**Epoch 2** (`gc2`): renumber the epoch-1 root group `{1, 5} ↦ {1, 2}`
(`enc 5 ↦ enc 2`, `enc 1` kept). **After** (`tau2`, lagging): a root insert `w`
(id 8 delta 8, payload 80) still in epoch-0 code, translated through *both* maps.
Hand-derived display order both sides: `w, z, (orig)` = `[80, 50, 20]` (root
deltas 8 > 5 > 2/1, newest first). Reads pinned identical throughout the tower.

FAIL companions: (a) `naive_composition_collides` — a *reclaiming* second map
makes `gc2 ∘ gc1` non-injective on the full first-epoch domain (a dead
coordinate and a live one collide on the reclaimed rank), so the composite is
NOT a stable-prefix map on the full domain — this is why `comp` carries the
surviving domain `(Rest', MintAt')`; (b) `id_addressing_breaks` — pinning the
runtime twin's erratum: after epoch one a renumbered coordinate no longer
telescopes to its event id, so an id-addressed second cut resolves to nothing
while a coordinate-addressed one resolves correctly. -/

namespace MultiEpochSPOT

open Sal.EmbedRGA (unaryCode)

/-- Epoch-0 cut state: one root record, id 2 delta 2, payload 20. -/
def s0 : EState ℕ := [(2, 20, unaryCode.enc 2)]

/-- Epoch-1 renumbering: root group `{2} ↦ {1}`. -/
def gc1 (c : List Bool) : List Bool :=
  if c = unaryCode.enc 2 then unaryCode.enc 1 else c

/-- Epoch-2 renumbering (on epoch-1 coordinates): root group `{1, 5} ↦ {1, 2}`. -/
def gc2 (c : List Bool) : List Bool :=
  if c = unaryCode.enc 5 then unaryCode.enc 2 else c

/-- Between-epoch settling continuation: a lagging root insert `z`. -/
def tau1 : List (Op (EOp ℕ)) := [(5, 0, .ins 50 [] 0)]

/-- Post-epoch-2 lagging continuation: a root insert `w`, still epoch-0 code. -/
def tau2 : List (Op (EOp ℕ)) := [(8, 0, .ins 80 [] 0)]

/-- The two-epoch run: compact `gc1`, continue `tau1`, compact `gc2`, continue
`tau2` (translated through the composite `gc2 ∘ gc1`). -/
def twoRun : EState ℕ :=
  applySeq (E unaryCode).toCRDTSig
    (eRemapSt gc2
      (applySeq (E unaryCode).toCRDTSig (eRemapSt gc1 s0) (tau1.map (eRemapOp gc1))))
    (tau2.map (eRemapOp (gc2 ∘ gc1)))

/-- The uncompacted control run: same ops, no compaction. -/
def ctrl : EState ℕ :=
  applySeq (E unaryCode).toCRDTSig (applySeq (E unaryCode).toCRDTSig s0 tau1) tau2

/-- **PASS**: reads pinned identical across BOTH epochs to the hand-derived
`[80, 50, 20]` (newest root delta first). Not empty, not the id list. -/
theorem two_epoch_reads_identical :
    SPOT.readE twoRun = [80, 50, 20] ∧ SPOT.readE ctrl = [80, 50, 20] := by
  native_decide

/-- **PASS**: the two-epoch run genuinely compacts (coordinate weight strictly
below the control) and is not the identity (records differ). -/
theorem two_epoch_compresses :
    SPOT.coordWeight twoRun < SPOT.coordWeight ctrl ∧ twoRun ≠ ctrl := by
  native_decide

/-- A reclaiming epoch-1 map (drops nothing yet) and epoch-2 map (reclaims a
dead sibling's rank): `enc 3 ↦ enc 1`, `enc 7 ↦ enc 2`, then `enc 2 ↦ enc 1`. -/
def gc1c (c : List Bool) : List Bool :=
  if c = unaryCode.enc 3 then unaryCode.enc 1
  else if c = unaryCode.enc 7 then unaryCode.enc 2 else c

def gc2c (c : List Bool) : List Bool :=
  if c = unaryCode.enc 2 then unaryCode.enc 1 else c

/-- **FAIL**: naive composition on the FULL first-epoch domain is
unsound under reclaim — the dead coordinate `enc 3` and the live `enc 7` collide
on the reclaimed rank `enc 1` under `gc2 ∘ gc1`, so the composite is not
injective (H1 fails) and cannot be a stable-prefix map on the full domain. This
is exactly why `comp` carries the surviving domain. -/
theorem naive_composition_collides :
    (gc2c ∘ gc1c) (unaryCode.enc 3) = (gc2c ∘ gc1c) (unaryCode.enc 7)
      ∧ unaryCode.enc 3 ≠ unaryCode.enc 7 := by
  native_decide

/-- The unary telescope decode: a root-or-chain coordinate's event id is its
count of `1`-bits (sum of deltas). -/
def unaryId (c : List Bool) : ℕ := (c.filter id).length

/-- **FAIL (erratum)**: after epoch one, a renumbered coordinate no longer
telescopes to its event id. An id-addressed second cut `{7}` (resolve by
prefix-sum) finds NO record in the renumbered state; the coordinate-addressed
cut finds the record. The second cut must be coordinate/record-addressed. -/
theorem id_addressing_breaks :
    unaryId (unaryCode.enc 7) = 7 ∧
    unaryId (gc1c (unaryCode.enc 7)) ≠ 7 ∧
    ([unaryCode.enc 2, unaryCode.enc 1].filter
      (fun c => decide (unaryId c = 7))) = [] ∧
    ([unaryCode.enc 2, unaryCode.enc 1].filter
      (fun c => decide (c = gc1c (unaryCode.enc 7)))) = [unaryCode.enc 2] := by
  native_decide

/-! ### The pin fired through `twoEpoch_reads`, not recomputed -/

/-- Epoch-1 map as a stable-prefix bundle (H2/H3 discharge by computation on
the at-hand pairs). `MintAt` carries both lagging deltas `5` (settling) and `8`
(post-epoch), the two ops the run replays through it. -/
def gcF1 : StablePrefixMap unaryCode where
  f := gc1
  Rest := fun c => c = unaryCode.enc 2
  MintAt := fun π d => π = [] ∧ (d = 5 ∨ d = 8)
  ext := by rintro π d ⟨rfl, (rfl | rfl)⟩ <;> decide
  ord := by
    rintro c c' (rfl | ⟨_, _, ⟨rfl, (rfl | rfl)⟩, rfl⟩)
                (rfl | ⟨_, _, ⟨rfl, (rfl | rfl)⟩, rfl⟩) <;> decide

/-- Epoch-2 map as a stable-prefix bundle (on epoch-1 coordinates). -/
def gcF2 : StablePrefixMap unaryCode where
  f := gc2
  Rest := fun c => c = unaryCode.enc 1 ∨ c = unaryCode.enc 5
  MintAt := fun π d => π = [] ∧ d = 8
  ext := by rintro π d ⟨rfl, rfl⟩; decide
  ord := by
    rintro c c' ((rfl | rfl) | ⟨_, _, ⟨rfl, rfl⟩, rfl⟩)
                ((rfl | rfl) | ⟨_, _, ⟨rfl, rfl⟩, rfl⟩) <;> decide

/-- The composite's surviving domain: the original coordinates present in the
epoch-1 (control) state, and the still-lagging mint `8`. -/
def Rest' : List Bool → Prop := fun c => c = unaryCode.enc 2 ∨ c = unaryCode.enc 5
def MintAt' : List Bool → ℕ → Prop := fun π d => π = [] ∧ d = 8

/-- The boundary conditions hold: `gc1`-images of survivors are epoch-2-at-hand,
the lagging mint stays a mint at both epochs. -/
def hCompat : CompatOn gcF1 gcF2 Rest' MintAt' where
  restF := by
    rintro c (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨[], 5, ⟨rfl, Or.inl rfl⟩, rfl⟩
  restG := by
    rintro c (rfl | rfl)
    · exact Or.inl (Or.inl (by decide))
    · exact Or.inl (Or.inr (by decide))
  mintF := by rintro π d ⟨rfl, rfl⟩; exact ⟨rfl, Or.inr rfl⟩
  mintG := by rintro π d ⟨rfl, rfl⟩; exact ⟨by decide, rfl⟩

/-- The epoch-1 (control) state, hand-derived: `z` above the original record. -/
theorem s1ctrl_eq :
    applySeq (E unaryCode).toCRDTSig s0 tau1
      = [(5, 50, unaryCode.enc 5), (2, 20, unaryCode.enc 2)] := by native_decide

/-- **PASS (via the theorem)**: `twoEpoch_reads` fired on the concrete instance
reproduces the two-epoch reads-identical pin — not recomputed, discharged
through the theorem's four hypotheses. -/
theorem two_epoch_via_theorem :
    (E unaryCode).query twoRun () = (E unaryCode).query ctrl () := by
  refine twoEpoch_reads gcF1 gcF2 Rest' MintAt' hCompat s0 tau1 tau2 ?_ ?_ ?_ ?_
  · rintro x hx
    simp only [s0, List.mem_singleton] at hx
    subst hx
    exact Or.inl rfl
  · rintro o ho e π a heq
    simp only [tau1, List.mem_singleton] at ho
    subst ho
    injection heq with h1 h2 h3
    subst h1; subst h2; subst h3
    exact ⟨rfl, Or.inl rfl⟩
  · intro x hx
    rw [s1ctrl_eq] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inl (Or.inr rfl)
    · exact Or.inl (Or.inl rfl)
  · rintro o ho e π a heq
    simp only [tau2, List.mem_singleton] at ho
    subst ho
    injection heq with h1 h2 h3
    subst h1; subst h2; subst h3
    exact ⟨rfl, rfl⟩

#print axioms two_epoch_reads_identical
#print axioms two_epoch_compresses
#print axioms naive_composition_collides
#print axioms id_addressing_breaks
#print axioms two_epoch_via_theorem

end MultiEpochSPOT

end Sal.ConditionedMRDTs
