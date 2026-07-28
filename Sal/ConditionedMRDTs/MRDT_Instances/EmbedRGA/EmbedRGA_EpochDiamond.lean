import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_HonestyRebase

/-!
# The epoch diamond: confluence of incomparable compactions

Design + Python validation: `whiteboard/epoch-protocol-note.md` (§8 states the
four obligations this file discharges), `whiteboard/litmus/epoch_diamond_check.py`
(the authoritative harness, 2400/2400 at strength s1). The single-replica (star)
theory is `EmbedRGA_Recoding.lean` (T1/T2, the `StablePrefixMap` bundle),
`EmbedRGA_MultiEpoch.lean` (`StablePrefixMap.comp` / `CompatOn`, the SEQUENTIAL
nested-cut composition), `EmbedRGA_CompatChain.lean` and
`EmbedRGA_HonestyRebase.lean` (the honesty rebasing `I = CodedAnchoredForest`).
This file is the MULTI-REPLICA protocol layer: two replicas that compacted at
*incomparable* settled cuts merge with no coordination.

## The reduction that makes it tractable

The join `W = S1 ∪ S2` is the common refinement, and `S1 ⊆ W`, `S2 ⊆ W`. So each
individual LEG is a NESTED (comparable) chain — exactly the case the sequential
machinery already closes: leg A (`S1` then `W`) and leg B (`S2` then `W`) each
compose to a valid `StablePrefixMap` via `StablePrefixMap.comp`. The genuinely
NEW content of the *incomparable* diamond is not a new algebraic obstruction; it
is exactly two facts:

* **O1 confluence = certificate-determinism.** All three maps (leg A, leg B, the
  one-shot at `W`) must AGREE. They do because the join map is a function of
  `W`'s certificate data ALONE (`OB-map-from-certificate`,
  `whiteboard/epoch-protocol-note.md` §2/§5.2): both
  replicas feed the same certificate to the same builder, so `spm W` is the same
  term on both sides — the "without coordination" content, captured here as
  definitional determinism (`certMap_deterministic`). Given agreement on the
  carried domain, `diamond_confluence` derives BIT-IDENTICAL states (s1), not
  merely equal reads.
* **O2 domain transport.** The composite's surviving domain must be the join
  cut's kept id-set transported by RECORD IDENTITY to epoch-0 coordinates
  (`transportedDom`), NOT computed by membership pullback: a coordinate DROPPED
  by the first map falls through verbatim and can ALIAS a kept later-epoch
  coordinate (`naive_pullback_aliases`, the incomparable analogue of
  `naive_composition_collides`). The transport reads epoch-0 coordinates from the
  (sorted, hence coordinate-nodup) original state, never by decoding a renumbered
  coordinate, so `id_addressing_breaks` does not apply.

O3 (`mapDrop_sound`) and O4 (`rED_*_join`, `ContOK`) are the GC and freshness
residues. The SPOTs replay directed cases c1–c4 and A3 from
`whiteboard/epoch-protocol-note.md`.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode keyLt keyLe key key_inj keyLt_irrefl
  coordOf coordOf_inj coordOf_append PosChain unaryCode enc_ne_nil)

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §0  Congruence plumbing: states/ops under agreeing / fixing maps -/

/-- Two re-maps that agree on every coordinate present in a state produce the
SAME state, bit for bit (list order, ids, elements untouched). This is the
state-level engine behind s1: bit-identity, not merely reads. -/
theorem eRemapSt_congr {f g : List Bool → List Bool} {s : EState α}
    (h : ∀ x ∈ s, f x.2.2 = g x.2.2) : eRemapSt f s = eRemapSt g s := by
  unfold eRemapSt
  apply List.map_congr_left
  intro r hr
  show eRemapRec f r = eRemapRec g r
  unfold eRemapRec
  rw [h r hr]

/-- A re-map fixing every coordinate present in a state is the identity on it. -/
theorem eRemapSt_id_of_fixes {f : List Bool → List Bool} {s : EState α}
    (h : ∀ x ∈ s, f x.2.2 = x.2.2) : eRemapSt f s = s := by
  unfold eRemapSt
  conv_rhs => rw [← List.map_id s]
  apply List.map_congr_left
  intro r hr
  show eRemapRec f r = id r
  simp only [eRemapRec, id_eq, h r hr, Prod.mk.eta]

/-- A re-map fixing an op's carried anchor prefix leaves the op untouched
(deletes are id-based, always untouched). -/
theorem eRemapOp_id_of_fixes {f : List Bool → List Bool} {o : Op (EOp α)}
    (h : ∀ (e : α) (π : List Bool) (a : ℕ), o.2.2 = EOp.ins e π a → f π = π) :
    eRemapOp f o = o := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | del x => rfl
  | ins e π a =>
      show (t, r, EOp.ins e (f π) a) = (t, r, EOp.ins e π a)
      rw [h e π a rfl]

/-! ## §1  O1 — the diamond lemma at s1

The join map is CERTIFICATE-DETERMINED: introduce it as a function of the
certificate data, so both replicas compute the identical map. Then the diamond
reduces to pointwise agreement of the two relative composites with the one-shot
on the carried surviving domain; from agreement we get bit-identical states. -/

/-- **The certificate data of a cut** (`whiteboard/epoch-protocol-note.md` §2): the settled surviving
coordinates, the settled-dead subset, and the declared in-flight set — and
NOTHING of a replica's private unsettled records. Two replicas holding the same
certificates hold the same `JoinCert`. -/
structure JoinCert (Γ : OrderedPrefixCode) where
  survivingCoords : List (List Bool)
  settledDead : List (List Bool)
  declared : List (List Bool × ℕ)

/-- **`OB-map-from-certificate` (`whiteboard/epoch-protocol-note.md` §5.2), as determinism.** The join map is
produced by a builder `𝒞` that is a function of the `JoinCert` ONLY. Hence two
replicas that computed the same join certificate install the *same* map with no
round trips — this `congrArg` IS the "without coordination" content: given equal
certificates, the maps are equal by definition, not by reconciliation. -/
theorem certMap_deterministic {Γ : OrderedPrefixCode}
    (𝒞 : JoinCert Γ → StablePrefixMap Γ) {c₁ c₂ : JoinCert Γ} (h : c₁ = c₂) :
    𝒞 c₁ = 𝒞 c₂ := congrArg 𝒞 h

/-- **O1 map-level path-equality on the carried domain.** Given that leg A's
composite `relA ∘ spmS1` and leg B's composite `relB ∘ spmS2` each agree with the
one-shot join map `spmW` on the carried domain `D`, all three coincide there. The
`comp`-closure (`EmbedRGA_MultiEpoch`) already makes each composite a genuine
`StablePrefixMap`; this adds that the two legs land on the same map. -/
theorem diamond_maps_agree {Γ : OrderedPrefixCode}
    {spmS1 spmS2 relA relB spmW : StablePrefixMap Γ} {D : List Bool → Prop}
    (hA : ∀ c, D c → relA.f (spmS1.f c) = spmW.f c)
    (hB : ∀ c, D c → relB.f (spmS2.f c) = spmW.f c) :
    ∀ c, D c → relA.f (spmS1.f c) = spmW.f c ∧ relB.f (spmS2.f c) = spmW.f c
      ∧ relA.f (spmS1.f c) = relB.f (spmS2.f c) :=
  fun c hc => ⟨hA c hc, hB c hc, (hA c hc).trans (hB c hc).symm⟩

/-- **O1, the diamond at s1 (state level).** For a cut state `s` whose records
lie in the carried surviving domain `D`, if both relative composites agree with
the one-shot on `D`, then the two-leg compactions and the one-shot compaction
produce BIT-IDENTICAL states (not merely equal reads), and their reads coincide.
This is the confluence the barrier-free merge asserts in vivo at every join. -/
theorem diamond_confluence {Γ : OrderedPrefixCode}
    (spmS1 spmS2 relA relB spmW : StablePrefixMap Γ)
    (D : List Bool → Prop) (s : EState α)
    (hsD : ∀ x ∈ s, D x.2.2)
    (hA : ∀ c, D c → relA.f (spmS1.f c) = spmW.f c)
    (hB : ∀ c, D c → relB.f (spmS2.f c) = spmW.f c) :
    eRemapSt (relA.f ∘ spmS1.f) s = eRemapSt spmW.f s
      ∧ eRemapSt (relB.f ∘ spmS2.f) s = eRemapSt spmW.f s
      ∧ (E Γ α).query (eRemapSt (relA.f ∘ spmS1.f) s) ()
          = (E Γ α).query (eRemapSt (relB.f ∘ spmS2.f) s) () := by
  have eA : eRemapSt (relA.f ∘ spmS1.f) s = eRemapSt spmW.f s :=
    eRemapSt_congr (fun x hx => hA x.2.2 (hsD x hx))
  have eB : eRemapSt (relB.f ∘ spmS2.f) s = eRemapSt spmW.f s :=
    eRemapSt_congr (fun x hx => hB x.2.2 (hsD x hx))
  exact ⟨eA, eB, by rw [eA, eB]⟩

/-- **O1 at s1, raw-function form** (no bundle needed): the confluence engine used
by the directed SPOTs. Same content as `diamond_confluence`, phrased over plain
coordinate maps so concrete `if`-table compactions instantiate it directly. -/
theorem diamond_confluence_fn {f1 f2 fa fb fw : List Bool → List Bool}
    (D : List Bool → Prop) (s : EState α)
    (hsD : ∀ x ∈ s, D x.2.2)
    (hA : ∀ c, D c → fa (f1 c) = fw c)
    (hB : ∀ c, D c → fb (f2 c) = fw c) :
    eRemapSt (fa ∘ f1) s = eRemapSt fw s
      ∧ eRemapSt (fb ∘ f2) s = eRemapSt fw s :=
  ⟨eRemapSt_congr (fun x hx => hA x.2.2 (hsD x hx)),
   eRemapSt_congr (fun x hx => hB x.2.2 (hsD x hx))⟩

/-- **O1 stated with the composition closure.** Leg A's composite as an actual
`StablePrefixMap.comp` (carrying the surviving domain `RA`/`MA`) equals the
one-shot `spmW` at rest, and symmetrically for leg B:
`relSPM(S1→W).comp(spm S1) = spm W = relSPM(S2→W).comp(spm S2)` at the state
level. -/
theorem diamond_confluence_comp {Γ : OrderedPrefixCode}
    (spmS1 spmS2 relA relB spmW : StablePrefixMap Γ)
    (RA : List Bool → Prop) (MA : List Bool → ℕ → Prop)
    (RB : List Bool → Prop) (MB : List Bool → ℕ → Prop)
    (hcA : CompatOn spmS1 relA RA MA) (hcB : CompatOn spmS2 relB RB MB)
    (D : List Bool → Prop) (s : EState α)
    (hsD : ∀ x ∈ s, D x.2.2)
    (hA : ∀ c, D c → relA.f (spmS1.f c) = spmW.f c)
    (hB : ∀ c, D c → relB.f (spmS2.f c) = spmW.f c) :
    eRemapSt (spmS1.comp relA RA MA hcA).f s = eRemapSt spmW.f s
      ∧ eRemapSt (spmS2.comp relB RB MB hcB).f s = eRemapSt spmW.f s := by
  obtain ⟨eA, eB, _⟩ := diamond_confluence spmS1 spmS2 relA relB spmW D s hsD hA hB
  refine ⟨?_, ?_⟩
  · rw [StablePrefixMap.comp_f]; exact eA
  · rw [StablePrefixMap.comp_f]; exact eB

/-! ## §2  O2 — the join-epoch CompatOn and the aliasing negative

The carried surviving domain is the join cut's kept id-set transported BY RECORD
IDENTITY to epoch-0 coordinates: read each kept record's epoch-0 coordinate off
the original state. It is NOT computed by membership pullback (aliasing) nor by
intersecting the two maps' kept sets (evicts later-settled records). -/

/-- **The transported domain** (`whiteboard/epoch-protocol-note.md` §5.1): the epoch-0 coordinates of the records
the join cut keeps, addressed by record identity `keptW : id → Prop` against the
original (never-compacted) state `s`. -/
def transportedDom (s : EState α) (keptW : ℕ → Prop) : List Bool → Prop :=
  fun c => ∃ x ∈ s, keptW x.1 ∧ x.2.2 = c

/-- **The transport is well-defined and alias-free** — the id-vs-coordinate point.
On a sorted (canonical) epoch-0 state the coordinates carry NO duplicates
(`coords_nodup_of_esorted`), so reading a coordinate off a kept record is a
genuine (duplicate-free) domain. Crucially the transport reads epoch-0
coordinates from the stored state; it never DECODES a renumbered coordinate back
to an id, so the `id_addressing_breaks` erratum (MultiEpoch §7) does not apply. -/
theorem transportedDom_coords_nodup {s : EState α} (hs : ESorted s) :
    (s.map (fun r => r.2.2)).Nodup :=
  coords_nodup_of_esorted hs

/-- **The join-epoch `CompatOn` at the transported domain.** A thin instantiation
of `compatOn_two_epoch` (`EmbedRGA_CompatChain`) fixing the carried domain to
`transportedDom s keptW`: every transported coordinate is at hand for `spmS1`
(`hRF`), its `spmS1`-image is at hand for `relA` (`hRG`), and the mints carry
over (`hMF`/`hMG`). This is the domain choice the diamond needs; the SPOT builds
it concretely for c1. -/
theorem diamond_CompatOn {Γ : OrderedPrefixCode} (spmS1 relA : StablePrefixMap Γ)
    (s : EState α) (keptW : ℕ → Prop) (MintAt' : List Bool → ℕ → Prop)
    (hRF : ∀ c, transportedDom s keptW c → spmS1.Dom c)
    (hRG : ∀ c, transportedDom s keptW c → relA.Dom (spmS1.f c))
    (hMF : ∀ π d, MintAt' π d → spmS1.MintAt π d)
    (hMG : ∀ π d, MintAt' π d → relA.MintAt (spmS1.f π) d) :
    CompatOn spmS1 relA (transportedDom s keptW) MintAt' :=
  compatOn_two_epoch spmS1 relA (transportedDom s keptW) MintAt' hRF hRG hMF hMG

/-! ## §3  O3 — map-drop under the ack + AllHeardSince certificate

Once every replica has advanced past epoch `e` AND every op minted before its
minter's advance is heard everywhere, every later-delivered op is minted at a
cutset containing the superseded cut, so its coordinate already lives in
epoch-`≥e` space — the earlier map `F` fixes it. Dropping `F` then changes no
fold. The ack-ONLY discipline is UNSOUND (the A3 SPOT). -/

/-- `F` acts as the identity on the coordinates satisfying `P` (the epoch-`≥e`
coordinates: coordinates already in `F`'s codomain). -/
def FixesOn {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    (P : List Bool → Prop) : Prop :=
  ∀ c, P c → F.f c = c

/-- **O3, the map-drop soundness lemma.** If the earlier map `F` fixes every
coordinate of the state `s` and every anchor prefix minted by the later
continuation `τ` (both epoch-`≥e`, by the ack + AllHeardSince certificate), then
translating through `F` is a no-op: dropping `F` from the composite chain
preserves the fold verbatim (hence every read). The certificate discipline is
what supplies `hs`/`hτ`; the ack-only shortcut does not (A3). -/
theorem mapDrop_sound {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    (s : EState α) (τ : List (Op (EOp α)))
    (hs : ∀ x ∈ s, F.f x.2.2 = x.2.2)
    (hτ : ∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.f π = π) :
    applySeq (E Γ α).toCRDTSig (eRemapSt F.f s) (τ.map (eRemapOp F.f))
      = applySeq (E Γ α).toCRDTSig s τ := by
  have hst : eRemapSt F.f s = s := eRemapSt_id_of_fixes hs
  have hop : τ.map (eRemapOp F.f) = τ := by
    conv_rhs => rw [← List.map_id τ]
    exact List.map_congr_left (fun o ho =>
      (eRemapOp_id_of_fixes (fun e π a h => hτ o ho e π a h)).trans (id_eq o).symm)
  rw [hst, hop]

/-! ## §4  O4 — ContOK at join epochs (freshness survives composition)

`rED` (dense renumbering) never grows a delta, so freshness against the original
sibling deltas survives ANY number of renumberings — the join-epoch generalization
of `rED_fresh_dominates` (MultiEpoch §5). The four ContOK clauses then hold for
every Lamport-fresh post-cut mint. -/

/-- **Renumbering composes to `≤ self`.** Two consecutive dense renumberings still
never grow a delta: `rED (renumber) (rED d) ≤ d`. -/
theorem rED_le_self_comp {k1 i1 k2 i2 : List (List ℕ)}
    (h1 : ∀ k ∈ k1, PosChain k) (h2 : ∀ k ∈ k2, PosChain k)
    (p : List ℕ) (e : ℕ) :
    rED k2 i2 p (rED k1 i1 p e) ≤ e :=
  le_trans (rED_le_self h2 p (rED k1 i1 p e)) (rED_le_self h1 p e)

/-- **Freshness survives the join epoch.** A delta `d` dominating every epoch-1
ORIGINAL kept sibling delta dominates the epoch-1-then-epoch-2 twice-renumbered
ordinal too. This is the `rED_fresh_dominates` argument lifted to a join epoch:
the fresh mint's rank cannot be perturbed by two rounds of renumbering. -/
theorem rED_fresh_dominates_join {k1 i1 k2 i2 : List (List ℕ)}
    (h1 : ∀ k ∈ k1, PosChain k) (h2 : ∀ k ∈ k2, PosChain k)
    {p : List ℕ} {d e : ℕ}
    (hfresh : ∀ k, (p ++ [k]) ∈ k1 → k < d) (he : (p ++ [e]) ∈ k1) :
    rED k2 i2 p (rED k1 i1 p e) < d :=
  lt_of_le_of_lt (rED_le_self_comp h1 h2 p e) (hfresh e he)

/-- **The four ContOK clauses** for a candidate mint (id `i`, minted coordinate
`c`) against a compacted state `s` and the keys already emitted by earlier mints
of the same continuation (`seen`). Clause (2), nodup insert ids, is the
list-level `Nodup` on the continuation and is checked separately in the SPOT. -/
structure ContOK (s : EState α) (seen : List (List Bool)) (i : ℕ)
    (c : List Bool) : Prop where
  freshId : ∀ x ∈ s, x.1 < i                     -- (1) fresh id exceeds state ids
  keyState : ∀ x ∈ s, key c ≠ key x.2.2          -- (3) mint key fresh vs state
  keySeen : ∀ k ∈ seen, key c ≠ key k            -- (4) mint keys pairwise distinct

/-- **O4, ContOK clause (3) at a join epoch, generically (root anchor).** A
Lamport-fresh root mint with delta `d` that DOMINATES every stored root sibling's
delta (each stored coordinate is `enc e` for some `1 ≤ e < d`, the domination
`rED_fresh_dominates_join` supplies) has a key distinct from every stored key —
so it never collides at any compacted state, join epochs included. The
codeword-injectivity does the work: distinct positive deltas mint distinct
codewords, hence distinct keys. -/
theorem contOK_root_key_fresh {Γ : OrderedPrefixCode} {s : EState α} {d : ℕ}
    (hd : 1 ≤ d)
    (hdom : ∀ x ∈ s, ∃ e, 1 ≤ e ∧ e < d ∧ x.2.2 = Γ.enc e) :
    ∀ x ∈ s, key (Γ.enc d) ≠ key x.2.2 := by
  intro x hx heq
  obtain ⟨e, he1, hed, hxe⟩ := hdom x hx
  rw [hxe] at heq
  have hcoord : Γ.enc d = Γ.enc e := key_inj heq
  exact Γ.enc_injOn hd he1 (fun h => absurd (h ▸ hed) (Nat.lt_irrefl d)) hcoord

/-! ## §5  Axiom audit — the abstract capstones -/

#print axioms eRemapSt_congr
#print axioms eRemapSt_id_of_fixes
#print axioms eRemapOp_id_of_fixes
#print axioms certMap_deterministic
#print axioms diamond_maps_agree
#print axioms diamond_confluence_fn
#print axioms diamond_confluence
#print axioms diamond_confluence_comp
#print axioms transportedDom_coords_nodup
#print axioms diamond_CompatOn
#print axioms mapDrop_sound
#print axioms rED_le_self_comp
#print axioms rED_fresh_dominates_join
#print axioms contOK_root_key_fresh

/-! ## §6  SPOTs — directed cases c1–c4, A3 (PASS + FAIL shaped)

Unary code (`enc d = 1^d 0`). Every expected value is hand-derived from the
`whiteboard/epoch-protocol-note.md` §4 tables, never `#eval`'d from the maps under test. The FAIL companions
are the required negatives: `naive_pullback_aliases` (a dropped coordinate falls
through verbatim and aliases a kept coordinate — the incomparable analogue of
`naive_composition_collides`), `c4_no_translation_flips` and `a3_ack_only_unsound`
(cross-epoch merges that flip a read without the translation the protocol owes),
`contOK_stale_collides` (a non-fresh mint collides). -/

namespace DiamondSPOT

open Sal.EmbedRGA (unaryCode)

/-! ### c1 — rank reclaim across the diamond, two-sided (`whiteboard/epoch-protocol-note.md` §4 c1)

Root inserts x1=(1), x2=(2), x3=(3), x4=(4); `del x1` settles only in S2,
`del x3` only in S1. `W` survivors: x2, x4 (x1, x3 dead). Hand-derived maps:
* leg A (`gcS1`: drop x3, rank {1,2,4}→{1,2,3}; `relA`: drop x1, rank {2,3}→{1,2});
* leg B (`gcS2`: drop x1, rank {2,3,4}→{1,2,3}; `relB`: drop x3(now (2)), rank
  {1,3}→{1,2});
* one-shot (`gcW`: drop x1,x3, rank {2,4}→{1,2}).
Both composites and the one-shot send x2↦(1), x4↦(2): s1, bit-identical. -/

def gcS1 (c : List Bool) : List Bool :=
  if c = unaryCode.enc 4 then unaryCode.enc 3 else c

def relA (c : List Bool) : List Bool :=
  if c = unaryCode.enc 2 then unaryCode.enc 1
  else if c = unaryCode.enc 3 then unaryCode.enc 2 else c

def gcS2 (c : List Bool) : List Bool :=
  if c = unaryCode.enc 2 then unaryCode.enc 1
  else if c = unaryCode.enc 3 then unaryCode.enc 2
  else if c = unaryCode.enc 4 then unaryCode.enc 3 else c

def relB (c : List Bool) : List Bool :=
  if c = unaryCode.enc 3 then unaryCode.enc 2 else c

def gcW (c : List Bool) : List Bool :=
  if c = unaryCode.enc 2 then unaryCode.enc 1
  else if c = unaryCode.enc 4 then unaryCode.enc 2 else c

/-- The join cut's kept records, epoch-0 coordinates, recency order (x4 newer). -/
def sW : EState ℕ := [(4, 40, unaryCode.enc 4), (2, 20, unaryCode.enc 2)]

def pathA : EState ℕ := eRemapSt (relA ∘ gcS1) sW
def pathB : EState ℕ := eRemapSt (relB ∘ gcS2) sW
def pathC : EState ℕ := eRemapSt gcW sW

/-- **PASS (s1, bit-identical)**: both relative composites and the one-shot land
on the SAME state, coordinate for coordinate — x4↦(2), x2↦(1). Not merely equal
reads: the shadow states are identical. -/
theorem c1_states_bit_identical :
    pathA = pathC ∧ pathB = pathC
      ∧ pathC = [(4, 40, unaryCode.enc 2), (2, 20, unaryCode.enc 1)] := by
  native_decide

/-- **PASS (reads = twin)**: every path reads `[40, 20]`, the never-compacted
twin's read. Not empty, not the id list. -/
theorem c1_reads_twin :
    SPOT.readE pathA = [40, 20] ∧ SPOT.readE pathB = [40, 20]
      ∧ SPOT.readE pathC = [40, 20] := by native_decide

/-- Post-cut straggler: a root insert `s` (id 9, delta 9), in epoch-0 code,
translated through the composite (its root prefix `[]` rides verbatim). -/
def strag : List (Op (EOp ℕ)) := [(9, 0, .ins 90 [] 0)]

def pathA' : EState ℕ :=
  applySeq (E unaryCode).toCRDTSig pathA (strag.map (eRemapOp (relA ∘ gcS1)))
def pathC' : EState ℕ :=
  applySeq (E unaryCode).toCRDTSig pathC (strag.map (eRemapOp gcW))
def twinStr : EState ℕ :=
  applySeq (E unaryCode).toCRDTSig
    [(4, 40, unaryCode.enc 4), (2, 20, unaryCode.enc 2)] strag

/-- **PASS**: the fresh straggler (delta 9 dominates every ordinal) rides through
every path and reads identically to the twin: `[90, 40, 20]`. -/
theorem c1_straggler_reads_twin :
    SPOT.readE pathA' = [90, 40, 20] ∧ SPOT.readE pathC' = [90, 40, 20]
      ∧ SPOT.readE twinStr = [90, 40, 20] := by native_decide

/-- **FAIL companion — the aliasing negative (O2, `whiteboard/epoch-protocol-note.md` §5.1).** Membership
pullback is unsound: the coordinate `enc 3` DROPPED by leg A falls through the
composite verbatim onto the reclaimed rank and ALIASES the kept `enc 4`, so a
domain computed by "is `f c` in range" is non-injective. The record-identity
transported domain excludes `enc 3` (x3's id is not kept) and includes `enc 4`
(x4's id is kept), which is why it is the only sound choice. -/
theorem naive_pullback_aliases :
    (relA ∘ gcS1) (unaryCode.enc 3) = (relA ∘ gcS1) (unaryCode.enc 4)
      ∧ unaryCode.enc 3 ≠ unaryCode.enc 4
      ∧ (∃ x ∈ sW, x.2.2 = unaryCode.enc 4)
      ∧ ¬ (∃ x ∈ sW, x.2.2 = unaryCode.enc 3) := by native_decide

/-- The two coordinates the transported domain carries (record identity: kept
ids {2, 4}), pinned distinct so the domain is genuinely alias-free (O2). -/
theorem c1_transported_domain :
    (sW.map (fun r => r.2.2)) = [unaryCode.enc 4, unaryCode.enc 2]
      ∧ unaryCode.enc 4 ≠ unaryCode.enc 2 := by native_decide

/-- **PASS (via the theorem, not recomputed)**: `diamond_confluence_fn` fired on
the concrete instance reproduces the c1 bit-identity, discharging its three
hypotheses (`hsD`, `hA`, `hB`) on the transported domain by `decide`. -/
theorem c1_via_theorem :
    eRemapSt (relA ∘ gcS1) sW = eRemapSt gcW sW
      ∧ eRemapSt (relB ∘ gcS2) sW = eRemapSt gcW sW := by
  refine diamond_confluence_fn
    (f1 := gcS1) (f2 := gcS2) (fa := relA) (fb := relB) (fw := gcW)
    (fun c => c = unaryCode.enc 2 ∨ c = unaryCode.enc 4) sW ?_ ?_ ?_
  · rintro x hx
    simp only [sW, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro c (rfl | rfl) <;> decide
  · rintro c (rfl | rfl) <;> decide

/-! ### c3 — the in-flight guard across the diamond (`whiteboard/epoch-protocol-note.md` §4 c3)

Root group a=(1), b=(2) dead, c=(3); f=(5) declared in flight at S1 (root group
FROZEN), settled under S2; d=(6) minted after S2, settled under S1. Both paths
and the one-shot end at a=(1), c=(2), f=(3), d=(4): freezing only DEFERS a
renumbering the join cut performs identically. -/

def gcS1_c3 (c : List Bool) : List Bool := c        -- frozen group: deltas verbatim
def relA_c3 (c : List Bool) : List Bool :=
  if c = unaryCode.enc 3 then unaryCode.enc 2
  else if c = unaryCode.enc 5 then unaryCode.enc 3
  else if c = unaryCode.enc 6 then unaryCode.enc 4 else c
def gcS2_c3 (c : List Bool) : List Bool :=
  if c = unaryCode.enc 3 then unaryCode.enc 2
  else if c = unaryCode.enc 5 then unaryCode.enc 3 else c
def relB_c3 (c : List Bool) : List Bool :=
  if c = unaryCode.enc 6 then unaryCode.enc 4 else c
def gcW_c3 (c : List Bool) : List Bool :=
  if c = unaryCode.enc 3 then unaryCode.enc 2
  else if c = unaryCode.enc 5 then unaryCode.enc 3
  else if c = unaryCode.enc 6 then unaryCode.enc 4 else c

/-- Join survivors, epoch-0 coords, recency order (d newest). -/
def sW_c3 : EState ℕ :=
  [(6, 60, unaryCode.enc 6), (5, 50, unaryCode.enc 5),
   (3, 30, unaryCode.enc 3), (1, 10, unaryCode.enc 1)]

/-- **PASS (s1)**: freeze-then-renumber (leg A) equals renumber-once (leg B) and
the one-shot at the codeword level — all land on d=(4), f=(3), c=(2), a=(1). -/
theorem c3_states_bit_identical :
    eRemapSt (relA_c3 ∘ gcS1_c3) sW_c3 = eRemapSt gcW_c3 sW_c3
      ∧ eRemapSt (relB_c3 ∘ gcS2_c3) sW_c3 = eRemapSt gcW_c3 sW_c3
      ∧ eRemapSt gcW_c3 sW_c3
          = [(6, 60, unaryCode.enc 4), (5, 50, unaryCode.enc 3),
             (3, 30, unaryCode.enc 2), (1, 10, unaryCode.enc 1)] := by
  native_decide

/-- **PASS (reads = twin)**: `[60, 50, 30, 10]` on every path. -/
theorem c3_reads_twin :
    SPOT.readE (eRemapSt (relA_c3 ∘ gcS1_c3) sW_c3) = [60, 50, 30, 10]
      ∧ SPOT.readE (eRemapSt gcW_c3 sW_c3) = [60, 50, 30, 10] := by native_decide

/-! ### c2 — fusion asymmetry (`whiteboard/epoch-protocol-note.md` §4 c2)

Unary spine r1..r4 with a live leaf x below; dels of r1,r2 settle in S1 only,
r3,r4 in S2 only. Path A fuses the prefix (r1,r2) then the rest, path B the
suffix (r3,r4) then the rest, the one-shot fuses the whole dead spine once — all
land on x = (1,1) because fusion always keeps the OUTERMOST head. Only x
survives; the maps drop the interior dead codewords. -/

def gcS1_c2 (c : List Bool) : List Bool :=
  if c = coordOf unaryCode [1, 1, 1, 1, 1] then coordOf unaryCode [1, 1, 1, 1] else c
def relA_c2 (c : List Bool) : List Bool :=
  if c = coordOf unaryCode [1, 1, 1, 1] then coordOf unaryCode [1, 1] else c
def gcS2_c2 (c : List Bool) : List Bool :=
  if c = coordOf unaryCode [1, 1, 1, 1, 1] then coordOf unaryCode [1, 1, 1, 1] else c
def relB_c2 (c : List Bool) : List Bool :=
  if c = coordOf unaryCode [1, 1, 1, 1] then coordOf unaryCode [1, 1] else c
def gcW_c2 (c : List Bool) : List Bool :=
  if c = coordOf unaryCode [1, 1, 1, 1, 1] then coordOf unaryCode [1, 1] else c

/-- The join survivor: the live leaf x, chain `[1,1,1,1,1]` (a 4-level dead
spine baked in). -/
def sW_c2 : EState ℕ := [(5, 50, coordOf unaryCode [1, 1, 1, 1, 1])]

/-- **PASS (s1)**: prefix-then-rest, suffix-then-rest and one-shot all fuse to
x = (1,1), bit for bit — fusion composes because it keeps the outermost head. -/
theorem c2_states_bit_identical :
    eRemapSt (relA_c2 ∘ gcS1_c2) sW_c2 = eRemapSt gcW_c2 sW_c2
      ∧ eRemapSt (relB_c2 ∘ gcS2_c2) sW_c2 = eRemapSt gcW_c2 sW_c2
      ∧ eRemapSt gcW_c2 sW_c2 = [(5, 50, coordOf unaryCode [1, 1])] := by
  native_decide

/-- **PASS (reads = twin)**: the single survivor reads `[50]` on every path. -/
theorem c2_reads_twin :
    SPOT.readE (eRemapSt (relA_c2 ∘ gcS1_c2) sW_c2) = [50]
      ∧ SPOT.readE (eRemapSt gcW_c2 sW_c2) = [50] := by native_decide

/-! ### c4 — the no-translation control, the required FAIL (`whiteboard/epoch-protocol-note.md` §4 c4)

x1=(1), x2=(2) at root, `del x1` settled. Compaction: x1 dropped, x2 (2)↦(1).
R2 (still epoch 0) mints y anchored at x2, coordinate (2,7). A raw union WITHOUT
translation places y's key before x2's: the read FLIPS from `[x2, y]` to
`[y, x2]`. Translating y's stable prefix ((2)↦(1)) restores the twin's read. -/

def sCompact_c4 : EState ℕ := [(2, 20, unaryCode.enc 1)]      -- x2 compacted to (1)

def rawMerge_c4 : EState ℕ :=
  eInsert (9, 90, unaryCode.enc 2 ++ unaryCode.enc 7) sCompact_c4
def fixMerge_c4 : EState ℕ :=
  eInsert (9, 90, unaryCode.enc 1 ++ unaryCode.enc 7) sCompact_c4
def twin_c4 : EState ℕ :=
  eInsert (9, 90, unaryCode.enc 2 ++ unaryCode.enc 7) [(2, 20, unaryCode.enc 2)]

/-- **FAIL companion**: the raw cross-epoch union flips the read
`[x2, y] = [20, 90]` to `[y, x2] = [90, 20]` — the defect the runtime's throw
guards against. Translation restores the twin's read; equality is pinned both
ways so the flip is not spurious. -/
theorem c4_no_translation_flips :
    SPOT.readE rawMerge_c4 = [90, 20]
      ∧ SPOT.readE twin_c4 = [20, 90]
      ∧ SPOT.readE rawMerge_c4 ≠ SPOT.readE twin_c4
      ∧ SPOT.readE fixMerge_c4 = SPOT.readE twin_c4 := by native_decide

/-! ### A3 — the ack-only map-drop certificate is UNSOUND (`whiteboard/epoch-protocol-note.md` §4 A3)

`Fdrop` is the epoch-0→1 map (renumber (2)↦(1)). A declared epoch-0 straggler
x (coordinate `enc 2`) arrives after every replica has acked. Under ack-only the
map is dropped, so x rides untranslated: `Fdrop (enc 2) ≠ enc 2` witnesses that x
is NOT in epoch-≥e space, so `mapDrop_sound`'s hypothesis fails, and the
untranslated child merge flips the read (as in c4). The sound side: an epoch-≥e
coordinate (`enc 1`) IS fixed by `Fdrop`, so under ack + AllHeardSince every later
mint is fixed and `mapDrop_sound` applies. -/

def Fdrop (c : List Bool) : List Bool :=
  if c = unaryCode.enc 2 then unaryCode.enc 1 else c

def a3_raw : EState ℕ :=
  eInsert (9, 90, unaryCode.enc 2 ++ unaryCode.enc 7) [(2, 20, unaryCode.enc 1)]
def a3_fix : EState ℕ :=
  eInsert (9, 90, Fdrop (unaryCode.enc 2) ++ unaryCode.enc 7) [(2, 20, unaryCode.enc 1)]

/-- **FAIL companion**: ack-only is unsound. The straggler's epoch-0 coordinate is
NOT fixed by the dropped map (`Fdrop (enc 2) ≠ enc 2`), so dropping the map
mistranslates and the merge reads differ (`a3_raw ≠ a3_fix`). -/
theorem a3_ack_only_unsound :
    Fdrop (unaryCode.enc 2) ≠ unaryCode.enc 2
      ∧ SPOT.readE a3_raw ≠ SPOT.readE a3_fix := by native_decide

/-- **PASS (the sound side)**: under ack + AllHeardSince every later-delivered op
is minted at a cutset ⊇ S, so its coordinate is already epoch-≥e — fixed by the
map (`Fdrop (enc 1) = enc 1`). That is exactly `mapDrop_sound`'s hypothesis. -/
theorem a3_strong_cert_fixes :
    Fdrop (unaryCode.enc 1) = unaryCode.enc 1 := by native_decide

/-! ### O4 — ContOK at a join epoch (`whiteboard/epoch-protocol-note.md` §8 ContOK, the 11029/0 target) -/

/-- A compacted (join-epoch) root state: two siblings at ranks (2), (1). -/
def sJoin : EState ℕ := [(2, 20, unaryCode.enc 2), (1, 10, unaryCode.enc 1)]

/-- **PASS**: a Lamport-fresh root mint (id 9, delta 9) satisfies all four ContOK
clauses at the compacted state — (1) id exceeds every state id; (2) continuation
insert ids nodup; (3) its key differs from every stored key; (4) two fresh mint
keys are pairwise distinct. The 11029/0 observation, one concrete instance. -/
theorem contOK_spot :
    (∀ x ∈ sJoin, x.1 < 9)
      ∧ ([9, 8] : List ℕ).Nodup
      ∧ (∀ x ∈ sJoin, key (unaryCode.enc 9) ≠ key x.2.2)
      ∧ key (unaryCode.enc 9) ≠ key (unaryCode.enc 8) := by native_decide

/-- **FAIL companion**: a STALE mint (delta 1, not fresh) collides — its key
equals the stored (1) record's key, violating clause (3). Freshness is
load-bearing. -/
theorem contOK_stale_collides :
    ¬ (∀ x ∈ sJoin, key (unaryCode.enc 1) ≠ key x.2.2) := by native_decide

/-- **PASS (via the theorem)**: `contOK_root_key_fresh` fired on `sJoin` with a
fresh delta 9 reproduces clause (3) — every stored root delta (2, 1) is `< 9`. -/
theorem contOK_clause3_via_theorem :
    ∀ x ∈ sJoin, key (unaryCode.enc 9) ≠ key x.2.2 := by
  refine contOK_root_key_fresh (Γ := unaryCode) (by decide) ?_
  rintro x hx
  simp only [sJoin, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨2, by decide, by decide, rfl⟩
  · exact ⟨1, by decide, by decide, rfl⟩

#print axioms c1_states_bit_identical
#print axioms c1_reads_twin
#print axioms c1_straggler_reads_twin
#print axioms naive_pullback_aliases
#print axioms c1_via_theorem
#print axioms c2_states_bit_identical
#print axioms c3_states_bit_identical
#print axioms c4_no_translation_flips
#print axioms a3_ack_only_unsound
#print axioms contOK_spot
#print axioms contOK_clause3_via_theorem

end DiamondSPOT

end Sal.ConditionedMRDTs
