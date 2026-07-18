import Sal.ConditionedMRDTs.Metatheory.Adequacy

/-!
# The stability VC: verified GC callbacks (task #96)

Mechanization of `whiteboard/stability-vc-note.md` (all sections, errata §9
applied). The runtime learns which events have reached every replica and calls
back into the datatype to shed redundant records. This file provides:

* **§1 `SettledAt`** (note §2): the semantic cut condition — `S ⊆ E(v)`,
  downward closed, all *existing* concurrency inside `E(v)` — and the
  runtime-facing **commit-shaped** evidence form (erratum §9.3), with the lemma
  `settledAtOn_of_evidence`: heard-from-everyone-since-`S` implies concurrency
  containment. Evidence quantifies over a covered replica set `J` (open
  membership is deferred, note §8).
* **§2 the VC bundle** `StabilityVC` (note §4) and the lifted configuration
  relation `ConfigRelS`. Erratum §9.2 applied: VC-S4 (`vc_merge`) is **not** a
  free argumentwise congruence — it is stated over related reachable pairs,
  encoded by threading the instance's auxiliary pair-invariant `Aux` (the
  external-invariant pattern) through every VC.
* **§3 the metatheorem** `stability_simulation` (note §5): every `Step3` step
  of the full run is matched, same label (query readback up to the observation),
  by the compacted run; a `SettledAt` compaction is a *stuttering* step — the
  full side takes a self-merge (a genuine `Step3.merge r r`, legal because
  `IsLCA` is reflexive), the compacted side registers `compact ŝ` at the same
  fresh slot, so DAG shapes never diverge. Reads are equal at every version
  (`stability_reads_equal`), and RA-linearizability is inherited
  *observationally* (`stability_ra_inherited`).

**Scope notes (deviations recorded for the note's §10).**
1. VC-S3's class (b) (in-flight ops referencing dropped records) has no
   separate update-time clause here: in the state-based ternary model in-flight
   effects arrive exclusively through `Step3.merge` branch states, so class (b)
   is absorbed into VC-S4. `vc_step` covers exactly class (a) (fresh mints).
2. `createReplica` is gated by the bundle's `canCreate`: a replica minted at
   the root after a compaction can mint events concurrent with the cut,
   destroying settledness — this is the note §8 open-membership deferral made
   operational. Instances that never compact take `canCreate := ⊤`.
3. Query labels carry the raw `D.Value`; the compacted side answers with its
   own raw value (`LabelSim.query` leaves it free) and the guarantee is
   observational (`stability_reads_equal` / `reads_replica_equal`).

**Step3V compatibility** (`settledAtOn_of_evidence_reachableV`): `SettledAt` is
a per-configuration predicate and the evidence lemma consumes only `StoreInv`,
which is a `Step3V` reachability invariant (`storeInv_reachableV`), so the
evidence route is available verbatim on the widened system. The simulation
itself is stated over `Step3` (what `gc_safety` uses); widening the matching to
`Step3V.mergeVirtual` would require VC-S4 at virtual-LCA states and is out of
scope.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

section Settled

variable {D : ConditionedMRDTSig}

/-! ## §1 SettledAt: the semantic cut condition and the evidence form -/

/-- Two events are concurrent in `C`: distinct and `vis`-unrelated. -/
def ConcOp (C : Configuration D) (e a : Op D.AppOp) : Prop :=
  e ≠ a ∧ ¬ C.vis e a ∧ ¬ C.vis a e

/-- **The semantic settled condition** (note §2), stated against the event set
`E` of the settling version: the cut is inside `E` and causally downward
closed, and every event *existing anywhere in the configuration* that is
concurrent with a cut member is already in `E`. -/
structure SettledAtOn (C : Configuration D) (E S : Set (Op D.AppOp)) : Prop where
  /-- `S ⊆ E(v)`. -/
  sub : S ⊆ E
  /-- `S` is causally downward closed. -/
  down : ∀ a b, C.vis a b → b ∈ S → a ∈ S
  /-- All existing concurrency with `S` is inside `E(v)`. -/
  conc : ∀ e ∈ C.events, (∃ a ∈ S, ConcOp C e a) → e ∈ E

/-- `SettledAt v S`: version `v` is allocated and its event set settles `S`. -/
def SettledAt (C : Configuration D) (v : Version) (S : Set (Op D.AppOp)) : Prop :=
  ∃ s E, C.ver v = some (s, E) ∧ SettledAtOn C E S

/-- **Commit-shaped per-replica evidence** (erratum §9.3): a version `c`
absorbed by `v` (`Reaches`), containing `S`, certified as replica `j`'s commit
by the chain clause: every `j`-event outside `E(c)` post-dates it, in
particular has all of `S` in its causal past. A pull that brings no new events
can still bring `c`; nothing here mentions minted events of the pull itself. -/
def EvidenceCommit (C : Configuration D) (v : Version) (S : Set (Op D.AppOp))
    (j : Replica) : Prop :=
  ∃ c sc Ec, Reaches C.parents c v ∧ C.ver c = some (sc, Ec) ∧ S ⊆ Ec ∧
    ∀ e ∈ C.events, Op.rep e = j → e ∉ Ec → ∀ a ∈ S, C.vis a e

/-- **The evidence lemma** (note §2): if `v` has absorbed an evidence commit
for every replica of a set `J` covering all event authors, then all existing
concurrency with `S` is inside `E(v)` — the runtime's per-replica commits
discharge the semantic condition. The only store fact consumed is
`events_mono` along `Reaches` (`StoreInv`). -/
theorem settledAtOn_of_evidence {C : Configuration D}
    (hStore : StoreInv C.ver C.parents)
    {v : Version} {s : D.State} {E S : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E))
    (hsub : S ⊆ E) (hdown : ∀ a b, C.vis a b → b ∈ S → a ∈ S)
    {J : Set Replica}
    (hJ : ∀ e ∈ C.events, Op.rep e ∈ J)
    (hev : ∀ j ∈ J, EvidenceCommit C v S j) :
    SettledAtOn C E S := by
  refine ⟨hsub, hdown, ?_⟩
  rintro e he ⟨a, ha, -, -, hnae⟩
  obtain ⟨c, sc, Ec, hreach, hc, hSc, hcert⟩ := hev (Op.rep e) (hJ e he)
  by_cases hmem : e ∈ Ec
  · exact storeInv_events_mono_reaches hStore hreach hc hv hmem
  · exact absurd (hcert e he rfl hmem a ha) hnae

/-- The version-level form: `SettledAt` from allocatedness + the evidence. -/
theorem settledAt_of_evidence {C : Configuration D}
    (hStore : StoreInv C.ver C.parents)
    {v : Version} {s : D.State} {E S : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E))
    (hsub : S ⊆ E) (hdown : ∀ a b, C.vis a b → b ∈ S → a ∈ S)
    {J : Set Replica}
    (hJ : ∀ e ∈ C.events, Op.rep e ∈ J)
    (hev : ∀ j ∈ J, EvidenceCommit C v S j) :
    SettledAt C v S :=
  ⟨s, E, hv, settledAtOn_of_evidence hStore hv hsub hdown hJ hev⟩

open LabeledTS in
/-- **Step3V compatibility** (cheap corollary): the evidence lemma is available
at every configuration reachable in the *widened* system `Step3V`, because
`StoreInv` is a `Step3V` reachability invariant. Nothing else in `SettledAt`
mentions the step relation. -/
theorem settledAt_of_evidence_reachableV {hInit : D.Inv D.init}
    {C : Configuration D}
    (hReach : (labeledTS3V D).ReachableFrom (initConfig D hInit) C)
    {v : Version} {s : D.State} {E S : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E))
    (hsub : S ⊆ E) (hdown : ∀ a b, C.vis a b → b ∈ S → a ∈ S)
    {J : Set Replica}
    (hJ : ∀ e ∈ C.events, Op.rep e ∈ J)
    (hev : ∀ j ∈ J, EvidenceCommit C v S j) :
    SettledAt C v S :=
  settledAt_of_evidence (storeInv_reachableV hReach) hv hsub hdown hJ hev

/-- **Event-shaped witness ⟹ commit-shaped evidence** (the bridge the erratum
warns is *not* a definition but is a valid *strengthening*): an event `w ∈ E(v)`
by `j` with all of `S` visible to it certifies `v` itself as `j`'s evidence
commit. Uses `vis` transitivity, per-version causal closure and the structural
same-replica totality — all supplied by `GoodConfig3` below. -/
theorem evidenceCommit_of_witness {C : Configuration D}
    (hTrans : ∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c)
    {v : Version} {s : D.State} {E S : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E))
    (hCausal : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (hEsub : ∀ a ∈ E, a ∈ C.events)
    (hSsub : S ⊆ E)
    {j : Replica} {w : Op D.AppOp}
    (hw : w ∈ E) (hrep : Op.rep w = j) (hpast : ∀ a ∈ S, C.vis a w) :
    EvidenceCommit C v S j := by
  refine ⟨v, s, E, Relation.ReflTransGen.refl, hv, hSsub, ?_⟩
  intro e he hej hne a ha
  have hwE : w ∈ C.events := hEsub w hw
  obtain ⟨r₁, s₁, hL₁, hs₁⟩ := he
  obtain ⟨r₂, s₂, hL₂, hs₂⟩ := hwE
  have hnew : e ≠ w := fun h => hne (h ▸ hw)
  have hrr : e.2.1 = w.2.1 := by
    show Op.rep e = Op.rep w
    rw [hej, hrep]
  rcases C.vis_total_same_replica hL₁ hs₁ hL₂ hs₂ hnew hrr with hew | hwe
  · exact absurd (hCausal e w hew hw) hne
  · exact hTrans (hpast a ha) hwe

/-- The `GoodConfig3` packaging of the witness bridge. -/
theorem evidenceCommit_of_witness_good {C : Configuration D}
    (hGood : GoodConfig3 C)
    {v : Version} {s : D.State} {E S : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E)) (hSsub : S ⊆ E)
    {j : Replica} {w : Op D.AppOp}
    (hw : w ∈ E) (hrep : Op.rep w = j) (hpast : ∀ a ∈ S, C.vis a w) :
    EvidenceCommit C v S j :=
  evidenceCommit_of_witness (fun hab hbc => hGood.vis_trans hab hbc) hv
    (hGood.ver_causal v s E hv) (hGood.ver_events_sub v s E hv) hSsub hw hrep
    hpast

/-- **The all-heads frontier condition**: every current head's event set
contains `S`. This is the same all-heads knowledge the commit GC (`gc_safety`)
requires; as a compaction *gate* alone it is the naive contract and UNSOUND
(the OR-set SPOT pins the countermodel) — instances use it only as the
stability side of the runtime contract, alongside `SettledAt`. -/
def AllHeard (C : Configuration D) (S : Set (Op D.AppOp)) : Prop :=
  ∀ r v s E, C.head r = some v → C.ver v = some (s, E) → S ⊆ E

end Settled

section Lifted

variable {D : ConditionedMRDTSig}

/-! ## §2 The lifted configuration relation -/

/-- **The lifted relation** (note §5): DAG shape, heads, visibility and event
sets shared verbatim; version payloads pointwise `R`-related (full on the left,
compacted on the right). `heads_alloc`/`head_none` are the two head-hygiene
facts of the full side that every reachable configuration enjoys; they are
carried here so the matching lemmas close without a reachability detour. -/
structure ConfigRelS (R : D.State → D.State → Prop)
    (C Ĉ : Configuration D) : Prop where
  L_eq : Ĉ.L = C.L
  vis_eq : Ĉ.vis = C.vis
  head_eq : Ĉ.head = C.head
  parents_eq : Ĉ.parents = C.parents
  heads_alloc : ∀ r v, C.head r = some v → (C.ver v).isSome
  head_none : ∀ r, C.head r = none → C.N r = none
  ver_events : ∀ v, (Ĉ.ver v).map Prod.snd = (C.ver v).map Prod.snd
  ver_rel : ∀ v s E ŝ Ê, C.ver v = some (s, E) → Ĉ.ver v = some (ŝ, Ê) →
    R s ŝ

namespace ConfigRelS

variable {R : D.State → D.State → Prop} {C Ĉ : Configuration D}

theorem events_eq (h : ConfigRelS R C Ĉ) : Ĉ.events = C.events := by
  unfold Configuration.events
  rw [h.L_eq]

/-- Allocation matches slot for slot. -/
theorem ver_isSome (h : ConfigRelS R C Ĉ) (v : Version) :
    (Ĉ.ver v).isSome = (C.ver v).isSome := by
  have hE := h.ver_events v
  cases hc : C.ver v with
  | none =>
    rw [hc] at hE
    cases hĉ : Ĉ.ver v with
    | none => rfl
    | some q => rw [hĉ] at hE; simp at hE
  | some p =>
    rw [hc] at hE
    cases hĉ : Ĉ.ver v with
    | none => rw [hĉ] at hE; simp at hE
    | some q => rfl

/-- A full-side allocation forces a compacted one with the *same* event set. -/
theorem ver_some (h : ConfigRelS R C Ĉ) {v : Version} {s : D.State}
    {E : Set (Op D.AppOp)} (hv : C.ver v = some (s, E)) :
    ∃ ŝ, Ĉ.ver v = some (ŝ, E) ∧ R s ŝ := by
  have hE := h.ver_events v
  rw [hv] at hE
  cases hĉ : Ĉ.ver v with
  | none => rw [hĉ] at hE; simp at hE
  | some q =>
    obtain ⟨ŝ, Ê⟩ := q
    rw [hĉ] at hE
    simp only [Option.map_some] at hE
    have hEE : Ê = E := by injection hE
    rw [hEE] at hĉ
    refine ⟨ŝ, ?_, h.ver_rel v s E ŝ E hv hĉ⟩
    rw [hEE]

theorem ver_none (h : ConfigRelS R C Ĉ) {v : Version}
    (hv : C.ver v = none) : Ĉ.ver v = none := by
  have hs := h.ver_isSome v
  rw [hv] at hs
  cases hĉ : Ĉ.ver v with
  | none => rfl
  | some q => rw [hĉ] at hs; simp at hs

/-- The compacted side answers every replica read with an `R`-related state. -/
theorem N_some (h : ConfigRelS R C Ĉ) {r : Replica} {s : D.State}
    (hN : C.N r = some s) : ∃ ŝ, Ĉ.N r = some ŝ ∧ R s ŝ := by
  cases hh : C.head r with
  | none =>
    have := h.head_none r hh
    rw [hN] at this
    cases this
  | some v =>
    have hcoh := C.head_coherent r v hh
    have halloc := h.heads_alloc r v hh
    obtain ⟨⟨sv, Ev⟩, hv⟩ := Option.isSome_iff_exists.mp halloc
    have hsv : sv = s := by
      have := hcoh.1
      rw [hv, hN] at this
      simpa using this
    subst hsv
    obtain ⟨ŝ, hĉ, hR⟩ := h.ver_some hv
    have hĥ : Ĉ.head r = some v := by rw [h.head_eq]; exact hh
    have hcohĉ := Ĉ.head_coherent r v hĥ
    refine ⟨ŝ, ?_, hR⟩
    have := hcohĉ.1
    rw [hĉ] at this
    simpa using this.symm

theorem N_none (h : ConfigRelS R C Ĉ) {r : Replica}
    (hN : C.N r = none) : Ĉ.N r = none := by
  have hL : C.L r = none := (C.dom_eq r).mp hN
  refine (Ĉ.dom_eq r).mpr ?_
  rw [h.L_eq]
  exact hL

theorem N_none_iff (h : ConfigRelS R C Ĉ) (r : Replica) :
    Ĉ.N r = none ↔ C.N r = none := by
  rw [Ĉ.dom_eq r, C.dom_eq r, h.L_eq]

/-- A compacted-side allocation reflects to the full side, same event set. -/
theorem ver_some' (h : ConfigRelS R C Ĉ) {v : Version} {ŝ : D.State}
    {Ê : Set (Op D.AppOp)} (hv : Ĉ.ver v = some (ŝ, Ê)) :
    ∃ s, C.ver v = some (s, Ê) := by
  have hE := h.ver_events v
  rw [hv] at hE
  cases hc : C.ver v with
  | none => rw [hc] at hE; simp at hE
  | some p =>
    obtain ⟨ps, pe⟩ := p
    rw [hc] at hE
    simp only [Option.map_some] at hE
    have hpe : Ê = pe := by injection hE
    subst hpe
    exact ⟨ps, rfl⟩

end ConfigRelS

/-- The lifted relation holds reflexively at any configuration whose heads are
hygienic, in particular at `initConfig` (`relS_init`). -/
theorem relS_refl {R : D.State → D.State → Prop} {C : Configuration D}
    (hrefl : ∀ s, R s s)
    (hha : ∀ r v, C.head r = some v → (C.ver v).isSome)
    (hhn : ∀ r, C.head r = none → C.N r = none) :
    ConfigRelS R C C where
  L_eq := rfl
  vis_eq := rfl
  head_eq := rfl
  parents_eq := rfl
  heads_alloc := hha
  head_none := hhn
  ver_events := fun _ => rfl
  ver_rel := fun v s E ŝ Ê hv hv' => by
    rw [hv] at hv'
    have : s = ŝ := by
      have := congrArg (Option.map Prod.fst) hv'
      simpa using this
    rw [← this]
    exact hrefl s

theorem relS_init {R : D.State → D.State → Prop} (hrefl : ∀ s, R s s)
    (hInit : D.Inv D.init) :
    ConfigRelS R (initConfig D hInit) (initConfig D hInit) := by
  refine relS_refl hrefl ?_ ?_
  · intro r v hh
    by_cases hr : r = 0
    · subst hr
      have h00 : (initConfig D hInit).head 0 = some 0 := rfl
      rw [h00] at hh
      injection hh with hh
      subst hh
      rw [(initConfig D hInit).ver_init]
      rfl
    · have : (initConfig D hInit).head r = none := by
        show (if r = 0 then some 0 else none) = none
        rw [if_neg hr]
      rw [this] at hh
      cases hh
  · intro r hh
    by_cases hr : r = 0
    · subst hr
      have : (initConfig D hInit).head 0 = some 0 := rfl
      rw [this] at hh
      cases hh
    · show (if r = 0 then some D.init else none) = none
      rw [if_neg hr]

/-! ## §2b The payload surgery

`restate Cb Nc verc …` is `Cb` (the *full-side target* of a step) with its
per-version states and replica heads replaced; event sets, DAG, heads and the
whole replica-keyed causal core are carried verbatim. The five obligations are
exactly what the `Configuration` invariants need; in particular `lca_events`
transfers because the event components are untouched. -/

def restate (Cb : Configuration D)
    (Nc : Replica → Option D.State)
    (verc : Version → Option (D.State × Set (Op D.AppOp)))
    (hE : ∀ v, (verc v).map Prod.snd = (Cb.ver v).map Prod.snd)
    (h0 : verc 0 = some (D.init, ∅))
    (hInv : ∀ v s e, verc v = some (s, e) → D.Inv s)
    (hNd : ∀ r, Nc r = none ↔ Cb.N r = none)
    (hcoh : ∀ r v, Cb.head r = some v → (verc v).map Prod.fst = Nc r) :
    Configuration D where
  N := Nc
  L := Cb.L
  vis := Cb.vis
  dom_eq := fun r => (hNd r).trans (Cb.dom_eq r)
  vis_src := Cb.vis_src
  vis_tgt := Cb.vis_tgt
  vis_causal := Cb.vis_causal
  timestamps_distinct := Cb.timestamps_distinct
  causal_mono := Cb.causal_mono
  vis_total_same_replica := Cb.vis_total_same_replica
  ver := verc
  head := Cb.head
  parents := Cb.parents
  parents_lt := Cb.parents_lt
  ver_init := h0
  head_coherent := fun r v h =>
    ⟨hcoh r v h, (hE v).trans (Cb.head_coherent r v h).2⟩
  ver_inv := hInv
  lca_events := by
    intro v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT hlca h1 h2 hT
    have conv : ∀ {w sw ew}, verc w = some (sw, ew) →
        ∃ sw', Cb.ver w = some (sw', ew) := by
      intro w sw ew hw
      have hEw := hE w
      rw [hw] at hEw
      cases hb : Cb.ver w with
      | none => rw [hb] at hEw; simp at hEw
      | some p =>
        obtain ⟨ps, pe⟩ := p
        rw [hb] at hEw
        simp only [Option.map_some] at hEw
        have hpe : ew = pe := by injection hEw
        subst hpe
        exact ⟨ps, rfl⟩
    obtain ⟨s₁', h1'⟩ := conv h1
    obtain ⟨s₂', h2'⟩ := conv h2
    obtain ⟨sT', hT'⟩ := conv hT
    exact Cb.lca_events hlca h1' h2' hT'

@[simp] theorem restate_ver (Cb : Configuration D) (Nc verc hE h0 hInv hNd hcoh) :
    (restate Cb Nc verc hE h0 hInv hNd hcoh).ver = verc := rfl

@[simp] theorem restate_N (Cb : Configuration D) (Nc verc hE h0 hInv hNd hcoh) :
    (restate Cb Nc verc hE h0 hInv hNd hcoh).N = Nc := rfl

@[simp] theorem restate_L (Cb : Configuration D) (Nc verc hE h0 hInv hNd hcoh) :
    (restate Cb Nc verc hE h0 hInv hNd hcoh).L = Cb.L := rfl

@[simp] theorem restate_vis (Cb : Configuration D) (Nc verc hE h0 hInv hNd hcoh) :
    (restate Cb Nc verc hE h0 hInv hNd hcoh).vis = Cb.vis := rfl

@[simp] theorem restate_head (Cb : Configuration D) (Nc verc hE h0 hInv hNd hcoh) :
    (restate Cb Nc verc hE h0 hInv hNd hcoh).head = Cb.head := rfl

@[simp] theorem restate_parents (Cb : Configuration D)
    (Nc verc hE h0 hInv hNd hcoh) :
    (restate Cb Nc verc hE h0 hInv hNd hcoh).parents = Cb.parents := rfl

end Lifted

section Bundle

variable {D : ConditionedMRDTSig}

/-! ## §2c The VC bundle (note §4, errata applied) -/

/-- **The stability VC bundle** for a fixed cut `S` and callback `compact`.

* `R` — the simulation relation (full left, compacted right); `vc_refl` keeps
  the pre-compaction run related.
* `obs` — the datatype's read interface; **VC-S2** is `vc_obs`.
* `Aux` — the instance's auxiliary pair-invariant: the *reachable-triples*
  side condition of erratum §9.2, threaded through `vc_step`/`vc_merge`/
  `vc_entry` and maintained by the `aux_*` obligations (external-invariant
  pattern, no instance file edited).
* **VC-S1** is `vc_entry` (the full side's stuttering self-merge payload
  `mergeL s s s` against `compact ŝ`), gated by `gate`, which must imply
  `SettledAt` (`gate_settled`) — the note §2 contract.
* **VC-S3** is `vc_step` — class (a) only; class (b) is absorbed into VC-S4
  (file header, scope note 1).
* **VC-S4** is `vc_merge` — *not* a free congruence: it fires only under
  `ConfigRelS ∧ Aux` at genuine merge premises (erratum §9.2).
* **VC-S5** is `vc_inv` (state-shape contract preservation; the honesty
  contract is inherited observationally by `stability_ra_inherited`).
* **VC-S6** (epoch coherence) is the standalone `EpochCoherentObs` below.
-/
structure StabilityVC (D : ConditionedMRDTSig) where
  R : D.State → D.State → Prop
  Obs : Type
  obs : D.State → Obs
  compact : D.State → D.State
  S : Set (Op D.AppOp)
  Aux : Configuration D → Configuration D → Prop
  gate : Configuration D → Configuration D → Replica → Version → Prop
  canCreate : Configuration D → Configuration D → Replica → Prop
  vc_refl : ∀ s, R s s
  vc_obs : ∀ {s ŝ}, R s ŝ → obs s = obs ŝ
  vc_inv : ∀ {s ŝ}, R s ŝ → D.Inv s → D.Inv ŝ
  gate_settled : ∀ {C Ĉ r v}, gate C Ĉ r v → SettledAt C v S
  vc_step : ∀ {C Ĉ : Configuration D}, ConfigRelS R C Ĉ → Aux C Ĉ →
    ∀ {t : Timestamp} {r : Replica} {o : D.AppOp} {v : Version}
      {s ŝ : D.State} {E : Set (Op D.AppOp)},
    C.head r = some v → C.ver v = some (s, E) → Ĉ.ver v = some (ŝ, E) →
    (∀ e' ∈ C.events, Op.time e' ≠ t) →
    (∀ w sw Ew, C.ver w = some (sw, Ew) → ∀ e' ∈ Ew, Op.time e' ≠ t) →
    R s ŝ → R (D.update s (t, r, o)) (D.update ŝ (t, r, o))
  vc_merge : ∀ {C Ĉ : Configuration D}, ConfigRelS R C Ĉ → Aux C Ĉ →
    ∀ {r₁ r₂ : Replica} {v₁ v₂ vT : Version} {s₁ s₂ sT ŝ₁ ŝ₂ ŝT : D.State}
      {E₁ E₂ ET : Set (Op D.AppOp)},
    C.head r₁ = some v₁ → C.head r₂ = some v₂ →
    C.ver v₁ = some (s₁, E₁) → C.ver v₂ = some (s₂, E₂) →
    IsLCA C.parents v₁ v₂ vT → C.ver vT = some (sT, ET) →
    Ĉ.ver v₁ = some (ŝ₁, E₁) → Ĉ.ver v₂ = some (ŝ₂, E₂) →
    Ĉ.ver vT = some (ŝT, ET) →
    R (D.mergeL sT s₁ s₂) (D.mergeL ŝT ŝ₁ ŝ₂)
  vc_entry : ∀ {C Ĉ : Configuration D}, ConfigRelS R C Ĉ → Aux C Ĉ →
    ∀ {r : Replica} {v : Version} {s ŝ : D.State} {E : Set (Op D.AppOp)},
    gate C Ĉ r v → C.head r = some v → C.ver v = some (s, E) →
    Ĉ.ver v = some (ŝ, E) →
    R (D.mergeL s s s) (compact ŝ)
  aux_init : ∀ hInit : D.Inv D.init,
    Aux (initConfig D hInit) (initConfig D hInit)
  aux_create : ∀ {C Ĉ C' Ĉ' : Configuration D} {r : Replica},
    ConfigRelS R C Ĉ → Aux C Ĉ → canCreate C Ĉ r →
    Step3 D C (.createReplica r) C' → Step3 D Ĉ (.createReplica r) Ĉ' →
    ConfigRelS R C' Ĉ' → Aux C' Ĉ'
  aux_apply : ∀ {C Ĉ C' Ĉ' : Configuration D} {t : Timestamp} {r : Replica}
      {o : D.AppOp},
    ConfigRelS R C Ĉ → Aux C Ĉ →
    Step3 D C (.apply t r o) C' → Step3 D Ĉ (.apply t r o) Ĉ' →
    ConfigRelS R C' Ĉ' → Aux C' Ĉ'
  aux_merge : ∀ {C Ĉ C' Ĉ' : Configuration D} {r₁ r₂ : Replica},
    ConfigRelS R C Ĉ → Aux C Ĉ →
    Step3 D C (.merge r₁ r₂) C' → Step3 D Ĉ (.merge r₁ r₂) Ĉ' →
    ConfigRelS R C' Ĉ' → Aux C' Ĉ'
  aux_compact : ∀ {C Ĉ C' Ĉ' : Configuration D} {r : Replica} {v vm : Version}
      {s ŝ : D.State} {E : Set (Op D.AppOp)},
    ConfigRelS R C Ĉ → Aux C Ĉ → gate C Ĉ r v →
    C.head r = some v → C.ver v = some (s, E) → Ĉ.ver v = some (ŝ, E) →
    C.ver vm = none → v < vm →
    Step3 D C (.merge r r) C' →
    C'.ver = (fun w => if w = vm then some (D.mergeL s s s, E ∪ E)
      else C.ver w) →
    C'.head = (fun r' => if r' = r then some vm else C.head r') →
    C'.L = updateRep C.L r (E ∪ E) →
    C'.vis = C.vis →
    C'.parents = (fun w => if w = vm then [v, v] else C.parents w) →
    Ĉ'.N = updateRep Ĉ.N r (compact ŝ) →
    Ĉ'.L = C'.L → Ĉ'.vis = C'.vis → Ĉ'.head = C'.head →
    Ĉ'.parents = C'.parents →
    Ĉ'.ver = (fun w => if w = vm then some (compact ŝ, E ∪ E) else Ĉ.ver w) →
    ConfigRelS R C' Ĉ' → Aux C' Ĉ'

/-- **VC-S6, epoch coherence, observational form** (deviation recorded in the
final report): compacting at `S` and then at `S' ⊇ S` lands in the same
*observational* class as compacting at `S'` directly. (As a same-`R`-class
statement it is false for graph-shaped relations: a tag dropped at the first
epoch whose second-epoch keeper has since died is kept by the direct `S'`
compaction; reads still agree, which is what the harness checks.) -/
def EpochCoherentObs (V V' : StabilityVC D) : Prop :=
  ∀ h : V'.Obs = V.Obs, ∀ s,
    h ▸ V'.obs (V'.compact (V.compact s)) = h ▸ V'.obs (V'.compact s)

/-- Label matching: mutating labels verbatim; a query answers with the raw
value of the answering side (the observational guarantee is
`stability_reads_equal` / `reads_replica_equal`). -/
inductive LabelSim (D : ConditionedMRDTSig) : Label3 D → Label3 D → Prop where
  | create (r : Replica) :
      LabelSim D (.createReplica r) (.createReplica r)
  | apply (t : Timestamp) (r : Replica) (o : D.AppOp) :
      LabelSim D (.apply t r o) (.apply t r o)
  | merge (r₁ r₂ : Replica) : LabelSim D (.merge r₁ r₂) (.merge r₁ r₂)
  | query (r : Replica) (q : D.Query) (val val' : D.Value) :
      LabelSim D (.query r q val) (.query r q val')

end Bundle

section Matching

variable {D : ConditionedMRDTSig} (V : StabilityVC D)

/-! ## §3 The matching lemmas: every full step is matched compactedly -/

/-- CreateReplica is matched verbatim (store untouched on either side). -/
theorem stability_match_create {C Ĉ C' : Configuration D} {r : Replica}
    (rel : ConfigRelS V.R C Ĉ) (aux : V.Aux C Ĉ)
    (hcc : V.canCreate C Ĉ r)
    (hstep : Step3 D C (.createReplica r) C') :
    ∃ Ĉ', Step3 D Ĉ (.createReplica r) Ĉ' ∧
      ConfigRelS V.R C' Ĉ' ∧ V.Aux C' Ĉ' := by
  cases hstep with
  | @createReplica _ h_fresh C' hN hL hvis hver hhead hparents =>
  have hE : ∀ w, (Ĉ.ver w).map Prod.snd = (C'.ver w).map Prod.snd := by
    intro w; rw [hver]; exact rel.ver_events w
  have hNd : ∀ r', updateRep Ĉ.N r D.init r' = none ↔ C'.N r' = none := by
    intro r'
    rw [hN]
    show updateRep Ĉ.N r D.init r' = none ↔ updateRep C.N r D.init r' = none
    unfold updateRep
    by_cases hr : r' = r
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr]
      exact rel.N_none_iff r'
  have hcoh : ∀ r' w, C'.head r' = some w →
      (Ĉ.ver w).map Prod.fst = updateRep Ĉ.N r D.init r' := by
    intro r' w hw
    simp only [hhead] at hw
    unfold updateRep
    by_cases hr : r' = r
    · rw [if_pos hr] at hw ⊢
      injection hw with hw
      subst hw
      rw [Ĉ.ver_init]
      rfl
    · rw [if_neg hr] at hw ⊢
      have hĥ : Ĉ.head r' = some w := by rw [rel.head_eq]; exact hw
      exact (Ĉ.head_coherent r' w hĥ).1
  let Ĉ' : Configuration D :=
    restate C' (updateRep Ĉ.N r D.init) Ĉ.ver hE Ĉ.ver_init Ĉ.ver_inv hNd hcoh
  have hstep' : Step3 D Ĉ (.createReplica r) Ĉ' := by
    refine Step3.createReplica (rel.N_none h_fresh) _ rfl ?_ ?_ rfl ?_ ?_
    · show C'.L = updateRep Ĉ.L r ∅
      rw [hL, rel.L_eq]
    · show C'.vis = Ĉ.vis
      rw [hvis, rel.vis_eq]
    · show C'.head = fun r' => if r' = r then some 0 else Ĉ.head r'
      rw [hhead, rel.head_eq]
    · show C'.parents = Ĉ.parents
      rw [hparents, rel.parents_eq]
  have hrel' : ConfigRelS V.R C' Ĉ' := by
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, hE, ?_⟩
    · intro r' w hw
      simp only [hhead] at hw
      rw [hver]
      by_cases hr : r' = r
      · rw [if_pos hr] at hw
        injection hw with hw
        subst hw
        rw [C.ver_init]
        rfl
      · rw [if_neg hr] at hw
        exact rel.heads_alloc r' w hw
    · intro r' hw
      simp only [hhead] at hw
      by_cases hr : r' = r
      · rw [if_pos hr] at hw
        cases hw
      · rw [if_neg hr] at hw
        rw [hN]
        show updateRep C.N r D.init r' = none
        unfold updateRep
        rw [if_neg hr]
        exact rel.head_none r' hw
    · intro w s E ŝ Ê hw hŵ
      rw [hver] at hw
      exact rel.ver_rel w s E ŝ Ê hw hŵ
  exact ⟨Ĉ', hstep', hrel', V.aux_create rel aux hcc
    (Step3.createReplica h_fresh C' hN hL hvis hver hhead hparents)
    hstep' hrel'⟩

/-- Apply is matched verbatim: same op, same fresh slot; the fresh payload is
related by **VC-S3** (`vc_step`). -/
theorem stability_match_apply {C Ĉ C' : Configuration D} {t : Timestamp}
    {r : Replica} {o : D.AppOp}
    (rel : ConfigRelS V.R C Ĉ) (aux : V.Aux C Ĉ)
    (hstep : Step3 D C (.apply t r o) C') :
    ∃ Ĉ', Step3 D Ĉ (.apply t r o) Ĉ' ∧
      ConfigRelS V.R C' Ĉ' ∧ V.Aux C' Ĉ' := by
  cases hstep with
  | @apply _ _ _ v s ev vnew h_head h_ver h_fresh_t h_fresh_store h_vnew
      h_rank C' hN hL hvis hver hhead hparents =>
  obtain ⟨ŝ, hĉv, hR⟩ := rel.ver_some h_ver
  have hR' : V.R (D.update s (t, r, o)) (D.update ŝ (t, r, o)) :=
    V.vc_step rel aux h_head h_ver hĉv h_fresh_t h_fresh_store hR
  have h0ne : (0 : Version) ≠ vnew := by
    intro h
    rw [← h] at h_vnew
    rw [C.ver_init] at h_vnew
    cases h_vnew
  have hE : ∀ w,
      ((fun w => if w = vnew
        then some (D.update ŝ (t, r, o), ev ∪ {(t, r, o)})
        else Ĉ.ver w) w).map Prod.snd = (C'.ver w).map Prod.snd := by
    intro w
    rw [hver]
    dsimp only
    by_cases hw : w = vnew
    · rw [if_pos hw, if_pos hw]
      rfl
    · rw [if_neg hw, if_neg hw]
      exact rel.ver_events w
  have h0 : (fun w => if w = vnew
      then some (D.update ŝ (t, r, o), ev ∪ {(t, r, o)})
      else Ĉ.ver w) 0 = some (D.init, ∅) := by
    dsimp only
    rw [if_neg h0ne]
    exact Ĉ.ver_init
  have hInvV : ∀ w sw ew, (fun w => if w = vnew
      then some (D.update ŝ (t, r, o), ev ∪ {(t, r, o)})
      else Ĉ.ver w) w = some (sw, ew) → D.Inv sw := by
    intro w sw ew hw
    dsimp only at hw
    by_cases hwn : w = vnew
    · rw [if_pos hwn] at hw
      injection hw with hw
      have hsw : sw = D.update ŝ (t, r, o) := (congrArg Prod.fst hw).symm
      rw [hsw]
      refine V.vc_inv hR' (C'.ver_inv vnew (D.update s (t, r, o))
        (ev ∪ {(t, r, o)}) ?_)
      rw [hver]
      simp
    · rw [if_neg hwn] at hw
      exact Ĉ.ver_inv w sw ew hw
  have hNd : ∀ r', updateRep Ĉ.N r (D.update ŝ (t, r, o)) r' = none ↔
      C'.N r' = none := by
    intro r'
    rw [hN]
    unfold updateRep
    by_cases hr : r' = r
    · rw [if_pos hr, if_pos hr]
      simp
    · rw [if_neg hr, if_neg hr]
      exact rel.N_none_iff r'
  have hcoh : ∀ r' w, C'.head r' = some w →
      ((fun w => if w = vnew
        then some (D.update ŝ (t, r, o), ev ∪ {(t, r, o)})
        else Ĉ.ver w) w).map Prod.fst
        = updateRep Ĉ.N r (D.update ŝ (t, r, o)) r' := by
    intro r' w hw
    simp only [hhead] at hw
    dsimp only
    unfold updateRep
    by_cases hr : r' = r
    · rw [if_pos hr] at hw ⊢
      injection hw with hw
      subst hw
      rw [if_pos rfl]
      rfl
    · rw [if_neg hr] at hw ⊢
      have hwne : w ≠ vnew := by
        intro h
        have := rel.heads_alloc r' w hw
        rw [h, h_vnew] at this
        cases this
      rw [if_neg hwne]
      have hĥ : Ĉ.head r' = some w := by rw [rel.head_eq]; exact hw
      exact (Ĉ.head_coherent r' w hĥ).1
  let Ĉ' : Configuration D :=
    restate C' (updateRep Ĉ.N r (D.update ŝ (t, r, o)))
      (fun w => if w = vnew
        then some (D.update ŝ (t, r, o), ev ∪ {(t, r, o)})
        else Ĉ.ver w) hE h0 hInvV hNd hcoh
  have hstep' : Step3 D Ĉ (.apply t r o) Ĉ' := by
    refine Step3.apply (v := v) (s := ŝ) (ev := ev) (vnew := vnew)
      ?_ hĉv ?_ ?_ (rel.ver_none h_vnew) h_rank _ rfl ?_ ?_ rfl ?_ ?_
    · rw [rel.head_eq]; exact h_head
    · intro e' he'
      rw [rel.events_eq] at he'
      exact h_fresh_t e' he'
    · intro w sw Ew hw
      obtain ⟨sw', hCw⟩ := rel.ver_some' hw
      exact h_fresh_store w sw' Ew hCw
    · show C'.L = updateRep Ĉ.L r (ev ∪ {(t, r, o)})
      rw [hL, rel.L_eq]
    · show C'.vis = fun a b => Ĉ.vis a b ∨ (ev a ∧ b = (t, r, o))
      rw [hvis, rel.vis_eq]
    · show C'.head = fun r' => if r' = r then some vnew else Ĉ.head r'
      rw [hhead, rel.head_eq]
    · show C'.parents = fun w => if w = vnew then [v] else Ĉ.parents w
      rw [hparents, rel.parents_eq]
  have hrel' : ConfigRelS V.R C' Ĉ' := by
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, hE, ?_⟩
    · intro r' w hw
      simp only [hhead] at hw
      rw [hver]
      dsimp only
      by_cases hr : r' = r
      · rw [if_pos hr] at hw
        injection hw with hw
        subst hw
        rw [if_pos rfl]
        rfl
      · rw [if_neg hr] at hw
        have hwne : w ≠ vnew := by
          intro h
          have := rel.heads_alloc r' w hw
          rw [h, h_vnew] at this
          cases this
        rw [if_neg hwne]
        exact rel.heads_alloc r' w hw
    · intro r' hw
      simp only [hhead] at hw
      by_cases hr : r' = r
      · rw [if_pos hr] at hw
        cases hw
      · rw [if_neg hr] at hw
        rw [hN]
        show updateRep C.N r (D.update s (t, r, o)) r' = none
        unfold updateRep
        rw [if_neg hr]
        exact rel.head_none r' hw
    · intro w sw Ew ŝw Êw hw hŵ
      rw [hver] at hw
      dsimp only at hw
      by_cases hwn : w = vnew
      · rw [if_pos hwn] at hw
        have hŵ' : (if w = vnew
            then some (D.update ŝ (t, r, o), ev ∪ {(t, r, o)})
            else Ĉ.ver w) = some (ŝw, Êw) := hŵ
        rw [if_pos hwn] at hŵ'
        injection hw with hw
        injection hŵ' with hŵ'
        have h1 : sw = D.update s (t, r, o) := (congrArg Prod.fst hw).symm
        have h2 : ŝw = D.update ŝ (t, r, o) := (congrArg Prod.fst hŵ').symm
        rw [h1, h2]
        exact hR'
      · rw [if_neg hwn] at hw
        have hŵ' : (if w = vnew
            then some (D.update ŝ (t, r, o), ev ∪ {(t, r, o)})
            else Ĉ.ver w) = some (ŝw, Êw) := hŵ
        rw [if_neg hwn] at hŵ'
        exact rel.ver_rel w sw Ew ŝw Êw hw hŵ'
  exact ⟨Ĉ', hstep', hrel', V.aux_apply rel aux
    (Step3.apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
      hN hL hvis hver hhead hparents)
    hstep' hrel'⟩

/-- Merge is matched verbatim: same heads, same LCA version, same fresh slot;
the merged payloads are related by **VC-S4** (`vc_merge`), which fires exactly
at the reachable-pair premises threaded here (erratum §9.2). -/
theorem stability_match_merge {C Ĉ C' : Configuration D} {r₁ r₂ : Replica}
    (rel : ConfigRelS V.R C Ĉ) (aux : V.Aux C Ĉ)
    (hstep : Step3 D C (.merge r₁ r₂) C') :
    ∃ Ĉ', Step3 D Ĉ (.merge r₁ r₂) Ĉ' ∧
      ConfigRelS V.R C' Ĉ' ∧ V.Aux C' Ĉ' := by
  cases hstep with
  | @merge _ _ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT h_head₁ h_head₂ h_ver₁
      h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂ C' hN hL hvis hver hhead
      hparents =>
  obtain ⟨ŝ₁, hĉ₁, hR₁⟩ := rel.ver_some h_ver₁
  obtain ⟨ŝ₂, hĉ₂, hR₂⟩ := rel.ver_some h_ver₂
  obtain ⟨ŝT, hĉT, hRT⟩ := rel.ver_some h_verT
  have hRm : V.R (D.mergeL sT s₁ s₂) (D.mergeL ŝT ŝ₁ ŝ₂) :=
    V.vc_merge rel aux h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT hĉ₁ hĉ₂ hĉT
  have h0ne : (0 : Version) ≠ vm := by
    intro h
    rw [← h] at h_vm
    rw [C.ver_init] at h_vm
    cases h_vm
  have hE : ∀ w,
      ((fun w => if w = vm then some (D.mergeL ŝT ŝ₁ ŝ₂, ev₁ ∪ ev₂)
        else Ĉ.ver w) w).map Prod.snd = (C'.ver w).map Prod.snd := by
    intro w
    rw [hver]
    dsimp only
    by_cases hw : w = vm
    · rw [if_pos hw, if_pos hw]
      rfl
    · rw [if_neg hw, if_neg hw]
      exact rel.ver_events w
  have h0 : (fun w => if w = vm then some (D.mergeL ŝT ŝ₁ ŝ₂, ev₁ ∪ ev₂)
      else Ĉ.ver w) 0 = some (D.init, ∅) := by
    dsimp only
    rw [if_neg h0ne]
    exact Ĉ.ver_init
  have hInvV : ∀ w sw ew, (fun w => if w = vm
      then some (D.mergeL ŝT ŝ₁ ŝ₂, ev₁ ∪ ev₂)
      else Ĉ.ver w) w = some (sw, ew) → D.Inv sw := by
    intro w sw ew hw
    dsimp only at hw
    by_cases hwn : w = vm
    · rw [if_pos hwn] at hw
      injection hw with hw
      have hsw : sw = D.mergeL ŝT ŝ₁ ŝ₂ := (congrArg Prod.fst hw).symm
      rw [hsw]
      refine V.vc_inv hRm (C'.ver_inv vm (D.mergeL sT s₁ s₂) (ev₁ ∪ ev₂) ?_)
      rw [hver]
      simp
    · rw [if_neg hwn] at hw
      exact Ĉ.ver_inv w sw ew hw
  have hNd : ∀ r', updateRep Ĉ.N r₁ (D.mergeL ŝT ŝ₁ ŝ₂) r' = none ↔
      C'.N r' = none := by
    intro r'
    rw [hN]
    unfold updateRep
    by_cases hr : r' = r₁
    · rw [if_pos hr, if_pos hr]
      simp
    · rw [if_neg hr, if_neg hr]
      exact rel.N_none_iff r'
  have hcoh : ∀ r' w, C'.head r' = some w →
      ((fun w => if w = vm then some (D.mergeL ŝT ŝ₁ ŝ₂, ev₁ ∪ ev₂)
        else Ĉ.ver w) w).map Prod.fst
        = updateRep Ĉ.N r₁ (D.mergeL ŝT ŝ₁ ŝ₂) r' := by
    intro r' w hw
    simp only [hhead] at hw
    dsimp only
    unfold updateRep
    by_cases hr : r' = r₁
    · rw [if_pos hr] at hw ⊢
      injection hw with hw
      subst hw
      rw [if_pos rfl]
      rfl
    · rw [if_neg hr] at hw ⊢
      have hwne : w ≠ vm := by
        intro h
        have := rel.heads_alloc r' w hw
        rw [h, h_vm] at this
        cases this
      rw [if_neg hwne]
      have hĥ : Ĉ.head r' = some w := by rw [rel.head_eq]; exact hw
      exact (Ĉ.head_coherent r' w hĥ).1
  let Ĉ' : Configuration D :=
    restate C' (updateRep Ĉ.N r₁ (D.mergeL ŝT ŝ₁ ŝ₂))
      (fun w => if w = vm then some (D.mergeL ŝT ŝ₁ ŝ₂, ev₁ ∪ ev₂)
        else Ĉ.ver w) hE h0 hInvV hNd hcoh
  have hstep' : Step3 D Ĉ (.merge r₁ r₂) Ĉ' := by
    refine Step3.merge (v₁ := v₁) (v₂ := v₂) (vT := vT) (vm := vm)
      ?_ ?_ hĉ₁ hĉ₂ ?_ hĉT (rel.ver_none h_vm) h_rank₁ h_rank₂ _
      rfl ?_ ?_ rfl ?_ ?_
    · rw [rel.head_eq]; exact h_head₁
    · rw [rel.head_eq]; exact h_head₂
    · rw [rel.parents_eq]; exact h_lca
    · show C'.L = updateRep Ĉ.L r₁ (ev₁ ∪ ev₂)
      rw [hL, rel.L_eq]
    · show C'.vis = Ĉ.vis
      rw [hvis, rel.vis_eq]
    · show C'.head = fun r' => if r' = r₁ then some vm else Ĉ.head r'
      rw [hhead, rel.head_eq]
    · show C'.parents = fun w => if w = vm then [v₁, v₂] else Ĉ.parents w
      rw [hparents, rel.parents_eq]
  have hrel' : ConfigRelS V.R C' Ĉ' := by
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, hE, ?_⟩
    · intro r' w hw
      simp only [hhead] at hw
      rw [hver]
      dsimp only
      by_cases hr : r' = r₁
      · rw [if_pos hr] at hw
        injection hw with hw
        subst hw
        rw [if_pos rfl]
        rfl
      · rw [if_neg hr] at hw
        have hwne : w ≠ vm := by
          intro h
          have := rel.heads_alloc r' w hw
          rw [h, h_vm] at this
          cases this
        rw [if_neg hwne]
        exact rel.heads_alloc r' w hw
    · intro r' hw
      simp only [hhead] at hw
      by_cases hr : r' = r₁
      · rw [if_pos hr] at hw
        cases hw
      · rw [if_neg hr] at hw
        rw [hN]
        show updateRep C.N r₁ (D.mergeL sT s₁ s₂) r' = none
        unfold updateRep
        rw [if_neg hr]
        exact rel.head_none r' hw
    · intro w sw Ew ŝw Êw hw hŵ
      rw [hver] at hw
      dsimp only at hw
      by_cases hwn : w = vm
      · rw [if_pos hwn] at hw
        have hŵ' : (if w = vm then some (D.mergeL ŝT ŝ₁ ŝ₂, ev₁ ∪ ev₂)
            else Ĉ.ver w) = some (ŝw, Êw) := hŵ
        rw [if_pos hwn] at hŵ'
        injection hw with hw
        injection hŵ' with hŵ'
        have h1 : sw = D.mergeL sT s₁ s₂ := (congrArg Prod.fst hw).symm
        have h2 : ŝw = D.mergeL ŝT ŝ₁ ŝ₂ := (congrArg Prod.fst hŵ').symm
        rw [h1, h2]
        exact hRm
      · rw [if_neg hwn] at hw
        have hŵ' : (if w = vm then some (D.mergeL ŝT ŝ₁ ŝ₂, ev₁ ∪ ev₂)
            else Ĉ.ver w) = some (ŝw, Êw) := hŵ
        rw [if_neg hwn] at hŵ'
        exact rel.ver_rel w sw Ew ŝw Êw hw hŵ'
  exact ⟨Ĉ', hstep', hrel', V.aux_merge rel aux
    (Step3.merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
      h_rank₂ C' hN hL hvis hver hhead hparents)
    hstep' hrel'⟩

/-- Query is matched by the compacted side's own readback; configurations are
unchanged on both sides. -/
theorem stability_match_query {C Ĉ : Configuration D} {r : Replica}
    {q : D.Query} {val : D.Value}
    (rel : ConfigRelS V.R C Ĉ) (_aux : V.Aux C Ĉ)
    (hstep : Step3 D C (.query r q val) C) :
    ∃ val', Step3 D Ĉ (.query r q val') Ĉ := by
  cases hstep with
  | @query _ _ _ s h_s h_val =>
    obtain ⟨ŝ, hNc, hR⟩ := rel.N_some h_s
    exact ⟨D.query ŝ q, Step3.query hNc rfl⟩

/-! ## §4 Compaction is a stuttering step -/

/-- `IsLCA` is reflexive: the merge rule accepts `r₁ = r₂`, which is what lets
the full side *stutter* through a genuine `Step3.merge r r` while the
compacted side installs the callback's result. -/
theorem isLCA_self (parents : Version → List Version) (v : Version) :
    IsLCA parents v v v :=
  ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, fun _ h₁ _ => h₁⟩

/-- The full-side stuttering target: a self-merge at `r`'s head `v`, allocated
at the fresh slot `vm`. The causal core is untouched — the merged event set is
`E ∪ E = E`, so `L` is even pointwise unchanged. -/
def selfMergeCfg (C : Configuration D) (r : Replica) (v vm : Version)
    (s : D.State) (E : Set (Op D.AppOp))
    (h_head : C.head r = some v) (h_ver : C.ver v = some (s, E))
    (h_vm : C.ver vm = none) (h_rank : v < vm)
    (hInvM : D.Inv (D.mergeL s s s))
    (hStore : StoreInv C.ver C.parents)
    (hHA : ∀ r' w, C.head r' = some w → (C.ver w).isSome) :
    Configuration D where
  N := updateRep C.N r (D.mergeL s s s)
  L := C.L
  vis := C.vis
  dom_eq := by
    intro r'
    have hL_r : C.L r = some E := by
      have h2 := (C.head_coherent r v h_head).2
      rw [h_ver] at h2
      exact h2.symm
    unfold updateRep
    by_cases hr : r' = r
    · rw [if_pos hr, hr, hL_r]
      simp
    · rw [if_neg hr]
      exact C.dom_eq r'
  vis_src := C.vis_src
  vis_tgt := C.vis_tgt
  vis_causal := C.vis_causal
  timestamps_distinct := C.timestamps_distinct
  causal_mono := C.causal_mono
  vis_total_same_replica := C.vis_total_same_replica
  ver := fun w => if w = vm then some (D.mergeL s s s, E) else C.ver w
  head := fun r' => if r' = r then some vm else C.head r'
  parents := fun w => if w = vm then [v, v] else C.parents w
  parents_lt := by
    intro w p hp
    by_cases hw : w = vm
    · rw [if_pos hw] at hp
      subst hw
      have hpv : p = v := by
        rcases List.mem_cons.mp hp with h | h
        · exact h
        · exact List.mem_singleton.mp h
      rw [hpv]
      exact h_rank
    · rw [if_neg hw] at hp
      exact C.parents_lt w p hp
  ver_init := by
    have h0ne : (0 : Version) ≠ vm := by
      intro h
      rw [← h] at h_vm
      rw [C.ver_init] at h_vm
      cases h_vm
    rw [if_neg h0ne]
    exact C.ver_init
  head_coherent := by
    intro r' w hw
    unfold updateRep
    by_cases hr : r' = r
    · rw [if_pos hr] at hw ⊢
      injection hw with hw
      subst hw
      rw [if_pos rfl]
      have hL_r : C.L r = some E := by
        have h2 := (C.head_coherent r v h_head).2
        rw [h_ver] at h2
        exact h2.symm
      rw [hr, hL_r]
      exact ⟨rfl, rfl⟩
    · rw [if_neg hr] at hw ⊢
      have hwne : w ≠ vm := by
        intro h
        have := hHA r' w hw
        rw [h, h_vm] at this
        cases this
      rw [if_neg hwne]
      exact C.head_coherent r' w hw
  ver_inv := by
    intro w sw ew hw
    by_cases hwn : w = vm
    · rw [if_pos hwn] at hw
      injection hw with hw
      have hsw : sw = D.mergeL s s s := (congrArg Prod.fst hw).symm
      rw [hsw]
      exact hInvM
    · rw [if_neg hwn] at hw
      exact C.ver_inv w sw ew hw
  lca_events := by
    intro w₁ w₂ wT t₁ F₁ t₂ F₂ tT FT hlca h1 h2 hT
    exact merged_store_lca_events
      (ver' := fun w => if w = vm then some (D.mergeL s s s, E) else C.ver w)
      (parents' := fun w => if w = vm then [v, v] else C.parents w)
      (sm := D.mergeL s s s)
      hStore h_vm h_ver h_ver
      (by simp)
      (fun w hw => by simp [hw])
      (by simp)
      (fun w hw => by simp [hw])
      hlca h1 h2 hT

/-- **The compaction diamond** (note §5): under the gate, the full side takes
the stuttering self-merge and the compacted side installs `compact ŝ` at the
same fresh slot; the lifted relation and the instance invariant survive. The
compacted side's move is the GC callback itself — deliberately *not* a `Step3`
step. -/
theorem stability_compact {C Ĉ : Configuration D} {r : Replica}
    {v vm : Version} {s ŝ : D.State} {E : Set (Op D.AppOp)}
    (rel : ConfigRelS V.R C Ĉ) (aux : V.Aux C Ĉ)
    (hgate : V.gate C Ĉ r v)
    (h_head : C.head r = some v) (h_ver : C.ver v = some (s, E))
    (hĉv : Ĉ.ver v = some (ŝ, E))
    (h_vm : C.ver vm = none) (h_rank : v < vm)
    (hInvM : D.Inv (D.mergeL s s s))
    (hStore : StoreInv C.ver C.parents) :
    ∃ C' Ĉ', Step3 D C (.merge r r) C' ∧
      C'.ver = (fun w => if w = vm then some (D.mergeL s s s, E ∪ E)
        else C.ver w) ∧
      Ĉ'.ver = (fun w => if w = vm then some (V.compact ŝ, E ∪ E)
        else Ĉ.ver w) ∧
      ConfigRelS V.R C' Ĉ' ∧ V.Aux C' Ĉ' := by
  have hL_r : C.L r = some E := by
    have h2 := (C.head_coherent r v h_head).2
    rw [h_ver] at h2
    exact h2.symm
  have h0ne : (0 : Version) ≠ vm := by
    intro h
    rw [← h] at h_vm
    rw [C.ver_init] at h_vm
    cases h_vm
  have hcpt : V.R (D.mergeL s s s) (V.compact ŝ) :=
    V.vc_entry rel aux hgate h_head h_ver hĉv
  let C' : Configuration D :=
    selfMergeCfg C r v vm s E h_head h_ver h_vm h_rank hInvM hStore
      rel.heads_alloc
  have hE : ∀ w,
      ((fun w => if w = vm then some (V.compact ŝ, E) else Ĉ.ver w) w).map
        Prod.snd = (C'.ver w).map Prod.snd := by
    intro w
    show _ = ((fun w => if w = vm then some (D.mergeL s s s, E)
      else C.ver w) w).map Prod.snd
    dsimp only
    by_cases hw : w = vm
    · rw [if_pos hw, if_pos hw]
      rfl
    · rw [if_neg hw, if_neg hw]
      exact rel.ver_events w
  have h0 : (fun w => if w = vm then some (V.compact ŝ, E) else Ĉ.ver w) 0
      = some (D.init, ∅) := by
    dsimp only
    rw [if_neg h0ne]
    exact Ĉ.ver_init
  have hInvV : ∀ w sw ew,
      (fun w => if w = vm then some (V.compact ŝ, E) else Ĉ.ver w) w
        = some (sw, ew) → D.Inv sw := by
    intro w sw ew hw
    dsimp only at hw
    by_cases hwn : w = vm
    · rw [if_pos hwn] at hw
      injection hw with hw
      have hsw : sw = V.compact ŝ := (congrArg Prod.fst hw).symm
      rw [hsw]
      exact V.vc_inv hcpt hInvM
    · rw [if_neg hwn] at hw
      exact Ĉ.ver_inv w sw ew hw
  have hNd : ∀ r', updateRep Ĉ.N r (V.compact ŝ) r' = none ↔
      C'.N r' = none := by
    intro r'
    show _ ↔ updateRep C.N r (D.mergeL s s s) r' = none
    unfold updateRep
    by_cases hr : r' = r
    · rw [if_pos hr, if_pos hr]
      simp
    · rw [if_neg hr, if_neg hr]
      exact rel.N_none_iff r'
  have hcoh : ∀ r' w, C'.head r' = some w →
      ((fun w => if w = vm then some (V.compact ŝ, E) else Ĉ.ver w) w).map
        Prod.fst = updateRep Ĉ.N r (V.compact ŝ) r' := by
    intro r' w hw
    have hw' : (if r' = r then some vm else C.head r') = some w := hw
    dsimp only
    unfold updateRep
    by_cases hr : r' = r
    · rw [if_pos hr] at hw' ⊢
      injection hw' with hw'
      subst hw'
      rw [if_pos rfl]
      rfl
    · rw [if_neg hr] at hw' ⊢
      have hwne : w ≠ vm := by
        intro h
        have := rel.heads_alloc r' w hw'
        rw [h, h_vm] at this
        cases this
      rw [if_neg hwne]
      have hĥ : Ĉ.head r' = some w := by rw [rel.head_eq]; exact hw'
      exact (Ĉ.head_coherent r' w hĥ).1
  let Ĉ' : Configuration D :=
    restate C' (updateRep Ĉ.N r (V.compact ŝ))
      (fun w => if w = vm then some (V.compact ŝ, E) else Ĉ.ver w)
      hE h0 hInvV hNd hcoh
  have hverC' : C'.ver = (fun w => if w = vm
      then some (D.mergeL s s s, E ∪ E) else C.ver w) := by
    funext w
    show (if w = vm then some (D.mergeL s s s, E) else C.ver w) = _
    by_cases hw : w = vm
    · rw [if_pos hw, if_pos hw, Set.union_self]
    · rw [if_neg hw, if_neg hw]
  have hverĈ' : Ĉ'.ver = (fun w => if w = vm
      then some (V.compact ŝ, E ∪ E) else Ĉ.ver w) := by
    funext w
    show (if w = vm then some (V.compact ŝ, E) else Ĉ.ver w) = _
    by_cases hw : w = vm
    · rw [if_pos hw, if_pos hw, Set.union_self]
    · rw [if_neg hw, if_neg hw]
  have hLeq : C'.L = updateRep C.L r (E ∪ E) := by
    show C.L = updateRep C.L r (E ∪ E)
    funext r'
    unfold updateRep
    by_cases hr : r' = r
    · rw [if_pos hr, hr, hL_r, Set.union_self]
    · rw [if_neg hr]
  have hstepC : Step3 D C (.merge r r) C' :=
    Step3.merge h_head h_head h_ver h_ver (isLCA_self C.parents v)
      h_ver h_vm h_rank h_rank C' rfl hLeq rfl hverC' rfl rfl
  have hrel' : ConfigRelS V.R C' Ĉ' := by
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, hE, ?_⟩
    · intro r' w hw
      have hw' : (if r' = r then some vm else C.head r') = some w := hw
      show ((fun w => if w = vm then some (D.mergeL s s s, E)
        else C.ver w) w).isSome
      dsimp only
      by_cases hr : r' = r
      · rw [if_pos hr] at hw'
        injection hw' with hw'
        subst hw'
        rw [if_pos rfl]
        rfl
      · rw [if_neg hr] at hw'
        have hwne : w ≠ vm := by
          intro h
          have := rel.heads_alloc r' w hw'
          rw [h, h_vm] at this
          cases this
        rw [if_neg hwne]
        exact rel.heads_alloc r' w hw'
    · intro r' hw
      have hw' : (if r' = r then some vm else C.head r') = none := hw
      show updateRep C.N r (D.mergeL s s s) r' = none
      unfold updateRep
      by_cases hr : r' = r
      · rw [if_pos hr] at hw'
        cases hw'
      · rw [if_neg hr] at hw' ⊢
        exact rel.head_none r' hw'
    · intro w sw Ew ŝw Êw hw hŵ
      have hw' : (if w = vm then some (D.mergeL s s s, E) else C.ver w)
          = some (sw, Ew) := hw
      have hŵ' : (if w = vm then some (V.compact ŝ, E) else Ĉ.ver w)
          = some (ŝw, Êw) := hŵ
      by_cases hwn : w = vm
      · rw [if_pos hwn] at hw' hŵ'
        injection hw' with hw'
        injection hŵ' with hŵ'
        have h1 : sw = D.mergeL s s s := (congrArg Prod.fst hw').symm
        have h2 : ŝw = V.compact ŝ := (congrArg Prod.fst hŵ').symm
        rw [h1, h2]
        exact hcpt
      · rw [if_neg hwn] at hw' hŵ'
        exact rel.ver_rel w sw Ew ŝw Êw hw' hŵ'
  have haux' : V.Aux C' Ĉ' :=
    V.aux_compact rel aux hgate h_head h_ver hĉv h_vm h_rank hstepC
      hverC' rfl hLeq rfl rfl rfl rfl rfl rfl rfl hverĈ' hrel'
  exact ⟨C', Ĉ', hstepC, hverC', hverĈ', hrel', haux'⟩

/-- **The umbrella matching lemma**: every full `Step3` step is matched by a
compacted step with a `LabelSim`-related label, preserving relation and
invariant. Creates are gated by the bundle's `canCreate` policy (scope note 2:
open membership). -/
theorem stability_match {C Ĉ C' : Configuration D} {ℓ : Label3 D}
    (rel : ConfigRelS V.R C Ĉ) (aux : V.Aux C Ĉ)
    (hcc : ∀ r, ℓ = .createReplica r → V.canCreate C Ĉ r)
    (hstep : Step3 D C ℓ C') :
    ∃ Ĉ' ℓ', Step3 D Ĉ ℓ' Ĉ' ∧ LabelSim D ℓ ℓ' ∧
      ConfigRelS V.R C' Ĉ' ∧ V.Aux C' Ĉ' := by
  cases ℓ with
  | createReplica r =>
    obtain ⟨Ĉ', h1, h2, h3⟩ :=
      stability_match_create V rel aux (hcc r rfl) hstep
    exact ⟨Ĉ', _, h1, LabelSim.create r, h2, h3⟩
  | apply t r o =>
    obtain ⟨Ĉ', h1, h2, h3⟩ := stability_match_apply V rel aux hstep
    exact ⟨Ĉ', _, h1, LabelSim.apply t r o, h2, h3⟩
  | merge r₁ r₂ =>
    obtain ⟨Ĉ', h1, h2, h3⟩ := stability_match_merge V rel aux hstep
    exact ⟨Ĉ', _, h1, LabelSim.merge r₁ r₂, h2, h3⟩
  | query r q val =>
    have hC' : C' = C := by cases hstep; rfl
    subst hC'
    obtain ⟨val', h1⟩ := stability_match_query V rel aux hstep
    exact ⟨Ĉ, _, h1, LabelSim.query r q val val', rel, aux⟩

/-! ## §5 The paired run and the metatheorem -/

/-- **The paired (twin) run**: the full run on the left, the compacted run on
the right. `step` records a matched `Step3` pair (produced by
`stability_match`); `compact` records a gated compaction — the full side's
stuttering self-merge (a genuine `Step3`, so the left projection of a
`StabReach` trace is an ordinary reachable run) against the compacted side's
callback move (produced by `stability_compact`). -/
inductive StabReach (V : StabilityVC D) (hInit : D.Inv D.init) :
    Configuration D → Configuration D → Prop where
  | init : StabReach V hInit (initConfig D hInit) (initConfig D hInit)
  | step {C Ĉ C' Ĉ' : Configuration D} {ℓ ℓ' : Label3 D} :
      StabReach V hInit C Ĉ → Step3 D C ℓ C' → Step3 D Ĉ ℓ' Ĉ' →
      LabelSim D ℓ ℓ' → ConfigRelS V.R C' Ĉ' → V.Aux C' Ĉ' →
      StabReach V hInit C' Ĉ'
  | compact {C Ĉ C' Ĉ' : Configuration D} {r : Replica} :
      StabReach V hInit C Ĉ → Step3 D C (.merge r r) C' →
      ConfigRelS V.R C' Ĉ' → V.Aux C' Ĉ' →
      StabReach V hInit C' Ĉ'

open LabeledTS in
/-- **The stability metatheorem** (note §5): along every paired run, the
lifted relation and the instance invariant hold, and the full side is an
ordinary `Step3`-reachable configuration (compactions project to stuttering
self-merges). With `stability_match` / `stability_compact` supplying the
inductive steps, every version of every reachable pair reads identically
(`stability_reads_equal`) and the compacted run inherits RA-linearizability
observationally (`stability_ra_inherited`). -/
theorem stability_simulation {V : StabilityVC D} {hInit : D.Inv D.init}
    {C Ĉ : Configuration D} (h : StabReach V hInit C Ĉ) :
    ConfigRelS V.R C Ĉ ∧ V.Aux C Ĉ ∧
      (labeledTS3 D).ReachableFrom (initConfig D hInit) C := by
  induction h with
  | init =>
    exact ⟨relS_init V.vc_refl hInit, V.aux_init hInit,
      Relation.ReflTransGen.refl⟩
  | @step C Ĉ C' Ĉ' ℓ ℓ' _ hstep hstep' hsim hrel haux ih =>
    exact ⟨hrel, haux, Relation.ReflTransGen.tail ih.2.2 ⟨ℓ, hstep⟩⟩
  | @compact C Ĉ C' Ĉ' r _ hstep hrel haux ih =>
    exact ⟨hrel, haux, Relation.ReflTransGen.tail ih.2.2 ⟨_, hstep⟩⟩

/-- **Reads equal at every version** (note §5): a version allocated on the
compacted side carries the full side's event set verbatim and reads
identically through the datatype's read interface. -/
theorem stability_reads_equal {V : StabilityVC D} {hInit : D.Inv D.init}
    {C Ĉ : Configuration D} (h : StabReach V hInit C Ĉ)
    {v : Version} {s ŝ : D.State} {E Ê : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E)) (hvc : Ĉ.ver v = some (ŝ, Ê)) :
    Ê = E ∧ V.obs ŝ = V.obs s := by
  obtain ⟨rel, -, -⟩ := stability_simulation h
  obtain ⟨ŝ', hĉ, hR⟩ := rel.ver_some hv
  rw [hvc] at hĉ
  injection hĉ with hĉ
  have h1 : ŝ = ŝ' := congrArg Prod.fst hĉ
  have h2 : Ê = E := congrArg Prod.snd hĉ
  subst h1
  exact ⟨h2, (V.vc_obs hR).symm⟩

/-- Replica readback agrees observationally (the query-label guarantee). -/
theorem reads_replica_equal {V : StabilityVC D} {hInit : D.Inv D.init}
    {C Ĉ : Configuration D} (h : StabReach V hInit C Ĉ)
    {r : Replica} {s ŝ : D.State}
    (hN : C.N r = some s) (hNc2 : Ĉ.N r = some ŝ) :
    V.obs ŝ = V.obs s := by
  obtain ⟨rel, -, -⟩ := stability_simulation h
  obtain ⟨ŝ', hĉ, hR⟩ := rel.N_some hN
  rw [hNc2] at hĉ
  injection hĉ with hĉ
  subst hĉ
  exact (V.vc_obs hR).symm

/-- **RA-linearizability inherited observationally** (note §5): every version
of the compacted run has a permutation witness of its (shared) event set,
respecting the linearization order of the compacted run's own causal core,
whose fold reads exactly as the compacted state — transported from the full
side's per-version RA-linearizability. -/
theorem stability_ra_inherited {V : StabilityVC D} {hInit : D.Inv D.init}
    {C Ĉ : Configuration D} (h : StabReach V hInit C Ĉ)
    (hRA : IsRALinearizable3 C) :
    ∀ (v : Version) (ŝ : D.State) (Ê : Set (Op D.AppOp)),
      Ĉ.ver v = some (ŝ, Ê) →
      ∃ π : List (Op D.AppOp),
        listPermOf π Ê ∧
        respects π (Sal.Emulation.lo (Configuration.core Ĉ)) ∧
        V.obs (applySeq D.toCRDTSig D.init π) = V.obs ŝ := by
  obtain ⟨rel, -, -⟩ := stability_simulation h
  intro v ŝ Ê hvc
  obtain ⟨s, hv⟩ := rel.ver_some' hvc
  obtain ⟨π, hperm, hresp, happ⟩ := hRA v s Ê hv
  have hlo : Sal.Emulation.lo (Configuration.core Ĉ)
      = Sal.Emulation.lo (Configuration.core C) := by
    funext e₁ e₂
    unfold Sal.Emulation.lo
    rw [core_vis, core_vis, rel.vis_eq]
  have hR : V.R s ŝ := rel.ver_rel v s Ê ŝ Ê hv hvc
  refine ⟨π, hperm, ?_, ?_⟩
  · rw [hlo]
    exact hresp
  · rw [happ]
    exact V.vc_obs hR

end Matching

/-! ## Axiom audit (framework layer) -/

#print axioms settledAtOn_of_evidence
#print axioms settledAt_of_evidence_reachableV
#print axioms evidenceCommit_of_witness_good
#print axioms stability_match
#print axioms stability_compact
#print axioms stability_simulation
#print axioms stability_reads_equal
#print axioms stability_ra_inherited

end Sal.ConditionedMRDTs
