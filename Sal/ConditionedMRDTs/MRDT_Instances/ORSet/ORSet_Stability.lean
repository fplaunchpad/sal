import Sal.ConditionedMRDTs.MRDT_Instances.ORSet.ORSet
import Sal.ConditionedMRDTs.Metatheory.Stability_VC

/-!
# OR-set drop-species compaction under `SettledAt`

An instance of the stability VC bundle: the production OR-set sheds redundant
add instances once the cut is settled.

* `orCompactC K nt`: the callback drops a tag `y ∈ K` exactly when its kept
  twin `nt y` is live. The state-dependent guard is required: a *static* drop
  set is unsound even under the settled gate (`SPOT.static_drop_unsound` pins
  it).
* `CutSpec`: what the cut data must satisfy: `K`-tags are staked by `S`-adds
  and each has a strictly newer `S`-add twin outside `K`.
* the σ-toolkit (`orAlive_add` … `orSettled_cover`): the five canonical-state
  facts the merge discharge runs on, versions of the OR-set σ-lemmas; the
  settled-discriminator lemma `orSettled_cover` is where `SettledAtOn` does
  its work (a cover of the newer twin minted outside a settled event set
  covers the older twin too).
* the SPOT layer: the countermodel (naive gate: reads diverge), the settled
  refusal (rem absorbed ⟹ nothing redundant), and the mixed-merge VC-S4 case,
  all hand-derived against `whiteboard/litmus/stability_vc_check.py` (tags
  there are `(elem, stamp)`, here `(stamp, elem)`).
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1 The cut data and the callback -/

/-- The OR-set read interface: which elements are present. -/
def orRead (s : ORSet.State) : ℕ → Prop :=
  fun e => ∃ ts, s (ts, e) = true

/-- **The drop-species callback**: drop `y ∈ K` exactly when its kept twin
`nt y` is currently live. The twin-liveness guard is load-bearing: dropping on
`K` alone loses the element when the kept twin has already been removed
(`SPOT.static_drop_unsound`). -/
def orCompactC (K : ℕ × ℕ → Bool) (nt : ℕ × ℕ → ℕ × ℕ)
    (s : ORSet.State) : ORSet.State :=
  fun y => s y && !(K y && s (nt y))

/-- **The cut data contract**: `K`-tags are staked by adds of the cut `S`,
and each has a strictly newer same-element `S`-add twin outside `K`. The
"newest" twin is not needed for soundness: any live kept witness preserves the
read. -/
structure CutSpec (S : Set (Op ORSetOp)) (K : ℕ × ℕ → Bool)
    (nt : ℕ × ℕ → ℕ × ℕ) : Prop where
  addK : ∀ y, K y = true → ∃ rd, (y.1, rd, ORSetOp.add y.2) ∈ S
  addNt : ∀ y, K y = true → ∃ rd, ((nt y).1, rd, ORSetOp.add y.2) ∈ S
  ntElem : ∀ y, K y = true → (nt y).2 = y.2
  ntNewer : ∀ y, K y = true → y.1 < (nt y).1
  ntK : ∀ y, K y = true → K (nt y) = false

/-- A non-`true` `Bool` is `false`. -/
private theorem bfalse {b : Bool} (h : ¬ b = true) : b = false := by
  cases hb : b
  · rfl
  · exact absurd hb h

section StateLemmas

variable {S : Set (Op ORSetOp)} {K : ℕ × ℕ → Bool} {nt : ℕ × ℕ → ℕ × ℕ}

/-- Off `K`, the callback is transparent. -/
theorem orCompactC_off (s : ORSet.State) {y : ℕ × ℕ} (h : K y = false) :
    orCompactC K nt s y = s y := by
  unfold orCompactC
  rw [h]
  cases s y <;> rfl

/-- The callback is idempotent. -/
theorem orCompactC_idem (hcut : CutSpec S K nt) (s : ORSet.State) :
    orCompactC K nt (orCompactC K nt s) = orCompactC K nt s := by
  funext y
  by_cases hK : K y = true
  · have hnt : K (nt y) = false := hcut.ntK y hK
    unfold orCompactC
    rw [hK, hnt]
    cases s y <;> cases s (nt y) <;> rfl
  · rw [orCompactC_off _ (bfalse hK), orCompactC_off _ (bfalse hK)]

/-- **VC-S2, state-locally**: the callback preserves the read — a dropped tag
always has its live kept twin witnessing the element. -/
theorem orRead_compactC (hcut : CutSpec S K nt) (s : ORSet.State) :
    orRead (orCompactC K nt s) = orRead s := by
  funext e
  refine propext ⟨?_, ?_⟩
  · rintro ⟨ts, h⟩
    refine ⟨ts, ?_⟩
    unfold orCompactC at h
    exact (Bool.and_eq_true_iff.mp h).1
  · rintro ⟨ts, h⟩
    by_cases hK : K (ts, e) = true
    · by_cases htw : s (nt (ts, e)) = true
      · -- the kept twin witnesses `e`
        have helem : (nt (ts, e)).2 = e := hcut.ntElem (ts, e) hK
        have hKnt : K (nt (ts, e)) = false := hcut.ntK (ts, e) hK
        rcases hnteq : nt (ts, e) with ⟨a, b⟩
        rw [hnteq] at helem htw hKnt
        refine ⟨a, ?_⟩
        have hb : b = e := helem
        rw [← hb]
        rw [orCompactC_off _ hKnt]
        exact htw
      · refine ⟨ts, ?_⟩
        unfold orCompactC
        rw [h, hK, bfalse htw]
        rfl
    · refine ⟨ts, ?_⟩
      rw [orCompactC_off _ (bfalse hK)]
      exact h
end StateLemmas

/-- The OR-set ternary merge is idempotent on the diagonal (the stuttering
self-merge payload collapses). -/
theorem orMergeL_self (s : ORSet.State) : ORSet.mergeL s s s = s := by
  funext y
  show orMergeL s s s y = s y
  unfold orMergeL
  cases s y <;> rfl

section UpdateLemmas

variable {S : Set (Op ORSetOp)} {K : ℕ × ℕ → Bool} {nt : ℕ × ℕ → ℕ × ℕ}

/-- **VC-S3, rem case**: removal (whole-element filter) commutes with the
callback — twins die together under a filter. -/
theorem orCompactC_rem (hcut : CutSpec S K nt) (s : ORSet.State)
    (t r e : ℕ) :
    ORSet.update (orCompactC K nt s) (t, r, ORSetOp.rem e)
      = orCompactC K nt (ORSet.update s (t, r, ORSetOp.rem e)) := by
  funext y
  show (orCompactC K nt s y && !(decide (y.2 = e)))
      = orCompactC K nt (fun p => s p && !(decide (p.2 = e))) y
  by_cases hK : K y = true
  · have helem : (nt y).2 = y.2 := hcut.ntElem y hK
    unfold orCompactC
    rw [hK]
    dsimp only
    rw [helem]
    cases s y <;> cases s (nt y) <;> cases hde : decide (y.2 = e) <;> rfl
  · have hK' : K y = false := bfalse hK
    rw [orCompactC_off _ hK']
    show _ = orCompactC K nt (fun p => s p && !(decide (p.2 = e))) y
    rw [orCompactC_off _ hK']

/-- **VC-S3, add case**: a fresh add commutes with the callback provided its
stamp is fresh against the cut's tags and twins. -/
theorem orCompactC_add (_hcut : CutSpec S K nt) (s : ORSet.State)
    (t r e : ℕ)
    (hfr : ∀ y : ℕ × ℕ, K y = true → y.1 ≠ t ∧ (nt y).1 ≠ t) :
    ORSet.update (orCompactC K nt s) (t, r, ORSetOp.add e)
      = orCompactC K nt (ORSet.update s (t, r, ORSetOp.add e)) := by
  funext y
  show (orCompactC K nt s y || decide (y = (t, e)))
      = orCompactC K nt (fun p => s p || decide (p = (t, e))) y
  by_cases hK : K y = true
  · have hy : decide (y = (t, e)) = false := by
      refine decide_eq_false ?_
      intro h
      exact (hfr y hK).1 (by rw [h])
    have hnt : decide (nt y = (t, e)) = false := by
      refine decide_eq_false ?_
      intro h
      exact (hfr y hK).2 (by rw [h])
    unfold orCompactC
    rw [hK]
    dsimp only
    rw [hy, hnt]
    cases s y <;> cases s (nt y) <;> rfl
  · have hK' : K y = false := bfalse hK
    rw [orCompactC_off _ hK']
    show _ = orCompactC K nt (fun p => s p || decide (p = (t, e))) y
    rw [orCompactC_off _ hK']

end UpdateLemmas

/-! ## §2 The σ-toolkit: canonical-state facts at versions -/

section Toolkit

variable {C : Configuration ORSet}

/-- A live tag's add is in the version's event set. -/
theorem orAlive_add (hGood : GoodConfig3 C) {v : Version} {s : ORSet.State}
    {E : Set (Op ORSetOp)} {y : ℕ × ℕ}
    (hv : C.ver v = some (s, E)) (hy : s y = true) :
    ∃ rd, (y.1, rd, ORSetOp.add y.2) ∈ E := by
  obtain ⟨o, hoF, hop, hots⟩ :=
    ORSet_canonical_bound (hGood.canonical v s E hv) hy
  obtain ⟨ts, rd, op⟩ := o
  have hop' : op = ORSetOp.add y.2 := hop
  have hots' : ts = y.1 := hots
  subst hop'
  subst hots'
  exact ⟨rd, hoF⟩

/-- A covered tag (a same-element rem that saw its add, both in the version's
event set) is dead. -/
theorem orCover_dead (hGood : GoodConfig3 C) {v : Version} {s : ORSet.State}
    {E : Set (Op ORSetOp)} {y : ℕ × ℕ} {rda tsr rdr : ℕ}
    (hv : C.ver v = some (s, E))
    (hadd : (y.1, rda, ORSetOp.add y.2) ∈ E)
    (hrem : (tsr, rdr, ORSetOp.rem y.2) ∈ E)
    (hvis : C.vis (y.1, rda, ORSetOp.add y.2) (tsr, rdr, ORSetOp.rem y.2)) :
    s y = false := by
  cases hsy : s y with
  | false => rfl
  | true =>
    exact (ORSet_live_no_later_rem (hGood.ver_events_sub v s E hv)
      (hGood.canonical v s E hv) hsy hadd rfl hrem hvis).elim

/-- A dead tag whose add the version knows has a cover in the version. -/
theorem orDead_cover (hGood : GoodConfig3 C) {v : Version} {s : ORSet.State}
    {E : Set (Op ORSetOp)} {y : ℕ × ℕ} {rda : ℕ}
    (hv : C.ver v = some (s, E))
    (hadd : (y.1, rda, ORSetOp.add y.2) ∈ E)
    (hdead : s y = false) :
    ∃ tsr rdr, (tsr, rdr, ORSetOp.rem y.2) ∈ E ∧
      C.vis (y.1, rda, ORSetOp.add y.2) (tsr, rdr, ORSetOp.rem y.2) := by
  by_contra h
  push_neg at h
  have hlive : s y = true := by
    refine ORSet_no_later_kill_live (hGood.ver_events_sub v s E hv)
      (hGood.canonical v s E hv) hadd ?_
    rintro ⟨ts', rd', op'⟩ hrr hop
    have hop' : op' = ORSetOp.rem y.2 := hop
    subst hop'
    exact h ts' rd' hrr
  rw [hlive] at hdead
  cases hdead

/-- Death persists to any version knowing more events. -/
theorem orDead_mono (hGood : GoodConfig3 C) {u w : Version}
    {su sw : ORSet.State} {Eu Ew : Set (Op ORSetOp)} {y : ℕ × ℕ} {rda : ℕ}
    (hu : C.ver u = some (su, Eu)) (hw : C.ver w = some (sw, Ew))
    (hadd : (y.1, rda, ORSetOp.add y.2) ∈ Eu) (hsub : Eu ⊆ Ew)
    (hdead : su y = false) : sw y = false := by
  obtain ⟨tsr, rdr, hrem, hvis⟩ := orDead_cover hGood hu hadd hdead
  exact orCover_dead hGood hw (hsub hadd) (hsub hrem) hvis

/-- Liveness transfers up to any version knowing fewer events
(contrapositive of `orDead_mono`). -/
theorem orLive_mono (hGood : GoodConfig3 C) {u w : Version}
    {su sw : ORSet.State} {Eu Ew : Set (Op ORSetOp)} {y : ℕ × ℕ} {rda : ℕ}
    (hu : C.ver u = some (su, Eu)) (hw : C.ver w = some (sw, Ew))
    (hadd : (y.1, rda, ORSetOp.add y.2) ∈ Eu) (hsub : Eu ⊆ Ew)
    (hlive : sw y = true) : su y = true := by
  by_contra h
  have := orDead_mono hGood hu hw hadd hsub (bfalse h)
  rw [this] at hlive
  cases hlive

/-- **The settled discriminator** (the note §2 argument, localized): a
same-element rem *outside* a settled event set that covers the newer twin
covers the older one too — the discriminating remove cannot exist. -/
theorem orSettled_cover {E S : Set (Op ORSetOp)}
    (hset : SettledAtOn C E S)
    {y n : ℕ × ℕ} {rdy rdn : ℕ}
    (hyS : (y.1, rdy, ORSetOp.add y.2) ∈ S)
    (hlt : y.1 < n.1)
    {tsr rdr : ℕ}
    (hrem_ev : (tsr, rdr, ORSetOp.rem y.2) ∈ C.events)
    (hrem_not : (tsr, rdr, ORSetOp.rem y.2) ∉ E)
    (hvisn : C.vis (n.1, rdn, ORSetOp.add y.2) (tsr, rdr, ORSetOp.rem y.2)) :
    C.vis (y.1, rdy, ORSetOp.add y.2) (tsr, rdr, ORSetOp.rem y.2) := by
  by_contra hnv
  have hn_ts : n.1 < tsr := C.causal_mono hvisn
  have hnv2 : ¬ C.vis (tsr, rdr, ORSetOp.rem y.2)
      (y.1, rdy, ORSetOp.add y.2) := by
    intro h
    have hlt2 : tsr < y.1 := C.causal_mono h
    have : y.1 < y.1 :=
      Nat.lt_trans (Nat.lt_trans hlt hn_ts) hlt2
    exact absurd this (Nat.lt_irrefl _)
  have hne : (tsr, rdr, ORSetOp.rem y.2) ≠ (y.1, rdy, ORSetOp.add y.2) := by
    intro h
    have := congrArg (fun o : Op ORSetOp => o.2.2) h
    exact ORSetOp.noConfusion this
  exact hrem_not (hset.conc _ hrem_ev ⟨_, hyS, hne, hnv2, hnv⟩)

/-- Timestamp uniqueness at the ternary configuration. -/
theorem orTs_unique {a b : Op ORSetOp}
    (ha : a ∈ C.events) (hb : b ∈ C.events) (h : a.1 = b.1) : a = b :=
  (Configuration.core C).ts_unique ha hb h

end Toolkit

/-! ## §2b Derived facts: freshness, epoch coherence, the discriminator -/

section Derived

variable {C : Configuration ORSet}

/-- A store-fresh timestamp is fresh against the cut's tags and twins. -/
theorem orK_fresh (hGood : GoodConfig3 C)
    {S : Set (Op ORSetOp)} {K : ℕ × ℕ → Bool} {nt : ℕ × ℕ → ℕ × ℕ}
    (hcut : CutSpec S K nt)
    {v : Version} {s : ORSet.State} {E : Set (Op ORSetOp)}
    (hv : C.ver v = some (s, E)) (hS : S ⊆ E)
    {t : ℕ} (h_fresh : ∀ e' ∈ C.events, Op.time e' ≠ t) :
    ∀ y : ℕ × ℕ, K y = true → y.1 ≠ t ∧ (nt y).1 ≠ t := by
  intro y hK
  obtain ⟨rdy, hyS⟩ := hcut.addK y hK
  obtain ⟨rdn, hnS⟩ := hcut.addNt y hK
  exact ⟨h_fresh _ (hGood.ver_events_sub v s E hv _ (hS hyS)),
    h_fresh _ (hGood.ver_events_sub v s E hv _ (hS hnS))⟩

/-- A live tag pins the *cut's* add into the version's event set (timestamp
uniqueness identifies the version's add with the cut's). -/
theorem orAliveS (hGood : GoodConfig3 C) {v : Version} {s : ORSet.State}
    {E : Set (Op ORSetOp)} {y : ℕ × ℕ} {rd : ℕ}
    (hv : C.ver v = some (s, E)) (hy : s y = true)
    (hSop : (y.1, rd, ORSetOp.add y.2) ∈ C.events) :
    (y.1, rd, ORSetOp.add y.2) ∈ E := by
  obtain ⟨rd', hmem⟩ := orAlive_add hGood hv hy
  have heq : ((y.1, rd', ORSetOp.add y.2) : Op ORSetOp)
      = (y.1, rd, ORSetOp.add y.2) :=
    orTs_unique (hGood.ver_events_sub v s E hv _ hmem) hSop rfl
  rw [← heq]
  exact hmem

/-- **The discriminator chain** (note §2, mechanized): the kept twin `n` is
live at a *settled* version `u` but dead at `w` (which knows `n`'s add). Its
killer must have seen the older twin `y` as well — so `y` is dead at `w` too,
and `y`'s add is in `E(w)`. This is the single lemma behind every mixed-merge
exclusion. -/
theorem orDiscriminator (hGood : GoodConfig3 C)
    {S : Set (Op ORSetOp)} {u w : Version} {su sw : ORSet.State}
    {Eu Ew : Set (Op ORSetOp)} {y n : ℕ × ℕ} {rdy rdn : ℕ}
    (hu : C.ver u = some (su, Eu)) (hw : C.ver w = some (sw, Ew))
    (hset : SettledAtOn C Eu S)
    (hyS : (y.1, rdy, ORSetOp.add y.2) ∈ S)
    (helem : n.2 = y.2) (hlt : y.1 < n.1)
    (hnu : (n.1, rdn, ORSetOp.add y.2) ∈ Eu)
    (hnw : (n.1, rdn, ORSetOp.add y.2) ∈ Ew)
    (hn_dead : sw n = false)
    (hn_live_u : su n = true) :
    sw y = false ∧ (y.1, rdy, ORSetOp.add y.2) ∈ Ew := by
  have hnw' : (n.1, rdn, ORSetOp.add n.2) ∈ Ew := by rw [helem]; exact hnw
  have hnu' : (n.1, rdn, ORSetOp.add n.2) ∈ Eu := by rw [helem]; exact hnu
  obtain ⟨tsr, rdr, hrem, hvisn⟩ := orDead_cover hGood hw hnw' hn_dead
  -- the killer is outside the settled version (else the twin were dead there)
  have hrem_not : (tsr, rdr, ORSetOp.rem n.2) ∉ Eu := by
    intro hin
    have := orCover_dead hGood hu hnu' hin hvisn
    rw [this] at hn_live_u
    cases hn_live_u
  -- settledness: it saw the older twin too
  have hvisy : C.vis (y.1, rdy, ORSetOp.add y.2)
      (tsr, rdr, ORSetOp.rem y.2) := by
    refine orSettled_cover (n := n) (rdn := rdn) hset hyS hlt
      (hGood.ver_events_sub w sw Ew hw _ (helem ▸ hrem)) (helem ▸ hrem_not) ?_
    have := hvisn
    rw [helem] at this
    exact this
  -- so the older twin's add — and its death — land in `E(w)`
  have hyw : (y.1, rdy, ORSetOp.add y.2) ∈ Ew :=
    hGood.ver_causal w sw Ew hw _ _ hvisy (helem ▸ hrem)
  exact ⟨orCover_dead hGood hw hyw (helem ▸ hrem) hvisy, hyw⟩

end Derived

/-! ## §2c VC-S4: the merge bodies

Pointwise, at a droppable tag `y` with kept twin `n`, the merge of hatted
arguments equals the hat of the merged raw arguments. Each body handles one
form profile of `(LCA, branch₁, branch₂)`; the semantic exclusions all route
through `orDiscriminator`. -/

section MergeBodies

variable {C : Configuration ORSet} {S : Set (Op ORSetOp)}
  {K : ℕ × ℕ → Bool} {nt : ℕ × ℕ → ℕ × ℕ}
  {v₁ v₂ vT : Version} {s₁ s₂ sT : ORSet.State}
  {E₁ E₂ ET : Set (Op ORSetOp)}

/-- Body 1 (the note §6 "interesting case"): compacted branch `1` against a
raw LCA payload and a raw sibling. -/
private theorem orMergeBody1 (hGood : GoodConfig3 C) (hcut : CutSpec S K nt)
    (h_ver₁ : C.ver v₁ = some (s₁, E₁)) (h_ver₂ : C.ver v₂ = some (s₂, E₂))
    (h_verT : C.ver vT = some (sT, ET))
    (hET : ET = E₁ ∩ E₂)
    (hS₁ : S ⊆ E₁) (hset₁ : SettledAtOn C E₁ S) :
    orMergeL sT (orCompactC K nt s₁) s₂
      = orCompactC K nt (orMergeL sT s₁ s₂) := by
  funext y
  by_cases hK : K y = true
  swap
  · have hK' := bfalse hK
    rw [orCompactC_off _ hK']
    show orMergeL sT (orCompactC K nt s₁) s₂ y
      = orMergeL sT s₁ s₂ y
    unfold orMergeL
    rw [orCompactC_off _ hK']
  -- the droppable tag: assemble the cut data
  obtain ⟨rdy, hyS⟩ := hcut.addK y hK
  obtain ⟨rdn, hnS⟩ := hcut.addNt y hK
  have helem : (nt y).2 = y.2 := hcut.ntElem y hK
  have hlt : y.1 < (nt y).1 := hcut.ntNewer y hK
  have hKn : K (nt y) = false := hcut.ntK y hK
  have hyE₁ : (y.1, rdy, ORSetOp.add y.2) ∈ E₁ := hS₁ hyS
  have hnE₁ : ((nt y).1, rdn, ORSetOp.add y.2) ∈ E₁ := hS₁ hnS
  have hyEv : (y.1, rdy, ORSetOp.add y.2) ∈ C.events :=
    hGood.ver_events_sub v₁ s₁ E₁ h_ver₁ _ hyE₁
  have hnEv : ((nt y).1, rdn, ORSetOp.add y.2) ∈ C.events :=
    hGood.ver_events_sub v₁ s₁ E₁ h_ver₁ _ hnE₁
  have hnEv' : ((nt y).1, rdn, ORSetOp.add (nt y).2) ∈ C.events := by
    rw [helem]; exact hnEv
  -- X1: alive in the raw sibling forces alive at the LCA
  have hX1 : s₂ y = true → sT y = true := by
    intro hbY
    have hyE₂ : (y.1, rdy, ORSetOp.add y.2) ∈ E₂ :=
      orAliveS hGood h_ver₂ hbY hyEv
    have hyET : (y.1, rdy, ORSetOp.add y.2) ∈ ET := by
      rw [hET]; exact ⟨hyE₁, hyE₂⟩
    by_contra h
    have := orDead_mono hGood h_verT h_ver₂ hyET
      (by rw [hET]; exact Set.inter_subset_right) (bfalse h)
    rw [this] at hbY
    cases hbY
  -- X2: the twin alive in the raw sibling forces it alive at the LCA
  have hX2 : s₂ (nt y) = true → sT (nt y) = true := by
    intro hbN
    have hnE₂' : ((nt y).1, rdn, ORSetOp.add (nt y).2) ∈ E₂ :=
      orAliveS hGood h_ver₂ hbN hnEv'
    have hnET : ((nt y).1, rdn, ORSetOp.add (nt y).2) ∈ ET := by
      rw [hET]; exact ⟨by rw [helem]; exact hnE₁, hnE₂'⟩
    by_contra h
    have := orDead_mono hGood h_verT h_ver₂ hnET
      (by rw [hET]; exact Set.inter_subset_right) (bfalse h)
    rw [this] at hbN
    cases hbN
  -- X3: twin alive at the compacted branch, dead in the sibling, tag alive
  -- in the sibling, twin alive at the LCA: the discriminator refutes it
  have hX3 : s₁ (nt y) = true → s₂ (nt y) = false → s₂ y = true →
      sT (nt y) = true → False := by
    intro haN hbN hbY hlN
    have hnET : ((nt y).1, rdn, ORSetOp.add (nt y).2) ∈ ET :=
      orAliveS hGood h_verT hlN hnEv'
    have hnE₂ : ((nt y).1, rdn, ORSetOp.add y.2) ∈ E₂ := by
      have := hnET
      rw [hET] at this
      have h2 := this.2
      rw [helem] at h2
      exact h2
    obtain ⟨hdead, -⟩ := orDiscriminator hGood h_ver₁ h_ver₂ hset₁ hyS helem
      hlt hnE₁ hnE₂ hbN haN
    rw [hdead] at hbY
    cases hbY
  -- X4: as X3 but the tag alive at the compacted branch and dead at the LCA
  have hX4 : s₁ (nt y) = true → s₂ (nt y) = false → s₁ y = true →
      sT y = false → sT (nt y) = true → False := by
    intro haN hbN haY hlY hlN
    have hnET : ((nt y).1, rdn, ORSetOp.add (nt y).2) ∈ ET :=
      orAliveS hGood h_verT hlN hnEv'
    have hnE₂ : ((nt y).1, rdn, ORSetOp.add y.2) ∈ E₂ := by
      have := hnET
      rw [hET] at this
      have h2 := this.2
      rw [helem] at h2
      exact h2
    obtain ⟨-, hyE₂⟩ := orDiscriminator hGood h_ver₁ h_ver₂ hset₁ hyS helem
      hlt hnE₁ hnE₂ hbN haN
    have hyET : (y.1, rdy, ORSetOp.add y.2) ∈ ET := by
      rw [hET]; exact ⟨hyE₁, hyE₂⟩
    have := orDead_mono hGood h_verT h_ver₁ hyET
      (by rw [hET]; exact Set.inter_subset_left) hlY
    rw [this] at haY
    cases haY
  -- the Boolean endgame
  show orMergeL sT (orCompactC K nt s₁) s₂ y
    = (orMergeL sT s₁ s₂ y && !(K y && orMergeL sT s₁ s₂ (nt y)))
  unfold orMergeL orCompactC
  rw [hK]
  cases hlY : sT y <;> cases hlN : sT (nt y) <;> cases haY : s₁ y <;>
    cases haN : s₁ (nt y) <;> cases hbY : s₂ y <;> cases hbN : s₂ (nt y) <;>
    simp_all

/-- Body 12: both branches compacted, raw LCA payload (staggered replicas
merging across a pre-compaction LCA). -/
private theorem orMergeBody12 (hGood : GoodConfig3 C) (hcut : CutSpec S K nt)
    (h_ver₁ : C.ver v₁ = some (s₁, E₁)) (h_ver₂ : C.ver v₂ = some (s₂, E₂))
    (h_verT : C.ver vT = some (sT, ET))
    (hET : ET = E₁ ∩ E₂)
    (hS₁ : S ⊆ E₁) (hset₁ : SettledAtOn C E₁ S)
    (hS₂ : S ⊆ E₂) (hset₂ : SettledAtOn C E₂ S) :
    orMergeL sT (orCompactC K nt s₁) (orCompactC K nt s₂)
      = orCompactC K nt (orMergeL sT s₁ s₂) := by
  funext y
  by_cases hK : K y = true
  swap
  · have hK' := bfalse hK
    rw [orCompactC_off _ hK']
    show orMergeL sT (orCompactC K nt s₁) (orCompactC K nt s₂) y
      = orMergeL sT s₁ s₂ y
    unfold orMergeL
    rw [orCompactC_off _ hK', orCompactC_off _ hK']
  obtain ⟨rdy, hyS⟩ := hcut.addK y hK
  obtain ⟨rdn, hnS⟩ := hcut.addNt y hK
  have helem : (nt y).2 = y.2 := hcut.ntElem y hK
  have hlt : y.1 < (nt y).1 := hcut.ntNewer y hK
  have hyET : (y.1, rdy, ORSetOp.add y.2) ∈ ET := by
    rw [hET]; exact ⟨hS₁ hyS, hS₂ hyS⟩
  have hsub₁ : ET ⊆ E₁ := by rw [hET]; exact Set.inter_subset_left
  have hsub₂ : ET ⊆ E₂ := by rw [hET]; exact Set.inter_subset_right
  have hnET' : ((nt y).1, rdn, ORSetOp.add (nt y).2) ∈ ET := by
    rw [helem, hET]; exact ⟨hS₁ hnS, hS₂ hnS⟩
  have hX1 : s₂ y = true → sT y = true := by
    intro hbY
    by_contra h
    have := orDead_mono hGood h_verT h_ver₂ hyET hsub₂ (bfalse h)
    rw [this] at hbY
    cases hbY
  have hX1a : s₁ y = true → sT y = true := by
    intro haY
    by_contra h
    have := orDead_mono hGood h_verT h_ver₁ hyET hsub₁ (bfalse h)
    rw [this] at haY
    cases haY
  have hX2 : s₂ (nt y) = true → sT (nt y) = true := by
    intro hbN
    by_contra h
    have := orDead_mono hGood h_verT h_ver₂ hnET' hsub₂ (bfalse h)
    rw [this] at hbN
    cases hbN
  have hX2a : s₁ (nt y) = true → sT (nt y) = true := by
    intro haN
    by_contra h
    have := orDead_mono hGood h_verT h_ver₁ hnET' hsub₁ (bfalse h)
    rw [this] at haN
    cases haN
  have hX5 : s₁ (nt y) = true → s₂ (nt y) = false → s₂ y = true → False := by
    intro haN hbN hbY
    obtain ⟨hdead, -⟩ := orDiscriminator hGood h_ver₁ h_ver₂ hset₁ hyS helem
      hlt (hS₁ hnS) (hS₂ hnS) hbN haN
    rw [hdead] at hbY
    cases hbY
  have hX6 : s₂ (nt y) = true → s₁ (nt y) = false → s₁ y = true → False := by
    intro hbN haN haY
    obtain ⟨hdead, -⟩ := orDiscriminator hGood h_ver₂ h_ver₁ hset₂ hyS helem
      hlt (hS₂ hnS) (hS₁ hnS) haN hbN
    rw [hdead] at haY
    cases haY
  show orMergeL sT (orCompactC K nt s₁) (orCompactC K nt s₂) y
    = (orMergeL sT s₁ s₂ y && !(K y && orMergeL sT s₁ s₂ (nt y)))
  unfold orMergeL orCompactC
  rw [hK]
  cases hlY : sT y <;> cases hlN : sT (nt y) <;> cases haY : s₁ y <;>
    cases haN : s₁ (nt y) <;> cases hbY : s₂ y <;> cases hbN : s₂ (nt y) <;>
    simp_all

/-- Body T: everything below a settled, compacted LCA. -/
private theorem orMergeBodyT (hGood : GoodConfig3 C) (hcut : CutSpec S K nt)
    (h_ver₁ : C.ver v₁ = some (s₁, E₁)) (h_ver₂ : C.ver v₂ = some (s₂, E₂))
    (h_verT : C.ver vT = some (sT, ET))
    (hET : ET = E₁ ∩ E₂)
    (hST : S ⊆ ET) (hsetT : SettledAtOn C ET S) :
    orMergeL (orCompactC K nt sT) (orCompactC K nt s₁) (orCompactC K nt s₂)
      = orCompactC K nt (orMergeL sT s₁ s₂) := by
  funext y
  by_cases hK : K y = true
  swap
  · have hK' := bfalse hK
    rw [orCompactC_off _ hK']
    show orMergeL (orCompactC K nt sT) (orCompactC K nt s₁)
        (orCompactC K nt s₂) y = orMergeL sT s₁ s₂ y
    unfold orMergeL
    rw [orCompactC_off _ hK', orCompactC_off _ hK', orCompactC_off _ hK']
  obtain ⟨rdy, hyS⟩ := hcut.addK y hK
  obtain ⟨rdn, hnS⟩ := hcut.addNt y hK
  have helem : (nt y).2 = y.2 := hcut.ntElem y hK
  have hlt : y.1 < (nt y).1 := hcut.ntNewer y hK
  have hsub₁ : ET ⊆ E₁ := by rw [hET]; exact Set.inter_subset_left
  have hsub₂ : ET ⊆ E₂ := by rw [hET]; exact Set.inter_subset_right
  have hyET : (y.1, rdy, ORSetOp.add y.2) ∈ ET := hST hyS
  have hnET : ((nt y).1, rdn, ORSetOp.add y.2) ∈ ET := hST hnS
  have hnET' : ((nt y).1, rdn, ORSetOp.add (nt y).2) ∈ ET := by
    rw [helem]; exact hnET
  have hu1 : s₁ y = true → sT y = true := by
    intro haY
    by_contra h
    have := orDead_mono hGood h_verT h_ver₁ hyET hsub₁ (bfalse h)
    rw [this] at haY
    cases haY
  have hu2 : s₂ y = true → sT y = true := by
    intro hbY
    by_contra h
    have := orDead_mono hGood h_verT h_ver₂ hyET hsub₂ (bfalse h)
    rw [this] at hbY
    cases hbY
  have hu3 : s₁ (nt y) = true → sT (nt y) = true := by
    intro haN
    by_contra h
    have := orDead_mono hGood h_verT h_ver₁ hnET' hsub₁ (bfalse h)
    rw [this] at haN
    cases haN
  have hu4 : s₂ (nt y) = true → sT (nt y) = true := by
    intro hbN
    by_contra h
    have := orDead_mono hGood h_verT h_ver₂ hnET' hsub₂ (bfalse h)
    rw [this] at hbN
    cases hbN
  have hX7 : s₁ (nt y) = false → sT (nt y) = true → s₁ y = true → False := by
    intro haN hlN haY
    obtain ⟨hdead, -⟩ := orDiscriminator hGood h_verT h_ver₁ hsetT hyS helem
      hlt hnET (hsub₁ hnET) haN hlN
    rw [hdead] at haY
    cases haY
  have hX8 : s₂ (nt y) = false → sT (nt y) = true → s₂ y = true → False := by
    intro hbN hlN hbY
    obtain ⟨hdead, -⟩ := orDiscriminator hGood h_verT h_ver₂ hsetT hyS helem
      hlt hnET (hsub₂ hnET) hbN hlN
    rw [hdead] at hbY
    cases hbY
  have hX9 : s₁ (nt y) = true → s₂ (nt y) = false → s₂ y = true → False := by
    intro haN hbN hbY
    exact hX8 hbN (hu3 haN) hbY
  have hX10 : s₂ (nt y) = true → s₁ (nt y) = false → s₁ y = true → False := by
    intro hbN haN haY
    exact hX7 haN (hu4 hbN) haY
  show orMergeL (orCompactC K nt sT) (orCompactC K nt s₁)
      (orCompactC K nt s₂) y
    = (orMergeL sT s₁ s₂ y && !(K y && orMergeL sT s₁ s₂ (nt y)))
  unfold orMergeL orCompactC
  rw [hK]
  cases hlY : sT y <;> cases hlN : sT (nt y) <;> cases haY : s₁ y <;>
    cases haN : s₁ (nt y) <;> cases hbY : s₂ y <;> cases hbN : s₂ (nt y) <;>
    simp_all

/-- Settledness is monotone in the container (same configuration). -/
theorem settledOn_mono {D : ConditionedMRDTSig} {C : Configuration D}
    {E E' S : Set (Op D.AppOp)} (hset : SettledAtOn C E S) (hEE : E ⊆ E') :
    SettledAtOn C E' S :=
  ⟨fun _ ha => hEE (hset.sub ha), hset.down,
    fun e he hc => hEE (hset.conc e he hc)⟩

/-- **VC-S4, form-committed** (the `mono` consumer): with branch 1 known
compacted-form (possibly coincident), the merge is the callback image. -/
theorem orMerge_compact_form1 (hGood : GoodConfig3 C) (hcut : CutSpec S K nt)
    {ŝ₁ ŝ₂ ŝT : ORSet.State}
    (h_ver₁ : C.ver v₁ = some (s₁, E₁)) (h_ver₂ : C.ver v₂ = some (s₂, E₂))
    (h_verT : C.ver vT = some (sT, ET))
    (hET : ET = E₁ ∩ E₂)
    (hd₁ : S ⊆ E₁ ∧ SettledAtOn C E₁ S ∧ ŝ₁ = orCompactC K nt s₁)
    (hsh₂ : ŝ₂ = s₂ ∨ (S ⊆ E₂ ∧ SettledAtOn C E₂ S ∧
      ŝ₂ = orCompactC K nt s₂))
    (hshT : ŝT = sT ∨ (S ⊆ ET ∧ SettledAtOn C ET S ∧
      ŝT = orCompactC K nt sT))
    (hmono₂ : ŝT ≠ sT → S ⊆ E₂ ∧ SettledAtOn C E₂ S ∧
      ŝ₂ = orCompactC K nt s₂) :
    orMergeL ŝT ŝ₁ ŝ₂ = orCompactC K nt (orMergeL sT s₁ s₂) := by
  obtain ⟨hS₁, hset₁, hf₁⟩ := hd₁
  by_cases hT : ŝT = sT
  · by_cases h2 : ŝ₂ = s₂
    · rw [hT, h2, hf₁]
      exact orMergeBody1 hGood hcut h_ver₁ h_ver₂ h_verT hET hS₁ hset₁
    · rcases hsh₂ with h | ⟨hS₂, hset₂, hf₂⟩
      · exact absurd h h2
      · rw [hT, hf₁, hf₂]
        exact orMergeBody12 hGood hcut h_ver₁ h_ver₂ h_verT hET hS₁ hset₁
          hS₂ hset₂
  · rcases hshT with h | ⟨hST, hsetT, hfT⟩
    · exact absurd h hT
    · obtain ⟨hS₂, hset₂, hf₂⟩ := hmono₂ hT
      rw [hfT, hf₁, hf₂]
      exact orMergeBodyT hGood hcut h_ver₁ h_ver₂ h_verT hET hST hsetT

/-- `orMerge_compact_form1`, branch-2 committed (via merge commutativity). -/
theorem orMerge_compact_form2 (hGood : GoodConfig3 C) (hcut : CutSpec S K nt)
    {ŝ₁ ŝ₂ ŝT : ORSet.State}
    (h_ver₁ : C.ver v₁ = some (s₁, E₁)) (h_ver₂ : C.ver v₂ = some (s₂, E₂))
    (h_verT : C.ver vT = some (sT, ET))
    (hET : ET = E₁ ∩ E₂)
    (hd₂ : S ⊆ E₂ ∧ SettledAtOn C E₂ S ∧ ŝ₂ = orCompactC K nt s₂)
    (hsh₁ : ŝ₁ = s₁ ∨ (S ⊆ E₁ ∧ SettledAtOn C E₁ S ∧
      ŝ₁ = orCompactC K nt s₁))
    (hshT : ŝT = sT ∨ (S ⊆ ET ∧ SettledAtOn C ET S ∧
      ŝT = orCompactC K nt sT))
    (hmono₁ : ŝT ≠ sT → S ⊆ E₁ ∧ SettledAtOn C E₁ S ∧
      ŝ₁ = orCompactC K nt s₁) :
    orMergeL ŝT ŝ₁ ŝ₂ = orCompactC K nt (orMergeL sT s₁ s₂) := by
  have hcomm : ∀ l a b : ORSet.State, orMergeL l a b = orMergeL l b a :=
    fun l a b => ORSet_mergeL_comm l a b
  rw [hcomm ŝT ŝ₁ ŝ₂, hcomm sT s₁ s₂]
  exact orMerge_compact_form1 hGood hcut h_ver₂ h_ver₁ h_verT
    (by rw [hET, Set.inter_comm]) hd₂ hsh₁ hshT hmono₁

/-- **VC-S4 for the OR-set** (erratum §9.2 form): merge congruence under the
per-version shape and flag-inheritance facts of the reachable pair — NOT a
free congruence. The disjunctive conclusion feeds the shape invariant at the
merged version. -/
theorem orMerge_compact (hGood : GoodConfig3 C) (hcut : CutSpec S K nt)
    {ŝ₁ ŝ₂ ŝT : ORSet.State}
    (h_ver₁ : C.ver v₁ = some (s₁, E₁)) (h_ver₂ : C.ver v₂ = some (s₂, E₂))
    (h_verT : C.ver vT = some (sT, ET))
    (hET : ET = E₁ ∩ E₂)
    (hsh₁ : ŝ₁ = s₁ ∨ (S ⊆ E₁ ∧ SettledAtOn C E₁ S ∧
      ŝ₁ = orCompactC K nt s₁))
    (hsh₂ : ŝ₂ = s₂ ∨ (S ⊆ E₂ ∧ SettledAtOn C E₂ S ∧
      ŝ₂ = orCompactC K nt s₂))
    (hshT : ŝT = sT ∨ (S ⊆ ET ∧ SettledAtOn C ET S ∧
      ŝT = orCompactC K nt sT))
    (hmono₁ : ŝT ≠ sT → S ⊆ E₁ ∧ SettledAtOn C E₁ S ∧
      ŝ₁ = orCompactC K nt s₁)
    (hmono₂ : ŝT ≠ sT → S ⊆ E₂ ∧ SettledAtOn C E₂ S ∧
      ŝ₂ = orCompactC K nt s₂) :
    orMergeL ŝT ŝ₁ ŝ₂ = orMergeL sT s₁ s₂
      ∨ (S ⊆ E₁ ∪ E₂ ∧ SettledAtOn C (E₁ ∪ E₂) S ∧
        orMergeL ŝT ŝ₁ ŝ₂ = orCompactC K nt (orMergeL sT s₁ s₂)) := by
  by_cases h1 : ŝ₁ = s₁
  · by_cases h2 : ŝ₂ = s₂
    · by_cases hT : ŝT = sT
      · left
        rw [hT, h1, h2]
      · obtain hd₁ := hmono₁ hT
        exact Or.inr ⟨fun a ha => Set.mem_union_left _ (hd₁.1 ha),
          settledOn_mono hd₁.2.1 Set.subset_union_left,
          orMerge_compact_form1 hGood hcut h_ver₁ h_ver₂ h_verT hET hd₁
            hsh₂ hshT hmono₂⟩
    · rcases hsh₂ with h | hd₂
      · exact absurd h h2
      · exact Or.inr ⟨fun a ha => Set.mem_union_right _ (hd₂.1 ha),
          settledOn_mono hd₂.2.1 Set.subset_union_right,
          orMerge_compact_form2 hGood hcut h_ver₁ h_ver₂ h_verT hET hd₂
            hsh₁ hshT hmono₁⟩
  · rcases hsh₁ with h | hd₁
    · exact absurd h h1
    · exact Or.inr ⟨fun a ha => Set.mem_union_left _ (hd₁.1 ha),
        settledOn_mono hd₁.2.1 Set.subset_union_left,
        orMerge_compact_form1 hGood hcut h_ver₁ h_ver₂ h_verT hET hd₁
          hsh₂ hshT hmono₂⟩

end MergeBodies

#print axioms orMerge_compact

/-! ## §2d Step-transfer lemmas: events, settledness, all-heads knowledge

Generic over the signature; consumed by the `Aux` maintenance below. -/

section StepTransfer

variable {D : ConditionedMRDTSig} {C C' : Configuration D}

/-- CreateReplica leaves the event universe unchanged. -/
theorem events_create {r : Replica} (h_fresh : C.N r = none)
    (hL : C'.L = updateRep C.L r ∅) :
    ∀ e, e ∈ C'.events ↔ e ∈ C.events := by
  intro e
  constructor
  · rintro ⟨r'', s'', hL'', hs⟩
    rw [hL] at hL''
    by_cases hr : r'' = r
    · rw [show updateRep C.L r ∅ r'' = some ∅ from by
        unfold updateRep; rw [if_pos hr]] at hL''
      injection hL'' with hL''
      rw [← hL''] at hs
      exact absurd hs (Set.notMem_empty e)
    · rw [show updateRep C.L r ∅ r'' = C.L r'' from by
        unfold updateRep; rw [if_neg hr]] at hL''
      exact ⟨r'', s'', hL'', hs⟩
  · rintro ⟨r'', s'', hL'', hs⟩
    have hr : r'' ≠ r := by
      intro h
      rw [h, (C.dom_eq r).mp h_fresh] at hL''
      cases hL''
    refine ⟨r'', s'', ?_, hs⟩
    rw [hL]
    unfold updateRep
    rw [if_neg hr]
    exact hL''

/-- Apply extends the event universe by exactly the fresh event. -/
theorem events_apply {t : Timestamp} {r : Replica} {o : D.AppOp}
    {v : Version} {s : D.State} {ev : Set (Op D.AppOp)}
    (h_head : C.head r = some v) (h_ver : C.ver v = some (s, ev))
    (hL : C'.L = updateRep C.L r (ev ∪ {(t, r, o)}))
    (hev_sub : ∀ a ∈ ev, a ∈ C.events) :
    ∀ e, e ∈ C'.events ↔ e ∈ C.events ∨ e = (t, r, o) := by
  have hLr : C.L r = some ev := by
    have h2 := (C.head_coherent r v h_head).2
    rw [h_ver] at h2
    exact h2.symm
  intro e
  constructor
  · rintro ⟨r'', s'', hL'', hs⟩
    rw [hL] at hL''
    by_cases hr : r'' = r
    · rw [show updateRep C.L r (ev ∪ {(t, r, o)}) r'' = some (ev ∪ {(t, r, o)})
        from by unfold updateRep; rw [if_pos hr]] at hL''
      injection hL'' with hL''
      rw [← hL''] at hs
      rcases hs with hs | hs
      · exact Or.inl (hev_sub e hs)
      · exact Or.inr hs
    · rw [show updateRep C.L r (ev ∪ {(t, r, o)}) r'' = C.L r'' from by
        unfold updateRep; rw [if_neg hr]] at hL''
      exact Or.inl ⟨r'', s'', hL'', hs⟩
  · intro h
    rcases h with ⟨r'', s'', hL'', hs⟩ | rfl
    · by_cases hr : r'' = r
      · rw [hr, hLr] at hL''
        injection hL'' with hL''
        refine ⟨r, ev ∪ {(t, r, o)}, ?_, Or.inl (by rw [hL'']; exact hs)⟩
        rw [hL]
        unfold updateRep
        rw [if_pos rfl]
      · refine ⟨r'', s'', ?_, hs⟩
        rw [hL]
        unfold updateRep
        rw [if_neg hr]
        exact hL''
    · refine ⟨r, ev ∪ {(t, r, o)}, ?_, Or.inr rfl⟩
      rw [hL]
      unfold updateRep
      rw [if_pos rfl]

/-- Merge leaves the event universe unchanged. -/
theorem events_merge {r₁ : Replica} {v₁ : Version} {s₁ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁) (h_ver₁ : C.ver v₁ = some (s₁, ev₁))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hev₂_sub : ∀ a ∈ ev₂, a ∈ C.events) :
    ∀ e, e ∈ C'.events ↔ e ∈ C.events := by
  have hLr : C.L r₁ = some ev₁ := by
    have h2 := (C.head_coherent r₁ v₁ h_head₁).2
    rw [h_ver₁] at h2
    exact h2.symm
  intro e
  constructor
  · rintro ⟨r'', s'', hL'', hs⟩
    rw [hL] at hL''
    by_cases hr : r'' = r₁
    · rw [show updateRep C.L r₁ (ev₁ ∪ ev₂) r'' = some (ev₁ ∪ ev₂) from by
        unfold updateRep; rw [if_pos hr]] at hL''
      injection hL'' with hL''
      rw [← hL''] at hs
      rcases hs with hs | hs
      · exact ⟨r₁, ev₁, hLr, hs⟩
      · exact hev₂_sub e hs
    · rw [show updateRep C.L r₁ (ev₁ ∪ ev₂) r'' = C.L r'' from by
        unfold updateRep; rw [if_neg hr]] at hL''
      exact ⟨r'', s'', hL'', hs⟩
  · rintro ⟨r'', s'', hL'', hs⟩
    by_cases hr : r'' = r₁
    · rw [hr, hLr] at hL''
      injection hL'' with hL''
      refine ⟨r₁, ev₁ ∪ ev₂, ?_, Or.inl (by rw [hL'']; exact hs)⟩
      rw [hL]
      unfold updateRep
      rw [if_pos rfl]
    · refine ⟨r'', s'', ?_, hs⟩
      rw [hL]
      unfold updateRep
      rw [if_neg hr]
      exact hL''

/-- Settledness transfers across steps that keep `vis` and the event universe
(merge, createReplica, the compaction move), to any larger cut container. -/
theorem settledOn_frame {E E' S : Set (Op D.AppOp)}
    (hset : SettledAtOn C E S)
    (hvis : C'.vis = C.vis)
    (hev : ∀ e, e ∈ C'.events ↔ e ∈ C.events)
    (hEE : E ⊆ E') :
    SettledAtOn C' E' S := by
  refine ⟨fun a ha => hEE (hset.sub ha), ?_, ?_⟩
  · intro a b hab hb
    rw [hvis] at hab
    exact hset.down a b hab hb
  · rintro e he ⟨a, ha, hne, hnv1, hnv2⟩
    rw [hvis] at hnv1 hnv2
    exact hEE (hset.conc e ((hev e).mp he) ⟨a, ha, hne, hnv1, hnv2⟩)

/-- Settledness transfers across an Apply whose minter has heard the cut:
the fresh event sees all of `S`, so no new concurrency is minted. -/
theorem settledOn_apply {t : Timestamp} {r : Replica} {o : D.AppOp}
    {ev E E' S : Set (Op D.AppOp)}
    (hset : SettledAtOn C E S)
    (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o)))
    (hev : ∀ e, e ∈ C'.events ↔ e ∈ C.events ∨ e = (t, r, o))
    (h_fresh_t : ∀ e' ∈ C.events, Op.time e' ≠ t)
    (hS_ev : ∀ o' ∈ S, o' ∈ C.events)
    (hS_minter : S ⊆ ev)
    (hEE : E ⊆ E') :
    SettledAtOn C' E' S := by
  have hnewS : ((t, r, o) : Op D.AppOp) ∉ S := by
    intro hin
    exact h_fresh_t _ (hS_ev _ hin) rfl
  refine ⟨fun a ha => hEE (hset.sub ha), ?_, ?_⟩
  · intro a b hab hb
    rw [hvis] at hab
    rcases hab with hab | ⟨-, rfl⟩
    · exact hset.down a b hab hb
    · exact absurd hb hnewS
  · rintro e he ⟨a, ha, hne, hnv1, hnv2⟩
    rcases (hev e).mp he with he' | rfl
    · refine hEE (hset.conc e he' ⟨a, ha, hne, ?_, ?_⟩)
      · intro h
        exact hnv1 (by rw [hvis]; exact Or.inl h)
      · intro h
        exact hnv2 (by rw [hvis]; exact Or.inl h)
    · exact absurd (by rw [hvis]; exact Or.inr ⟨hS_minter ha, rfl⟩) hnv2

/-- All-heads knowledge survives an Apply. -/
theorem allHeard_apply {S : Set (Op D.AppOp)} {t : Timestamp} {r : Replica}
    {o : D.AppOp} {v vnew : Version} {s : D.State} {ev : Set (Op D.AppOp)}
    (hAH : AllHeard C S)
    (h_head : C.head r = some v) (h_ver : C.ver v = some (s, ev))
    (h_vnew : C.ver vnew = none)
    (hHA : ∀ r' w, C.head r' = some w → (C.ver w).isSome)
    (hver : C'.ver = fun w => if w = vnew
      then some (D.update s (t, r, o), ev ∪ {(t, r, o)}) else C.ver w)
    (hhead : C'.head = fun r' => if r' = r then some vnew else C.head r') :
    AllHeard C' S := by
  intro r' w s' E' hh hv
  simp only [hhead] at hh
  rw [hver] at hv
  dsimp only at hv
  by_cases hr : r' = r
  · rw [if_pos hr] at hh
    injection hh with hh
    subst hh
    rw [if_pos rfl] at hv
    injection hv with hv
    have hE' : E' = ev ∪ {(t, r, o)} := (congrArg Prod.snd hv).symm
    rw [hE']
    exact fun a ha => Set.mem_union_left _ (hAH r v s ev h_head h_ver ha)
  · rw [if_neg hr] at hh
    have hwne : w ≠ vnew := by
      intro h
      have := hHA r' w hh
      rw [h, h_vnew] at this
      cases this
    rw [if_neg hwne] at hv
    exact hAH r' w s' E' hh hv

/-- All-heads knowledge survives a Merge (and the compaction move's
self-merge). -/
theorem allHeard_merge {S : Set (Op D.AppOp)} {r₁ : Replica}
    {v₁ vm : Version} {s₁ : D.State} {ev₁ ev₂ : Set (Op D.AppOp)}
    {sm : D.State}
    (hAH : AllHeard C S)
    (h_head₁ : C.head r₁ = some v₁) (h_ver₁ : C.ver v₁ = some (s₁, ev₁))
    (h_vm : C.ver vm = none)
    (hHA : ∀ r' w, C.head r' = some w → (C.ver w).isSome)
    (hver : C'.ver = fun w => if w = vm then some (sm, ev₁ ∪ ev₂)
      else C.ver w)
    (hhead : C'.head = fun r' => if r' = r₁ then some vm else C.head r') :
    AllHeard C' S := by
  intro r' w s' E' hh hv
  simp only [hhead] at hh
  rw [hver] at hv
  dsimp only at hv
  by_cases hr : r' = r₁
  · rw [if_pos hr] at hh
    injection hh with hh
    subst hh
    rw [if_pos rfl] at hv
    injection hv with hv
    have hE' : E' = ev₁ ∪ ev₂ := (congrArg Prod.snd hv).symm
    rw [hE']
    exact fun a ha => Set.mem_union_left _ (hAH r₁ v₁ s₁ ev₁ h_head₁ h_ver₁ ha)
  · rw [if_neg hr] at hh
    have hwne : w ≠ vm := by
      intro h
      have := hHA r' w hh
      rw [h, h_vm] at this
      cases this
    rw [if_neg hwne] at hv
    exact hAH r' w s' E' hh hv

end StepTransfer

/-- **VC-S6, observationally**: staggered re-compaction reads as the direct
coarser compaction (`EpochCoherentObs`); the same-`R`-class form is false for
graph relations. -/
theorem orEpoch_obs {S S' : Set (Op ORSetOp)} {K K' : ℕ × ℕ → Bool}
    {nt nt' : ℕ × ℕ → ℕ × ℕ}
    (hcut : CutSpec S K nt) (hcut' : CutSpec S' K' nt') (s : ORSet.State) :
    orRead (orCompactC K' nt' (orCompactC K nt s))
      = orRead (orCompactC K' nt' s) := by
  rw [orRead_compactC hcut', orRead_compactC hcut, orRead_compactC hcut']

/-! ## §2e The auxiliary pair-invariant and its maintenance -/

/-- A compaction has been absorbed somewhere: some version's payloads differ. -/
def ORFlagged (C Ĉ : Configuration ORSet) : Prop :=
  ∃ v s E ŝ Ê, C.ver v = some (s, E) ∧ Ĉ.ver v = some (ŝ, Ê) ∧ ŝ ≠ s

/-- **The OR-set pair-invariant**: the full side is reachable; every version's
compacted payload is the full one or its callback image *at a settled,
cut-containing event set*; compactedness is inherited down the DAG; and once
any compaction is absorbed, every head has heard the cut (the runtime frontier
that keeps settledness stable under new mints). -/
structure ORAux (S : Set (Op ORSetOp)) (K : ℕ × ℕ → Bool)
    (nt : ℕ × ℕ → ℕ × ℕ) (C Ĉ : Configuration ORSet) : Prop where
  reach : (labeledTS3 ORSet).ReachableFrom (initConfig ORSet trivial) C
  shape : ∀ v s E ŝ Ê, C.ver v = some (s, E) → Ĉ.ver v = some (ŝ, Ê) →
    ŝ = s ∨ (S ⊆ E ∧ SettledAtOn C E S ∧ ŝ = orCompactC K nt s)
  mono : ∀ {v w : Version} {sv ŝv sw ŝw : ORSet.State}
    {Ev Êv Ew Êw : Set (Op ORSetOp)}, Reaches C.parents w v →
    C.ver w = some (sw, Ew) → Ĉ.ver w = some (ŝw, Êw) → ŝw ≠ sw →
    C.ver v = some (sv, Ev) → Ĉ.ver v = some (ŝv, Êv) →
    S ⊆ Ev ∧ SettledAtOn C Ev S ∧ ŝv = orCompactC K nt sv
  heard : ORFlagged C Ĉ → AllHeard C S

namespace ORAux

variable {S : Set (Op ORSetOp)} {K : ℕ × ℕ → Bool} {nt : ℕ × ℕ → ℕ × ℕ}
  {C Ĉ : Configuration ORSet}

theorem good (h : ORAux S K nt C Ĉ) : GoodConfig3 C :=
  goodConfig3_reachableV ORSet_joinLemma3 (reachableV_of_reachable h.reach)

theorem store (h : ORAux S K nt C Ĉ) : StoreInv C.ver C.parents :=
  storeInv_reachable h.reach

end ORAux

/-- A fresh (unallocated) version reaches nothing allocated. -/
private theorem not_reaches_fresh {D : ConditionedMRDTSig}
    {C : Configuration D} {vnew v' : Version}
    (hStore : StoreInv C.ver C.parents)
    (h_vnew : C.ver vnew = none) (hv' : (C.ver v').isSome)
    (hr : Reaches C.parents vnew v') : False := by
  rcases (Relation.ReflTransGen.cases_head hr) with h | ⟨b, hstep, -⟩
  · rw [← h, h_vnew] at hv'
    cases hv'
  · have := hStore.parents_alloc b vnew hstep
    rw [h_vnew] at this
    cases this

/-- Aux maintenance: CreateReplica (gated on no prior compaction). -/
theorem orAux_create {S : Set (Op ORSetOp)} {K : ℕ × ℕ → Bool}
    {nt : ℕ × ℕ → ℕ × ℕ} {C Ĉ C' Ĉ' : Configuration ORSet} {r : Replica}
    (aux : ORAux S K nt C Ĉ) (hcc : ∀ v, Ĉ.ver v = C.ver v)
    (hstepC : Step3 ORSet C (.createReplica r) C')
    (hstepĈ : Step3 ORSet Ĉ (.createReplica r) Ĉ') :
    ORAux S K nt C' Ĉ' := by
  cases hstepC with
  | @createReplica _ h_freshC _ hNC hLC hvisC hverC hheadC hparC =>
  cases hstepĈ with
  | @createReplica _ h_freshĈ _ hNĈ hLĈ hvisĈ hverĈ hheadĈ hparĈ =>
  have hsame : ∀ v s E ŝ Ê, C'.ver v = some (s, E) → Ĉ'.ver v = some (ŝ, Ê) →
      ŝ = s := by
    intro v s E ŝ Ê hv hĉ
    rw [hverC] at hv
    rw [hverĈ, hcc v, hv] at hĉ
    injection hĉ with hĉ
    exact (congrArg Prod.fst hĉ).symm
  refine ⟨Relation.ReflTransGen.tail aux.reach
    ⟨_, Step3.createReplica h_freshC _ hNC hLC hvisC hverC hheadC hparC⟩,
    ?_, ?_, ?_⟩
  · intro v s E ŝ Ê hv hĉ
    exact Or.inl (hsame v s E ŝ Ê hv hĉ)
  · intro v w sv ŝv sw ŝw Ev Êv Ew Êw hr hw hŵ hne hv hĉ
    exact absurd (hsame w sw Ew ŝw Êw hw hŵ) hne
  · rintro ⟨v, s, E, ŝ, Ê, hv, hĉ, hne⟩
    exact absurd (hsame v s E ŝ Ê hv hĉ) hne

/-- The simulation relation of the OR-set instance. -/
def orRel (K : ℕ × ℕ → Bool) (nt : ℕ × ℕ → ℕ × ℕ)
    (s ŝ : ORSet.State) : Prop :=
  ŝ = s ∨ ŝ = orCompactC K nt s

/-- Aux maintenance: Apply. -/
theorem orAux_apply {S : Set (Op ORSetOp)} {K : ℕ × ℕ → Bool}
    {nt : ℕ × ℕ → ℕ × ℕ} (hcut : CutSpec S K nt)
    {C Ĉ C' Ĉ' : Configuration ORSet} {t : Timestamp} {r : Replica}
    {o : ORSetOp}
    (rel : ConfigRelS (orRel K nt) C Ĉ) (aux : ORAux S K nt C Ĉ)
    (hstepC : Step3 ORSet C (.apply t r o) C')
    (hstepĈ : Step3 ORSet Ĉ (.apply t r o) Ĉ')
    (rel' : ConfigRelS (orRel K nt) C' Ĉ') :
    ORAux S K nt C' Ĉ' := by
  have hGood := aux.good
  have hStore := aux.store
  cases hstepC with
  | @apply _ _ _ v s ev vnew h_head h_ver h_fresh_t h_fresh_store h_vnew
      h_rank _ hNC hLC hvisC hverC hheadC hparC =>
  cases hstepĈ with
  | @apply _ _ _ vH sH evH vnewH hh_head hh_ver hh_fresh_t hh_fresh_store
      hh_vnew hh_rank _ hNH hLH hvisH hverH hheadH hparH =>
  -- link the compacted step's data to the full step's
  have hvH : vH = v := by
    have := hh_head
    rw [rel.head_eq, h_head] at this
    injection this with this
    exact this.symm
  rw [hvH] at hh_ver
  have hevH : evH = ev := by
    have hEv := rel.ver_events v
    rw [h_ver, hh_ver] at hEv
    simp only [Option.map_some] at hEv
    injection hEv
  rw [hevH] at hh_ver hverH
  have hvnewH : vnewH = vnew := by
    by_contra hne
    have hsome := rel'.ver_isSome vnew
    rw [hverC, hverH] at hsome
    dsimp only at hsome
    rw [if_pos rfl, if_neg (fun h => hne h.symm)] at hsome
    have := rel.ver_isSome vnew
    rw [h_vnew] at this
    rw [this] at hsome
    cases hsome
  rw [hvnewH] at hverH
  -- shared machinery
  have hev_sub : ∀ a ∈ ev, a ∈ C.events := hGood.ver_events_sub v s ev h_ver
  have hEvents : ∀ e, e ∈ C'.events ↔ e ∈ C.events ∨ e = (t, r, o) :=
    events_apply h_head h_ver hLC hev_sub
  have hpar_old : ∀ x, x ≠ vnew → C'.parents x = C.parents x := by
    intro x hx
    rw [hparC]
    dsimp only
    rw [if_neg hx]
  have hflag_step : S ⊆ ev → SettledAtOn C ev S →
      sH = orCompactC K nt s →
      S ⊆ ev ∪ {(t, r, o)} ∧ SettledAtOn C' (ev ∪ {(t, r, o)}) S ∧
        ORSet.update sH (t, r, o)
          = orCompactC K nt (ORSet.update s (t, r, o)) := by
    intro hS hset hf
    refine ⟨fun a ha => Set.mem_union_left _ (hS ha), ?_, ?_⟩
    · exact settledOn_apply hset hvisC hEvents h_fresh_t
        (fun o' ho' => hev_sub _ (hS ho')) hS Set.subset_union_left
    · rw [hf]
      cases o with
      | add e =>
        exact orCompactC_add hcut s t r e
          (orK_fresh hGood hcut h_ver hS h_fresh_t)
      | rem e => exact orCompactC_rem hcut s t r e
  have hsettled_old : ORFlagged C Ĉ → ∀ {E' : Set (Op ORSetOp)},
      SettledAtOn C E' S → SettledAtOn C' E' S := by
    intro hfl E' hset
    have hAH := aux.heard hfl
    exact settledOn_apply hset hvisC hEvents h_fresh_t
      (fun o' ho' => hev_sub _ (hAH r v s ev h_head h_ver ho'))
      (hAH r v s ev h_head h_ver) (fun a ha => ha)
  refine ⟨Relation.ReflTransGen.tail aux.reach
    ⟨_, Step3.apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank _
      hNC hLC hvisC hverC hheadC hparC⟩, ?_, ?_, ?_⟩
  · -- shape
    intro w s' E' ŝ' Ê' hw hŵ
    rw [hverC] at hw
    rw [hverH] at hŵ
    dsimp only at hw hŵ
    by_cases hwn : w = vnew
    · rw [if_pos hwn] at hw hŵ
      injection hw with hw
      injection hŵ with hŵ
      have hs' : s' = ORSet.update s (t, r, o) := (congrArg Prod.fst hw).symm
      have hE' : E' = ev ∪ {(t, r, o)} := (congrArg Prod.snd hw).symm
      have hŝ' : ŝ' = ORSet.update sH (t, r, o) := (congrArg Prod.fst hŵ).symm
      rcases aux.shape v s ev sH ev h_ver hh_ver with hsame | ⟨hS, hset, hf⟩
      · left
        rw [hs', hŝ', hsame]
      · right
        obtain ⟨h1, h2, h3⟩ := hflag_step hS hset hf
        rw [hs', hE', hŝ']
        exact ⟨h1, h2, h3⟩
    · rw [if_neg hwn] at hw hŵ
      rcases aux.shape w s' E' ŝ' Ê' hw hŵ with hsame | ⟨hS, hset, hf⟩
      · exact Or.inl hsame
      · by_cases hŝs : ŝ' = s'
        · exact Or.inl hŝs
        · exact Or.inr ⟨hS,
            hsettled_old ⟨w, s', E', ŝ', Ê', hw, hŵ, hŝs⟩ hset, hf⟩
  · -- mono
    intro v' w' sv ŝv sw ŝw Ev Êv Ew Êw hr hw hŵ hne hv hĉ
    rw [hverC] at hw hv
    rw [hverH] at hŵ hĉ
    dsimp only at hw hŵ hv hĉ
    by_cases hv'n : v' = vnew
    · rw [if_pos hv'n] at hv hĉ
      injection hv with hv
      injection hĉ with hĉ
      have hsv : sv = ORSet.update s (t, r, o) := (congrArg Prod.fst hv).symm
      have hEv : Ev = ev ∪ {(t, r, o)} := (congrArg Prod.snd hv).symm
      have hŝv : ŝv = ORSet.update sH (t, r, o) := (congrArg Prod.fst hĉ).symm
      have hflag : S ⊆ ev ∧ SettledAtOn C ev S ∧
          sH = orCompactC K nt s := by
        rw [hv'n] at hr
        rcases reaches_new_target (ps := [v]) hStore.parents_alloc h_vnew
          (by rw [hparC]; simp)
          hpar_old
          (by
            intro p hp
            rw [List.mem_singleton.mp hp, h_ver]
            rfl) hr with hw'eq | ⟨p, hp, hre⟩
        · -- the strict version is the fresh node itself
          rw [hw'eq, if_pos rfl] at hw hŵ
          injection hw with hw
          injection hŵ with hŵ
          injection hw with hw1 hw2
          injection hŵ with hŵ1 hŵ2
          have hŝs : sH ≠ s := by
            intro h
            exact hne (by rw [← hŵ1, ← hw1, h])
          rcases aux.shape v s ev sH ev h_ver hh_ver with hsame |
            ⟨hS, hset, hf⟩
          · exact absurd hsame hŝs
          · exact ⟨hS, hset, hf⟩
        · have hpv : p = v := List.mem_singleton.mp hp
          rw [hpv] at hre
          have hw'ne : w' ≠ vnew := by
            intro h
            exact not_reaches_fresh hStore h_vnew (by rw [h_ver]; rfl)
              (h ▸ hre)
          rw [if_neg hw'ne] at hw hŵ
          exact aux.mono hre hw hŵ hne h_ver hh_ver
      obtain ⟨h1, h2, h3⟩ := hflag_step hflag.1 hflag.2.1 hflag.2.2
      rw [hsv, hEv, hŝv]
      exact ⟨h1, h2, h3⟩
    · rw [if_neg hv'n] at hv hĉ
      have hre : Reaches C.parents w' v' :=
        reaches_old_of_new hStore.parents_alloc h_vnew hpar_old hr
          (by rw [hv]; rfl)
      have hw'ne : w' ≠ vnew := by
        intro h
        exact not_reaches_fresh hStore h_vnew (by rw [hv]; rfl) (h ▸ hre)
      rw [if_neg hw'ne] at hw hŵ
      obtain ⟨hSv, hsetv, hfv⟩ := aux.mono hre hw hŵ hne hv hĉ
      exact ⟨hSv, hsettled_old ⟨w', sw, Ew, ŝw, Êw, hw, hŵ, hne⟩ hsetv, hfv⟩
  · -- heard
    rintro ⟨u, su, Eu, ŝu, Êu, hu, hû, hneu⟩
    have hflC : ORFlagged C Ĉ := by
      rw [hverC] at hu
      rw [hverH] at hû
      dsimp only at hu hû
      by_cases hun : u = vnew
      · rw [if_pos hun] at hu hû
        injection hu with hu
        injection hû with hû
        injection hu with hu1 hu2
        injection hû with hû1 hû2
        have hŝs : sH ≠ s := by
          intro h
          exact hneu (by rw [← hû1, ← hu1, h])
        exact ⟨v, s, ev, sH, ev, h_ver, hh_ver, hŝs⟩
      · rw [if_neg hun] at hu hû
        exact ⟨u, su, Eu, ŝu, Êu, hu, hû, hneu⟩
    exact allHeard_apply (aux.heard hflC) h_head h_ver h_vnew
      rel.heads_alloc hverC hheadC

/-- Aux maintenance: Merge — the VC-S4 payload plus the frame transfers. -/
theorem orAux_merge {S : Set (Op ORSetOp)} {K : ℕ × ℕ → Bool}
    {nt : ℕ × ℕ → ℕ × ℕ} (hcut : CutSpec S K nt)
    {C Ĉ C' Ĉ' : Configuration ORSet} {r₁ r₂ : Replica}
    (rel : ConfigRelS (orRel K nt) C Ĉ) (aux : ORAux S K nt C Ĉ)
    (hstepC : Step3 ORSet C (.merge r₁ r₂) C')
    (hstepĈ : Step3 ORSet Ĉ (.merge r₁ r₂) Ĉ')
    (rel' : ConfigRelS (orRel K nt) C' Ĉ') :
    ORAux S K nt C' Ĉ' := by
  have hGood := aux.good
  have hStore := aux.store
  cases hstepC with
  | @merge _ _ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT h_head₁ h_head₂ h_ver₁
      h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂ _ hNC hLC hvisC hverC hheadC
      hparC =>
  cases hstepĈ with
  | @merge _ _ w₁ w₂ wT wm t₁ t₂ tT fv₁ fv₂ fvT hh_head₁ hh_head₂ hh_ver₁
      hh_ver₂ hh_lca hh_verT hh_vm hh_rank₁ hh_rank₂ _ hNH hLH hvisH hverH
      hheadH hparH =>
  -- link the compacted step's data
  have hw₁ : w₁ = v₁ := by
    have := hh_head₁
    rw [rel.head_eq, h_head₁] at this
    injection this with this
    exact this.symm
  have hw₂ : w₂ = v₂ := by
    have := hh_head₂
    rw [rel.head_eq, h_head₂] at this
    injection this with this
    exact this.symm
  rw [hw₁] at hh_ver₁ hh_lca
  rw [hw₂] at hh_ver₂ hh_lca
  have hwT : wT = vT := by
    refine isLCA_unique C.parents_lt ?_ h_lca
    rw [← rel.parents_eq]
    exact hh_lca
  rw [hwT] at hh_verT
  have hfvT : fvT = evT := by
    have hEv := rel.ver_events vT
    rw [h_verT, hh_verT] at hEv
    simp only [Option.map_some] at hEv
    injection hEv
  rw [hfvT] at hh_verT
  have hfv₁ : fv₁ = ev₁ := by
    have hEv := rel.ver_events v₁
    rw [h_ver₁, hh_ver₁] at hEv
    simp only [Option.map_some] at hEv
    injection hEv
  have hfv₂ : fv₂ = ev₂ := by
    have hEv := rel.ver_events v₂
    rw [h_ver₂, hh_ver₂] at hEv
    simp only [Option.map_some] at hEv
    injection hEv
  rw [hfv₁] at hh_ver₁ hverH
  rw [hfv₂] at hh_ver₂ hverH
  have hwm : wm = vm := by
    by_contra hne
    have hsome := rel'.ver_isSome vm
    rw [hverC, hverH] at hsome
    dsimp only at hsome
    rw [if_pos rfl, if_neg (fun h => hne h.symm)] at hsome
    have := rel.ver_isSome vm
    rw [h_vm] at this
    rw [this] at hsome
    cases hsome
  rw [hwm] at hverH
  -- shared machinery
  have hev₂_sub : ∀ a ∈ ev₂, a ∈ C.events :=
    hGood.ver_events_sub v₂ s₂ ev₂ h_ver₂
  have hEvents : ∀ e, e ∈ C'.events ↔ e ∈ C.events :=
    events_merge h_head₁ h_ver₁ hLC hev₂_sub
  have hET : evT = ev₁ ∩ ev₂ := C.lca_events h_lca h_ver₁ h_ver₂ h_verT
  have hpar_old : ∀ x, x ≠ vm → C'.parents x = C.parents x := by
    intro x hx
    rw [hparC]
    dsimp only
    rw [if_neg hx]
  have hsettled' : ∀ {E' : Set (Op ORSetOp)},
      SettledAtOn C E' S → SettledAtOn C' E' S := by
    intro E' hset
    exact settledOn_frame hset hvisC hEvents (fun a ha => ha)
  -- the VC-S4 shape at the fresh node, disjunctive
  have hshape_new :
      ORSet.mergeL tT t₁ t₂ = ORSet.mergeL sT s₁ s₂
      ∨ (S ⊆ ev₁ ∪ ev₂ ∧ SettledAtOn C (ev₁ ∪ ev₂) S ∧
        ORSet.mergeL tT t₁ t₂
          = orCompactC K nt (ORSet.mergeL sT s₁ s₂)) :=
    orMerge_compact hGood hcut h_ver₁ h_ver₂ h_verT hET
      (aux.shape v₁ s₁ ev₁ t₁ ev₁ h_ver₁ hh_ver₁)
      (aux.shape v₂ s₂ ev₂ t₂ ev₂ h_ver₂ hh_ver₂)
      (aux.shape vT sT evT tT evT h_verT hh_verT)
      (fun hne => aux.mono h_lca.1 h_verT hh_verT hne h_ver₁ hh_ver₁)
      (fun hne => aux.mono h_lca.2.1 h_verT hh_verT hne h_ver₂ hh_ver₂)
  refine ⟨Relation.ReflTransGen.tail aux.reach
    ⟨_, Step3.merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
      h_rank₂ _ hNC hLC hvisC hverC hheadC hparC⟩, ?_, ?_, ?_⟩
  · -- shape
    intro w s' E' ŝ' Ê' hw hŵ
    rw [hverC] at hw
    rw [hverH] at hŵ
    dsimp only at hw hŵ
    by_cases hwn : w = vm
    · rw [if_pos hwn] at hw hŵ
      injection hw with hw
      injection hŵ with hŵ
      have hs' : s' = ORSet.mergeL sT s₁ s₂ := (congrArg Prod.fst hw).symm
      have hE' : E' = ev₁ ∪ ev₂ := (congrArg Prod.snd hw).symm
      have hŝ' : ŝ' = ORSet.mergeL tT t₁ t₂ := (congrArg Prod.fst hŵ).symm
      rcases hshape_new with heq | ⟨hSu, hsetu, heq⟩
      · left
        rw [hs', hŝ', heq]
      · right
        rw [hs', hE', hŝ']
        exact ⟨hSu, hsettled' hsetu, heq⟩
    · rw [if_neg hwn] at hw hŵ
      rcases aux.shape w s' E' ŝ' Ê' hw hŵ with hsame | ⟨hS, hset, hf⟩
      · exact Or.inl hsame
      · exact Or.inr ⟨hS, hsettled' hset, hf⟩
  · -- mono
    intro v' w' sv ŝv sw ŝw Ev Êv Ew Êw hr hw hŵ hne hv hĉ
    rw [hverC] at hw hv
    rw [hverH] at hŵ hĉ
    dsimp only at hw hŵ hv hĉ
    by_cases hv'n : v' = vm
    · rw [if_pos hv'n] at hv hĉ
      injection hv with hv
      injection hĉ with hĉ
      have hsv : sv = ORSet.mergeL sT s₁ s₂ := (congrArg Prod.fst hv).symm
      have hEv : Ev = ev₁ ∪ ev₂ := (congrArg Prod.snd hv).symm
      have hŝv : ŝv = ORSet.mergeL tT t₁ t₂ := (congrArg Prod.fst hĉ).symm
      have hform : S ⊆ ev₁ ∪ ev₂ ∧ SettledAtOn C (ev₁ ∪ ev₂) S ∧
          ORSet.mergeL tT t₁ t₂
            = orCompactC K nt (ORSet.mergeL sT s₁ s₂) := by
        rw [hv'n] at hr
        rcases reaches_new_target (ps := [v₁, v₂]) hStore.parents_alloc h_vm
          (by rw [hparC]; simp)
          hpar_old
          (by
            intro p hp
            rcases List.mem_cons.mp hp with h | h
            · rw [h, h_ver₁]; rfl
            · rw [List.mem_singleton.mp h, h_ver₂]; rfl)
          hr with hw'eq | ⟨p, hp, hre⟩
        · -- the strict version is the fresh node itself
          rw [hw'eq, if_pos rfl] at hw hŵ
          injection hw with hw
          injection hŵ with hŵ
          injection hw with hw1 hw2
          injection hŵ with hŵ1 hŵ2
          rcases hshape_new with heq | ⟨hSu, hsetu, heq⟩
          · exact absurd (by rw [← hŵ1, ← hw1, heq]) hne
          · exact ⟨hSu, hsetu, heq⟩
        · -- a strict proper ancestor: it sits below a branch
          have hd : (S ⊆ ev₁ ∧ SettledAtOn C ev₁ S ∧
              t₁ = orCompactC K nt s₁) ∨
              (S ⊆ ev₂ ∧ SettledAtOn C ev₂ S ∧
              t₂ = orCompactC K nt s₂) := by
            have hw'ne : w' ≠ vm := by
              intro h
              rcases List.mem_cons.mp hp with h' | h'
              · exact not_reaches_fresh hStore h_vm
                  (by rw [h_ver₁]; rfl) (h ▸ (h' ▸ hre))
              · exact not_reaches_fresh hStore h_vm
                  (by rw [h_ver₂]; rfl)
                  (h ▸ (List.mem_singleton.mp h' ▸ hre))
            rw [if_neg hw'ne] at hw hŵ
            rcases List.mem_cons.mp hp with h' | h'
            · rw [h'] at hre
              exact Or.inl (aux.mono hre hw hŵ hne h_ver₁ hh_ver₁)
            · rw [List.mem_singleton.mp h'] at hre
              exact Or.inr (aux.mono hre hw hŵ hne h_ver₂ hh_ver₂)
          rcases hd with hd₁ | hd₂
          · exact ⟨fun a ha => Set.mem_union_left _ (hd₁.1 ha),
              settledOn_mono hd₁.2.1 Set.subset_union_left,
              orMerge_compact_form1 hGood hcut h_ver₁ h_ver₂ h_verT hET hd₁
                (aux.shape v₂ s₂ ev₂ t₂ ev₂ h_ver₂ hh_ver₂)
                (aux.shape vT sT evT tT evT h_verT hh_verT)
                (fun hne' => aux.mono h_lca.2.1 h_verT hh_verT hne' h_ver₂
                  hh_ver₂)⟩
          · exact ⟨fun a ha => Set.mem_union_right _ (hd₂.1 ha),
              settledOn_mono hd₂.2.1 Set.subset_union_right,
              orMerge_compact_form2 hGood hcut h_ver₁ h_ver₂ h_verT hET hd₂
                (aux.shape v₁ s₁ ev₁ t₁ ev₁ h_ver₁ hh_ver₁)
                (aux.shape vT sT evT tT evT h_verT hh_verT)
                (fun hne' => aux.mono h_lca.1 h_verT hh_verT hne' h_ver₁
                  hh_ver₁)⟩
      rw [hsv, hEv, hŝv]
      exact ⟨hform.1, hsettled' hform.2.1, hform.2.2⟩
    · rw [if_neg hv'n] at hv hĉ
      have hre : Reaches C.parents w' v' :=
        reaches_old_of_new hStore.parents_alloc h_vm hpar_old hr
          (by rw [hv]; rfl)
      have hw'ne : w' ≠ vm := by
        intro h
        exact not_reaches_fresh hStore h_vm (by rw [hv]; rfl) (h ▸ hre)
      rw [if_neg hw'ne] at hw hŵ
      obtain ⟨hSv, hsetv, hfv⟩ := aux.mono hre hw hŵ hne hv hĉ
      exact ⟨hSv, hsettled' hsetv, hfv⟩
  · -- heard
    rintro ⟨u, su, Eu, ŝu, Êu, hu, hû, hneu⟩
    have hflC : ORFlagged C Ĉ := by
      rw [hverC] at hu
      rw [hverH] at hû
      dsimp only at hu hû
      by_cases hun : u = vm
      · rw [if_pos hun] at hu hû
        injection hu with hu
        injection hû with hû
        injection hu with hu1 hu2
        injection hû with hû1 hû2
        -- the fresh node is strict, so some input is strict
        by_cases h1 : t₁ = s₁
        · by_cases h2 : t₂ = s₂
          · by_cases hT : tT = sT
            · exfalso
              refine hneu ?_
              rw [← hû1, ← hu1, h1, h2, hT]
            · exact ⟨vT, sT, evT, tT, evT, h_verT, hh_verT, hT⟩
          · exact ⟨v₂, s₂, ev₂, t₂, ev₂, h_ver₂, hh_ver₂, h2⟩
        · exact ⟨v₁, s₁, ev₁, t₁, ev₁, h_ver₁, hh_ver₁, h1⟩
      · rw [if_neg hun] at hu hû
        exact ⟨u, su, Eu, ŝu, Êu, hu, hû, hneu⟩
    exact allHeard_merge (aux.heard hflC) h_head₁ h_ver₁ h_vm
      rel.heads_alloc hverC hheadC

/-- Aux maintenance: the compaction move itself (VC-S1's context). -/
theorem orAux_compact {S : Set (Op ORSetOp)} {K : ℕ × ℕ → Bool}
    {nt : ℕ × ℕ → ℕ × ℕ} (hcut : CutSpec S K nt)
    {C Ĉ C' Ĉ' : Configuration ORSet} {r : Replica} {v vm : Version}
    {s ŝ : ORSet.State} {E : Set (Op ORSetOp)}
    (rel : ConfigRelS (orRel K nt) C Ĉ) (aux : ORAux S K nt C Ĉ)
    (hgate : SettledAt C v S ∧ AllHeard C S)
    (h_head : C.head r = some v) (h_ver : C.ver v = some (s, E))
    (hĉv : Ĉ.ver v = some (ŝ, E))
    (h_vm : C.ver vm = none) (_h_rank : v < vm)
    (hstepC : Step3 ORSet C (.merge r r) C')
    (hverC : C'.ver = fun w => if w = vm
      then some (ORSet.mergeL s s s, E ∪ E) else C.ver w)
    (hheadC : C'.head = fun r' => if r' = r then some vm else C.head r')
    (hLC : C'.L = updateRep C.L r (E ∪ E))
    (hvisC : C'.vis = C.vis)
    (hparC : C'.parents = fun w => if w = vm then [v, v] else C.parents w)
    (hverH : Ĉ'.ver = fun w => if w = vm
      then some (orCompactC K nt ŝ, E ∪ E) else Ĉ.ver w) :
    ORAux S K nt C' Ĉ' := by
  have hGood := aux.good
  have hStore := aux.store
  obtain ⟨⟨sv, Ev, hvv, hsetv⟩, hAH⟩ := hgate
  rw [h_ver] at hvv
  injection hvv with hvv
  have hEv : Ev = E := (congrArg Prod.snd hvv).symm
  rw [hEv] at hsetv
  have hS_E : S ⊆ E := hsetv.sub
  have hEvents : ∀ e, e ∈ C'.events ↔ e ∈ C.events :=
    events_merge h_head h_ver hLC (hGood.ver_events_sub v s E h_ver)
  have hsettled' : ∀ {E' : Set (Op ORSetOp)},
      SettledAtOn C E' S → SettledAtOn C' E' S := by
    intro E' hset
    exact settledOn_frame hset hvisC hEvents (fun a ha => ha)
  have hpar_old : ∀ x, x ≠ vm → C'.parents x = C.parents x := by
    intro x hx
    rw [hparC]
    dsimp only
    rw [if_neg hx]
  -- the fresh node's payload relation (VC-S1's residue)
  have hform_new : orCompactC K nt ŝ
      = orCompactC K nt (ORSet.mergeL s s s) := by
    rw [orMergeL_self]
    rcases aux.shape v s E ŝ E h_ver hĉv with hsame | ⟨-, -, hf⟩
    · rw [hsame]
    · rw [hf, orCompactC_idem hcut]
  have hnew : S ⊆ E ∪ E ∧ SettledAtOn C' (E ∪ E) S ∧
      orCompactC K nt ŝ = orCompactC K nt (ORSet.mergeL s s s) :=
    ⟨fun a ha => Set.mem_union_left _ (hS_E ha),
      hsettled' (settledOn_mono hsetv Set.subset_union_left), hform_new⟩
  refine ⟨Relation.ReflTransGen.tail aux.reach ⟨_, hstepC⟩, ?_, ?_, ?_⟩
  · -- shape
    intro w s' E' ŝ' Ê' hw hŵ
    rw [hverC] at hw
    rw [hverH] at hŵ
    dsimp only at hw hŵ
    by_cases hwn : w = vm
    · rw [if_pos hwn] at hw hŵ
      injection hw with hw
      injection hŵ with hŵ
      right
      have h1 : s' = ORSet.mergeL s s s := (congrArg Prod.fst hw).symm
      have h2 : E' = E ∪ E := (congrArg Prod.snd hw).symm
      have h3 : ŝ' = orCompactC K nt ŝ := (congrArg Prod.fst hŵ).symm
      rw [h1, h2, h3]
      exact hnew
    · rw [if_neg hwn] at hw hŵ
      rcases aux.shape w s' E' ŝ' Ê' hw hŵ with hsame | ⟨hS, hset, hf⟩
      · exact Or.inl hsame
      · exact Or.inr ⟨hS, hsettled' hset, hf⟩
  · -- mono
    intro v' w' sv' ŝv' sw' ŝw' Ev' Êv' Ew' Êw' hr hw hŵ hne hv hĉ
    rw [hverC] at hw hv
    rw [hverH] at hŵ hĉ
    dsimp only at hw hŵ hv hĉ
    by_cases hv'n : v' = vm
    · rw [if_pos hv'n] at hv hĉ
      injection hv with hv
      injection hĉ with hĉ
      have h1 : sv' = ORSet.mergeL s s s := (congrArg Prod.fst hv).symm
      have h2 : Ev' = E ∪ E := (congrArg Prod.snd hv).symm
      have h3 : ŝv' = orCompactC K nt ŝ := (congrArg Prod.fst hĉ).symm
      rw [h1, h2, h3]
      exact hnew
    · rw [if_neg hv'n] at hv hĉ
      have hre : Reaches C.parents w' v' :=
        reaches_old_of_new hStore.parents_alloc h_vm hpar_old hr
          (by rw [hv]; rfl)
      have hw'ne : w' ≠ vm := by
        intro h
        exact not_reaches_fresh hStore h_vm (by rw [hv]; rfl) (h ▸ hre)
      rw [if_neg hw'ne] at hw hŵ
      obtain ⟨hSv, hsetw, hfv⟩ := aux.mono hre hw hŵ hne hv hĉ
      exact ⟨hSv, hsettled' hsetw, hfv⟩
  · -- heard: the gate carries the frontier
    intro _
    exact allHeard_merge hAH h_head h_ver h_vm rel.heads_alloc hverC hheadC

/-! ## §2f The bundle: the six VC discharges, and the capstone -/

/-- **The OR-set stability bundle**: `Redundant_S` as the twin-guarded drop
`orCompactC`, `R_S` as `orRel`, the cut gated by `SettledAt` plus the
all-heads frontier; all six VCs discharged, the metatheorem instantiated. -/
def orStabilityVC {S : Set (Op ORSetOp)} {K : ℕ × ℕ → Bool}
    {nt : ℕ × ℕ → ℕ × ℕ} (hcut : CutSpec S K nt) : StabilityVC ORSet where
  R := orRel K nt
  Obs := ℕ → Prop
  obs := orRead
  compact := orCompactC K nt
  S := S
  Aux := ORAux S K nt
  gate := fun C _ _ v => SettledAt C v S ∧ AllHeard C S
  canCreate := fun C Ĉ _ => ∀ v, Ĉ.ver v = C.ver v
  vc_refl := fun _ => Or.inl rfl
  vc_obs := by
    intro s ŝ h
    rcases h with rfl | rfl
    · rfl
    · exact (orRead_compactC hcut s).symm
  vc_inv := fun _ _ => trivial
  gate_settled := fun h => h.1
  vc_step := by
    intro C Ĉ rel aux t r o v s ŝ E h_head h_ver hĉv h_fresh_t h_fresh_store hR
    rcases aux.shape v s E ŝ E h_ver hĉv with hsame | ⟨hS, hset, hf⟩
    · rw [hsame]
      exact Or.inl rfl
    · rw [hf]
      cases o with
      | add e =>
        rw [orCompactC_add hcut s t r e
          (orK_fresh aux.good hcut h_ver hS h_fresh_t)]
        exact Or.inr rfl
      | rem e =>
        rw [orCompactC_rem hcut s t r e]
        exact Or.inr rfl
  vc_merge := by
    intro C Ĉ rel aux r₁ r₂ v₁ v₂ vT s₁ s₂ sT ŝ₁ ŝ₂ ŝT E₁ E₂ ET h_head₁
      h_head₂ h_ver₁ h_ver₂ h_lca h_verT hĉ₁ hĉ₂ hĉT
    have hET := C.lca_events h_lca h_ver₁ h_ver₂ h_verT
    rcases orMerge_compact aux.good hcut h_ver₁ h_ver₂ h_verT hET
      (aux.shape _ _ _ _ _ h_ver₁ hĉ₁) (aux.shape _ _ _ _ _ h_ver₂ hĉ₂)
      (aux.shape _ _ _ _ _ h_verT hĉT)
      (fun hne => aux.mono h_lca.1 h_verT hĉT hne h_ver₁ hĉ₁)
      (fun hne => aux.mono h_lca.2.1 h_verT hĉT hne h_ver₂ hĉ₂)
      with heq | ⟨-, -, heq⟩
    · exact Or.inl heq
    · exact Or.inr heq
  vc_entry := by
    intro C Ĉ rel aux r v s ŝ E hgate h_head h_ver hĉv
    right
    rcases aux.shape v s E ŝ E h_ver hĉv with hsame | ⟨-, -, hf⟩
    · rw [hsame, orMergeL_self]
    · rw [hf, orMergeL_self, orCompactC_idem hcut]
  aux_init := by
    intro hInit
    refine ⟨Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
    · intro v s E ŝ Ê hv hĉ
      rw [hv] at hĉ
      injection hĉ with hĉ
      exact Or.inl (congrArg Prod.fst hĉ).symm
    · intro v w sv ŝv sw ŝw Ev Êv Ew Êw hr hw hŵ hne hv hĉ
      rw [hw] at hŵ
      injection hŵ with hŵ
      exact absurd (congrArg Prod.fst hŵ).symm hne
    · rintro ⟨v, s, E, ŝ, Ê, hv, hĉ, hne⟩
      rw [hv] at hĉ
      injection hĉ with hĉ
      exact absurd (congrArg Prod.fst hĉ).symm hne
  aux_create := fun _ aux hcc h1 h2 _ => orAux_create aux hcc h1 h2
  aux_apply := fun rel aux h1 h2 rel' => orAux_apply hcut rel aux h1 h2 rel'
  aux_merge := fun rel aux h1 h2 rel' => orAux_merge hcut rel aux h1 h2 rel'
  aux_compact := fun rel aux hg hh hv hĉ hvm hrank hstep hver hhead hL hvis
      hpar _ _ _ _ _ hverH _ =>
    orAux_compact hcut rel aux hg hh hv hĉ hvm hrank hstep hver hhead hL
      hvis hpar hverH

/-- **The OR-set stability capstone, reads**: along every paired run, every
version reads identically through the OR-set read interface. -/
theorem ORSet_stability_reads {S : Set (Op ORSetOp)} {K : ℕ × ℕ → Bool}
    {nt : ℕ × ℕ → ℕ × ℕ} (hcut : CutSpec S K nt)
    {C Ĉ : Configuration ORSet}
    (h : StabReach (orStabilityVC hcut) trivial C Ĉ)
    {v : Version} {s ŝ : ORSet.State} {E Ê : Set (Op ORSetOp)}
    (hv : C.ver v = some (s, E)) (hĉ : Ĉ.ver v = some (ŝ, Ê)) :
    Ê = E ∧ orRead ŝ = orRead s :=
  stability_reads_equal h hv hĉ

/-- **The OR-set stability capstone, RA-linearizability inherited**: every
version of the compacted run reads as the fold of a linearization of its own
event set — from `ORSet_ra_linearizable3` on the (genuinely `Step3`-reachable)
full projection. -/
theorem ORSet_stability_ra {S : Set (Op ORSetOp)} {K : ℕ × ℕ → Bool}
    {nt : ℕ × ℕ → ℕ × ℕ} (hcut : CutSpec S K nt)
    {C Ĉ : Configuration ORSet}
    (h : StabReach (orStabilityVC hcut) trivial C Ĉ) :
    ∀ (v : Version) (ŝ : ORSet.State) (Ê : Set (Op ORSetOp)),
      Ĉ.ver v = some (ŝ, Ê) →
      ∃ π : List (Op ORSetOp),
        listPermOf π Ê ∧
        respects π (Sal.Emulation.lo (Configuration.core Ĉ)) ∧
        orRead (applySeq ORSet.toCRDTSig ORSet.init π) = orRead ŝ :=
  stability_ra_inherited h
    (ORSet_ra_linearizable3 C (stability_simulation h).2.2)

#print axioms orStabilityVC
#print axioms ORSet_stability_reads
#print axioms ORSet_stability_ra

/-! ## §3 SPOT — hand-derived, matching `whiteboard/litmus/stability_vc_check.py`

Tags here are `(stamp, elem)` (the harness uses `(elem, stamp)`); elements
`a, b, c ↦ 10, 11, 12`. Every block is PASS+FAIL shaped; expected values are
hand-derived from the harness's directed scenarios, never `#eval`'d. -/

namespace StabilitySPOT

/-- Finite-support states from tag lists. -/
def st (l : List (ℕ × ℕ)) : ORSet.State := fun y => decide (y ∈ l)

/-- The concrete cut: adds of element `10` at stamps `1 < 2` (harness `e1`,
`e2`); the older instance `(1,10)` is droppable, kept twin `(2,10)`. -/
def Sc : Set (Op ORSetOp) :=
  {o | o = (1, 0, ORSetOp.add 10) ∨ o = (2, 1, ORSetOp.add 10)}

def Kc : ℕ × ℕ → Bool := fun y => decide (y = (1, 10))

def ntc : ℕ × ℕ → ℕ × ℕ := fun y => if y = (1, 10) then (2, 10) else y

theorem cutSpec_c : CutSpec Sc Kc ntc where
  addK y hK := by
    have hy : y = (1, 10) := of_decide_eq_true hK
    subst hy
    exact ⟨0, Or.inl rfl⟩
  addNt y hK := by
    have hy : y = (1, 10) := of_decide_eq_true hK
    subst hy
    exact ⟨1, Or.inr (by decide)⟩
  ntElem y hK := by
    have hy : y = (1, 10) := of_decide_eq_true hK
    subst hy
    decide
  ntNewer y hK := by
    have hy : y = (1, 10) := of_decide_eq_true hK
    subst hy
    decide
  ntK y hK := by
    have hy : y = (1, 10) := of_decide_eq_true hK
    subst hy
    decide

/-- Merge output tags come from the inputs (bounds the read witnesses). -/
theorem orMergeL_live {l a b : ORSet.State} {y : ℕ × ℕ}
    (h : orMergeL l a b y = true) :
    l y = true ∨ a y = true ∨ b y = true := by
  cases hl : l y with
  | true => exact Or.inl rfl
  | false =>
    cases ha : a y with
    | true => exact Or.inr (Or.inl rfl)
    | false =>
      cases hb : b y with
      | true => exact Or.inr (Or.inr rfl)
      | false =>
        unfold orMergeL at h
        rw [hl, ha, hb] at h
        exact Bool.noConfusion h

/-! ### The discriminating-remove countermodel (harness §(2)+(3))

Delivery merge at R2 against the in-flight rem's branch: LCA payload `V'`
(both adds live), R2's head (full vs naively compacted), R1's branch where the
rem killed only `t2` (it never saw `t1`). -/

/-- `V'`: the shared LCA payload, both adds live. -/
def lV : ORSet.State := st [(1, 10), (2, 10)]
/-- R2's head, naively compacted: the older instance dropped. -/
def aNaive : ORSet.State := st [(2, 10)]
/-- R1's branch: the rem killed `t2`; `a` survives through `t1`. -/
def bRem : ORSet.State := st [(1, 10)]

def mControl : ORSet.State := orMergeL lV lV bRem
def mNaive : ORSet.State := orMergeL lV aNaive bRem

/-- Control (hand-derived): `a` survives through `t1`. -/
theorem countermodel_control : mControl (1, 10) = true := by decide

/-- The naive-compacted merge kills both instances. -/
theorem countermodel_naive_dead :
    mNaive (1, 10) = false ∧ mNaive (2, 10) = false := by decide

/-- **FAIL pin (the countermodel fires)**: reads DIVERGE under the naive
gate — control reads `{a}`, the compacted run reads `∅` (harness verdict
`['a']` vs `[]`). -/
theorem countermodel_diverges : orRead mControl 10 ∧ ¬ orRead mNaive 10 := by
  constructor
  · exact ⟨1, by decide⟩
  · rintro ⟨ts, h⟩
    have hts : ts = 1 ∨ ts = 2 := by
      rcases orMergeL_live h with hl | ha | hb
      · have hmem : ((ts, 10) : ℕ × ℕ) ∈ [((1:ℕ), (10:ℕ)), (2, 10)] :=
          of_decide_eq_true hl
        rcases List.mem_cons.mp hmem with h1 | h1
        · exact Or.inl (congrArg Prod.fst h1)
        · exact Or.inr (congrArg Prod.fst (List.mem_singleton.mp h1))
      · have hmem : ((ts, 10) : ℕ × ℕ) ∈ [((2:ℕ), (10:ℕ))] :=
          of_decide_eq_true ha
        exact Or.inr (congrArg Prod.fst (List.mem_singleton.mp hmem))
      · have hmem : ((ts, 10) : ℕ × ℕ) ∈ [((1:ℕ), (10:ℕ))] :=
          of_decide_eq_true hb
        exact Or.inl (congrArg Prod.fst (List.mem_singleton.mp hmem))
    rcases hts with rfl | rfl
    · rw [countermodel_naive_dead.1] at h
      cases h
    · rw [countermodel_naive_dead.2] at h
      cases h

/-! ### The settled path (harness `test_countermodel_settled`) -/

/-- The compaction point once the rem is absorbed: only `t1` lives. -/
def sAfterRem : ORSet.State := st [(1, 10)]

/-- **PASS pin (correct refusal)**: with the kept twin dead, the callback
drops NOTHING (harness: "rem already applied: only t1 lives, nothing
redundant"). -/
theorem settled_refusal : orCompactC Kc ntc sAfterRem (1, 10) = true := by
  decide

/-- The refusal is total: the compacted state is the state itself. -/
theorem settled_refusal_id : orCompactC Kc ntc sAfterRem = sAfterRem := by
  funext y
  by_cases hy : y = (1, 10)
  · subst hy
    decide
  · exact orCompactC_off _ (decide_eq_false hy)

/-- **FAIL companion**: the *static* drop (the tempting twin-blind callback)
loses the element at the very same state. -/
def orCompactStatic (K : ℕ × ℕ → Bool) (s : ORSet.State) : ORSet.State :=
  fun y => s y && !(K y)

theorem static_drop_unsound :
    orCompactStatic Kc sAfterRem (1, 10) = false ∧
      ¬ orRead (orCompactStatic Kc sAfterRem) 10 := by
  refine ⟨by decide, ?_⟩
  rintro ⟨ts, h⟩
  have hs : sAfterRem (ts, 10) = true := (Bool.and_eq_true_iff.mp h).1
  have hmem : ((ts, 10) : ℕ × ℕ) ∈ [((1:ℕ), (10:ℕ))] := of_decide_eq_true hs
  have hts : ts = 1 := congrArg Prod.fst (List.mem_singleton.mp hmem)
  subst hts
  rw [show orCompactStatic Kc sAfterRem (1, 10) = false from by decide] at h
  cases h

/-! ### The mixed merge (VC-S4; harness `test_vc_s4_argumentwise`)

R0's compacted head (`A`-position) merges against the full stored LCA payload
and the full sibling; hand-derived: control `{t1,t2,t3,t4}`, treatment
`{t2,t3,t4}` — exactly the compacted control. -/

def lS4 : ORSet.State := st [(1, 10), (2, 10)]
def aS4full : ORSet.State := st [(1, 10), (2, 10), (3, 11)]
def aS4comp : ORSet.State := st [(2, 10), (3, 11)]
def bS4 : ORSet.State := st [(1, 10), (2, 10), (4, 12)]

def mS4 : ORSet.State := orMergeL lS4 aS4full bS4
def mS4c : ORSet.State := orMergeL lS4 aS4comp bS4

/-- The compacted `A`-argument is a genuine callback image. -/
theorem s4_entry : aS4comp = orCompactC Kc ntc aS4full := by
  funext y
  by_cases hy : y = (1, 10)
  · subst hy
    decide
  · rw [orCompactC_off _ (decide_eq_false hy)]
    show decide _ = decide _
    by_cases h2 : y ∈ [((2:ℕ), (10:ℕ)), (3, 11)]
    · rw [decide_eq_true h2, decide_eq_true (List.mem_cons_of_mem _ h2)]
    · rw [decide_eq_false h2, decide_eq_false (fun hmem => by
        rcases List.mem_cons.mp hmem with h | h
        · exact hy h
        · exact h2 h)]

/-- **PASS pin (VC-S4, mixed merge)**: the compacted-side merge IS the
callback image of the control merge — pointwise at every tag. -/
theorem s4_vc : mS4c = orCompactC Kc ntc mS4 := by
  funext y
  by_cases hy : y = (1, 10)
  · subst hy
    decide
  · rw [orCompactC_off _ (decide_eq_false hy)]
    show orMergeL lS4 aS4comp bS4 y = orMergeL lS4 aS4full bS4 y
    have ha : aS4comp y = aS4full y := by
      show decide _ = decide _
      by_cases h2 : y ∈ [((2:ℕ), (10:ℕ)), (3, 11)]
      · rw [decide_eq_true h2, decide_eq_true (List.mem_cons_of_mem _ h2)]
      · rw [decide_eq_false h2, decide_eq_false (fun hmem => by
          rcases List.mem_cons.mp hmem with h | h
          · exact hy h
          · exact h2 h)]
    unfold orMergeL
    rw [ha]

/-- The drop propagates like a deletion, and reads match the control at every
element (harness: both read `{a,b,c}`; `(a,1)` gone from the treatment). -/
theorem s4_values :
    mS4 (1, 10) = true ∧ mS4c (1, 10) = false ∧ mS4c (2, 10) = true ∧
      mS4c (3, 11) = true ∧ mS4c (4, 12) = true := by decide

theorem s4_reads_equal : orRead mS4c = orRead mS4 := by
  rw [s4_vc, orRead_compactC cutSpec_c]

#print axioms cutSpec_c
#print axioms countermodel_diverges
#print axioms settled_refusal_id
#print axioms static_drop_unsound
#print axioms s4_vc
#print axioms s4_reads_equal

end StabilitySPOT

end Sal.ConditionedMRDTs
