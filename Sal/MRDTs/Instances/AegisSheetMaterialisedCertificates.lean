import Sal.MRDTs.Instances.AegisSheetMaterialisedJoin

/-!
# Issuance and replay adequacy for the materialised AegisSheet

The issuance predicate checks, at the issuer's materialised state, that a
removal names exactly the live tokens of its identifier, that a write names
active versions of its cell, that a range edit names active versions of its
range, that a purge covers versions present at its coordinates, and the D1
clause: a cell write, direct or inverse, requires both axes live. Honesty of
every replay context reached by issued operations follows by fold provenance:
an entry present in the issuer's state was added by an event of its causal
past. The replay-adequacy certificate is then `ofJoinOn` with the Join of the
previous file.
-/

namespace Sal.MRDTs.Instances.AegisSheet.Materialised

open Sal.MRDTs.Foundation

/-! ## Fold provenance -/

variable {α : Type} [DecidableEq α] (N : NR α)

/-- Every entry of a fold's component was added by some element. -/
theorem NR.fold_adds (proj : MState → Finset α)
    (hinit : proj MState.empty = ∅)
    (hstep : ∀ s e, proj (mupdate s e) = N.step (proj s) e) :
    ∀ ρ : List MEvent, ∀ x ∈ proj (applySeq M.toUpdateSig M.init ρ), ∃ k ∈ ρ, x ∈ N.adds k := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
    intro x hx
    simp [applySeq, M, hinit] at hx
  | append_singleton ρ e ih =>
    intro x hx
    have hstep' : applySeq M.toUpdateSig M.init (ρ ++ [e])
        = mupdate (applySeq M.toUpdateSig M.init ρ) e := by
      unfold applySeq
      rw [List.foldl_append]
      rfl
    rw [hstep', hstep] at hx
    simp only [NR.step, Finset.mem_union, Finset.mem_filter, List.mem_toFinset] at hx
    rcases hx with ⟨hx, _⟩ | hx
    · obtain ⟨k, hk, hxk⟩ := ih x hx
      exact ⟨k, List.mem_append_left _ hk, hxk⟩
    · exact ⟨e, List.mem_append_right _ (List.mem_singleton_self e), hx⟩

/-! ## The issuance predicate -/

/-- Live tokens of an identifier at a state. -/
def liveTokensOf (s : MState) (axis : Axis) (id : StableId) : Finset Timestamp :=
  (s.tokens.filter fun x => x.1 = axis ∧ x.2.1 = id).image fun x => x.2.2

/-- Active version timestamps of a cell at a state. -/
def activeCellTimesOf (s : MState) (row column : StableId) : Finset Timestamp :=
  (s.cells.filter fun v => v.1 = row ∧ v.2.1 = column).image fun v => v.2.2.1

/-- Active version timestamps of a range at a state. -/
def activeRangeTimesOf (s : MState) (id : RangeId) : Finset Timestamp :=
  (s.ranges.filter fun v => v.1 = id).image fun v => v.2.1

/-- Allocation survives retirement of `known`: the retained position also
records that the identifier has already been used. -/
def allocated (s : MState) (axis : Axis) (id : StableId) : Prop :=
  (axis, id) ∈ s.known ∨ ∃ p ∈ s.pos, posKey p = (axis, id)

/-- The effect clauses of the issuer's guard, by the effect of the operation:
a removal names exactly the live tokens of its identifier; every other
operation names no token; an insert must be unallocated even after retirement.
A write names the active versions of its cell and requires both axes live
(D1); a range edit names the active versions of its range. A purge covers
present versions, has valid cutoff/coordinate metadata, and names only dead
coordinates. Neither a roster nor a designated issuer is required. -/
def mEffect (e : MEvent) (s : MState) : Prop :=
  match MEvent.action e with
  | .axis u =>
      match u.after with
      | none =>
          mLive s u.axis u.id = true ∧ e.2.2.kills = liveTokensOf s u.axis u.id
      | some _ =>
          e.2.2.kills = ∅ ∧
            (u.kind = .insert → ¬ allocated s u.axis u.id) ∧
            (u.kind = .move → mLive s u.axis u.id = true)
  | .cell u =>
      mLive s .row u.row = true ∧ mLive s .column u.column = true ∧
        u.overwrites = activeCellTimesOf s u.row u.column ∧ e.2.2.kills = ∅
  | .range u => u.overwrites = activeRangeTimesOf s u.id ∧ e.2.2.kills = ∅
  | .purge m =>
      (∀ entry ∈ m.covered, ∃ v ∈ s.cells, (v.1, v.2.1) = entry.2 ∧ v.2.2.1 = entry.1) ∧
        e.2.2.kills = ∅ ∧ m.validB = true ∧
        (∀ coordinate ∈ m.coordinates,
          mLive s .row coordinate.1 = false ∨ mLive s .column coordinate.2 = false)

/-- The before-image clauses of a direct command, decided at the materialised
state: the union model's guards `currentAxisPositions`, `cellValues`, and
`rangeValues` read through the materialised observers. -/
def mBefore (s : MState) : Action → Prop
  | .axis u =>
      match u.kind with
      | .insert => u.before = none ∧ u.after.isSome = true
      | .move =>
          mPositions s u.axis u.id = optionFinset u.before ∧ u.before.isSome = true ∧
            u.after.isSome = true
      | .remove =>
          mPositions s u.axis u.id = optionFinset u.before ∧ u.before.isSome = true ∧
            u.after = none
      | .restore => False
  | .cell u => mCellValues s u.row u.column = u.before
  | .range u => mRangeValues s u.id = optionFinset u.before
  | .purge _ => True

/-- The issuer's guard: the effect clauses, and for a direct command its
before-image clauses. An undo carries no before-image clause here; its
validity against the issuer's log is the separate premise `UndoHonest` of the
converse theorem. -/
def mApplicable (e : MEvent) (s : MState) : Prop :=
  mEffect e s ∧
    match e.2.2.command with
    | .direct a => mBefore s a
    | .undo _ _ => True

instance (e : MEvent) (s : MState) : Decidable (mApplicable e s) := by
  unfold mApplicable mEffect mBefore allocated
  repeat' first | infer_instance | split

def generation : Issuance M where
  CanIssue := mApplicable

/-! ## Mint honesty implies the honesty of the replay context -/

section Bridge
variable {C : Configuration M}

/-- The causal past of `e`, as a set. -/
private def past (C : Configuration M) (e : MEvent) : Set MEvent :=
  {e' ∈ C.events | C.vis e' e}

theorem honest_of_mint (h : MintHonest M mApplicable C) :
    Honest (Configuration.replayContext C) where
  kills_seen := by
    intro e he u hu hafter t ht
    rw [Configuration.replayContext_events] at he
    obtain ⟨π, hperm, _, hg⟩ := h e he
    have hg' : mEffect e (applySeq M.toUpdateSig M.init π) := hg.1
    unfold mEffect at hg'
    simp only [hu, hafter] at hg'
    obtain ⟨_, hkills⟩ := hg'
    rw [hkills] at ht
    simp only [liveTokensOf, Finset.mem_image, Finset.mem_filter] at ht
    obtain ⟨x, ⟨hxs, hx1, hx2⟩, hxt⟩ := ht
    obtain ⟨k, hkπ, hxk⟩ :=
      tokNR.fold_adds MState.tokens tokens_init tokens_step π x hxs
    have hkpast : k ∈ C.events ∧ C.vis k e := (hperm.2 k).mp hkπ
    refine ⟨k, ?_, ?_, hkpast.2, ?_⟩
    · rw [Configuration.replayContext_events]; exact hkpast.1
    · rw [← hxt]; exact (tokAdds_ts k x hxk).symm
    · -- the adder keeps the identifier
      have hxk' : x ∈ tokAdds k := hxk
      unfold tokAdds at hxk'
      cases hk : MEvent.action k with
      | axis v =>
        simp only [hk] at hxk'
        cases hv : v.after with
        | none => simp [hv] at hxk'
        | some p =>
          simp only [hv, Option.isSome_some, if_true, List.mem_singleton] at hxk'
          left
          refine ⟨v, rfl, ?_, ?_, by rw [hv]; rfl⟩
          · rw [← hx1, hxk']
          · rw [← hx2, hxk']
      | cell w =>
        simp only [hk] at hxk'
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hxk'
        right
        refine ⟨w, rfl, ?_⟩
        rcases hxk' with hxk' | hxk'
        · have ha : u.axis = Axis.row := by rw [← hx1, hxk']
          rw [ha]
          rw [← hx2, hxk']
        · have ha : u.axis = Axis.column := by rw [← hx1, hxk']
          rw [ha]
          rw [← hx2, hxk']
      | range _ => simp [hk] at hxk'
      | purge _ => simp [hk] at hxk'
  overwrites_seen := by
    intro e he u hu t ht
    rw [Configuration.replayContext_events] at he
    obtain ⟨π, hperm, _, hg⟩ := h e he
    have hg' : mEffect e (applySeq M.toUpdateSig M.init π) := hg.1
    unfold mEffect at hg'
    rw [hu] at hg'
    obtain ⟨_, _, hov, _⟩ := hg'
    rw [hov] at ht
    simp only [activeCellTimesOf, Finset.mem_image, Finset.mem_filter] at ht
    obtain ⟨v, ⟨hvs, hv1, hv2⟩, hvt⟩ := ht
    obtain ⟨k, hkπ, hvk⟩ :=
      cellNR.fold_adds MState.cells cells_init cells_step π v hvs
    have hkpast : k ∈ C.events ∧ C.vis k e := (hperm.2 k).mp hkπ
    refine ⟨k, ?_, ?_, hkpast.2, ?_⟩
    · rw [Configuration.replayContext_events]; exact hkpast.1
    · rw [← hvt]; exact (cellAdds_ts k v hvk).symm
    · have hvk' : v ∈ cellAdds k := hvk
      unfold cellAdds at hvk'
      cases hk : MEvent.action k with
      | cell w =>
        simp only [hk] at hvk'
        simp only [List.mem_singleton] at hvk'
        refine ⟨w, rfl, ?_, ?_⟩
        · rw [← hv1, hvk']
        · rw [← hv2, hvk']
      | axis _ => simp only [hk] at hvk'; simp at hvk'
      | range _ => simp only [hk] at hvk'; simp at hvk'
      | purge _ => simp only [hk] at hvk'; simp at hvk'
  range_overwrites_seen := by
    intro e he u hu t ht
    rw [Configuration.replayContext_events] at he
    obtain ⟨π, hperm, _, hg⟩ := h e he
    have hg' : mEffect e (applySeq M.toUpdateSig M.init π) := hg.1
    unfold mEffect at hg'
    rw [hu] at hg'
    rw [hg'.1] at ht
    simp only [activeRangeTimesOf, Finset.mem_image, Finset.mem_filter] at ht
    obtain ⟨v, ⟨hvs, hv1⟩, hvt⟩ := ht
    obtain ⟨k, hkπ, hvk⟩ :=
      rangeNR.fold_adds MState.ranges ranges_init ranges_step π v hvs
    have hkpast : k ∈ C.events ∧ C.vis k e := (hperm.2 k).mp hkπ
    refine ⟨k, ?_, ?_, hkpast.2, ?_⟩
    · rw [Configuration.replayContext_events]; exact hkpast.1
    · rw [← hvt]; exact (rangeAdds_ts k v hvk).symm
    · have hvk' : v ∈ rangeAdds k := hvk
      unfold rangeAdds at hvk'
      cases hk : MEvent.action k with
      | range w =>
        simp only [hk] at hvk'
        simp only [List.mem_singleton] at hvk'
        exact ⟨w, rfl, by rw [← hv1, hvk']⟩
      | axis _ => simp only [hk] at hvk'; simp at hvk'
      | cell _ => simp only [hk] at hvk'; simp at hvk'
      | purge _ => simp only [hk] at hvk'; simp at hvk'
  covered_seen := by
    intro e he m hm entry hentry
    rw [Configuration.replayContext_events] at he
    obtain ⟨π, hperm, _, hg⟩ := h e he
    have hg' : mEffect e (applySeq M.toUpdateSig M.init π) := hg.1
    unfold mEffect at hg'
    rw [hm] at hg'
    obtain ⟨v, hvs, hvc, hvt⟩ := hg'.1 entry hentry
    obtain ⟨k, hkπ, hvk⟩ :=
      cellNR.fold_adds MState.cells cells_init cells_step π v hvs
    have hkpast : k ∈ C.events ∧ C.vis k e := (hperm.2 k).mp hkπ
    refine ⟨k, ?_, ?_, hkpast.2, ?_⟩
    · rw [Configuration.replayContext_events]; exact hkpast.1
    · rw [← hvt]; exact (cellAdds_ts k v hvk).symm
    · have hvk' : v ∈ cellAdds k := hvk
      unfold cellAdds at hvk'
      cases hk : MEvent.action k with
      | cell w =>
        simp only [hk] at hvk'
        simp only [List.mem_singleton] at hvk'
        refine ⟨w, rfl, ?_⟩
        rw [← hvc, hvk']
      | axis _ => simp only [hk] at hvk'; simp at hvk'
      | range _ => simp only [hk] at hvk'; simp at hvk'
      | purge _ => simp only [hk] at hvk'; simp at hvk'

end Bridge

/-- Issued executions establish the honesty predicate. -/
theorem issuanceEstablishes : IssuanceEstablishes M generation Honest :=
  fun _ hMint => honest_of_mint hMint

/-- **Replay adequacy of the materialised sheet**, for ordinary and
virtual-merge-base executions issued under `generation`. -/
def replayAdequacy : ReplayAdequacyCertificate M generation :=
  ReplayAdequacyCertificate.ofJoinOn m_joinOn issuanceEstablishes

#print axioms replayAdequacy

/-! ## The verification package -/

/-- The datatype's own sequential machine: the fold of `mupdate`, every list
legal, observation through `mview`. The certificate built on it records
convergence of every version to this fold. What the fold means in union-model
terms is `Issued.fold` with `observationEquivalence`
(`AegisSheetMaterialisedUpdate.lean`, `AegisSheetMaterialisedBridge.lean`). -/
def spec : SequentialSpec M where
  State := MState
  init := MState.empty
  step := mupdate
  Legal := fun _ => True
  query := fun s _ => mview s

noncomputable def verified : VerifiedMRDT M where
  issuance := generation
  interaction := InteractionSpec.raw M
  replayAdequacy := replayAdequacy
  Spec := spec
  Rel := (· = ·)
  sequentialCorrectness := SequentialCorrectnessCertificate.ofTotal
    (fun _ => True.intro) (fun _ => rfl) (fun _ _ => rfl)

#print axioms verified

end Sal.MRDTs.Instances.AegisSheet.Materialised
