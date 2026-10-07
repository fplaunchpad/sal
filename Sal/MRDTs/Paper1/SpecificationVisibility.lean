import Sal.MRDTs.Paper1.Soundness

/-!
# Independent specification-conflict visibility

The active ralin.tex definition omits this condition. An excluded manuscript
source file also discusses it; it is not an appendix of the included paper.
These declarations keep the stronger candidate separate from `RALinearizable`, so strengthening the
criterion cannot silently change the result being mechanized. Commutation is
defined by contextual swaps in the independent history language, rather than by
an implementation state or event timestamp.
-/

namespace Sal.MRDTs.Paper1
open Foundation

def HistorySpec.Commutes {U Q V : Type} (S : HistorySpec U Q V) (a b : U) : Prop :=
  ∀ pre suf,
    S.admits (pre ++ [.update a, .update b] ++ suf) ↔
    S.admits (pre ++ [.update b, .update a] ++ suf)

theorem HistorySpec.commutes_symm {U Q V : Type} {S : HistorySpec U Q V}
    {a b : U} (h : S.Commutes a b) : S.Commutes b a :=
  fun pre suf => (h pre suf).symm

theorem HistoryMachine.commutes_of_diamond {U Q V : Type} (M : HistoryMachine U Q V)
    (a b : U)
    (diamond : ∀ s t,
      Runs M.transition s [.update a, .update b] t ↔
      Runs M.transition s [.update b, .update a] t) : M.toSpec.Commutes a b := by
  intro pre suf
  have exchange : ∀ (x y : U),
      (∀ s t, Runs M.transition s [.update x, .update y] t →
        Runs M.transition s [.update y, .update x] t) →
      M.toSpec.admits (pre ++ [.update x, .update y] ++ suf) →
      M.toSpec.admits (pre ++ [.update y, .update x] ++ suf) := by
    intro x y swap accepted
    obtain ⟨final, run⟩ := accepted
    have grouped : Runs M.transition M.initial
        (pre ++ ([.update x, .update y] ++ suf)) final := by
      simpa only [List.append_assoc] using run
    obtain ⟨s, hp, rest⟩ := grouped.split pre ([.update x, .update y] ++ suf)
    obtain ⟨t, pair, hs⟩ := rest.split [.update x, .update y] suf
    exact ⟨final, by simpa only [List.append_assoc] using
      (hp.append ((swap s t pair).append hs))⟩
  exact ⟨exchange a b (fun s t => (diamond s t).mp),
    exchange b a (fun s t => (diamond s t).mpr)⟩

theorem DeterministicSpec.language_commutes {U Q V : Type}
    (M : DeterministicSpec U Q V) (a b : U)
    (commute : ∀ s, M.update (M.update s a) b = M.update (M.update s b) a) :
    M.toSpec.Commutes a b := by
  apply M.machine.commutes_of_diamond a b
  intro s t
  have pair : ∀ x y : U,
      Runs M.machine.transition s [.update x, .update y] t ↔
      t = M.update (M.update s x) y := by
    intro x y
    constructor
    · intro h
      cases h with
      | cons hx rest =>
          cases rest with
          | cons hy rest =>
              cases rest
              change _ = M.update s x at hx
              change _ = M.update _ y at hy
              simpa only [hx] using hy
    · intro h
      subst t
      exact .cons rfl (.cons rfl (.nil _))
  rw [pair a b, pair b a, commute]

def specVisibility {D : MRDTSig} (S : HistorySpec D.AppOp D.Query D.Value)
    (C : ReplayContext D.toUpdateSig) (a b : Op D.AppOp) : Prop :=
  C.vis a b ∧ ¬ S.Commutes a.op b.op

/-- Separate candidate criterion: each witness
must preserve independent specification conflicts as well as `loOn`. -/
def SpecificationRALinearizable (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ r v s E, C.head r = some v → C.ver v = some (s, E) →
    ∀ q, ∃ π : List (Op D.AppOp),
      listPermOf π E ∧ respects π (paperOrder P C.replayContext E) ∧
      respects π (specVisibility S C.replayContext) ∧
      S.admits (projectedUpdates π ++ [.query q (D.query s q)])

theorem SpecificationRALinearizable.active {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {C : Configuration D}
    (h : SpecificationRALinearizable D P S C) : RALinearizable D P S C := by
  intro r v s E hh hv q
  obtain ⟨π, hp, hr, _, ha⟩ := h r v s E hh hv q
  exact ⟨π, hp, hr, ha⟩

/-- A sufficient sequential bridge premise: implementation commutation must
not erase an independent specification conflict. -/
def SpecificationConflictsCovered (D : MRDTSig)
    (S : HistorySpec D.AppOp D.Query D.Value) : Prop :=
  ∀ a b : Op D.AppOp, ¬ S.Commutes a.op b.op → ¬ D.toUpdateSig.commutes a b

theorem specVisibility_sub_paperOrder {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} (covered : SpecificationConflictsCovered D S)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (a b : Op D.AppOp)
    (h : specVisibility S C a b) : paperOrder P C E a b :=
  Or.inl ⟨h.1, covered a b h.2⟩

theorem specificationRA_of_replay_total {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {C : Configuration D}
    (laws : RestrictedLaws D.toUpdateSig P)
    (replay : @HasReplayWitness D P.lift C)
    (covered : SpecificationConflictsCovered D S) (sound : FoldHistorySound D S) :
    SpecificationRALinearizable D P S C := by
  intro r v s E hh hv q
  obtain ⟨π, hp, hr, accepted⟩ := ra_of_replay_total laws replay sound v s E hv q
  exact ⟨π, hp, hr, hr.imp (fun {_ _} h => h ∘ specVisibility_sub_paperOrder covered _ E _ _),
    accepted⟩

theorem specificationRA_of_canonical_total {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {C : Configuration D}
    (laws : RestrictedLaws D.toUpdateSig P)
    (canonical : @CanonicalConfig D P.lift C)
    (covered : SpecificationConflictsCovered D S) (sound : FoldHistorySound D S) :
    SpecificationRALinearizable D P S C := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  exact specificationRA_of_replay_total laws (hasReplayWitness_of_canonical canonical)
    covered sound

/-- An alternative to global specification-conflict coverage: use issuance
and execution evidence to choose a replay respecting both relations. This is a
sequential fold premise on event sets, not a restatement about stored states. -/
def IssuedSpecificationHistoryAdequacy (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value) (I : Issuance D) : Prop :=
  ∀ C, MintHonest D I.CanIssue C →
    ∀ E : Set (Op D.AppOp),
      (∀ e ∈ E, e ∈ C.events) →
      (∀ a b, C.vis a b → b ∈ E → a ∈ E) →
      (∃ π, listPermOf π E) →
      ∀ q, ∃ π : List (Op D.AppOp),
        listPermOf π E ∧ respects π (paperOrder P C.replayContext E) ∧
        respects π (specVisibility S C.replayContext) ∧
        S.admits (projectedUpdates π ++
          [.query q (D.query (applySeq D.toUpdateSig D.init π) q)])

theorem specificationRA_of_canonical_issued {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {I : Issuance D} {C : Configuration D}
    (laws : RestrictedLaws D.toUpdateSig P) (canonical : @CanonicalConfig D P.lift C)
    (honest : MintHonest D I.CanIssue C)
    (adequacy : IssuedSpecificationHistoryAdequacy D P S I) :
    SpecificationRALinearizable D P S C := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  intro r v s E _ hv q
  have hs := canonical.canonical v s E hv
  obtain ⟨π, hp, hr, specResp, accepted⟩ := adequacy C honest E
    (canonical.version_events_supported v s E hv)
    (canonical.version_events_causal v s E hv)
    (by obtain ⟨w, hw, _, _⟩ := hs; exact ⟨w, hw⟩) q
  have hresp : respects π (@loOn D.toUpdateSig P.lift C.replayContext E) :=
    hr.imp (fun {_ _} h => h ∘ (paperOrder_iff_loOn laws _ _ _ _).mpr)
  have heq := isCanonicalState_unique_of_replayLaws laws.replayLaws
    (canonical.version_events_supported v s E hv)
    hs ⟨π, hp, hresp, rfl⟩
  exact ⟨π, hp, hr, specResp, by simpa [heq] using accepted⟩

theorem specificationCertifiedRA_of_join_issued
    {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {I : Issuance D}
    (laws : RestrictedLaws D.toUpdateSig P)
    (join : ∀ C, MintHonest D I.CanIssue C → @JoinAt D P.lift C.replayContext)
    (history : IssuedSpecificationHistoryAdequacy D P S I)
    {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    SpecificationRALinearizable D P S C := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  exact specificationRA_of_canonical_issued laws
    (canonicalConfig_of_mintCertifiedV join reach) reach.mintHonest history

end Sal.MRDTs.Paper1
