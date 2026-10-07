import Sal.MRDTs.Paper1.CertifiedFugueRawOrderObstruction
import Sal.MRDTs.Paper1.CertifiedFugueInvariantReplay

/-! The original Fugue issuer permits insertion naming a deleted birth. The
independent live-anchor language distinguishes its order with that deletion.
This obstruction uses specification visibility alone, for every state domain. -/
namespace Sal.MRDTs.Paper1.CertifiedFugueInvariantObstruction
open Foundation Sal.EmbedRGA
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax
open CertifiedFugueRawOrderObstruction
attribute [local instance] Instances.SidedEmbedRGA.FugueMax.rc

private theorem allOps_enum : listPermOf allOps (↑((indices 3).image event) : Set Event) := by
  refine ⟨by decide,?_⟩
  intro e
  simp only [allOps,List.mem_cons,List.not_mem_nil,or_false,Finset.mem_coe,Finset.mem_image]
  constructor
  · intro h
    rcases h with rfl|rfl|rfl <;> exact ⟨_,by decide,rfl⟩
  · rintro ⟨i,_,rfl⟩
    fin_cases i <;> simp

private theorem list_legal_prefix (pre suf : KnowM) (legal : listLegal (pre++suf)) : listLegal pre := by
  obtain ⟨nd,positive,checks⟩ := legal
  refine ⟨?_,?_,?_⟩
  · exact (List.nodup_append.mp (by simpa only [List.map_append] using nd)).1
  · intro g hg
    exact positive g (List.mem_append_left _ hg)
  · intro before g after split
    exact checks before g (after++suf) (by simp only [split,List.append_assoc,List.cons_append])

private theorem spec_legal_prefix (pre suf : List Event)
    (legal : (listSpec unaryCode).Legal (pre++suf)) : (listSpec unaryCode).Legal pre := by
  exact list_legal_prefix (pre.map recordOf) (suf.map recordOf)
    (by simpa only [listSpec,List.map_append] using legal)

private theorem empty_legal : (listSpec unaryCode).Legal [] := by
  simp [listSpec,listLegal]

private theorem finite_history_rejection : ∀π∈allOps.permutations',
    respects π required → ¬(listSpec unaryCode).Legal π := by
  unfold respects
  decide +kernel

theorem good_history_admitted :
    (GuardedHistory.language (listSpec unaryCode)).admits
      (projectedLabels id goodHistory ++ [.query () [3]]) := by
  apply (GuardedHistory.admits_updates_query_iff (listSpec unaryCode)
    empty_legal spec_legal_prefix goodHistory () [3]).mpr
  constructor
  · decide +kernel
  · change [3] = ((listRun (goodHistory.map recordOf)).filter (fun p => p.1 != 0)).map Prod.fst
    decide +kernel

theorem deletion_replacement_spec_conflict :
    ¬ (GuardedHistory.language (listSpec unaryCode)).Commutes (event 1) (event 2) := by
  intro comm
  have accepted := good_history_admitted
  have bad := (comm [.update (event 0)] [.query () [3]]).mpr accepted
  have decoded := (GuardedHistory.admits_updates_query_iff (listSpec unaryCode)
    empty_legal spec_legal_prefix allOps () [3]).mp bad
  have illegal : ¬ (listSpec unaryCode).Legal allOps := by decide +kernel
  exact illegal decoded.1

theorem required_specVisibility : ∀ a b, required a b →
    projectedSpecVisibility id (GuardedHistory.language (listSpec unaryCode))
      (config 3).replayContext a b := by
  rintro a b ⟨rfl,rfl⟩
  exact ⟨by change vis 3 (event 1) (event 2); decide,
    deletion_replacement_spec_conflict⟩

theorem no_spec_visible_history (answer : List Nat) :
    ¬ ∃ π : List Event, listPermOf π (↑((indices 3).image event) : Set Event) ∧
      respects π (projectedSpecVisibility id (GuardedHistory.language (listSpec unaryCode))
        (config 3).replayContext) ∧
      (GuardedHistory.language (listSpec unaryCode)).admits
        (projectedLabels id π ++ [.query () answer]) := by
  rintro ⟨π,perm,ordered,admitted⟩
  have permutation : π.Perm allOps :=
    (List.perm_ext_iff_of_nodup perm.1 allOps_enum.1).mpr
      (fun e => (perm.2 e).trans (allOps_enum.2 e).symm)
  have requiredOrder : respects π required := ordered.imp fun {_ _} no edge =>
    no (required_specVisibility _ _ edge)
  have decoded := (GuardedHistory.admits_updates_query_iff (listSpec unaryCode)
    empty_legal spec_legal_prefix π () answer).mp admitted
  exact finite_history_rejection π (List.mem_permutations'.mpr permutation) requiredOrder decoded.1

theorem no_invariant_criterion (Inv : State → Prop) (P : OperationPolicy Payload) :
    ¬ InvariantOrder.VersionsRA RGAM Inv P
      (GuardedHistory.language (listSpec unaryCode)) (config 3) := by
  intro witness
  obtain ⟨π,perm,_,ordered,admitted⟩ := witness 3 (records 3).1
    (↑((indices 3).image event) : Set Event) (by rfl) ()
  exact no_spec_visible_history _ ⟨π,perm,ordered,admitted⟩

theorem certified_failure (Inv : State → Prop) (P : OperationPolicy Payload) :
    MintCertifiedReach RGAM issuance (config 3) ∧
    ¬ InvariantOrder.VersionsRA RGAM Inv P
      (GuardedHistory.language (listSpec unaryCode)) (config 3) :=
  ⟨mint_certified,no_invariant_criterion Inv P⟩

abbrev valid := CertifiedFugueInvariant.Valid unaryCode (config 3).replayContext

/-- All concrete states of the original three-step execution belong to the
independently justified invariant domain, including the deleted-anchor state. -/
theorem trace_states_valid (v : V) : valid (state v) := by
  apply CertifiedFugueInvariant.stored_valid unaryCode (.ordinary mint_certified)
    (v := v.val) (H := (↑((indices v).image event) : Set Event))
  fin_cases v <;> rfl

theorem domain_closed : InvariantOrder.Closed RGAM (config 3).replayContext valid := by
  have good := CertifiedFugueVCExecution.canonicalConfig unaryCode (.ordinary mint_certified)
  exact CertifiedFugueInvariant.closed unaryCode (config 3) (mint_honest 3)
    (fun _ _ _ h k => good.vis_trans h k)

private theorem supported (i : I) : event i ∈ (config 3).events := by
  refine ⟨0,(↑((indices 3).image event) : Set Event),?_,?_⟩
  · rfl
  · exact Finset.mem_image.mpr ⟨i,by fin_cases i <;> decide,rfl⟩

/-- The implementation issue is fixed: the relevant effectors commute on all
valid states. The original sequential language still distinguishes the orders. -/
theorem implementation_spec_separation :
    InvariantOrder.Commutes RGAM.toUpdateSig valid (event 1) (event 2) ∧
    ¬ (GuardedHistory.language (listSpec unaryCode)).Commutes (event 1) (event 2) := by
  refine ⟨?_,deletion_replacement_spec_conflict⟩
  have good := CertifiedFugueVCExecution.canonicalConfig unaryCode (.ordinary mint_certified)
  apply (CertifiedFugueInvariant.invariant_commutes_iff unaryCode (config 3)
    (mint_honest 3) (fun _ _ _ h k => good.vis_trans h k)
    (event 1) (event 2) (supported 1) (supported 2)).mpr
  change (3 : Nat) ≠ 1
  decide

/-- PASS+FAIL: the independent list admits the reordered result, but the full
criterion cannot admit this original certified execution, in a closed domain. -/
theorem valid_execution_counterexample :
    MintCertifiedReach RGAM issuance (config 3) ∧
    (∀v : V,valid (state v)) ∧
    InvariantOrder.Closed RGAM (config 3).replayContext valid ∧
    RGAM.query (state 3) () = [3] ∧ RGAM.query (state 3) () ≠ [] ∧
    (GuardedHistory.language (listSpec unaryCode)).admits
      (projectedLabels id goodHistory ++ [.query () [3]]) ∧
    ¬ InvariantOrder.VersionsRA RGAM valid (commutingPolicy Payload)
      (GuardedHistory.language (listSpec unaryCode)) (config 3) :=
  ⟨mint_certified,trace_states_valid,domain_closed,final_read.1,final_read.2,
    good_history_admitted,no_invariant_criterion valid _⟩

#print axioms domain_closed
#print axioms trace_states_valid
#print axioms implementation_spec_separation
#print axioms valid_execution_counterexample
#print axioms deletion_replacement_spec_conflict
#print axioms no_spec_visible_history
#print axioms certified_failure
end Sal.MRDTs.Paper1.CertifiedFugueInvariantObstruction
