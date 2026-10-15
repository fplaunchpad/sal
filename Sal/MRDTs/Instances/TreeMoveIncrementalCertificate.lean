import Sal.MRDTs.Instances.TreeMoveIncrementalMRDT
import Sal.MRDTs.Paper1.Automation.CertifiedOriginBridge
import Sal.MRDTs.Paper1.CertifiedHistoryDecoding

/-! The incremental log/tree implementation retains the independent in-place
tree machine and source forest/trash client legality. Five-VC replay
provenance is separate from the sequential meaning of query answers. -/
namespace Sal.MRDTs.Instances.TreeMove.Incremental
open Sal.MRDTs.Foundation
open Sal.MRDTs.Paper1
open Classical

/-- Independent sequential language: natural tree transitions, sorted distinct
events, and a causal origin satisfying the explicit editor wrapper. No tree
visibility, rendering, implementation state, or requested answer occurs here. -/
def SourceClientLegal (ops : List Event) : Prop :=
  SequentialLegal ops ∧
  ∀ pre e post, ops = pre ++ e :: post →
    ∃ origin : Finset Event, origin ⊆ pre.toFinset ∧ sourceApplicable e origin

theorem sourceClientLegal_prefix (pre suf : List Event)
    (h : SourceClientLegal (pre ++ suf)) : SourceClientLegal pre :=
  ⟨sequentialLegal_prefix pre suf h.1, split_guard_prefix h.2⟩

/-- Causal origins do not impose a hidden visibility restriction: with the
source forest wrapper, word legality is just event order plus reserved roots.
Global clock freshness is supplied by certified execution, independently. -/
theorem sourceClientLegal_iff (ops : List Event) :
    SourceClientLegal ops ↔ SequentialLegal ops ∧
      ∀ e ∈ ops, e.op.child ≠ root ∧ e.op.child ≠ trash := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    intro e member
    obtain ⟨pre,post,split⟩ := List.mem_iff_append.mp member
    obtain ⟨origin,_,guard⟩ := h.2 pre e post split
    exact guard.2
  · rintro ⟨sorted,reserved⟩
    refine ⟨sorted,?_⟩
    intro pre e post split
    refine ⟨∅,Finset.empty_subset _,?_,?_⟩
    · simp
    · exact reserved e (by rw [split]; simp)

noncomputable def sequentialSpec : SequentialSpec D where
  toSequentialMachine := Sal.MRDTs.Instances.TreeMove.spec
  Legal := SourceClientLegal
  query t _ := visibleTree t

noncomputable def language := GuardedHistory.language sequentialSpec

theorem observes_sorted (ops : List Event) (legal : SequentialLegal ops) (q : Unit) :
    D.query (applySeq D.toUpdateSig D.init ops) q =
      sequentialSpec.query (sequentialSpec.run ops) q := by
  cases q
  rw [applySeq_initial]
  change query (encode ops.toFinset) = _
  rw [query_encode]
  change visibleTree (render ops.toFinset) = visibleTree (Sal.MRDTs.Instances.TreeMove.spec.run ops)
  have refines := Sal.MRDTs.Instances.TreeMove.sequentialSound ops legal
  rw [stateRel,Sal.MRDTs.Instances.TreeMove.applySeq_eq_toFinset] at refines
  exact congrArg visibleTree refines

theorem canonicalConfig {C : Configuration D}
    (execution : CertifiedExecution D generation C) : CanonicalConfig C :=
  execution.canonicalConfig (fun _ _ => joinAt _)

theorem history : EventExecutionHistoryAdequacy D (commutingPolicy Move) language generation := by
  intro C execution v s E stored q
  have good := canonicalConfig execution
  obtain ⟨ops,perm,_,fold⟩ := good.canonical v s E stored
  have represented : ops.toFinset = decode s := by
    have decoded := congrArg decode fold
    rw [decode_applySeq] at decoded
    change decode (encode ∅) ∪ ops.toFinset = decode s at decoded
    simpa using decoded
  let replay := orderedEvents (decode s)
  have enumerates : listPermOf replay E := by
    refine ⟨Finset.sort_nodup _ _,?_⟩
    intro e
    simp only [replay,orderedEvents,Finset.mem_sort]
    rw [← represented]
    simpa using perm.2 e
  have sorted : SequentialLegal replay :=
    ⟨Finset.sort_nodup _ _,Finset.pairwise_sort _ _⟩
  have visible : respects replay C.vis := by
    unfold respects
    refine sorted.2.imp ?_
    intro a b le backward
    have opposite := eventLE_of_timestamp_lt (C.causal_mono backward)
    have equal : a = b := eventKey_injective (le_antisymm le opposite)
    subst b
    exact Nat.lt_irrefl _ (C.causal_mono backward)
  have origins : ∀ pre e post, replay = pre ++ e :: post →
      ∃ origin : Finset Event, origin ⊆ pre.toFinset ∧ sourceApplicable e origin := by
    apply Automation.mint_origin_prefix encode sourceApplicable applySeq_initial
      (fun e origin guard => ?_) execution.mintHonest
      (good.version_events_supported v s E stored)
      (fun a b vis member => good.version_events_causal v s E stored a b vis member)
      enumerates visible
    simpa using (canIssue_iff e (encode origin)).mp guard
  exact ⟨replay,Automation.guarded_replay_witness sequentialSpec sourceClientLegal_prefix all_comm
    C E replay enumerates visible ⟨sorted,origins⟩ (observes_sorted replay sorted) q⟩

noncomputable def conditions : ConcreteMRDT.ScopedVCConditions
    (commutingPolicy Move) language generation :=
  ConcreteMRDT.CommutingPort.automatedScopedConditions all_comm fiveVC generation history

theorem certifiedV : EventCertifiedSpecificationRAV D (commutingPolicy Move) language generation :=
  fun _ reach => conditions.versionsV reach

theorem certified : EventCertifiedSpecificationRA D (commutingPolicy Move) language generation :=
  certifiedV.ordinary

theorem executions (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D generation).Execution (initConfig D) trace) :
    ConcreteMRDT.ExecutionCorrect (commutingPolicy Move) language trace :=
  conditions.executions trace execution

theorem executionsV (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D generation).Execution (initConfig D) trace) :
    ConcreteMRDT.ExecutionCorrect (commutingPolicy Move) language trace :=
  conditions.executionsV trace execution

theorem materialized_safe (s : State) : TreeSafe s.val.tree := by
  rw [s.property,canonical_tree]
  exact render_safe _

theorem observable_safe (s : State) : TreeSafe (query s) :=
  visibleTree_safe (materialized_safe s)

def stateRel (s : State) (t : Tree) : Prop := s.val.tree = t

private theorem empty_legal : SourceClientLegal [] := by
  refine ⟨⟨List.nodup_nil,List.Pairwise.nil⟩,?_⟩
  intro pre e post split
  have length := congrArg List.length split
  simp only [List.length_nil,List.length_append,List.length_cons] at length
  omega

/-- The production registry package retains the same independent machine.
Its proof consumes the new five-VC replay provenance and source forest/trash mint guards. -/
noncomputable def sequentialCorrectness : SequentialCorrectnessCertificate D generation
    (EventOrder.unconstrained D.toUpdateSig) sequentialSpec stateRel where
  sound C execution _ := by
    have good := canonicalConfig execution
    intro v s E stored
    obtain ⟨old,oldPerm,_,oldFold⟩ := good.canonical v s E stored
    have represented : old.toFinset = decode s := by
      have decoded := congrArg decode oldFold
      rw [decode_applySeq] at decoded
      change decode (encode ∅) ∪ old.toFinset = decode s at decoded
      simpa using decoded
    obtain ⟨ops,perm,_,_,accepted⟩ := history C execution v s E stored ()
    obtain ⟨legal,_⟩ := (GuardedHistory.admits_updates_query_iff sequentialSpec
      empty_legal sourceClientLegal_prefix ops () _).mp accepted
    have matching : ops.toFinset = decode s := by
      rw [← represented]
      ext e
      simp only [List.mem_toFinset]
      exact (perm.2 e).trans (oldPerm.2 e).symm
    have relation : stateRel s (sequentialSpec.run ops) := by
      have tree : s.val.tree = render (decode s) := by
        rw [s.property,canonical_tree]
        rfl
      have sound := Sal.MRDTs.Instances.TreeMove.sequentialSound ops legal.1
      rw [Sal.MRDTs.Instances.TreeMove.stateRel,
        Sal.MRDTs.Instances.TreeMove.applySeq_eq_toFinset] at sound
      change s.val.tree = Sal.MRDTs.Instances.TreeMove.spec.run ops
      rw [tree,← matching,sound]
    refine ⟨ops,perm,?_,legal,relation,?_⟩
    · unfold respects
      apply List.pairwise_of_forall
      intro a b
      simp [loOn,UpdateSig.replayBefore,EventOrder.Before,EventOrder.unconstrained]
    · intro q
      change visibleTree s.val.tree = visibleTree (sequentialSpec.run ops)
      rw [relation]

noncomputable def verified : VerifiedMRDT D where
  issuance := generation
  replayOrder := EventOrder.unconstrained D.toUpdateSig
  replayAdequacy := ReplayAdequacyCertificate.ofJoin generation joinAt
  Spec := sequentialSpec
  Rel := stateRel
  sequentialCorrectness := sequentialCorrectness

#print axioms history
#print axioms certifiedV
#print axioms executionsV
#print axioms verified
end Sal.MRDTs.Instances.TreeMove.Incremental

open Lean Elab Command in
elab "audit_incremental_tree_move" : command => do
  let env ← getEnv
  for root in [``Sal.MRDTs.Instances.TreeMove.Incremental.verified,
      ``Sal.MRDTs.Instances.TreeMove.Incremental.certifiedV,
      ``Sal.MRDTs.Instances.TreeMove.Incremental.executions,
      ``Sal.MRDTs.Instances.TreeMove.Incremental.executionsV] do
    let mut seen : NameSet := {}
    let mut pending := [root]
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      unless seen.contains name do
        seen := seen.insert name
        if let some info := env.find? name then
          pending := info.getUsedConstantsAsSet.toList ++ pending
    for required in [``Sal.MRDTs.Instances.TreeMove.Incremental.fiveVC,
        ``Sal.MRDTs.Paper1.Automation.CommonVerification.verify,
        ``Sal.MRDTs.Paper1.ConcreteMRDT.Raw.join_at_sizes,
        ``Sal.MRDTs.Instances.TreeMove.Incremental.applyRaw_build,
        ``Sal.MRDTs.Instances.TreeMove.Incremental.undo_push,
        ``Sal.MRDTs.Instances.TreeMove.Incremental.decode_injective,
        ``Sal.MRDTs.Instances.TreeMove.Incremental.candidate_safe_iff,
        ``Sal.MRDTs.Instances.TreeMove.Incremental.history] do
      unless seen.contains required do
        throwError "{root} does not consume {required}"
    for forbidden in [``Sal.MRDTs.Instances.TreeMove.join,
        ``Sal.MRDTs.Instances.TreeMove.sequentialCorrectness,
        ``Sal.MRDTs.Instances.TreeMove.verified] do
      if seen.contains forbidden then
        throwError "{root} uses the old event-carrier certificate {forbidden}"
    let axioms ← liftCoreM <| Lean.collectAxioms root
    for ax in axioms do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo "Incremental TreeMove endpoints consume source undo/redo, exact-state kernels, common five-VC verification and merge induction; only standard logical axioms."

audit_incremental_tree_move
