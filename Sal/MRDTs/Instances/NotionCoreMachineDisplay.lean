import Sal.MRDTs.Instances.NotionCoreMachineHonestReplay

/-! Actual display enumeration is a permutation of the unique stored block IDs.
This concerns the interpreter's display list, not Map enumeration order or a
claim that concurrent split display order equals physical interval order. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDisplay
open NotionCoreMachine
open NotionCorePayload (Operation Transaction)
open NotionCoreMachineCreators

abbrev Aligned (state : State) : Prop :=
  NotionCoreDisplayOrder.Aligned ⟨state.forest,state.display⟩

@[simp] theorem putInstance_display (state : State) (inst : Nat) (value : Instance) :
    (putInstance state inst value).display = state.display := by
  unfold putInstance
  split <;> rfl

private theorem frame (state result : State) (aligned : Aligned state)
    (forest : names result.forest = names state.forest)
    (display : result.display = state.display) : Aligned result := by
  change (names result.forest).Nodup ∧ result.display.Perm (names result.forest)
  rw [forest,display]
  exact aligned

theorem operation_aligned (state result : State) (op : Operation)
    (aligned : Aligned state) (accepted : applyOperation state op = some result) :
    Aligned result := by
  cases op with
  | create block afterBlock =>
    by_cases existsBlock : state.forest.any (fun b => b.id == blockName block) = true
    · have same : state = result := by simpa [applyOperation,existsBlock] using accepted
      subst result
      exact aligned
    · have absent : blockName block ∉ NotionCoreDisplayOrder.names state.forest := by
        simpa [NotionCoreDisplayOrder.names,List.any_eq_true] using existsBlock
      have absentDisplay : blockName block ∉ state.display := fun member =>
        absent (aligned.2.mem_iff.mp member)
      have filtered : state.display.filter (· != blockName block) = state.display := by
        apply List.filter_eq_self.mpr
        intro bid member
        simp only [bne_iff_ne]
        exact fun equal => absentDisplay (equal ▸ member)
      have fresh := NotionCoreDisplayOrder.create_aligned
        ⟨state.forest,state.display⟩ (blockName block) (afterBlock.map blockName) aligned absent
      simp only [applyOperation,existsBlock,Bool.false_eq_true,if_false] at accepted
      simp only [apply_ite,putInstance_forest,ite_self] at accepted
      simp only [existsBlock,Bool.false_eq_true,if_false,Option.some.injEq] at accepted
      subst result
      simpa [Aligned,NotionCoreDisplayOrder.create,filtered] using fresh
  | insert block inst first origin atoms =>
    simp only [applyOperation] at accepted
    cases selected : integrateRows (getInstance state (blockName inst)).rows
        (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
          (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
    | none => simp [selected] at accepted
    | some rows =>
      simp [selected] at accepted
      subst result
      simpa [Aligned] using aligned
  | erase block inst targets =>
    simp only [applyOperation, Option.some.injEq] at accepted
    subst result
    simpa [Aligned] using aligned
  | marker block inst id origin =>
    simp only [applyOperation] at accepted
    cases selected : integrate (getInstance state (blockName inst)).rows ⟨⟨id,.split⟩,origin⟩ with
    | none => simp [selected] at accepted
    | some rows =>
      simp only [selected] at accepted
      dsimp only [Bind.bind, Option.bind] at accepted
      let updated := putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows}
      cases divided : NotionCoreSliceForest.splitForest (physical updated)
          (NotionCorePhysicalReplay.address (blockName inst) id) updated.forest with
      | none =>
        have divided' := divided
        simp only [updated, putInstance_forest] at divided'
        simp [divided'] at accepted
      | some forest =>
        have equal := splitForest_names _ _ _ forest divided
        simp only [updated, putInstance_forest] at equal
        have divided' := divided
        simp only [updated, putInstance_forest] at divided'
        simp only [putInstance_forest, divided'] at accepted
        split at accepted
        · simp at accepted
          subst result
          simpa [Aligned, NotionCoreDisplayOrder.Aligned, NotionCoreDisplayOrder.names, names, updated] using frame state {updated with forest := forest} aligned equal (by simp [updated])
        · contradiction
  | moveInto block inst marker target =>
    simp only [applyOperation] at accepted
    split at accepted
    · contradiction
    · cases detached : NotionCoreSliceForest.detachForest
          (NotionCorePhysicalReplay.address (blockName inst) marker) state.forest with
      | none => simp [detached] at accepted
      | some pair =>
        simp [detached] at accepted
        subst result
        have same := detachForest_names _ _ pair.1 pair.2 detached
        exact frame state _ aligned (by simpa using same) rfl


theorem operations_aligned (state result : State) (ops : List Operation)
    (aligned : Aligned state) (accepted : applyOperations state ops = some result) :
    Aligned result := by
  induction ops generalizing state with
  | nil =>
    have same : state = result := by simpa [applyOperations] using accepted
    exact same ▸ aligned
  | cons op rest ih =>
    cases first : applyOperation state op with
    | none => simp [applyOperations,first] at accepted
    | some middle =>
      apply ih middle (operation_aligned state middle op aligned first)
      simpa [applyOperations,first] using accepted

theorem replay_aligned (state result : State) (txs : List Transaction)
    (aligned : Aligned state) (accepted : replay state txs = some result) :
    Aligned result := by
  induction txs generalizing state with
  | nil =>
    have same : state = result := by simpa [replay] using accepted
    exact same ▸ aligned
  | cons tx rest ih =>
    cases first : applyTransaction state tx with
    | none => simp [replay,first] at accepted
    | some middle =>
      apply ih middle (operations_aligned state middle _ aligned first)
      simpa [replay,first] using accepted

/-- Accepted reconstruction displays every stored block exactly once. This does
not identify the display permutation with physical interval order. -/
theorem reconstructed_aligned (network : NotionCorePayloadNetwork.State)
    (peer : NotionRunAllocation.Session) (state : State)
    (accepted : NotionCoreReconstruction.reconstruct network peer = some state) :
    Aligned state := by
  apply replay_aligned {} state (NotionCoreReconstruction.transactions network peer)
  · exact ⟨by simp [NotionCoreDisplayOrder.names],List.Perm.refl []⟩
  · exact accepted

#print axioms reconstructed_aligned

#print axioms operation_aligned
#print axioms replay_aligned
end Sal.MRDTs.Instances.NotionCoreMachineDisplay
