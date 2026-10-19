import Sal.MRDTs.Instances.NotionCoreStructuralFacts
import Sal.MRDTs.Instances.NotionCoreMachineDisplay

/-! Display is a separate structural component from physical interval ownership.
This module isolates its creation-link fold from text, erase and split routing. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralDisplay
open NotionCorePayload (Transaction Operation BlockKey)
open NotionCoreMachine
open NotionCoreMachineDisplay (Aligned)

def displayOperation (display : List Nat) : Operation → List Nat
  | .create block afterBlock =>
      if blockName block ∈ display then display else
        NotionCoreDisplayOrder.insert display (blockName block) (afterBlock.map blockName)
  | _ => display

def displayOperations (display : List Nat) (ops : List Operation) : List Nat :=
  ops.foldl displayOperation display

def displayTransactions (display : List Nat) (txs : List Transaction) : List Nat :=
  txs.foldl (fun display tx => displayOperations display (NotionCorePayload.operations tx)) display

theorem operation_display (state result : State) (op : Operation)
    (accepted : applyOperation state op = some result) :
    result.display = displayOperation state.display op := by
  cases op with
  | create block afterBlock =>
      by_cases shown : blockName block ∈ state.display
      · simpa [applyOperation,displayOperation,shown] using congrArg (Option.map (·.display)) accepted.symm
      · have filtered : state.display.filter (· != blockName block) = state.display := by
          apply List.filter_eq_self.mpr
          intro bid member
          simp only [bne_iff_ne]
          exact fun equal => shown (equal ▸ member)
        simp only [applyOperation,shown,↓reduceIte] at accepted
        have mapped := congrArg (Option.map (·.display)) accepted
        simpa [displayOperation,shown,filtered,putInstance] using mapped.symm
  | insert block inst first origin atoms =>
      simp only [applyOperation] at accepted
      cases selected : integrateRows (getInstance state (blockName inst)).rows
          (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
            (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
      | none => simp [selected] at accepted
      | some rows =>
          simp [selected] at accepted
          subst result
          simp [displayOperation]
  | erase block inst targets =>
      simp only [applyOperation,Option.some.injEq] at accepted
      subst result
      simp [displayOperation]
  | marker block inst id origin =>
      simp only [applyOperation] at accepted
      cases selected : integrate (getInstance state (blockName inst)).rows ⟨⟨id,.split⟩,origin⟩ with
      | none => simp [selected] at accepted
      | some rows =>
          simp only [selected] at accepted
          dsimp only [Bind.bind,Option.bind] at accepted
          cases divided : NotionCoreSliceForest.splitForest
              (physical (putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows}))
              (NotionCorePhysicalReplay.address (blockName inst) id)
              (putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows}).forest with
          | none =>
              simp only [NotionCoreMachineCreators.putInstance_forest] at divided
              simp [divided] at accepted
          | some forest =>
              simp only [NotionCoreMachineCreators.putInstance_forest] at divided
              simp only [NotionCoreMachineCreators.putInstance_forest,divided] at accepted
              split at accepted
              · simp at accepted
                subst result
                simp [displayOperation]
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
            rfl
  | merge source inst stop =>
      simp only [applyOperation,Option.some.injEq] at accepted
      subst result
      rfl

theorem operations_display (state result : State) (ops : List Operation)
    (accepted : applyOperations state ops = some result) :
    result.display = displayOperations state.display ops := by
  induction ops generalizing state with
  | nil => simpa [applyOperations,displayOperations] using congrArg (Option.map (·.display)) accepted.symm
  | cons op rest ih =>
      cases first : applyOperation state op with
      | none => simp [applyOperations,first] at accepted
      | some middle =>
          have tail : applyOperations middle rest = some result := by
            simpa [applyOperations,first] using accepted
          rw [ih middle tail]
          rw [operation_display state middle op first]
          rfl

theorem replay_display (state result : State) (txs : List Transaction)
    (accepted : replay state txs = some result) :
    result.display = displayTransactions state.display txs := by
  induction txs generalizing state with
  | nil => simpa [replay,displayTransactions] using congrArg (Option.map (·.display)) accepted.symm
  | cons tx rest ih =>
      cases first : applyTransaction state tx with
      | none => simp [replay,first] at accepted
      | some middle =>
          have tail : replay middle rest = some result := by simpa [replay,first] using accepted
          rw [ih middle tail]
          rw [operations_display state middle _ first]
          rfl

abbrev Link := BlockKey × Option BlockKey

def creation (tx : Transaction) : Option Link := match tx.payload with
  | .bootstrap _ => some (.initial,none)
  | .create after => some (.issued tx.id,after)
  | .split block _ _ => some (.issued tx.id,some block)
  | _ => none

def displayLink (display : List Nat) (link : Link) : List Nat :=
  displayOperation display (.create link.1 link.2)
def displayLinks (display : List Nat) (links : List Link) : List Nat :=
  links.foldl displayLink display

private theorem erase_groups_display (display : List Nat) (block : BlockKey)
    (groups : List (BlockKey × List NotionRunAllocation.Id)) :
    displayOperations display (groups.map fun group => .erase block group.1 group.2) = display := by
  induction groups generalizing display with
  | nil => rfl
  | cons group rest ih => exact ih display

theorem transaction_display_links (display : List Nat) (tx : Transaction) :
    displayOperations display (NotionCorePayload.operations tx) =
      displayLinks display (creation tx).toList := by
  cases tx with
  | mk id payload =>
    cases payload with
    | erase block groups =>
      simp [NotionCorePayload.operations,erase_groups_display,creation,displayLinks]
    | _ =>
      simp [NotionCorePayload.operations,displayOperations,displayOperation,
        creation,displayLinks,displayLink]

theorem transactions_display_links (display : List Nat) (txs : List Transaction) :
    displayTransactions display txs = displayLinks display (txs.filterMap creation) := by
  induction txs generalizing display with
  | nil => rfl
  | cons tx rest ih =>
      change displayTransactions (displayOperations display (NotionCorePayload.operations tx)) rest = _
      rw [ih,transaction_display_links]
      cases selected : creation tx <;>
        simp [selected,displayLinks]

open NotionCoreStructuralFacts (Fact ofTransactions)
def linkSet (facts : Finset Fact) : Finset Link :=
  facts.biUnion fun fact => match fact with
    | .created block after => {(block,after)}
    | _ => ∅

def creatorKey (link : Link) : NotionRunAllocation.Id := match link.1 with
  | .initial => ⟨1,[65]⟩
  | .issued id => id

def Ascending (a b : Link) : Prop := NotionCoreSourceInvariant.Desc (creatorKey b) (creatorKey a)
instance : DecidableRel Ascending := fun _ _ => inferInstanceAs (Decidable (NotionCoreSourceInvariant.Desc _ _))

noncomputable def orderedLinks (facts : Finset Fact) : List Link :=
  (linkSet facts).toList.mergeSort (fun a b => decide (Ascending a b))
/-- Facts-only display computation. It sorts and folds creation links, never
executing insert, deletion, marker integration, or interval movement. It is a
creation-link fold rather than the stronger direct origin-tree traversal. -/
noncomputable def displayFacts (facts : Finset Fact) : List Nat :=
  displayLinks [] (orderedLinks facts)

@[simp] theorem created_decodeList (tx : Transaction) (block : BlockKey) (after : Option BlockKey) :
    Fact.created block after ∈ NotionCoreStructuralFacts.decodeList tx ↔
      creation tx = some (block,after) := by
  cases tx with
  | mk id payload => cases payload <;>
      simp [NotionCoreStructuralFacts.decodeList,NotionCoreStructuralFacts.extra,creation,eq_comm]

@[simp] theorem linkSet_membership (facts : Finset Fact) (link : Link) :
    link ∈ linkSet facts ↔ Fact.created link.1 link.2 ∈ facts := by
  simp only [linkSet,Finset.mem_biUnion]
  constructor
  · rintro ⟨fact,member,inside⟩
    cases fact <;> simp only [Finset.notMem_empty,Finset.mem_singleton] at inside
    rename_i block after
    subst link
    exact member
  · intro member
    exact ⟨_,member,by simp⟩

theorem linkSet_transactions (txs : List Transaction) :
    linkSet (ofTransactions txs) = (txs.filterMap creation).toFinset := by
  ext link
  simp only [linkSet_membership,ofTransactions,List.mem_toFinset,List.mem_flatMap,
    created_decodeList,List.mem_filterMap]

local instance : Std.Total Ascending where
  total a b := by
    rcases NotionCoreSourceInvariant.before_trichotomy (creatorKey a) (creatorKey b) with before | same | reverse
    · exact Or.inl (Or.inl before)
    · exact Or.inl (Or.inr same.symm)
    · exact Or.inr (Or.inl reverse)
local instance : IsTrans Link Ascending where
  trans a b c ab bc :=
    (inferInstance : IsTrans NotionRunAllocation.Id NotionCoreSourceInvariant.Desc).trans
      (creatorKey c) (creatorKey b) (creatorKey a) bc ab

theorem orderedLinks_transactions (txs : List Transaction)
    (ordered : (txs.filterMap creation).Pairwise
      (fun a b => NotionRunAllocation.Before (creatorKey a) (creatorKey b))) :
    orderedLinks (ofTransactions txs) = txs.filterMap creation := by
  let canonical := txs.filterMap creation
  have canonicalIds : (canonical.map creatorKey).Nodup := by
    apply List.pairwise_map.mpr
    apply ordered.imp
    intro a b before same
    rw [same] at before
    exact NotionCoreSourceInvariant.before_irrefl _ before
  have canonicalUnique : canonical.Nodup := by
    apply ordered.imp
    intro a b before same
    subst b
    exact NotionCoreSourceInvariant.before_irrefl _ before
  have enumeration : (linkSet (ofTransactions txs)).toList.Perm canonical := by
    rw [linkSet_transactions]
    exact List.toFinset_toList canonicalUnique
  have permutation : (orderedLinks (ofTransactions txs)).Perm canonical :=
    (List.mergeSort_perm _ _).trans enumeration
  have actualIds : ((orderedLinks (ofTransactions txs)).map creatorKey).Nodup :=
    (permutation.map creatorKey).nodup_iff.mpr canonicalIds
  have sorted : (orderedLinks (ofTransactions txs)).Pairwise Ascending :=
    List.pairwise_mergeSort' Ascending _
  have actualOrdered : (orderedLinks (ofTransactions txs)).Pairwise
      (fun a b => NotionRunAllocation.Before (creatorKey a) (creatorKey b)) := by
    apply (sorted.and (List.pairwise_map.mp actualIds)).imp
    intro a b both
    rcases both.1 with before | equal
    · exact before
    · exact False.elim (both.2 equal.symm)
  exact permutation.eq_of_pairwise (fun _ _ _ _ forward reverse =>
    False.elim (NotionCoreSourceInvariant.before_asymm forward reverse)) actualOrdered ordered

theorem creation_key (tx : Transaction) (link : Link)
    (bootstrap : ∀ atoms, tx.payload = .bootstrap atoms → tx.id = ⟨1,[65]⟩)
    (selected : creation tx = some link) : creatorKey link = tx.id := by
  cases tx with
  | mk id payload =>
      cases payload <;> simp [creation] at selected
      all_goals subst link
      all_goals simp only [creatorKey]
      exact (bootstrap _ rfl).symm

theorem creationLinks_ordered (txs : List Transaction)
    (ordered : txs.Pairwise (fun a b => NotionRunAllocation.Before a.id b.id))
    (keys : ∀ tx ∈ txs, ∀ link, creation tx = some link → creatorKey link = tx.id) :
    (txs.filterMap creation).Pairwise
      (fun a b => NotionRunAllocation.Before (creatorKey a) (creatorKey b)) := by
  apply List.pairwise_filterMap.mpr
  apply ordered.imp_of_mem
  intro a b ha hb before link selected other selectedOther
  rw [keys a ha link selected,keys b hb other selectedOther]
  exact before

/-- Direct fact display equals actual replay under explicit sorted creator-key
conditions. Freshness, successful interval routing and desired output are not
assumed by this projection; replay acceptance only selects an actual result. -/
theorem displayFacts_replay (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state)
    (ordered : (txs.filterMap creation).Pairwise
      (fun a b => NotionRunAllocation.Before (creatorKey a) (creatorKey b))) :
    displayFacts (ofTransactions txs) = state.display := by
  rw [displayFacts,orderedLinks_transactions txs ordered]
  rw [← transactions_display_links]
  exact (replay_display {} state txs accepted).symm

/-- Honest archive ordering discharges all extra creator-key hypotheses,
including a lower-key independent create that precedes bootstrap. -/
theorem honest_display (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (state : State)
    (accepted : replay {} (NotionCoreReconstruction.transactionsFor network version) = some state) :
    displayFacts (ofTransactions (NotionCoreReconstruction.transactionsFor network version)) = state.display := by
  have payloadReach := NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable)
  apply displayFacts_replay _ state accepted
  apply creationLinks_ordered _ (NotionCoreReconstruction.transactionsFor_ordered network payloadReach version)
  intro tx member link selected
  apply creation_key tx link ?_ selected
  intro atoms payload
  obtain ⟨entry,published,same,_⟩ := NotionCoreReconstruction.transactionsFor_received network version tx member
  have exactTx := NotionCoreRootCreators.archived_bootstrap network payloadReach entry published atoms (same ▸ payload)
  have txEq : tx = NotionCorePayload.bootstrap atoms := same.symm.trans exactTx
  simp only [txEq,NotionCorePayload.bootstrap]

namespace SPOT
private def seed : Transaction := NotionCorePayload.bootstrap [97,98]
private def left : Transaction := ⟨⟨3,[66]⟩,.create (some .initial)⟩
private def right : Transaction := ⟨⟨3,[67]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def earlier : Transaction := ⟨⟨1,[64]⟩,.create none⟩
theorem concurrent_creation_control :
    displayFacts (ofTransactions [seed,left,right]) =
      [0,blockName (.issued right.id),blockName (.issued left.id)] ∧
    displayFacts (ofTransactions [seed,left,right]) ≠
      [0,blockName (.issued left.id),blockName (.issued right.id)] := by
  have ordered : ([seed,left,right].filterMap creation).Pairwise
      (fun a b => NotionRunAllocation.Before (creatorKey a) (creatorKey b)) := by decide +kernel
  simp only [displayFacts,orderedLinks_transactions _ ordered]
  decide +kernel

theorem prebootstrap_creation_control :
    displayFacts (ofTransactions [earlier,seed]) = [0,blockName (.issued earlier.id)] ∧
    displayFacts (ofTransactions [earlier,seed]) ≠ [blockName (.issued earlier.id),0] := by
  have ordered : ([earlier,seed].filterMap creation).Pairwise
      (fun a b => NotionRunAllocation.Before (creatorKey a) (creatorKey b)) := by decide +kernel
  simp only [displayFacts,orderedLinks_transactions _ ordered]
  decide +kernel
end SPOT

#print axioms honest_display
#print axioms replay_display
end Sal.MRDTs.Instances.NotionCoreStructuralDisplay
