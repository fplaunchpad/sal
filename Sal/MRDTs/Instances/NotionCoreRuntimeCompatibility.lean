import Sal.MRDTs.Instances.NotionCoreRuntimeStateProofs
import Sal.MRDTs.Instances.NotionCoreArchiveOrder

/-! Honest archive allocation derives the key compatibility required by the
single-value native maps. No query answer or replay-success assumption occurs. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeCompatibility
open NotionCoreRuntimeState (Compatible)
open NotionCorePayload (BlockKey Transaction)
open NotionCoreStructuralFacts (Fact decodeList ofTransactions)
open NotionCoreStructuralDisplay (creation)

private theorem cut_target (tx : Transaction) (inst : BlockKey) (id : NotionRunAllocation.Id)
    (target : BlockKey) (member : Fact.cut inst id target ∈ decodeList tx) : target = .issued id := by
  cases tx with
  | mk key payload =>
      cases payload <;> simp [decodeList,NotionCoreStructuralFacts.extra] at member; simp_all

private theorem created_initial (tx : Transaction) (afterBlock : Option BlockKey)
    (selected : creation tx = some (.initial,afterBlock)) : afterBlock = none := by
  cases tx with
  | mk id payload => cases payload <;> simp [creation] at selected; simp_all

private theorem created_issued_key (tx : Transaction) (id : NotionRunAllocation.Id)
    (afterBlock : Option BlockKey) (selected : creation tx = some (.issued id,afterBlock)) : tx.id = id := by
  cases tx with
  | mk key payload => cases payload <;> simp [creation] at selected <;> simp_all

/-- One honestly allocated archive has globally unique birth IDs and source
transaction keys. These facts derive every immutable-map conflict guard. -/
theorem archive_compatible (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network) :
    Compatible (ofTransactions (network.entries.map (·.tx))) := by
  let txs := network.entries.map NotionCorePayloadNetwork.Entry.tx
  have keys := NotionCoreArchiveOrder.archive_keys_unique network reachable
  let born := txs.flatMap (fun tx => NotionCorePayload.births tx (fun _ _ => false))
  have unique : (born.map NotionCorePayload.birthId).Nodup := by
    simpa [born,txs,NotionCoreReplayGraph.allIds,List.map_flatMap,List.flatMap_map,Function.comp_def] using
      NotionCoreReplayGraph.all_births_unique reachable (fun _ _ => false)
  refine ⟨?_,?_,?_⟩
  · intro inst a b ha hb same
    have belongs (row : NotionCoreParentMap.Row) (member : Fact.birth inst row ∈ ofTransactions txs) :
        (inst,row) ∈ born := by
      simp only [ofTransactions,List.mem_toFinset,List.mem_flatMap,NotionCoreStructuralFacts.birth_decodeList] at member
      exact List.mem_flatMap.mpr member
    have pairEq := List.inj_on_of_nodup_map unique (belongs a ha) (belongs b hb) same
    exact congrArg Prod.snd pairEq
  · intro inst id a b ha hb
    have target (owner : BlockKey) (member : Fact.cut inst id owner ∈ ofTransactions txs) : owner = .issued id := by
      simp only [ofTransactions,List.mem_toFinset,List.mem_flatMap] at member
      obtain ⟨tx,_,decoded⟩ := member
      exact cut_target tx inst id owner decoded
    exact (target a ha).trans (target b hb).symm
  · intro block a b ha hb
    simp only [ofTransactions,List.mem_toFinset,List.mem_flatMap,NotionCoreStructuralDisplay.created_decodeList] at ha hb
    obtain ⟨ta,ma,sa⟩ := ha
    obtain ⟨tb,mb,sb⟩ := hb
    cases block with
    | initial => exact (created_initial ta a sa).trans (created_initial tb b sb).symm
    | issued id =>
        have same := (created_issued_key ta id a sa).trans (created_issued_key tb id b sb).symm
        have txEq := List.inj_on_of_nodup_map keys ma mb same
        subst tb
        have pairEq := Option.some.inj (sa.symm.trans sb)
        exact congrArg Prod.snd pairEq

/-- A local or merged version's facts inherit the common honest archive's
compatibility. The subset hypothesis is structural coverage, not desired output. -/
theorem honest_subset_compatible (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network) (facts : Finset Fact)
    (subset : facts ⊆ ofTransactions (network.entries.map (·.tx))) : Compatible facts :=
  (archive_compatible network reachable).mono subset

#print axioms archive_compatible
#print axioms honest_subset_compatible
end Sal.MRDTs.Instances.NotionCoreRuntimeCompatibility
