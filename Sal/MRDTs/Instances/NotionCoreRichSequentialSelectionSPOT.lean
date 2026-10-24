import Sal.MRDTs.Instances.NotionCoreRichSequentialSelection

/-! Hand-derived paired clipping/current-verdict controls. The selected
identity lists are calculated from abc, rather than evaluated from the caller. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Sal.MRDTs.Instances.NotionCoreRichSequential.Selection.SPOT
open NotionCoreSpec

private def seed : Command := .core [.create 0 0 none,.insert (0,.start)
  [character 0 (0,1) 97,character 0 (0,2) 98,character 0 (0,3) 99]]
private def boldB : Command := .format [⟨0,.before (0,2),.before (0,3)⟩] true
private def current : Option State := execute {} [seed,boldB]

/-- Upper bounds clip to the visible suffix; they do not reject the request
or return the whole block. Starts beyond END and reversed bounds are empty. -/
theorem clipped_selection_control :
    (current >>= fun state => selectedAddresses state 0 1 99) =
      some [(0,.event (0,2)),(0,.event (0,3))] ∧
    (current >>= fun state => selectedAddresses state 0 1 99) ≠ none ∧
    (current >>= fun state => selectedAddresses state 0 1 99) ≠
      some [(0,.event (0,1)),(0,.event (0,2)),(0,.event (0,3))] ∧
    (current >>= fun state => selectedAddresses state 0 99 100) = some [] ∧
    (current >>= fun state => selectedAddresses state 0 99 100) ≠ none ∧
    (current >>= fun state => selectedAddresses state 0 2 1) = some [] ∧
    (current >>= fun state => selectedAddresses state 0 2 1) ≠ some [(0,.event (0,3))] := by decide +kernel

/-- The complete clipped selection controls the single issued Boolean:
b alone is all bold, whereas the clipped b,c suffix is mixed. -/
theorem clipped_verdict_control :
    (current >>= fun state => selectedVerdict state 0 1 2) = some false ∧
    (current >>= fun state => selectedVerdict state 0 1 2) ≠ some true ∧
    (current >>= fun state => selectedVerdict state 0 1 99) = some true ∧
    (current >>= fun state => selectedVerdict state 0 1 99) ≠ some false ∧
    (current >>= fun state => selectedAddresses state 1 0 1) = none ∧
    (current >>= fun state => selectedAddresses state 1 0 1) ≠ some [] := by decide +kernel

private def raw : Option NotionCoreAtomicFormattingMachine.State :=
  NotionCoreAtomicFormattingMachine.replay {} [⟨⟨1,[65]⟩,.edit (.bootstrap [97,98,99])⟩]
private def rawSelected (start stop : Nat) : Option (List (Address × Bool)) := do
  let state ← raw
  let selected ← NotionCoreRichProtocolNetwork.selection state .initial start stop
  pure (selected.map fun char =>
    (NotionCorePhysicalReplay.address char.textInstance char.item.id,char.bold))
private def rawPrepared (start stop : Nat) : Option NotionCoreRichPayload.Payload :=
  raw >>= fun state => NotionCoreRichProtocolNetwork.formatPayload state .initial start stop

/-- The actual repaired caller clips a stop past END and emits one maximal
suffix interval. Empty/reversed slices emit no transaction. -/
theorem actual_clipped_caller_control :
    rawSelected 1 99 = some [((0,.event (Encodable.encode [65],2)),false),
      ((0,.event (Encodable.encode [65],3)),false)] ∧
    rawSelected 1 99 ≠ none ∧
    rawPrepared 1 99 = some (.format
      [⟨0,⟨.item ⟨2,[65]⟩,.before⟩,⟨.finish,.before⟩⟩] true) ∧
    rawPrepared 1 99 ≠ some (.format [] true) ∧
    rawPrepared 3 99 = none ∧
    rawPrepared 3 99 ≠ rawPrepared 1 99 ∧
    rawPrepared 2 1 = none ∧
    rawPrepared 2 1 ≠ rawPrepared 1 99 := by decide +kernel

#print axioms clipped_selection_control
#print axioms clipped_verdict_control
#print axioms actual_clipped_caller_control
end Sal.MRDTs.Instances.NotionCoreRichSequential.Selection.SPOT
