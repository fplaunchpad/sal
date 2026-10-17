import Sal.MRDTs.Instances.NotionCoreMachine
import Sal.MRDTs.Instances.NotionCoreSourceDocument

/-! Translate typed atomic payloads into the existing independent source-command
language. This is a static label translation, not another document interpreter.
The transaction stays one history update even when it contains two commands.
Source identifier encodings are semantic names, not Sal event labels. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineCommands
open NotionCorePayload (Transaction)
open NotionCoreMachine (blockName)
open NotionCorePhysicalReplay (originAddress address atom)

/-- Fresh characters are live; the canonical simulation must derive this fact
from issuance, rather than assuming that pending deletes cannot target them. -/
def text (tx : Transaction) (inst : Nat) (atoms : List Nat) : List NotionCoreSource.Atom :=
  (NotionCorePayload.textItems tx.id atoms (fun _ => false)).map (atom inst)

def commands (tx : Transaction) : List NotionCoreSourceDocument.Command :=
  match tx.payload with
  | .bootstrap atoms => [.create 0 0 none, .insert (0,.start) (text tx 0 atoms)]
  | .create after =>
      [.create (blockName (.issued tx.id)) (blockName (.issued tx.id)) (after.map blockName)]
  | .insert _ inst origin atoms => [.insert (originAddress (blockName inst) origin) (text tx (blockName inst) atoms)]
  | .erase _ groups => groups.map fun group => .delete (group.2.map (address (blockName group.1)))
  | .split block inst origin =>
      [.create (blockName (.issued tx.id)) (blockName (.issued tx.id)) (some (blockName block)),
       .split (originAddress (blockName inst) origin) (address (blockName inst) tx.id)
         (blockName (.issued tx.id))]
  | .merge source target => [.merge (blockName source) (blockName target)]

/-- A split group retains creation and splitting in source order, rather than
flattening them into separate externally observable transactions. -/
theorem split_group (id : NotionRunAllocation.Id) (block inst : NotionCorePayload.BlockKey)
    (origin : NotionCoreOriginTree.Origin) :
    (commands ⟨id,.split block inst origin⟩).length = 2 ∧
    commands ⟨id,.split block inst origin⟩ ≠ [] := by
  simp [commands]

/-- Erasure gives one delete per instance group, each naming its text
instance, which can differ from the block. -/
theorem erase_instance (id : NotionRunAllocation.Id) (block : NotionCorePayload.BlockKey)
    (groups : List (NotionCorePayload.BlockKey × List NotionRunAllocation.Id)) :
    commands ⟨id,.erase block groups⟩ =
      groups.map fun group => .delete (group.2.map (address (blockName group.1))) := rfl

/-- A merge is one source command naming both blocks, not a removal. -/
theorem merge_command (id : NotionRunAllocation.Id) (source target : NotionCorePayload.BlockKey) :
    commands ⟨id,.merge source target⟩ = [.merge (blockName source) (blockName target)] ∧
    (commands ⟨id,.merge source target⟩).map NotionCoreSourceDocument.Command.semantic =
      [.merge (blockName source) (blockName target)] := ⟨rfl, rfl⟩

end Sal.MRDTs.Instances.NotionCoreMachineCommands
