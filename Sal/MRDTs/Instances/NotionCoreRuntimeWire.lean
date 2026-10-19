import Lean.Data.Json
import Sal.MRDTs.Instances.NotionCorePayload

/-! JSON AST boundary for the compiled typed core. The native driver uses these
functions directly. Parsing JSON bytes and the external demo-to-typed adapter
remain explicit trust/validation boundaries, not assumed kernel theorems. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeWire
open Lean
open NotionRunAllocation (Id)
open NotionCorePayload (BlockKey Payload Transaction)
open NotionCoreOriginTree (Origin)

def field (value : Json) (name : String) : Except String Json := value.getObjVal? name

def decodeNats (value : Json) : Except String (List Nat) := do
  (← value.getArr?).toList.mapM Json.getNat?

def encodeNats (values : List Nat) : Json := .arr (values.map toJson).toArray

def decodeId (value : Json) : Except String Id := do
  return ⟨← (← field value "counter").getNat?, ← decodeNats (← field value "session")⟩

def encodeId (id : Id) : Json :=
  Json.mkObj [("counter",toJson id.counter),("session",encodeNats id.session)]

def decodeBlock (value : Json) : Except String BlockKey := do
  match value with
  | .str "initial" => return .initial
  | _ => return .issued (← decodeId (← field value "issued"))

def encodeBlock : BlockKey → Json
  | .initial => .str "initial"
  | .issued id => Json.mkObj [("issued",encodeId id)]

def decodeOrigin (value : Json) : Except String Origin := do
  match value with
  | .str "start" => return .start
  | _ => return .item (← decodeId (← field value "item"))

def encodeOrigin : Origin → Json
  | .start => .str "start"
  | .item id => Json.mkObj [("item",encodeId id)]

/-- One instance group of an erase: its text instance and target IDs. -/
def decodeGroup (value : Json) : Except String (BlockKey × List Id) := do
  return (← decodeBlock (← field value "instance"),
    ← (← (← field value "targets").getArr?).toList.mapM decodeId)

def encodeGroup (group : BlockKey × List Id) : List (String × Json) :=
  [("instance",encodeBlock group.1),("targets",.arr (group.2.map encodeId).toArray)]

def decodePayload (value : Json) : Except String Payload := do
  match ← (← field value "kind").getStr? with
  | "bootstrap" => return .bootstrap (← decodeNats (← field value "atoms"))
  | "create" =>
    let after ← field value "after"
    match after with
    | .null => return .create none
    | _ => return .create (some (← decodeBlock after))
  | "insert" => return (.insert (← decodeBlock (← field value "block"))
      (← decodeBlock (← field value "instance")) (← decodeOrigin (← field value "origin"))
      (← decodeNats (← field value "atoms")))
  | "erase" =>
    let block ← decodeBlock (← field value "block")
    match value.getObjVal? "groups" with
    | .ok groups => return .erase block (← (← groups.getArr?).toList.mapM decodeGroup)
    | .error _ => return .erase block [← decodeGroup value]
  | "split" => return (.split (← decodeBlock (← field value "block"))
      (← decodeBlock (← field value "instance")) (← decodeOrigin (← field value "origin")))
  | "merge" =>
    let stop ← field value "stop"
    let stop ← match stop with
      | .null => pure none
      | _ => pure (some (← decodeId stop))
    return (.merge (← decodeBlock (← field value "source"))
      (← decodeBlock (← field value "instance")) stop)
  | other => throw s!"unsupported core payload: {other}"

def encodePayload (payload : Payload) : Json := Json.mkObj (match payload with
  | .bootstrap atoms => [("kind",.str "bootstrap"),("atoms",encodeNats atoms)]
  | .create after => [("kind",.str "create"),("after",after.map encodeBlock |>.getD .null)]
  | .insert block inst origin atoms => [("kind",.str "insert"),("block",encodeBlock block),
      ("instance",encodeBlock inst),("origin",encodeOrigin origin),("atoms",encodeNats atoms)]
  | .erase block [group] => [("kind",.str "erase"),("block",encodeBlock block)] ++ encodeGroup group
  | .erase block groups => [("kind",.str "erase"),("block",encodeBlock block),
      ("groups",.arr (groups.map fun group => Json.mkObj (encodeGroup group)).toArray)]
  | .split block inst origin => [("kind",.str "split"),("block",encodeBlock block),
      ("instance",encodeBlock inst),("origin",encodeOrigin origin)]
  | .merge source inst stop => [("kind",.str "merge"),("source",encodeBlock source),
      ("instance",encodeBlock inst),("stop",stop.map encodeId |>.getD .null)])

def decodeTransaction (value : Json) : Except String Transaction := do
  return ⟨← decodeId (← field value "id"), ← decodePayload (← field value "payload")⟩

def encodeTransaction (tx : Transaction) : Json :=
  Json.mkObj [("id",encodeId tx.id),("payload",encodePayload tx.payload)]

namespace SPOT
private def sample : Transaction := ⟨⟨7,[65,55357,56832]⟩,
  .insert .initial (.issued ⟨2,[66]⟩) (.item ⟨3,[66]⟩) [97,128512]⟩
/-- Session units and text atoms are distinct encodings; neither is truncated
or silently converted to the other. Expected identity and atoms are literal. -/
theorem typed_roundtrip :
    (decodeTransaction (encodeTransaction sample)).toOption = some sample ∧
    (decodeTransaction (encodeTransaction sample)).toOption ≠ some (NotionCorePayload.bootstrap []) := by
  decide +kernel

private def mergeSample : Transaction := ⟨⟨9,[66]⟩, .merge (.issued ⟨3,[66]⟩) .initial (some ⟨5,[67]⟩)⟩
private def finishMergeSample : Transaction := ⟨⟨9,[66]⟩, .merge (.issued ⟨3,[66]⟩) .initial none⟩
/-- A merge round-trips with its source, its anchor's instance and its
anchor's stop in place: the source and instance are not swapped, a stop is
not dropped, and a missing stop is not invented. -/
theorem merge_roundtrip :
    (decodeTransaction (encodeTransaction mergeSample)).toOption = some mergeSample ∧
    (decodeTransaction (encodeTransaction mergeSample)).toOption ≠
      some ⟨⟨9,[66]⟩, .merge .initial (.issued ⟨3,[66]⟩) (some ⟨5,[67]⟩)⟩ ∧
    (decodeTransaction (encodeTransaction mergeSample)).toOption ≠ some finishMergeSample ∧
    (decodeTransaction (encodeTransaction finishMergeSample)).toOption = some finishMergeSample ∧
    (decodeTransaction (encodeTransaction finishMergeSample)).toOption ≠ some mergeSample := by
  decide +kernel

private def errorMessage {α : Type} : Except String α → Option String
  | .error message => some message
  | .ok _ => none

theorem reject_unknown :
    errorMessage (decodePayload (Json.mkObj [("kind",.str "format")])) = some "unsupported core payload: format" ∧
    (decodePayload (Json.mkObj [("kind",.str "format")])).toOption ≠ some (.bootstrap []) := by
  decide +kernel
end SPOT

#print axioms SPOT.typed_roundtrip
#print axioms SPOT.merge_roundtrip
#print axioms SPOT.reject_unknown
end Sal.MRDTs.Instances.NotionCoreRuntimeWire
