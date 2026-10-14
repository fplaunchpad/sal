import Sal.MRDTs.Instances.NotionCoreRuntimeEngine
import Sal.MRDTs.Instances.NotionCoreRuntimeAdapter
import Sal.MRDTs.Instances.NotionCoreRuntimeWire

/-! Persistent native harness. Typed decoding and JSON serialization are outside
reported operation time. The executed receipt/merge/query functions are the
same pure Lean definitions used by the refinement proofs. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeMain
open Lean
open NotionCoreRuntimeWire
open NotionCorePayload (Transaction)
abbrev Engine := NotionCoreRuntimeEngine.State
abbrev Stores := Std.HashMap String Engine

inductive Request where
  | init (replica : String)
  | receive (replica : String) (transactions : List Transaction)
  | merge (target source : String)
  | clone (target source : String)
  | query (replica : String)
  | gap (replica : String) (ticks : Nat)
  | stats (replica : String)

def stringField (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?

def decodeRequest (j : Json) : Except String Request := do
  match ← stringField j "op" with
  | "init" => return .init (← stringField j "replica")
  | "receive" => return (.receive (← stringField j "replica")
      (← (← (← field j "transactions").getArr?).toList.mapM decodeTransaction))
  | "merge" => return .merge (← stringField j "target") (← stringField j "source")
  | "clone" => return .clone (← stringField j "target") (← stringField j "source")
  | "query" => return .query (← stringField j "replica")
  | "gap" => return .gap (← stringField j "replica") (← (← field j "ticks").getNat?)
  | "stats" => return .stats (← stringField j "replica")
  | op => throw s!"unknown request: {op}"

def getStore (stores : Stores) (replica : String) : Except String Engine :=
  match stores[replica]? with
  | some state => .ok state
  | none => .error s!"unknown replica: {replica}"

inductive Reply where
  | unit
  | view (value : Option NotionCoreHistory.View)
  | stats (transactions rows cuts blocks clock : Nat)

def execute (stores : Stores) : Request → Except String (Stores × Reply)
  | .init replica =>
    if stores.contains replica then .error "replica already exists"
    else .ok (stores.insert replica NotionCoreRuntimeEngine.empty,.unit)
  | .receive replica transactions => do
    let next ← NotionCoreRuntimeEngine.receiveMany (← getStore stores replica) transactions
    return (stores.insert replica next,.unit)
  | .merge target source => do
    let next ← NotionCoreRuntimeEngine.merge (← getStore stores target) (← getStore stores source)
    return (stores.insert target next,.unit)
  | .clone target source => do
    if stores.contains target then throw "replica already exists"
    let next ← NotionCoreRuntimeEngine.merge NotionCoreRuntimeEngine.empty
      (← getStore stores source)
    return (stores.insert target next,.unit)
  | .query replica => do
    let state ← getStore stores replica
    return (stores,.view (NotionCoreRuntimeAdapter.observeState state.core))
  | .gap replica ticks => do
    let next := NotionCoreRuntimeEngine.gap (← getStore stores replica) ticks
    return (stores.insert replica next,.unit)
  | .stats replica => do
    let state ← getStore stores replica
    return (stores,.stats state.metadata.archive.length state.core.births.size state.core.cuts.size
      state.core.created.size state.metadata.peer.clock)

def encodeReply : Reply → Except String Json
  | .unit => .ok .null
  | .stats transactions rows cuts blocks clock => .ok (Json.mkObj
      [("transactions",toJson transactions),("rows",toJson rows),("cuts",toJson cuts),
       ("blocks",toJson blocks),("clock",toJson clock)])
  | .view none => .ok .null
  | .view (some blocks) => do
      let encoded ← blocks.mapM fun (name,text) => do
        let some block := NotionCoreMachineClient.decodeBlock name
          | throw "noncanonical output block name"
        return Json.mkObj [("block",encodeBlock block),("text",encodeNats text)]
      return .arr encoded.toArray

def errorReply (message : String) : Json :=
  Json.mkObj [("ok",.bool false),("error",.str message),("elapsedNs",toJson (0 : Nat))]

partial def loop (input output : IO.FS.Stream) (stores : Stores) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then return
  let decoded := Json.parse line >>= decodeRequest
  match decoded with
  | .error message =>
    output.putStrLn (errorReply message).compress
    output.flush
    loop input output stores
  | .ok request =>
    let started ← IO.monoNanosNow
    match execute stores request with
    | .error message =>
      output.putStrLn (errorReply message).compress
      output.flush
      loop input output stores
    | .ok (next,reply) =>
      let stopped ← IO.monoNanosNow
      match encodeReply reply with
      | .error message => output.putStrLn (errorReply message).compress
      | .ok value => output.putStrLn (Json.mkObj
          [("ok",.bool true),("value",value),("elapsedNs",toJson (stopped-started))]).compress
      output.flush
      loop input output next

end Sal.MRDTs.Instances.NotionCoreRuntimeMain

def main : IO Unit := do
  Sal.MRDTs.Instances.NotionCoreRuntimeMain.loop (← IO.getStdin) (← IO.getStdout) ∅
