import Sal.MRDTs.Instances.NotionCoreRichNetwork
import Sal.MRDTs.Instances.NotionCoreRichMRDT
import Sal.MRDTs.Instances.NotionCoreFormattingAtomicSpec

/-! A complete actual-caller execution refutes atomic selection refinement for
per-segment Lamport arbitration. Every edit comes from actual positional core
preparation, every toggle from actual rich selection, and every ID from source
allocation. No raw injected selection, verdict, clock gap, reused ID, or after
anchor is used. Rich payloads remain whole atomic carrier elements.

This concerns the maximal-run candidate and an atomic selection specification.
It preserves the original demo's distinct N002/N003 counterexamples.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 4096
namespace Sal.MRDTs.Instances.NotionCoreRichAtomicCounterexample
open NotionCoreRichNetwork
open NotionCoreRichPayload (Payload Part)
open NotionCoreFormattingSource (Anchor)
open NotionRunAllocation (Id Session)

def A : Session := [65]
def B : Session := [66]
def C : Session := [67]
def id (counter : Nat) (session : Session := A) : Id := ⟨counter,session⟩
def before (counter : Nat) : Anchor := ⟨.item (id counter),.before⟩
def finish : Anchor := ⟨.finish,.before⟩
def part (lower upper : Anchor) : Part := ⟨0,lower,upper⟩

def markPayload : Payload := .format [part (before 2) (before 5)] true
def splitA : Payload := .edit (.split .initial .initial (.item (id 2)))
def splitC : Payload := .edit (.split .initial .initial (.item (id 3)))
def mergeA : Payload := .edit (.merge (.issued (id 7 C)) .initial (some (id 7 A)))
def create : Payload := .edit (.create none)
def addPayload : Payload := .format [part (before 1) (before 3),part (before 4) finish] true
def removePayload : Payload := .format [part (before 2) (before 5)] false

def base : State := seeded [97,98,99,100,101]
def marked : State := emit base A markPayload
def copied : State := exchange (exchange marked B A) C A
def dividedA : State := emit copied A splitA
def dividedC : State := emit dividedA C splitC
def joined : State := exchange dividedC A C
def mergedA : State := emit joined A mergeA
def createdA : State := emit mergedA A create
def createdB1 : State := emit createdA B create
def createdB2 : State := emit createdB1 B create
def prepared : State := emit createdB2 B create
def added : State := emit prepared A addPayload
def removed : State := emit added B removePayload
def final : State := exchange removed A B

private theorem issue_of_prepared (state : State) (session : Session) (request : Request)
    (payload : Payload) (prepared : prepareAt state session request = some payload)
    (checked : (references payload).all (known state session) = true) :
    issue state session request = some (emit state session payload) := by
  simp [issue,prepared,checked]

theorem mark_prepared : prepareAt base A (.toggle .initial 1 4) = some markPayload := by decide +kernel
theorem splitA_prepared : prepareAt copied A (.edit (.split .initial 2)) = some splitA := by decide +kernel
theorem splitC_prepared : prepareAt dividedA C (.edit (.split .initial 3)) = some splitC := by decide +kernel
theorem mergeA_prepared : prepareAt joined A (.edit (.merge (.issued (id 7 C)))) = some mergeA := by decide +kernel
theorem createA_prepared : prepareAt mergedA A (.edit (.create none)) = some create := by decide +kernel
theorem createB1_prepared : prepareAt createdA B (.edit (.create none)) = some create := by decide +kernel
theorem createB2_prepared : prepareAt createdB1 B (.edit (.create none)) = some create := by decide +kernel
theorem createB3_prepared : prepareAt createdB2 B (.edit (.create none)) = some create := by decide +kernel
theorem add_prepared : prepareAt prepared A (.toggle .initial 0 4) = some addPayload := by decide +kernel
theorem remove_prepared : prepareAt added B (.toggle .initial 1 4) = some removePayload := by decide +kernel

theorem marked_reachable : Reach marked := by
  apply Reach.request A (.toggle .initial 1 4) (.bootstrap [97,98,99,100,101])
  exact issue_of_prepared base A _ markPayload mark_prepared (by decide +kernel)

theorem prepared_reachable : Reach prepared := by
  have copiedReach : Reach copied := .exchange C A (.exchange B A marked_reachable)
  have dividedAReach : Reach dividedA := .request A (.edit (.split .initial 2)) copiedReach
    (issue_of_prepared copied A _ splitA splitA_prepared (by decide +kernel))
  have dividedCReach : Reach dividedC := .request C (.edit (.split .initial 3)) dividedAReach
    (issue_of_prepared dividedA C _ splitC splitC_prepared (by decide +kernel))
  have joinedReach : Reach joined := .exchange A C dividedCReach
  have mergedReach : Reach mergedA := .request A (.edit (.merge (.issued (id 7 C)))) joinedReach
    (issue_of_prepared joined A _ mergeA mergeA_prepared (by decide +kernel))
  have createdAReach : Reach createdA := .request A (.edit (.create none)) mergedReach
    (issue_of_prepared mergedA A _ create createA_prepared (by decide +kernel))
  have createdB1Reach : Reach createdB1 := .request B (.edit (.create none)) createdAReach
    (issue_of_prepared createdA B _ create createB1_prepared (by decide +kernel))
  have createdB2Reach : Reach createdB2 := .request B (.edit (.create none)) createdB1Reach
    (issue_of_prepared createdB1 B _ create createB2_prepared (by decide +kernel))
  exact .request B (.edit (.create none)) createdB2Reach
    (issue_of_prepared createdB2 B _ create createB3_prepared (by decide +kernel))

theorem final_reachable : Reach final := by
  have addReach : Reach added := .request A (.toggle .initial 0 4) prepared_reachable
    (issue_of_prepared prepared A _ addPayload add_prepared (by decide +kernel))
  have removeReach : Reach removed := .request B (.toggle .initial 1 4) addReach
    (issue_of_prepared added B _ removePayload remove_prepared (by decide +kernel))
  exact .exchange A B removeReach

def selected (network : State) (session : Session) (start stop : Nat) :=
  (reconstruct network session >>= fun state => selection state .initial start stop).map
    (List.map fun character => (character.item.id.counter,character.bold))

def flags (network : State) (session : Session) : Option (List Bool) :=
  (reconstruct network session).map fun state =>
    NotionCoreFormattingAtomicSpec.addresses.map (NotionCoreFormattingMachine.boldAt state)

def displayed (network : State) (session : Session) :=
  (reconstruct network session >>= NotionCoreFormattingMachine.render).map fun document =>
    document.map fun block => block.2.map NotionCoreFormattingMachine.RichAtom.value

/-- PASS+FAIL: A actually sees displayed abde while B sees abcde. Their
selected rich characters force opposite global verdicts; no caller supplies
bold bits or a noncontiguous identity list directly. -/
theorem actual_selection_control :
    selected prepared A 0 4 = some [(1,false),(2,true),(4,true),(5,false)] ∧
    selected prepared B 1 4 = some [(2,true),(3,true),(4,true)] ∧
    selected prepared A 0 4 ≠ some [(1,false),(2,true),(3,true),(4,true)] ∧
    flags prepared A = some [false,true,true,true,false] ∧
    flags prepared B = some [false,true,true,true,false] := by decide +kernel

/-- PASS+FAIL: all five identities remain visible. Empty blocks advance
clocks but do not supply a hidden insertion/deletion explanation for b ≠ d. -/
theorem actual_display_control :
    displayed prepared A = some [[],[97,98,100,101],[99]] ∧
    displayed prepared B = some [[],[],[],[97,98,99,100,101]] ∧
    displayed final A = some [[],[],[],[],[97,98,100,101],[99]] ∧
    displayed final A ≠ some [[],[],[],[],[97,98,99,100,101]] := by decide +kernel

/-- PASS+FAIL: actual harmless creates advance B's clock; A's two splits,
merge and create likewise reach 9. One atomic format reserves two IDs, the
other one. Their globally fresh runs interleave in per-segment priority. -/
theorem clock_and_batch_control :
    (prepared.allocation.peers A).clock = 9 ∧ (prepared.allocation.peers B).clock = 9 ∧
    (added.entries.head?.map fun entry =>
      (entry.transaction.id,entry.transaction.payload.width,entry.transaction.annotations.map
        (fun located => (located.2.id.counter,located.2.value)))) = some (id 10 A,2,[(10,true),(11,true)]) ∧
    (removed.entries.head?.map fun entry =>
      (entry.transaction.id,entry.transaction.payload.width,entry.transaction.annotations.map
        (fun located => (located.2.id.counter,located.2.value)))) = some (id 10 B,1,[(10,false)]) ∧
    (added.allocation.peers A).clock = 11 ∧ (removed.allocation.peers B).clock = 10 ∧
    (added.allocation.peers A).clock ≠ 10 := by decide +kernel

/-- PASS+FAIL: neither toggle's actual mint past contains the other toggle's
reservation. Both pasts do contain the initial mark; they are not empty-past
fixtures masquerading as issuers observing the shared marked state. -/
theorem concurrent_pasts_control :
    (added.entries.head?.map fun entry => entry.past.contains ⟨id 10 B,1⟩) = some false ∧
    (removed.entries.head?.map fun entry => entry.past.contains ⟨id 10 A,2⟩) = some false ∧
    (added.entries.head?.map fun entry => entry.past.contains ⟨id 6 A,1⟩) = some true ∧
    (removed.entries.head?.map fun entry => entry.past.contains ⟨id 6 A,1⟩) = some true ∧
    (removed.entries.head?.map fun entry => entry.past.contains ⟨id 10 A,2⟩) ≠ some true := by decide +kernel

/-- PASS+FAIL: the final actual source evaluator fractures the two atomic
format batches. b follows B's removal while d follows A's later second span.
The canonical transaction replay itself still commits whole transactions. -/
theorem fractured_read_control :
    flags final A = some [true,false,false,true,true] ∧
    flags final A ≠ some [true,false,false,false,true] ∧
    flags final A ≠ some [true,true,false,true,true] := by decide +kernel

/-- No atomic sequential history made from these three format operations,
with arbitrary structural reshapes interspersed, explains the actual read.
The independent theorem is stronger than enumerating the two final toggles:
every format operation selects both b and d and keeps their marks equal. -/
theorem no_atomic_history (document : NotionCoreSpec.Document)
    (events : List NotionCoreFormattingAtomicSpec.HistoryEvent) :
    flags final A ≠ some (NotionCoreFormattingAtomicSpec.flags
      (NotionCoreFormattingAtomicSpec.history (NotionCoreFormattingSpec.plain document) events)) := by
  rw [fractured_read_control.1]
  intro equal
  exact NotionCoreFormattingAtomicSpec.no_plain_history document events (Option.some.inj equal).symm

theorem actual_allocation_unique :
    ∀ left ∈ final.allocation.published, ∀ right ∈ final.allocation.published,
      ∀ item, left.Contains item → right.Contains item → left = right :=
  NotionRunAllocation.reachable_unique_owner (allocation_reachable final_reachable)

def viewFlags (document : NotionCoreRichMRDT.View) : List Bool :=
  NotionCoreFormattingAtomicSpec.addresses.map fun address =>
    (((document.flatMap Prod.snd).find? fun atom => atom.address == address).map
      NotionCoreFormattingMachine.RichAtom.bold).getD false

noncomputable def carrierFlags : Option (List Bool) :=
  (NotionCoreRichMRDT.observe (NotionCoreRichMRDT.carrierFor final A)).map viewFlags

/-- PASS+FAIL: the actual FinsetStore query over whole rich transactions has
the fractured visible read. This uses the derived archive-enumeration bridge;
it does not substitute the list interpreter or a selected-ID renderer for D. -/
theorem actual_carrier_read :
    carrierFlags = some [true,false,false,true,true] ∧
    carrierFlags ≠ some [true,false,false,false,true] ∧
    carrierFlags ≠ some [true,true,false,true,true] := by
  simp only [carrierFlags,NotionCoreRichMRDT.observe_carrierFor final final_reachable A]
  decide +kernel

/-- PASS+FAIL: all five original identities are still displayed. In
particular b's false flag is an actual read, not viewFlags' absent-item
default. The hand-derived display order is abde followed by c. -/
theorem actual_visible_identity_control :
    ((NotionCoreRichMRDT.observe (NotionCoreRichMRDT.carrierFor final A)).map
      fun document => (document.flatMap Prod.snd).map fun atom => (atom.address,atom.bold)) =
      some [(NotionCoreFormattingAtomicSpec.address 1,true),
        (NotionCoreFormattingAtomicSpec.address 2,false),
        (NotionCoreFormattingAtomicSpec.address 4,true),
        (NotionCoreFormattingAtomicSpec.address 5,true),
        (NotionCoreFormattingAtomicSpec.address 3,false)] ∧
    ((NotionCoreRichMRDT.observe (NotionCoreRichMRDT.carrierFor final A)).map
      fun document => (document.flatMap Prod.snd).map fun atom => atom.address) ≠
      some [NotionCoreFormattingAtomicSpec.address 1,NotionCoreFormattingAtomicSpec.address 4,
        NotionCoreFormattingAtomicSpec.address 5,NotionCoreFormattingAtomicSpec.address 3] := by
  rw [NotionCoreRichMRDT.observe_carrierFor final final_reachable A]
  decide +kernel

theorem no_atomic_carrier_history (document : NotionCoreSpec.Document)
    (events : List NotionCoreFormattingAtomicSpec.HistoryEvent) :
    carrierFlags ≠ some (NotionCoreFormattingAtomicSpec.flags
      (NotionCoreFormattingAtomicSpec.history (NotionCoreFormattingSpec.plain document) events)) := by
  rw [actual_carrier_read.1]
  intro equal
  exact NotionCoreFormattingAtomicSpec.no_plain_history document events (Option.some.inj equal).symm

#print axioms final_reachable
#print axioms actual_selection_control
#print axioms clock_and_batch_control
#print axioms fractured_read_control
#print axioms no_atomic_history
#print axioms actual_allocation_unique
#print axioms actual_carrier_read
#print axioms actual_visible_identity_control
#print axioms no_atomic_carrier_history
end Sal.MRDTs.Instances.NotionCoreRichAtomicCounterexample
