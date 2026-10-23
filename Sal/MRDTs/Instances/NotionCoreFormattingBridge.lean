import Sal.MRDTs.Instances.NotionCoreFormattingSpec
import Sal.MRDTs.Instances.NotionCoreFormattingSource

/-!
Immediate sequential formatting refinement under exact visible coverage.

`coordinate` relates retained semantic addresses to physical source preorder
positions. Its correctness, including agreement between source items and core
slots, remains a caller obligation. Exact coverage is an explicit falsifiable
premise, not a theorem about the original JavaScript selection preparation.
The comparison applies a newly issued ordered batch over the current marks.
It does not prove that these operations outrank every existing operation,
preserve future insertion inheritance, or satisfy the Notion protocol's RA VCs.
-/
namespace Sal.MRDTs.Instances.NotionCoreFormattingBridge

open NotionCoreSpec
open NotionCoreFormattingSpec
open NotionCoreOriginTree (Forest)

abbrev Located := Nat × NotionCoreFormattingSource.MarkOp

def coversAt (forests : Nat → Forest) (coordinate : Address → Nat)
    (operation : Located) (address : Address) : Bool :=
  decide (address.1 = operation.1) &&
    NotionCoreFormattingSource.covers (forests operation.1) operation.2 (coordinate address)

/-- The instance guard is essential: positions in different text instances
have independent coordinates even after their slots move between blocks. -/
def applyLocated (forests : Nat → Forest) (coordinate : Address → Nat)
    (operation : Located) (address : Address) (initial : Bool) : Bool :=
  if address.1 = operation.1 then
    NotionCoreFormattingSource.applyOrdered (forests operation.1) [operation.2] (coordinate address) initial
  else initial

theorem applyLocated_eq (forests : Nat → Forest) (coordinate : Address → Nat)
    (operation : Located) (address : Address) (initial : Bool) :
    applyLocated forests coordinate operation address initial =
      if coversAt forests coordinate operation address then operation.2.value else initial := by
  by_cases same : address.1 = operation.1 <;>
    simp [applyLocated, coversAt, same, NotionCoreFormattingSource.applyOrdered_singleton]

def applyBatch (forests : Nat → Forest) (coordinate : Address → Nat)
    (address : Address) : List Located → Bool → Bool
  | [], initial => initial
  | operation :: rest, initial =>
      applyBatch forests coordinate address rest
        (applyLocated forests coordinate operation address initial)

/-- All intervals emitted by one toggle share the issuer's add/remove value.
Overlaps in this immediate batch therefore do not affect its meaning. -/
theorem applyBatch_uniform (forests : Nat → Forest) (coordinate : Address → Nat)
    (address : Address) (operations : List Located) (value initial : Bool)
    (uniform : ∀ operation ∈ operations, operation.2.value = value) :
    applyBatch forests coordinate address operations initial =
      if operations.any (fun operation => coversAt forests coordinate operation address)
      then value else initial := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
    have first := uniform operation (by simp)
    have tail : ∀ op ∈ rest, op.2.value = value := fun op member => uniform op (by simp [member])
    simp only [applyBatch, ih _ tail, applyLocated_eq, List.any_cons, first]
    by_cases firstCover : coversAt forests coordinate operation address = true <;>
      by_cases restCover : rest.any (fun op => coversAt forests coordinate op address) = true <;>
        simp [firstCover, restCover]

def sourceUpdate (s : State) (forests : Nat → Forest) (coordinate : Address → Nat)
    (operations : List Located) : State :=
  {s with bold := fun address => applyBatch forests coordinate address operations (s.bold address)}

/-- Only displayed slots need coverage agreement. Hidden anchors and future
characters may retain different source interval behaviour. -/
def ExactCoverage (doc : Document) (forests : Nat → Forest) (coordinate : Address → Nat)
    (operations : List Located) (targets : List Address) : Prop :=
  ∀ block ∈ doc, block.alive = true → ∀ slot ∈ block.slots, slot.visible = true →
    operations.any (fun operation => coversAt forests coordinate operation slot.address) =
      targets.contains slot.address

/-- A source batch with exactly the selected visible coverage implements the
independent identity assignment at the rich view. No document shape, text,
or unselected visible mark can be changed by this refinement. -/
theorem exact_coverage_refines_assign (s : State) (forests : Nat → Forest)
    (coordinate : Address → Nat) (operations : List Located) (targets : List Address)
    (value : Bool)
    (uniform : ∀ operation ∈ operations, operation.2.value = value)
    (coverage : ExactCoverage s.document forests coordinate operations targets) :
    richView (sourceUpdate s forests coordinate operations) = richView (assign s targets value) := by
  apply richView_congr
  intro block member alive slot retained visible
  change applyBatch forests coordinate slot.address operations (s.bold slot.address) = _
  rw [applyBatch_uniform forests coordinate slot.address operations value _ uniform,
    coverage block member alive slot retained visible]

theorem exact_coverage_refines_toggle (s : State) (forests : Nat → Forest)
    (coordinate : Address → Nat) (operations : List Located) (targets : List Address)
    (uniform : ∀ operation ∈ operations, operation.2.value = toggleValue s targets)
    (coverage : ExactCoverage s.document forests coordinate operations targets) :
    richView (sourceUpdate s forests coordinate operations) = richView (toggle s targets) :=
  exact_coverage_refines_assign s forests coordinate operations targets _ uniform coverage

/-- The actual source preparation refines the independent toggle whenever
its issuer verdict agrees and its intervals have exactly the intended visible
coverage. Neither premise is inferred from the source implementation. -/
theorem prepared_toggle_refines (s : State) (forests : Nat → Forest)
    (coordinate : Address → Nat) (session : NotionRunAllocation.Session) (counter : Nat)
    (selection : List NotionCoreFormattingSource.Character) (targets : List Address)
    (issuerAgreement : selection.all NotionCoreFormattingSource.Character.bold = targets.all s.bold)
    (coverage : ExactCoverage s.document forests coordinate
      (NotionCoreFormattingSource.toggleBold forests session counter selection) targets) :
    richView (sourceUpdate s forests coordinate
      (NotionCoreFormattingSource.toggleBold forests session counter selection)) = richView (toggle s targets) := by
  apply exact_coverage_refines_toggle s forests coordinate _ targets _ coverage
  intro operation member
  rw [NotionCoreFormattingSource.toggleBold_value forests session counter selection operation member]
  simp [toggleValue, issuerAgreement]

/-! Hand-derived positive coverage and an overcoverage falsifier. The physical
forest contains a,b at indices 0,1; the selected identity is a alone. -/
private def forest : Forest :=
  .cons (.node ⟨⟨1, [97]⟩, .text 97 false⟩ .nil)
    (.cons (.node ⟨⟨2, [97]⟩, .text 98 false⟩ .nil) .nil)

private def fixture : State := plain
  [⟨10, 0, [root 0, character 0 (0, 1) 97, character 0 (0, 2) 98], true⟩]

private def coordinates : Address → Nat := fun address =>
  if address = (0, .event (0, 1)) then 0 else 1

private def target : List Address := [(0, .event (0, 1))]

private def exactOperation : Located :=
  (0, ⟨⟨3, [97]⟩, ⟨.start, .before⟩, ⟨.item ⟨2, [97]⟩, .before⟩, true⟩)

private def spillingOperation : Located :=
  (0, ⟨⟨3, [97]⟩, ⟨.start, .before⟩, ⟨.finish, .before⟩, true⟩)

private theorem exact_fixture_coverage :
    ExactCoverage fixture.document (fun _ => forest) coordinates [exactOperation] target := by
  intro block member _ slot retained visible
  change block ∈ [_] at member
  simp only [List.mem_singleton] at member
  subst block
  change slot ∈ [root 0, character 0 (0, 1) 97, character 0 (0, 2) 98] at retained
  simp only [List.mem_cons, List.not_mem_nil, or_false] at retained
  rcases retained with rfl | rfl | rfl
  · simp [root] at visible
  · decide
  · decide

/-- The refinement hypothesis has a concrete witness and excludes the
neighbouring interval that spills onto b. -/
theorem coverage_control :
    ExactCoverage fixture.document (fun _ => forest) coordinates [exactOperation] target ∧
    ¬ ExactCoverage fixture.document (fun _ => forest) coordinates [spillingOperation] target := by
  refine ⟨exact_fixture_coverage, ?_⟩
  intro coverage
  have impossible := coverage
    ⟨10, 0, [root 0, character 0 (0, 1) 97, character 0 (0, 2) 98], true⟩ (by simp [fixture, plain])
    rfl (character 0 (0, 2) 98) (by simp) rfl
  have opposite :
      [spillingOperation].any (fun op => coversAt (fun _ => forest) coordinates op
        (character 0 (0, 2) 98).address) ≠ target.contains (character 0 (0, 2) 98).address := by decide
  exact opposite impossible

/-- The exact interval implements bold(a), and this effect is not a no-op. -/
theorem exact_interval_control :
    richView (sourceUpdate fixture (fun _ => forest) coordinates [exactOperation]) =
      richView (assign fixture target true) ∧
    richView (sourceUpdate fixture (fun _ => forest) coordinates [exactOperation]) ≠
      richView fixture := by
  refine ⟨exact_coverage_refines_assign fixture (fun _ => forest) coordinates [exactOperation]
    target true ?_ exact_fixture_coverage, ?_⟩
  · intro operation member
    simp only [List.mem_singleton] at member
    subst operation
    rfl
  · decide

/-- Covering both a,b cannot implement selecting a alone. The failed general
claim remains refuted when the exact-coverage premise is removed. -/
theorem overcoverage_control :
    richView (sourceUpdate fixture (fun _ => forest) coordinates [spillingOperation]) =
      [(10, [⟨(0, .event (0, 1)), 97, true⟩, ⟨(0, .event (0, 2)), 98, true⟩])] ∧
    richView (sourceUpdate fixture (fun _ => forest) coordinates [spillingOperation]) ≠
      richView (assign fixture target true) := by decide

#print axioms exact_coverage_refines_assign
#print axioms prepared_toggle_refines
#print axioms coverage_control
#print axioms overcoverage_control

end Sal.MRDTs.Instances.NotionCoreFormattingBridge
