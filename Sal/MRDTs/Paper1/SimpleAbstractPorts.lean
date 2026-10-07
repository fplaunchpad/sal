import Sal.MRDTs.Paper1.CommutingVCReplay
import Sal.MRDTs.Paper1.SimpleEventPorts

/-! Abstraction-VC ports of the eight simple production MRDTs. Each abstraction
retains exactly the state returned by its public query (set, finite set,
Boolean function, or integer). Independent list-based history languages are
reused from SimpleEventPorts. Join and represented-version supply are derived
through the metadata VC induction, not taken from the old Join certificates. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT.SimplePorts
open Foundation
open SimpleEventPorts (setMachine finiteMachine booleanMachine deltaMachine)
noncomputable section

/-- Identity abstraction for datatypes whose public query exposes all state.
This semantic model is separate from the independent history specification. -/
def identity (D : MRDTSig) : Model D where
  Abstract := D.State
  abs := id
  step := D.update
  read := D.query
  update_abs := fun _ _ => rfl
  query_abs := fun _ _ => rfl

theorem identity_complete (D : MRDTSig) (q : D.Query)
    (separates : ∀ s t, D.query s q = D.query t q → s = t) :
    (identity D).QueryComplete := by
  intro s t h
  exact separates s t (h [] q)

variable {A : Type} [DecidableEq A]

namespace Add
abbrev D := SimpleEventPorts.Add.D (A := A)
abbrev generation := SimpleEventPorts.Add.generation (A := A)
def model : Model (D (A := A)) := identity D

theorem complete : (model (A := A)).QueryComplete :=
  identity_complete D () (fun _ _ h => h)

theorem compatible : SpecificationCompatibility (model (A := A)) setMachine.toSpec :=
  fun a b _ => SimpleEventPorts.Add.commutes a b

def conditions : VCConditions (model (A := A)) (commutingPolicy A) setMachine.toSpec generation where
  toVCReplayConditions := CommutingPort.vcReplayConditions model complete
    Instances.AddStore.all_comm Instances.AddStore.mergeLaws Instances.AddStore.deltaLaws
    Instances.AddStore.commutingPeelLaw generation
  compatibility := compatible
  historySound := SimpleEventPorts.Add.simulation.sound

abbrev certificate := (conditions (A := A)).toCertificate

theorem versions {C : Configuration (D (A := A))}
    (reach : MintCertifiedReach D generation C) :
    VersionsRALinearizable model (commutingPolicy A) setMachine.toSpec C :=
  certificate.versions reach

theorem versionsV {C : Configuration (D (A := A))}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C) :
    VersionsRALinearizable model (commutingPolicy A) setMachine.toSpec C :=
  certificate.versionsV reach

theorem executions (trace : List (Label (D (A := A)) × Configuration D))
    (run : (certifiedTS D generation).Execution (initConfig D) trace) :
    ExecutionCorrect model (commutingPolicy A) setMachine.toSpec trace :=
  conditions.executions trace run

theorem executionsV (trace : List (Label (D (A := A)) × Configuration D))
    (run : (certifiedTSV D generation).Execution (initConfig D) trace) :
    ExecutionCorrect model (commutingPolicy A) setMachine.toSpec trace :=
  conditions.executionsV trace run
end Add

namespace Finite
abbrev D := SimpleEventPorts.Finite.D (A := A)
abbrev generation := SimpleEventPorts.Finite.generation (A := A)
def model : Model (D (A := A)) := identity D

theorem complete : (model (A := A)).QueryComplete :=
  identity_complete D () (fun _ _ h => h)

theorem compatible : SpecificationCompatibility (model (A := A)) finiteMachine.toSpec :=
  fun a b _ => SimpleEventPorts.Finite.commutes a b

def conditions : VCConditions (model (A := A)) (commutingPolicy A) finiteMachine.toSpec generation where
  toVCReplayConditions := CommutingPort.vcReplayConditions model complete
    Instances.FinsetStore.all_comm Instances.FinsetStore.mergeLaws Instances.FinsetStore.deltaLaws
    Instances.FinsetStore.commutingPeelLaw generation
  compatibility := compatible
  historySound := SimpleEventPorts.Finite.simulation.sound

abbrev certificate := (conditions (A := A)).toCertificate

theorem versions {C : Configuration (D (A := A))}
    (reach : MintCertifiedReach D generation C) :
    VersionsRALinearizable model (commutingPolicy A) finiteMachine.toSpec C :=
  certificate.versions reach

theorem versionsV {C : Configuration (D (A := A))}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C) :
    VersionsRALinearizable model (commutingPolicy A) finiteMachine.toSpec C :=
  certificate.versionsV reach

theorem executions (trace : List (Label (D (A := A)) × Configuration D))
    (run : (certifiedTS D generation).Execution (initConfig D) trace) :
    ExecutionCorrect model (commutingPolicy A) finiteMachine.toSpec trace :=
  conditions.executions trace run

theorem executionsV (trace : List (Label (D (A := A)) × Configuration D))
    (run : (certifiedTSV D generation).Execution (initConfig D) trace) :
    ExecutionCorrect model (commutingPolicy A) finiteMachine.toSpec trace :=
  conditions.executionsV trace run
end Finite

namespace Boolean
abbrev D := SimpleEventPorts.Boolean.D (A := A)
abbrev generation := SimpleEventPorts.Boolean.generation (A := A)
def model : Model (D (A := A)) := identity D

theorem complete : (model (A := A)).QueryComplete :=
  identity_complete D () (fun _ _ h => h)

theorem compatible : SpecificationCompatibility (model (A := A)) booleanMachine.toSpec :=
  fun a b _ => SimpleEventPorts.Boolean.commutes a b

def conditions : VCConditions (model (A := A)) (commutingPolicy A) booleanMachine.toSpec generation where
  toVCReplayConditions := CommutingPort.vcReplayConditions model complete
    Instances.FlatGrowOnly.all_comm Instances.FlatGrowOnly.mergeLaws Instances.FlatGrowOnly.deltaLaws
    Instances.FlatGrowOnly.commutingPeelLaw generation
  compatibility := compatible
  historySound := SimpleEventPorts.Boolean.simulation.sound

abbrev certificate := (conditions (A := A)).toCertificate

theorem versions {C : Configuration (D (A := A))}
    (reach : MintCertifiedReach D generation C) :
    VersionsRALinearizable model (commutingPolicy A) booleanMachine.toSpec C :=
  certificate.versions reach

theorem versionsV {C : Configuration (D (A := A))}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C) :
    VersionsRALinearizable model (commutingPolicy A) booleanMachine.toSpec C :=
  certificate.versionsV reach

theorem executions (trace : List (Label (D (A := A)) × Configuration D))
    (run : (certifiedTS D generation).Execution (initConfig D) trace) :
    ExecutionCorrect model (commutingPolicy A) booleanMachine.toSpec trace :=
  conditions.executions trace run

theorem executionsV (trace : List (Label (D (A := A)) × Configuration D))
    (run : (certifiedTSV D generation).Execution (initConfig D) trace) :
    ExecutionCorrect model (commutingPolicy A) booleanMachine.toSpec trace :=
  conditions.executionsV trace run
end Boolean

namespace Delta
variable (delta : A → Int)
abbrev D := SimpleEventPorts.Delta.D delta
abbrev generation := SimpleEventPorts.Delta.generation delta
def model : Model (D delta) := identity (D delta)

theorem complete : (model delta).QueryComplete :=
  identity_complete (D delta) () (fun _ _ h => h)

theorem compatible : SpecificationCompatibility (model delta) (deltaMachine delta).toSpec :=
  fun a b _ => SimpleEventPorts.Delta.commutes delta a b

def conditions : VCConditions (model delta) (commutingPolicy A)
    (deltaMachine delta).toSpec (generation delta) where
  toVCReplayConditions := CommutingPort.vcReplayConditions (model delta) (complete delta)
    (Instances.FlatCounters.all_comm delta) (Instances.FlatCounters.mergeLaws delta)
    (Instances.FlatCounters.deltaLaws delta) (Instances.FlatCounters.commutingPeelLaw delta)
    (generation delta)
  compatibility := compatible delta
  historySound := (SimpleEventPorts.Delta.simulation delta).sound

abbrev certificate := (conditions delta).toCertificate

theorem versions {C : Configuration (D delta)}
    (reach : MintCertifiedReach (D delta) (generation delta) C) :
    VersionsRALinearizable (model delta) (commutingPolicy A) (deltaMachine delta).toSpec C :=
  (certificate delta).versions reach

theorem versionsV {C : Configuration (D delta)}
    (reach : MintCertifiedReachV (D delta) (canonicalVirtualMergeBase (D delta)) (generation delta) C) :
    VersionsRALinearizable (model delta) (commutingPolicy A) (deltaMachine delta).toSpec C :=
  (certificate delta).versionsV reach

theorem executions (trace : List (Label (D delta) × Configuration (D delta)))
    (run : (certifiedTS (D delta) (generation delta)).Execution (initConfig (D delta)) trace) :
    ExecutionCorrect (model delta) (commutingPolicy A) (deltaMachine delta).toSpec trace :=
  (conditions delta).executions trace run

theorem executionsV (trace : List (Label (D delta) × Configuration (D delta)))
    (run : (certifiedTSV (D delta) (generation delta)).Execution (initConfig (D delta)) trace) :
    ExecutionCorrect (model delta) (commutingPolicy A) (deltaMachine delta).toSpec trace :=
  (conditions delta).executionsV trace run
end Delta

/-- Names matching the eight registry entries. GSet and generic AddStore share
one checked family; counter and IOC both have mathematical delta one. -/
abbrev gsetConditions := Add.conditions (A := Nat)
abbrev addStoreConditions := Add.conditions (A := Nat)
abbrev finiteAddConditions := Finite.conditions (A := Nat)
abbrev counterConditions := Delta.conditions (A := Unit) (fun _ => 1)
abbrev iocConditions := Delta.conditions (A := Instances.FlatCounters.IOCOp) (fun _ => 1)
abbrev pnConditions := Delta.conditions Instances.FlatCounters.pnDelta
abbrev booleanSetConditions := Boolean.conditions (A := Nat)
abbrev booleanMapConditions := Boolean.conditions (A := Nat × Nat)

abbrev gsetVersions {C : Configuration (Add.D (A := Nat))} := Add.versions (C := C)
abbrev gsetVersionsV {C : Configuration (Add.D (A := Nat))} := Add.versionsV (C := C)
abbrev addStoreVersions {C : Configuration (Add.D (A := Nat))} := Add.versions (C := C)
abbrev addStoreVersionsV {C : Configuration (Add.D (A := Nat))} := Add.versionsV (C := C)
abbrev finiteAddVersions {C : Configuration (Finite.D (A := Nat))} := Finite.versions (C := C)
abbrev finiteAddVersionsV {C : Configuration (Finite.D (A := Nat))} := Finite.versionsV (C := C)
abbrev counterVersions {C : Configuration (Delta.D (A := Unit) (fun _ => 1))} :=
  Delta.versions (C := C) (fun _ => 1)
abbrev counterVersionsV {C : Configuration (Delta.D (A := Unit) (fun _ => 1))} :=
  Delta.versionsV (C := C) (fun _ => 1)
abbrev iocVersions {C : Configuration (Delta.D (A := Instances.FlatCounters.IOCOp) (fun _ => 1))} :=
  Delta.versions (C := C) (fun _ => 1)
abbrev iocVersionsV {C : Configuration (Delta.D (A := Instances.FlatCounters.IOCOp) (fun _ => 1))} :=
  Delta.versionsV (C := C) (fun _ => 1)
abbrev pnVersions {C : Configuration (Delta.D Instances.FlatCounters.pnDelta)} :=
  Delta.versions (C := C) Instances.FlatCounters.pnDelta
abbrev pnVersionsV {C : Configuration (Delta.D Instances.FlatCounters.pnDelta)} :=
  Delta.versionsV (C := C) Instances.FlatCounters.pnDelta
abbrev booleanSetVersions {C : Configuration (Boolean.D (A := Nat))} := Boolean.versions (C := C)
abbrev booleanSetVersionsV {C : Configuration (Boolean.D (A := Nat))} := Boolean.versionsV (C := C)
abbrev booleanMapVersions {C : Configuration (Boolean.D (A := Nat × Nat))} := Boolean.versions (C := C)
abbrev booleanMapVersionsV {C : Configuration (Boolean.D (A := Nat × Nat))} := Boolean.versionsV (C := C)

abbrev gsetExecutions := Add.executions (A := Nat)
abbrev gsetExecutionsV := Add.executionsV (A := Nat)
abbrev addStoreExecutions := Add.executions (A := Nat)
abbrev addStoreExecutionsV := Add.executionsV (A := Nat)
abbrev finiteAddExecutions := Finite.executions (A := Nat)
abbrev finiteAddExecutionsV := Finite.executionsV (A := Nat)
abbrev counterExecutions := Delta.executions (A := Unit) (fun _ => 1)
abbrev counterExecutionsV := Delta.executionsV (A := Unit) (fun _ => 1)
abbrev iocExecutions := Delta.executions (A := Instances.FlatCounters.IOCOp) (fun _ => 1)
abbrev iocExecutionsV := Delta.executionsV (A := Instances.FlatCounters.IOCOp) (fun _ => 1)
abbrev pnExecutions := Delta.executions Instances.FlatCounters.pnDelta
abbrev pnExecutionsV := Delta.executionsV Instances.FlatCounters.pnDelta
abbrev booleanSetExecutions := Boolean.executions (A := Nat)
abbrev booleanSetExecutionsV := Boolean.executionsV (A := Nat)
abbrev booleanMapExecutions := Boolean.executions (A := Nat × Nat)
abbrev booleanMapExecutionsV := Boolean.executionsV (A := Nat × Nat)

/-- Existing hand-derived PASS+FAIL language controls are unchanged by the
abstraction VC port; acceptance does not consult the chosen abstraction. -/
abbrev add_control := SimpleEventPorts.add_control
abbrev finite_add_control := SimpleEventPorts.finite_add_control
abbrev increment_control := SimpleEventPorts.increment_control
abbrev pn_control := SimpleEventPorts.pn_control
abbrev boolean_control := SimpleEventPorts.boolean_control
abbrev immutable_map_control := SimpleEventPorts.immutable_map_control

#print axioms gsetConditions
#print axioms addStoreConditions
#print axioms finiteAddConditions
#print axioms counterConditions
#print axioms iocConditions
#print axioms pnConditions
#print axioms booleanSetConditions
#print axioms booleanMapConditions
#print axioms pnExecutionsV
end
end Sal.MRDTs.Paper1.AbstractMRDT.SimplePorts
