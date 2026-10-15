import Sal.MRDTs.Instances.TreeMoveIncremental
import Sal.MRDTs.Paper1.Automation.CommutingAssembly

namespace Sal.MRDTs.Instances.TreeMove.Incremental
open Sal.MRDTs.Foundation
open Sal.MRDTs.Paper1
open Classical

/-- Independent log consistency: every undo edge is the one recorded while
applying older moves, and the materialized tree is the result of that log.
This predicate is checked by receive/merge closure below. It is not an
issuability test and contains no query answer. -/
def Coherent (s : RawState) : Prop := s = canonical (events s)
abbrev State := {s : RawState // Coherent s}

noncomputable def encode (E : Finset Event) : State :=
  ⟨canonical E,by simp [Coherent,canonical_events]⟩
def decode (s : State) : Finset Event := events s.val

@[simp] theorem decode_encode (E : Finset Event) : decode (encode E) = E := canonical_events E
@[simp] theorem encode_decode (s : State) : encode (decode s) = s := by
  apply Subtype.ext
  exact s.property.symm

theorem decode_injective : Function.Injective decode := by
  intro a b eq
  rw [← encode_decode a,← encode_decode b,eq]

theorem receive_coherent {s : RawState} (coherent : Coherent s) (e : Event) :
    Coherent (receive s e) := by
  rw [coherent,receive_canonical]
  simp [Coherent,canonical_events]

noncomputable def update (s : State) (e : Event) : State :=
  ⟨receive s.val e,receive_coherent s.property e⟩

@[simp] theorem update_encode (E : Finset Event) (e : Event) :
    update (encode E) e = encode (insert e E) := by
  apply Subtype.ext
  exact receive_canonical E e

@[simp] theorem decode_update (s : State) (e : Event) :
    decode (update s e) = insert e (decode s) := by
  rw [← encode_decode s,update_encode,decode_encode]
  simp only [decode_encode]

theorem receive_fold (ops : List Event) (E : Finset Event) :
    ops.foldl receive (canonical E) = canonical (E ∪ ops.toFinset) := by
  induction ops generalizing E with
  | nil => simp
  | cons e rest ih =>
    simp only [List.foldl_cons,receive_canonical,ih,List.toFinset_cons]
    congr 1
    ext x; simp <;> tauto

/-- State exchange runs the source delivery algorithm on the other branch's
log. Shared events are suppressed by receive. The ancestor is immaterial for
this op-based algorithm's state exchange; no tree is replayed from scratch. -/
noncomputable def mergeRaw (_l a b : RawState) : RawState :=
  (b.log.map LogEntry.event).foldl receive a

theorem mergeRaw_canonical (L A B : Finset Event) :
    mergeRaw (canonical L) (canonical A) (canonical B) = canonical (A ∪ B) := by
  rw [mergeRaw,receive_fold]
  change canonical (A ∪ events (canonical B)) = _
  rw [canonical_events]

theorem mergeRaw_coherent {l a b : RawState}
    (ha : Coherent a) : Coherent (mergeRaw l a b) := by
  unfold mergeRaw
  rw [ha,receive_fold]
  simp [Coherent,canonical_events]

noncomputable def merge (l a b : State) : State :=
  ⟨mergeRaw l.val a.val b.val,mergeRaw_coherent a.property⟩

@[simp] theorem merge_encode (L A B : Finset Event) :
    merge (encode L) (encode A) (encode B) = encode (A ∪ B) := by
  apply Subtype.ext
  exact mergeRaw_canonical L A B

@[simp] theorem decode_merge (l a b : State) :
    decode (merge l a b) = decode a ∪ decode b := by
  rw [← encode_decode l,← encode_decode a,← encode_decode b,merge_encode,decode_encode]
  simp only [decode_encode]

/-- Query reads the maintained tree. It does not sort or inspect the log. -/
noncomputable def query (s : State) : Tree := visibleTree s.val.tree

@[simp] theorem query_encode (E : Finset Event) :
    query (encode E) = visibleTree (render E) := by
  change visibleTree (canonical E).tree = _
  rw [canonical_tree]

noncomputable def D : MRDTSig where
  State := State
  dec_state := Classical.decEq _
  init := encode ∅
  AppOp := Move
  dec_op := inferInstance
  Query := Unit
  Value := Tree
  update := update
  query s _ := query s
  merge := merge

/-- Editor wrapper for the source forest algorithm. Fresh event identifiers
are required and the distinguished root/trash sentinels cannot be moved.
Destinations need not exist or be visible; hidden children can be restored.
The raw Fig.4 algorithm itself does not reserve either sentinel. -/
def sourceApplicable (e : Event) (origin : Finset Event) : Prop :=
  (∀ old ∈ origin, (old.1,old.2.1) ≠ (e.1,e.2.1)) ∧
  e.op.child ≠ root ∧ e.op.child ≠ trash

def canIssue (e : Event) (s : State) : Prop := sourceApplicable e (decode s)

theorem canIssue_iff (e : Event) (s : State) :
    canIssue e s ↔ sourceApplicable e (decode s) := Iff.rfl

/-- Source forest/trash destinations have no existence or visibility guard. -/
theorem canIssue_parent (s : State) (e : Event) (parent : Node) :
    canIssue (e.1,e.2.1,⟨parent,e.op.metadata,e.op.child⟩) s ↔ canIssue e s := by
  rfl

def generation : Issuance D where
  CanIssue := canIssue

theorem all_comm (a b : Event) : D.toUpdateSig.commutes a b := by
  intro s
  apply decode_injective
  change decode (update (update s a) b) = decode (update (update s b) a)
  simp [Finset.insert_comm]

/-- Exact-state kernels are transported through the proved log/tree
isomorphism, not through observation equality. The state includes oldParent
metadata and rejected operations. -/
theorem kernels : Automation.TransferSimple.EmptyPastKernels D := by
  constructor
  · intro l a b; apply decode_injective
    change decode (merge l a b) = decode (merge l b a)
    simp [Finset.union_comm]
  · intro s; apply decode_injective
    change decode (merge (encode ∅) (encode ∅) s) = decode s
    simp
  · intro s e; apply decode_injective
    change decode (merge (encode ∅) s (update (encode ∅) e)) = decode (update s e)
    ext x; simp <;> tauto
  · intro l B t b e; apply decode_injective
    change decode (merge l (merge B t (update B e)) b) =
      decode (merge B (merge l t b) (update B e))
    ext x; simp <;> tauto
  · intro B t₀ t₁ t₂ e; apply decode_injective
    change decode (merge (merge B t₀ (update B e)) (merge B t₁ (update B e))
        (merge B t₂ (update B e))) = decode (merge B (merge t₀ t₁ t₂) (update B e))
    ext x; simp <;> tauto

def input : Automation.CommonVerification.Input D (commutingPolicy Move)
    (ConcreteMRDT.CommutingPort.representation D)
    (ConcreteMRDT.CommutingPort.scheme all_comm) :=
  .commuting all_comm kernels rfl rfl rfl

theorem fiveVC : ConcreteMRDT.Raw.MergeVCs (commutingPolicy Move)
    (ConcreteMRDT.CommutingPort.representation D)
    (ConcreteMRDT.CommutingPort.scheme all_comm) :=
  Automation.CommonVerification.verify input

theorem joinAt (C : ReplayContext D.toUpdateSig) : JoinAt D C :=
  ConcreteMRDT.CommutingPort.automatedJoinAt all_comm fiveVC C

theorem decode_applySeq (s : State) (ops : List Event) :
    decode (applySeq D.toUpdateSig s ops) = decode s ∪ ops.toFinset := by
  induction ops generalizing s with
  | nil => simp [applySeq]
  | cons e rest ih =>
    change decode (applySeq D.toUpdateSig (update s e) rest) = _
    rw [ih,decode_update]
    ext x; simp <;> tauto

theorem applySeq_initial (ops : List Event) :
    applySeq D.toUpdateSig D.init ops = encode ops.toFinset := by
  apply decode_injective
  rw [decode_applySeq]
  change decode (encode ∅) ∪ ops.toFinset = _
  simp

theorem fold_query (ops : List Event) :
    D.query (applySeq D.toUpdateSig D.init ops) () =
      Sal.MRDTs.Instances.TreeMove.D.query ops.toFinset () := by
  rw [applySeq_initial]
  exact query_encode _

#print axioms receive_coherent
#print axioms mergeRaw_coherent
#print axioms fiveVC
#print axioms joinAt
end Sal.MRDTs.Instances.TreeMove.Incremental
