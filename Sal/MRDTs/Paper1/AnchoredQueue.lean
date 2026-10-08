import Sal.MRDTs.Paper1.CertifiedRGAInvariantCertificate

/-! A compact anchored-enqueue queue. The live-list implementation uses the
embedded-chain kernel; its issuance discipline and independent FIFO semantics
are different from the sequence datatype. No removed birth records are stored.
The carried coordinate certifies the observed tail's position, even if that
anchor is removed on another branch before delivery. -/
namespace Sal.MRDTs.Paper1.AnchoredQueue
open Foundation Instances.EmbedRGA Sal.EmbedRGA

abbrev Event := Op (EOp Nat)
abbrev State := EState Nat
abbrev Q : MRDTSig := E unaryCode Nat

/-- Public queue observation matches the existing tagged-head interface. The
full value-list kernel query is retained for stronger internal controls. -/
def headQuery (s : State) (_ : Unit) : Option (Nat × Nat) :=
  s.head?.map (fun r => (r.1,r.2.1))

def publicQueue : MRDTSig := { Q with
  Value := Option (Nat × Nat)
  query := headQuery }


def enq (value : Nat) (tail : Nat) (coordinate : List Bool) : EOp Nat :=
  .ins value coordinate tail
def deq (head : Nat) : EOp Nat := .del head

def CanIssue (e : Event) (s : State) : Prop :=
  match e with
  | (t, _, .ins _ pref anchor) => anchor < t ∧
      ((s = [] ∧ anchor = 0 ∧ pref = []) ∨
        s.getLast?.map (fun r => (r.1,r.2.2)) = some (anchor,pref))
  | (_, _, .del target) => s.head?.map Prod.fst = some target

def issuance : Issuance Q := ⟨CanIssue⟩

/-- FIFO abstraction ignores both the tail identity and its coordinate. -/
def fifoStep (s : List (Nat × Nat)) (e : Event) : List (Nat × Nat) :=
  match e.op with
  | .ins value _ _ => s ++ [(e.time,value)]
  | .del target => s.filter (fun r => decide (r.1 ≠ target))

def fifoFold (es : List Event) : List (Nat × Nat) := es.foldl fifoStep []

def fifoApplicable (s : List (Nat × Nat)) (e : Event) : Prop :=
  match e.op with
  | .ins _ _ _ => e.time ∉ s.map Prod.fst
  | .del target => target ∉ s.map Prod.fst ∨ s.head?.map Prod.fst = some target

def fifoLegal (es : List Event) : Prop :=
  ∀ pre e post, es = pre ++ e :: post → fifoApplicable (fifoFold pre) e ∧
    (eIsIns e = true → e.time ∉ eInsIds pre) ∧
    (∀ target, e.op = .del target → target ∈ eInsIds pre)

noncomputable def fifoSpec : SequentialSpec Q where
  State := List (Nat × Nat)
  init := []
  step := fifoStep
  Legal := fifoLegal
  query := fun s _ => s.map Prod.snd

theorem fifoLegal_prefix {xs ys : List Event} (h : fifoLegal (xs ++ ys)) :
    fifoLegal xs := by
  intro pre e post eq
  apply h pre e (post ++ ys)
  simp [eq,List.append_assoc]

/-- Independent history language, with named-head legality and idempotent
absent deletion. It never consults representation coordinates or replay state. -/
noncomputable def language := GuardedHistory.language fifoSpec

theorem issue_implies_embedded {e : Event} {s : State} (h : CanIssue e s) :
    eApplicable e s := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | ins value pref anchor =>
      obtain ⟨ht, empty | last⟩ := h
      · exact ⟨ht,Or.inl ⟨empty.2.1,empty.2.2⟩⟩
      · obtain ⟨⟨a,v,p⟩,mem,eq⟩ := Option.map_eq_some_iff.mp last
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
        exact ⟨ht,Or.inr ⟨v,List.mem_of_getLast? mem⟩⟩
  | del target =>
      obtain ⟨⟨a,v,p⟩,mem,eq⟩ := Option.map_eq_some_iff.mp h
      change a = target at eq
      subst a
      exact List.mem_map.mpr ⟨_,List.mem_of_head? mem,rfl⟩

/-- Head-only deletion makes deleting an observed tail a singleton case.
This fact is specific to queue issuance, and fails for arbitrary sequence deletion. -/
theorem deleting_tail_is_singleton {s : State} {target t r : Nat}
    (ids : (eIds s).Nodup) (head : CanIssue (t,r,deq target) s)
    (tail : s.getLast?.map Prod.fst = some target) : s.length = 1 := by
  cases s with
  | nil => simp [CanIssue,deq] at head
  | cons a xs =>
      have ha : a.1 = target := by simpa [CanIssue,deq] using head
      cases xs with
      | nil => rfl
      | cons b bs =>
          have hn : a.1 ∉ eIds (b :: bs) := (List.nodup_cons.mp ids).1
          simp only [List.getLast?_cons_cons] at tail
          obtain ⟨x,hx,he⟩ := Option.map_eq_some_iff.mp tail
          have hm : target ∈ eIds (b :: bs) :=
            List.mem_map.mpr ⟨x,List.mem_of_getLast? hx,he⟩
          exact False.elim (hn (ha.symm ▸ hm))

instance (e : Event) (s : State) : Decidable (CanIssue e s) := by
  unfold CanIssue
  split <;> infer_instance
instance (s : List (Nat × Nat)) (e : Event) : Decidable (fifoApplicable s e) := by
  unfold fifoApplicable
  split <;> infer_instance

theorem mint_weaken {C : Configuration Q} (h : MintHonest Q CanIssue C) :
    MintHonest Q (generation unaryCode).CanIssue C := by
  intro e he
  obtain ⟨ops,perm,order,guard⟩ := h e he
  exact ⟨ops,perm,order,issue_implies_embedded guard⟩

theorem issued_weaken {C C' : Configuration Q} {l : Label Q}
    (h : IssuedStep Q issuance C l C') :
    IssuedStep Q (generation unaryCode) C l C' := by
  cases h with
  | nonApply raw non => exact .nonApply raw non
  | apply head version guard raw => exact .apply head version (issue_implies_embedded guard) raw

theorem reach_weaken {C : Configuration Q} (h : MintCertifiedReach Q issuance C) :
    MintCertifiedReach Q (generation unaryCode) C := by
  induction h with
  | init => exact .init
  | step _ before step after ih =>
      exact .step ih (mint_weaken before) (issued_weaken step) (mint_weaken after)

theorem issuedV_weaken {C C' : Configuration Q} {l : Label Q}
    (h : IssuedStepV Q (canonicalVirtualMergeBase Q) issuance C l C') :
    IssuedStepV Q (canonicalVirtualMergeBase Q) (generation unaryCode) C l C' := by
  cases h with
  | base one => exact .base (issued_weaken one)
  | virtual raw non => exact .virtual raw non

theorem reachV_weaken {C : Configuration Q}
    (h : MintCertifiedReachV Q (canonicalVirtualMergeBase Q) issuance C) :
    MintCertifiedReachV Q (canonicalVirtualMergeBase Q) (generation unaryCode) C := by
  induction h with
  | init => exact .init
  | step _ before step after ih =>
      exact .step ih (mint_weaken before) (issuedV_weaken step) (mint_weaken after)

theorem execution_weaken {C : Configuration Q} (h : CertifiedExecution Q issuance C) :
    CertifiedExecution Q (generation unaryCode) C := by
  cases h with
  | ordinary h => exact .ordinary (reach_weaken h)
  | virtual h => exact .virtual (reachV_weaken h)

abbrev Valid (C : Configuration Q) := CertifiedRGAInvariant.Valid unaryCode C.replayContext

/-- Representation closure is independent of FIFO linearization. -/
theorem closed {C : Configuration Q} (h : CertifiedExecution Q issuance C) :
    InvariantOrder.Closed Q C.replayContext (Valid C) :=
  CertifiedRGAInvariantCertificate.closed unaryCode (execution_weaken h)

theorem stored_valid {C : Configuration Q} (h : CertifiedExecution Q issuance C)
    {v s H} (stored : C.ver v = some (s,H)) : Valid C s :=
  CertifiedRGAInvariantCertificate.stored_valid unaryCode (execution_weaken h) stored

theorem virtual_base_valid {C : Configuration Q} (h : CertifiedExecution Q issuance C)
    {v w s t H K} (left : C.ver v = some (s,H)) (right : C.ver w = some (t,K)) :
    Valid C (virtualMergeBaseState C v w) :=
  CertifiedRGAInvariantCertificate.virtual_base_valid unaryCode (execution_weaken h) left right

theorem concurrent_commutes {C : Configuration Q} (h : CertifiedExecution Q issuance C)
    {a b : Event} (ha : a ∈ C.events) (hb : b ∈ C.events)
    (notab : ¬ C.vis a b) (notba : ¬ C.vis b a) :
    InvariantOrder.Commutes Q.toUpdateSig (Valid C) a b :=
  CertifiedRGAInvariantReplay.concurrent_commutes unaryCode C.replayContext
    (eHonest_core (eHonest_of_mint (execution_weaken h).mintHonest)) a b ha hb notab notba

theorem scoped_laws {C : Configuration Q} (h : CertifiedExecution Q issuance C)
    {v s H} (stored : C.ver v = some (s,H)) :
    InvariantReplay.RestrictedLaws (CertifiedRGAInvariantReplay.scope unaryCode C H)
      (Valid C) CertifiedRGAInvariantReplay.policy :=
  CertifiedRGAInvariantReplay.laws unaryCode (execution_weaken h) stored

/-- Named new-framework merge VC package for the compact queue kernel.
Issuance restriction changes no effector or merge algebra. -/
theorem mergeVCs : ConcreteMRDT.Raw.MergeVCs
    CertifiedRGAVCReplay.Embedded.policy
    (CertifiedRGAVCReplay.Embedded.representation (α := Nat) unaryCode)
    (CertifiedRGAVCReplay.Embedded.scheme unaryCode) :=
  CertifiedRGAVC.Embedded.mergeVCs unaryCode

theorem representationJoin : ConcreteMRDT.RepresentationJoin
    (CertifiedRGAVCReplay.Embedded.representation (α := Nat) unaryCode) :=
  CertifiedRGAVC.Embedded.representationJoin unaryCode

theorem storedCanonical {C : Configuration Q} (h : CertifiedExecution Q issuance C)
    {v s H} (stored : C.ver v = some (s,H)) :
    InvariantReplay.Canonical (CertifiedRGAInvariantReplay.scope unaryCode C H)
      (Valid C) CertifiedRGAInvariantReplay.policy Q.init s :=
  CertifiedRGAInvariantReplay.storedCanonical unaryCode (execution_weaken h) stored

theorem storedCanonicalV {C : Configuration Q}
    (h : MintCertifiedReachV Q (canonicalVirtualMergeBase Q) issuance C)
    {v s H} (stored : C.ver v = some (s,H)) :
    InvariantReplay.Canonical (CertifiedRGAInvariantReplay.scope unaryCode C H)
      (Valid C) CertifiedRGAInvariantReplay.policy Q.init s :=
  storedCanonical (.virtual h) stored

#print axioms concurrent_commutes
#print axioms scoped_laws
end Sal.MRDTs.Paper1.AnchoredQueue
