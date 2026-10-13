import Sal.MRDTs.Paper1.Automation.TransferSimple

/-! Corrected candidate, NOT source-equivalent and NOT identified with the
missing manuscript definition. Transfer credits and debits use additive
three-way merge. Rebalance is prepared into an explicit transfer request;
its effect does not re-read the concurrent state. -/
namespace Sal.MRDTs.Instances.TransferableBoundedCounter.Corrected
open Foundation
open Classical

inductive Action where
  | participants (ids : Finset Nat)
  | allocate (amount : Nat)
  | transfer (amount target : Nat)
  | rebalance (amount target : Nat)
  deriving DecidableEq

structure State where
  credits : Nat → Int
  debits : Nat → Int
  allocations : Nat → Int
  members : Finset Nat

def initial (capacity owner : Nat) : State :=
  ⟨fun r => if r = owner then capacity else 0, fun _ => 0, fun _ => 0, ∅⟩
def available (s : State) (r : Nat) : Int := s.credits r - s.debits r - s.allocations r

def bump (f : Nat → Int) (r amount : Nat) : Nat → Int :=
  fun k => f k + if k = r then (amount : Int) else 0

def update (s : State) (e : Op Action) : State := match e.op with
  | .participants ids => { s with members := s.members ∪ ids }
  | .allocate n => { s with allocations := bump s.allocations e.2.1 n }
  | .transfer n target | .rebalance n target =>
    { s with credits := bump s.credits target n, debits := bump s.debits e.2.1 n }

def applicable (owner : Nat) (s : State) (e : Op Action) : Prop := match e.op with
  | .participants _ => True
  | .allocate n | .transfer n _ => (n : Int) ≤ available s e.2.1
  | .rebalance n target =>
    target ∈ insert owner s.members ∧ e.2.1 ∈ insert owner s.members ∧
    (∀ r ∈ insert owner s.members, available s target ≤ available s r ∧ available s r ≤ available s e.2.1) ∧
    (n : Int) = (available s e.2.1 - available s target) / 2 ∧
    (n : Int) ≤ available s e.2.1

/-- Credits, debits and allocations combine by inclusion/exclusion at the
actual common base. Membership combines by grow-only union. -/
def merge (base a b : State) : State :=
  ⟨fun r => a.credits r + b.credits r - base.credits r,
   fun r => a.debits r + b.debits r - base.debits r,
   fun r => a.allocations r + b.allocations r - base.allocations r,
   a.members ∪ b.members⟩

inductive Query where
  | available (replica : Nat)
  | reserved (replica : Nat)
  | allocated (replica : Nat)
  deriving DecidableEq

def reserved (s : State) (r : Nat) : Int := s.credits r - s.debits r

def query (s : State) : Query → Int
  | .available r => available s r
  | .reserved r => reserved s r
  | .allocated r => s.allocations r

noncomputable def D (capacity owner : Nat) : MRDTSig where
  State := State
  dec_state := fun _ _ => Classical.propDecidable _
  init := initial capacity owner
  AppOp := Action
  dec_op := inferInstance
  Query := Query
  Value := Int
  update := update
  query := query
  merge := merge

@[ext] theorem state_ext {s t : State}
    (c : ∀ r, s.credits r = t.credits r)
    (d : ∀ r, s.debits r = t.debits r)
    (a : ∀ r, s.allocations r = t.allocations r)
    (m : s.members = t.members) : s = t := by
  cases s; cases t
  simp_all only [State.mk.injEq]
  exact ⟨funext c, funext d, funext a, trivial⟩

theorem all_comm (capacity owner : Nat) : ∀ a b : Op Action,
    (D capacity owner).toUpdateSig.commutes a b := by
  rintro ⟨ta,ra,oa⟩ ⟨tb,rb,ob⟩ s
  change update (update s (ta,ra,oa)) (tb,rb,ob) = update (update s (tb,rb,ob)) (ta,ra,oa)
  cases oa <;> cases ob <;> apply state_ext
  all_goals try { intro r; simp only [update, Op.op, bump]; (try split_ifs) <;> omega }
  all_goals simp [update, Op.op, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]

/-- Stored membership is a grow-only delta; the initial owner is implicit
in `participants`. This keeps the concrete merge's initialization neutral. -/
def participants (owner : Nat) (s : State) : Finset Nat := insert owner s.members

/-- API preparation validates against the issuing replica's current state.
Only issued effect records are replayed by `update`; failed API requests emit
no record and leave the state unchanged. -/
noncomputable def prepare (owner : Nat) (s : State) (source : Nat) (action : Action) : Option Action :=
  if applicable owner s (0,source,action) then some action else none

noncomputable def prepareAllocate (owner : Nat) (s : State) (source : Nat) (n : Int) : Option Action :=
  if n < 0 then none else prepare owner s source (.allocate n.toNat)

noncomputable def prepareTransfer (owner : Nat) (s : State) (source target : Nat) (n : Int) : Option Action :=
  if n < 0 then none else prepare owner s source (.transfer n.toNat target)

noncomputable def extrema (owner : Nat) (s : State) : Option ((Int × Nat) × (Int × Nat)) :=
  ((participants owner s).sort (· ≤ ·)).foldl (fun acc r =>
    let p := (available s r,r)
    let le := fun (a b : Int × Nat) => decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2))
    match acc with
    | none => some (p,p)
    | some (lo,hi) => some ((if le p lo then p else lo), (if le hi p then p else hi))) none

/-- Rebalance chooses lexicographic extrema at preparation and stores the
half-gap target/amount in the event. Replay performs the recorded transfer. -/
noncomputable def prepareRebalance (owner : Nat) (s : State) (source : Nat) : Option Action :=
  match extrema owner s with
  | none => none
  | some (lo,hi) => if hi.2 = source then
      prepare owner s source (.rebalance ((hi.1 - lo.1) / 2).toNat lo.2)
    else none

def applyPrepared (s : State) (ts source : Nat) (request : Option Action) : State :=
  match request with | none => s | some action => update s (ts,source,action)

theorem prepare_sound {owner source : Nat} {s : State} {action issued : Action}
    (h : prepare owner s source action = some issued) :
    issued = action ∧ applicable owner s (0,source,issued) := by
  unfold prepare at h
  split at h
  · have eq := Option.some.inj h
    subst issued
    exact ⟨rfl,by assumption⟩
  · contradiction

/-- Guard checks do not depend on timestamps. -/
theorem applicable_timestamp (owner : Nat) (s : State) (source ts : Nat) (action : Action) :
    applicable owner s (ts,source,action) ↔ applicable owner s (0,source,action) := by
  cases action <;> rfl

theorem kernels (capacity owner : Nat) :
    Paper1.Automation.TransferSimple.EmptyPastKernels (D capacity owner) := by
  constructor
  · intro l a b
    apply state_ext
    all_goals try { intro r; simp only [D, merge]; omega }
    simp [D, merge, Finset.union_comm]
  · intro s
    apply state_ext
    all_goals simp [D, merge, initial]
  · intro s e
    obtain ⟨ts,r,op⟩ := e
    cases op <;> apply state_ext
    all_goals try { intro k; simp only [D, merge, update, Op.op, bump, initial]; (try split_ifs) <;> omega }
    all_goals simp [D, merge, update, Op.op, initial]
  · intro l B t b e
    obtain ⟨ts,r,op⟩ := e
    cases op <;> apply state_ext
    all_goals try { intro k; simp only [D, merge, update, Op.op, bump]; (try split_ifs) <;> omega }
    all_goals simp [D, merge, update, Op.op, Finset.union_assoc,
      Finset.union_left_comm, Finset.union_comm]
  · intro B t₀ t₁ t₂ e
    obtain ⟨ts,r,op⟩ := e
    cases op <;> apply state_ext
    all_goals try { intro k; simp only [D, merge, update, Op.op, bump]; (try split_ifs) <;> omega }
    all_goals ext k; simp [D, merge, update, Op.op]; tauto

theorem fiveVC (capacity owner : Nat) :
    Paper1.ConcreteMRDT.Raw.MergeVCs
      (Paper1.commutingPolicy Action)
      (Paper1.ConcreteMRDT.CommutingPort.representation (D capacity owner))
      (Paper1.ConcreteMRDT.CommutingPort.scheme (all_comm capacity owner)) :=
  Paper1.Automation.TransferSimple.assemble _ (all_comm capacity owner) (kernels capacity owner)

theorem replayLaws (capacity owner : Nat) : ReplayLaws (D capacity owner).toUpdateSig := by
  apply ReplayLaws.of_all_comm (all_comm capacity owner)
  apply replayAcyclic_of_noReplayChain
  intro a b c h
  exact OrderResult.noConfusion h.1

theorem mergeLaws (capacity owner : Nat) : MergeLaws (D capacity owner) :=
  ⟨replayLaws capacity owner, (kernels capacity owner).comm, (kernels capacity owner).initial⟩

theorem deltaLaws (capacity owner : Nat) : DeltaLaws (D capacity owner) := by
  constructor
  · intro m x₀ x₁ x₂ c
    apply state_ext
    all_goals try { intro r; simp only [D,merge]; omega }
    ext r; simp [D,merge]; tauto
  · intro l m x c y
    apply state_ext
    all_goals try { intro r; simp only [D,merge]; omega }
    ext r; simp [D,merge]; tauto

theorem peel (capacity owner : Nat) : CommutingPeelLaw (D capacity owner) := by
  constructor
  rintro a ⟨ts,r,op⟩ π₀ π₂ _ _
  generalize applySeq (D capacity owner).toUpdateSig (D capacity owner).init π₀ = X
  generalize applySeq (D capacity owner).toUpdateSig (D capacity owner).init π₂ = Y
  change merge X (update a (ts,r,op)) Y = update (merge X a Y) (ts,r,op)
  cases op <;> apply state_ext
  all_goals try { intro k; simp only [D,merge,update,Op.op,bump] <;> (try split_ifs) <;> omega }
  all_goals ext k; simp [D,merge,update,Op.op] <;> tauto

/-- Join is obtained from the five concrete VCs through the shared metadata
induction; it does not invoke the historical arbitrary-state-law join route. -/
theorem join (capacity owner : Nat) : Join (D capacity owner) := by
  let D' := D capacity owner
  have commute := all_comm capacity owner
  intro C E₁ E₂ l a b trans irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb
  have rep : ∀ E s, Paper1.ConcreteMRDT.Supported C E →
      @IsCanonicalState D'.toUpdateSig (EventOrder.default _) C E s →
      Paper1.ConcreteMRDT.CommutingPort.representation D' C E s := by
    rintro E s sup ⟨π,hp,_,hf⟩
    exact ⟨sup,π,hp,hf⟩
  obtain ⟨π₁,hp₁,_,_⟩ := ha
  obtain ⟨π₂,hp₂,_,_⟩ := hb
  have perm := listPermOf_union (D := D'.toUpdateSig) hp₁ hp₂
  have kit := Paper1.ConcreteMRDT.CommutingPort.replaySupply commute C
  have sizes := Paper1.ConcreteMRDT.Raw.join_at_sizes (fiveVC capacity owner)
    (Paper1.ConcreteMRDT.CommutingPort.unique commute)
    Paper1.ConcreteMRDT.CommutingPort.initial Paper1.ConcreteMRDT.CommutingPort.finite
    C (fun _ _ _ h k => trans h k) irrefl kit.represented kit.peel
  have joined := sizes _ E₁ E₂ l a b _ perm rfl sup₁ sup₂
    (fun _ _ h _ => h.elim) (fun _ _ h _ => h.elim)
    (rep _ _ (fun e h => sup₁ e h.1) hl)
    (rep _ _ sup₁ ⟨π₁,hp₁,by assumption,by assumption⟩)
    (rep _ _ sup₂ ⟨π₂,hp₂,by assumption,by assumption⟩)
  obtain ⟨_,π,hp,hf⟩ := joined
  exact ⟨π,hp,hp.1.imp (fun {_ _} _ => by
    simp [loOn,UpdateSig.replayBefore,UpdateSig.replayOrder,EventOrder.default,
      EventOrder.unconstrained]),hf⟩

def generation (capacity owner : Nat) : Issuance (D capacity owner) where
  CanIssue := fun e s => applicable owner s e

#print axioms fiveVC
#print axioms join
end Sal.MRDTs.Instances.TransferableBoundedCounter.Corrected
