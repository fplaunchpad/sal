import Sal.MRDTs.Instances.NotionCoreMachine

/-! Executable prefix checkpoints for the actual atomic interpreter. Refresh
scans the longest unchanged transaction prefix without executing it, then
executes only the changed suffix. Errors remain errors. This is a replay
alternative, not a direct structured merge theorem. -/
namespace Sal.MRDTs.Instances.NotionCoreIncrementalReplay
open NotionCorePayload (Transaction)
open NotionCoreMachine (State)

structure Checkpoint where
  tx : Transaction
  after : Option State
  deriving DecidableEq, Repr
structure Cache where
  entries : List Checkpoint
  current : Option State
  deriving DecidableEq, Repr
structure Refresh where
  cache : Cache
  reused : Nat
  replayed : Nat
  deriving DecidableEq, Repr

def step (before : Option State) (tx : Transaction) : Option State :=
  before >>= fun state => NotionCoreMachine.applyTransaction state tx

def build (before : Option State) : List Transaction → Cache
  | [] => ⟨[],before⟩
  | tx :: rest =>
    let after := step before tx
    let tail := build after rest
    ⟨⟨tx,after⟩ :: tail.entries,tail.current⟩

/-- Only `build` calls the atomic interpreter. The equal-prefix branch reads
its stored checkpoint and does not recompute its transaction. -/
def refresh (before : Option State) (old : List Checkpoint) (new : List Transaction) : Refresh :=
  match old, new with
  | _, [] => ⟨⟨[],before⟩,0,0⟩
  | [], new => ⟨build before new,0,new.length⟩
  | cp :: old, tx :: rest =>
    if cp.tx = tx then
      let tail := refresh cp.after old rest
      ⟨⟨cp :: tail.cache.entries,tail.cache.current⟩,tail.reused + 1,tail.replayed⟩
    else ⟨build before (tx :: rest),0,(tx :: rest).length⟩

def initial : Cache := ⟨[],some {}⟩
def transactions (cache : Cache) : List Transaction := cache.entries.map (·.tx)
def updateTo (cache : Cache) (new : List Transaction) : Refresh :=
  refresh (some {}) cache.entries new
/-- Query renders the maintained physical state, with no transaction replay. -/
def query (cache : Cache) := cache.current >>= NotionCoreMachine.render

inductive Trace : Option State → List Checkpoint → Option State → Prop
  | nil (before) : Trace before [] before
  | cons {before cp rest final} : cp.after = step before cp.tx →
      Trace cp.after rest final → Trace before (cp :: rest) final

def Valid (cache : Cache) : Prop := Trace (some {}) cache.entries cache.current

/-! Bounded execution oracle is intentionally placed before the general proof.
Its expected document is hand derived from ab, then inserting X after a. -/
namespace SPOT
private def seed : Transaction := NotionCorePayload.bootstrap [97,98]
private def x : Transaction := ⟨⟨4,[66]⟩,.insert .initial .initial (.item ⟨1,[65]⟩) [88]⟩
private def late : Transaction := ⟨⟨3,[67]⟩,.create none⟩
private def old := build (some {}) [seed,x]
private def changed := updateTo old [seed,late,x]
theorem late_arrival_control :
    changed.reused = 1 ∧ changed.replayed = 2 ∧
    query changed.cache = some [(NotionCoreMachine.blockName (.issued late.id),[]),(0,[97,88,98])] ∧
    query changed.cache ≠ some [(0,[97,88,98])] := by decide +kernel

theorem duplicate_control :
    (updateTo old [seed,x]).reused = 2 ∧ (updateTo old [seed,x]).replayed = 0 ∧
    query (updateTo old [seed,x]).cache = some [(0,[97,88,98])] ∧
    query (updateTo old [seed,x]).cache ≠ some [(0,[97,98])] := by decide +kernel
private def choices : List Transaction :=
  [seed,x,late, ⟨⟨5,[68]⟩,.erase .initial .initial [⟨1,[65]⟩]⟩,
   ⟨⟨6,[69]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩]
def words : Nat → List (List Transaction)
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun rest => choices.map (· :: rest)
/-- Exhaustive bounded transitions, including malformed replay failures,
insert, erase and split; evaluation evidence is not a general theorem. -/
def boundedOracle : Bool := (words 3).all fun old =>
  (words 2).all fun new =>
    (updateTo (build (some {}) old) new).cache.current == NotionCoreMachine.replay {} new
#eval boundedOracle
private def high : Transaction := ⟨⟨4,[68]⟩,.create none⟩
theorem append_only_rejected :
    query (updateTo (build (some {}) [seed,high]) [seed,late,high]).cache =
      some [(NotionCoreMachine.blockName (.issued high.id),[]),
        (NotionCoreMachine.blockName (.issued late.id),[]),(0,[97,98])] ∧
    query (build (some {}) [seed,high,late]) ≠
      some [(NotionCoreMachine.blockName (.issued high.id),[]),
        (NotionCoreMachine.blockName (.issued late.id),[]),(0,[97,98])] := by decide +kernel
end SPOT

theorem build_trace (before : Option State) (txs : List Transaction) :
    Trace before (build before txs).entries (build before txs).current := by
  induction txs generalizing before with
  | nil => exact .nil before
  | cons tx rest ih => exact .cons rfl (ih (step before tx))

theorem build_transactions (before : Option State) (txs : List Transaction) :
    transactions (build before txs) = txs := by
  induction txs generalizing before with
  | nil => rfl
  | cons tx rest ih => simpa [transactions,build] using congrArg (tx :: ·) (ih (step before tx))

theorem refresh_trace {before : Option State} {old : List Checkpoint} {final : Option State}
    (valid : Trace before old final) (new : List Transaction) :
    Trace before (refresh before old new).cache.entries (refresh before old new).cache.current := by
  induction valid generalizing new with
  | nil before =>
      cases new with
      | nil => exact .nil before
      | cons tx rest => exact build_trace before (tx :: rest)
  | @cons before cp old final checkpoint tail ih =>
      cases new with
      | nil => exact .nil before
      | cons tx rest =>
          by_cases same : cp.tx = tx
          · simpa [refresh,same] using Trace.cons checkpoint (ih rest)
          · simpa [refresh,same] using build_trace before (tx :: rest)

theorem refresh_transactions (before : Option State) (old : List Checkpoint)
    (new : List Transaction) : transactions (refresh before old new).cache = new := by
  induction old generalizing before new with
  | nil =>
      cases new with
      | nil => rfl
      | cons tx rest => exact build_transactions before (tx :: rest)
  | cons cp old ih =>
      cases new with
      | nil => rfl
      | cons tx rest =>
          by_cases same : cp.tx = tx
          · simpa [refresh,same,transactions] using congrArg (tx :: ·) (ih cp.after rest)
          · simpa [refresh,same] using build_transactions before (tx :: rest)

theorem replay_cons (before : Option State) (tx : Transaction) (rest : List Transaction) :
    (before >>= fun s => NotionCoreMachine.replay s (tx :: rest)) =
      (step before tx >>= fun s => NotionCoreMachine.replay s rest) := by
  cases before with
  | none => rfl
  | some s => cases h : NotionCoreMachine.applyTransaction s tx <;>
      simp [step,NotionCoreMachine.replay,h]

theorem Trace.current_eq_replay {before entries final} (valid : Trace before entries final) :
    final = (before >>= fun s => NotionCoreMachine.replay s (entries.map (·.tx))) := by
  induction valid with
  | nil before => cases before <;> rfl
  | @cons before cp rest final checkpoint tail ih =>
      simpa only [List.map_cons,replay_cons,← checkpoint] using ih

theorem updateTo_valid {cache : Cache} (valid : Valid cache) (new : List Transaction) :
    Valid (updateTo cache new).cache := refresh_trace valid new

theorem updateTo_current {cache : Cache} (valid : Valid cache) (new : List Transaction) :
    (updateTo cache new).cache.current = NotionCoreMachine.replay {} new := by
  have sound := (updateTo_valid valid new).current_eq_replay
  change (updateTo cache new).cache.current =
    NotionCoreMachine.replay {} (transactions (updateTo cache new).cache) at sound
  simpa only [updateTo,refresh_transactions] using sound

theorem query_eq_replay {cache : Cache} (valid : Valid cache) :
    query cache = (NotionCoreMachine.replay {} (transactions cache) >>= NotionCoreMachine.render) := by
  rw [query,valid.current_eq_replay]
  rfl

/-- Length of the longest transaction prefix shared by both lists. -/
def commonPrefixLength : List Transaction → List Transaction → Nat
  | a :: old, b :: new => if a = b then commonPrefixLength old new + 1 else 0
  | _, _ => 0

theorem refresh_reused (before : Option State) (old : List Checkpoint) (new : List Transaction) :
    (refresh before old new).reused = commonPrefixLength (old.map (·.tx)) new := by
  induction old generalizing before new with
  | nil => cases new <;> rfl
  | cons cp old ih =>
      cases new with
      | nil => rfl
      | cons tx rest =>
          by_cases same : cp.tx = tx
          · simp [refresh,commonPrefixLength,same,ih]
          · simp [refresh,commonPrefixLength,same]

/-- Exact suffix replay-step budget (an upper bound on interpreter calls): the equal-prefix branch adds no calls.
Scanning/copying the prefix is not included in this interpreter budget. -/
theorem refresh_budget (before : Option State) (old : List Checkpoint) (new : List Transaction) :
    (refresh before old new).reused + (refresh before old new).replayed = new.length := by
  induction old generalizing before new with
  | nil => cases new <;> simp [refresh]
  | cons cp old ih =>
      cases new with
      | nil => rfl
      | cons tx rest =>
          by_cases same : cp.tx = tx
          · simp only [refresh,same,if_pos,List.length_cons]
            have h := ih cp.after rest
            omega
          · simp [refresh,same]

/-- Valid checkpoints are uniquely determined by their transaction sequence;
there is no quotient or weakened state equality. -/
theorem Trace.canonical {before entries final} (valid : Trace before entries final) :
    (⟨entries,final⟩ : Cache) = build before (entries.map (·.tx)) := by
  induction valid with
  | nil before => rfl
  | @cons before cp rest final checkpoint tail ih =>
      cases cp with
      | mk tx after =>
          simp only at checkpoint
          subst after
          simpa only [List.map_cons,build] using congrArg
            (fun c : Cache => (⟨⟨tx,step before tx⟩ :: c.entries,c.current⟩ : Cache)) ih

theorem valid_canonical {cache : Cache} (valid : Valid cache) :
    cache = build (some {}) (transactions cache) := valid.canonical

#print axioms updateTo_current
#print axioms query_eq_replay
#print axioms refresh_budget
#print axioms refresh_reused
end Sal.MRDTs.Instances.NotionCoreIncrementalReplay
