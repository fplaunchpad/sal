import Sal.Emulation.CRDT_TS
import Sal.Emulation.Op_Based_TS
import Sal.Emulation.Weak_Simulation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.GetD

/-!
# Shapiro operation-to-state emulation

This is the original `(s_m, M, D)` construction from Shapiro et al. (2011),
rather than the message-set-only variant. `s_m` is the materialized op-based
state, `M` is the finite set of known messages, and `D ⊆ M` records messages
whose effects have already been applied. Learning another replica's state
unions its known messages into `M` and causally drains `M \ D` into `s_m`.

The explicit schedule interface separates the construction from the later
Liittschwager-style simulation proof. Priority 4 will derive schedules from
finite acyclic causal orders and relate system labels; this file establishes
the emulator and its local operational invariants.
-/

namespace Sal.Emulation

open Classical

/-- A deterministic enumeration of every finite message set, compatible with
the causal order. The existence proof belongs to the simulation layer; keeping
it explicit prevents an unjustified topological-sort placeholder here. -/
structure CausalSchedule (D : OpCRDTSig) (hb : D.Msg → D.Msg → Prop) where
  order : Finset D.Msg → List D.Msg
  nodup : ∀ K, (order K).Nodup
  complete : ∀ K m, m ∈ order K ↔ m ∈ K
  causal : ∀ K, (order K).Pairwise fun later earlier => ¬ hb later earlier

/-- Shapiro's emulating state `(s_m, M, D)`. -/
structure EmulatorState (D : OpCRDTSig) where
  materialized : D.State
  known : Finset D.Msg
  delivered : Finset D.Msg
deriving DecidableEq

namespace EmulatorState

variable {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}

/-- The representation invariant stated by the original construction. -/
def WellFormed (x : EmulatorState D) : Prop := x.delivered ⊆ x.known

/-- Delivered messages form a causal down-set inside the known messages. -/
def CausallyClosed (hb : D.Msg → D.Msg → Prop) (x : EmulatorState D) : Prop :=
  ∀ m, m ∈ x.delivered → ∀ p, p ∈ x.known → hb p m → p ∈ x.delivered

/-- The full representation invariant needed by enabled delivery. -/
def Invariant (hb : D.Msg → D.Msg → Prop) (x : EmulatorState D) : Prop :=
  x.WellFormed ∧ x.CausallyClosed hb

/-- Messages learned but not yet applied to the materialized state. -/
def pending (x : EmulatorState D) : Finset D.Msg := x.known \ x.delivered

/-- A message can be delivered once it is known, has not been delivered, and
every known causal predecessor has been delivered. -/
def DeliveryEnabled (hb : D.Msg → D.Msg → Prop)
    (x : EmulatorState D) (m : D.Msg) : Prop :=
  m ∈ x.known ∧ m ∉ x.delivered ∧
    ∀ p, p ∈ x.known → hb p m → p ∈ x.delivered

/-- Generation-side obligations for immediate self-delivery of a newly
prepared message. Causal broadcast implementations discharge these from their
clock discipline. -/
def PrepareEnabled (hb : D.Msg → D.Msg → Prop)
    (x : EmulatorState D) (m : D.Msg) : Prop :=
  m ∉ x.known ∧
  (∀ p, p ∈ x.known → hb p m → p ∈ x.delivered) ∧
  (∀ q, q ∈ x.delivered → ¬ hb m q)

/-- Apply and record one message. `known.insert` also supports the local
prepare/effect step, where a freshly prepared message was not known before. -/
def deliverOne (x : EmulatorState D) (m : D.Msg) : EmulatorState D where
  materialized := D.effect m x.materialized
  known := insert m x.known
  delivered := insert m x.delivered

/-- Explicit internal delivery transition used by the later weak simulation. -/
inductive InternalDeliver (hb : D.Msg → D.Msg → Prop) :
    EmulatorState D → D.Msg → EmulatorState D → Prop where
  | step {x m} (henabled : DeliveryEnabled hb x m) :
      InternalDeliver hb x m (deliverOne x m)

/-- Apply all as-yet-undelivered messages in the policy's causal order. -/
def drain (sched : CausalSchedule D hb)
    (x : EmulatorState D) (allKnown : Finset D.Msg) : EmulatorState D :=
  let todo := (sched.order allKnown).filter (fun m => m ∉ x.delivered)
  { materialized := todo.foldl (fun s m => D.effect m s) x.materialized
    known := allKnown
    delivered := allKnown }

/-- Local op-based preparation followed by immediate self-delivery. -/
def prepare (r : Replica) (op : D.AppOp) (x : EmulatorState D) : EmulatorState D :=
  deliverOne x (D.prepare r op x.materialized)

theorem wellFormed_init :
    WellFormed ({ materialized := D.init, known := ∅, delivered := ∅ } : EmulatorState D) := by
  intro m hm
  simp at hm

theorem wellFormed_deliverOne {x : EmulatorState D} (hx : x.WellFormed) (m : D.Msg) :
    (x.deliverOne m).WellFormed := by
  intro p hp
  simp only [deliverOne, Finset.mem_insert] at hp ⊢
  exact hp.elim Or.inl (fun h => Or.inr (hx h))

theorem wellFormed_prepare {x : EmulatorState D} (hx : x.WellFormed)
    (r : Replica) (op : D.AppOp) : (x.prepare r op).WellFormed :=
  wellFormed_deliverOne hx _

theorem causallyClosed_deliverOne {x : EmulatorState D} {m : D.Msg}
    (hx : x.CausallyClosed hb)
    (hpred : ∀ p, p ∈ x.known → hb p m → p ∈ x.delivered)
    (hback : ∀ q, q ∈ x.delivered → ¬ hb m q) :
    (x.deliverOne m).CausallyClosed hb := by
  intro q hq p hp hpq
  simp only [deliverOne, Finset.mem_insert] at hq hp ⊢
  rcases hq with rfl | hq
  · rcases hp with rfl | hp
    · exact Or.inl rfl
    · exact Or.inr (hpred p hp hpq)
  · rcases hp with rfl | hp
    · exact absurd hpq (hback q hq)
    · exact Or.inr (hx q hq p hp hpq)

theorem invariant_prepare {x : EmulatorState D} (hx : x.Invariant hb)
    {r : Replica} {op : D.AppOp}
    (henabled : PrepareEnabled hb x (D.prepare r op x.materialized)) :
    (x.prepare r op).Invariant hb := by
  refine ⟨wellFormed_prepare hx.1 r op, ?_⟩
  exact causallyClosed_deliverOne hx.2 henabled.2.1 henabled.2.2

theorem wellFormed_internalDeliver {x x' : EmulatorState D} {m : D.Msg}
    (hx : x.WellFormed) (h : InternalDeliver hb x m x') : x'.WellFormed := by
  cases h
  exact wellFormed_deliverOne hx m

theorem invariant_internalDeliver {x x' : EmulatorState D} {m : D.Msg}
    (hx : x.Invariant hb) (h : InternalDeliver hb x m x') : x'.Invariant hb := by
  cases h with
  | step henabled =>
      refine ⟨wellFormed_deliverOne hx.1 m, ?_⟩
      exact causallyClosed_deliverOne hx.2 henabled.2.2
        (fun q hq hmq => henabled.2.1 (hx.2 q hq m henabled.1 hmq))

theorem wellFormed_drain (sched : CausalSchedule D hb)
    (x : EmulatorState D) (allKnown : Finset D.Msg) :
    (x.drain sched allKnown).WellFormed := by
  intro m hm
  simpa [drain] using hm

theorem invariant_drain (sched : CausalSchedule D hb)
    (x : EmulatorState D) (allKnown : Finset D.Msg) :
    (x.drain sched allKnown).Invariant hb := by
  refine ⟨wellFormed_drain sched x allKnown, ?_⟩
  intro m hm p hp _
  simpa [drain] using hp

theorem known_mono_deliverOne (x : EmulatorState D) (m : D.Msg) :
    x.known ⊆ (x.deliverOne m).known := by
  intro p hp
  simp [deliverOne, hp]

theorem drain_known (sched : CausalSchedule D hb)
    (x : EmulatorState D) (allKnown : Finset D.Msg) :
    (x.drain sched allKnown).known = allKnown := rfl

theorem drain_delivered (sched : CausalSchedule D hb)
    (x : EmulatorState D) (allKnown : Finset D.Msg) :
    (x.drain sched allKnown).delivered = allKnown := rfl

/-- When a fully drained receiver learns exactly one fresh message, snapshot
drain is the same state change as one op-message delivery.  This is the local
algebraic fact used by the network simulation. -/
theorem drain_insert_eq_deliverOne (sched : CausalSchedule D hb)
    (x : EmulatorState D) (m : D.Msg)
    (hfull : x.known = x.delivered) (hfresh : m ∉ x.delivered) :
    x.drain sched (insert m x.known) = x.deliverOne m := by
  have hmKnown : m ∉ x.known := by simpa [hfull] using hfresh
  have hfilter :
      (sched.order (insert m x.known)).filter
        (fun p => decide (p ∉ x.delivered)) = [m] := by
    let pending := (sched.order (insert m x.known)).filter
      (fun p => decide (p ∉ x.delivered))
    have hmem : ∀ p, p ∈ pending ↔ p = m := by
      intro p
      simp only [pending, List.mem_filter, decide_eq_true_eq,
        sched.complete, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hp, hnot⟩
        · rfl
        · have hnot' : p ∉ x.delivered := by simpa using hnot
          exact absurd (hfull ▸ hp) hnot'
      · rintro rfl
        exact ⟨Or.inl rfl, by simpa using hfresh⟩
    have hnonempty : pending ≠ [] := by
      intro he
      have := (hmem m).2 rfl
      simp [he] at this
    have hnodup : pending.Nodup := List.Nodup.filter _ (sched.nodup _)
    cases hpending : pending with
    | nil => exact absurd hpending hnonempty
    | cons a tail =>
        have ha : a = m := (hmem a).1 (by simp [hpending])
        subst a
        cases tail with
        | nil => simpa [pending] using hpending
        | cons b rest =>
            have hb : b = m := (hmem b).1 (by simp [hpending])
            subst b
            rw [hpending] at hnodup
            simp at hnodup
  have hfilter' :
      (sched.order (insert m x.delivered)).filter
        (fun p => decide (p ∉ x.delivered)) = [m] := by
    simpa [hfull] using hfilter
  unfold drain deliverOne
  rw [hfull, hfilter']
  simp

end EmulatorState

section
variable (D : OpCRDTSig) {hb : D.Msg → D.Msg → Prop}

/-- Lift an op-based CRDT using Shapiro's materialized/known/delivered state.
Merge is intentionally directional: it performs `d(s, M ∪ M', D)` from the
left state, exactly as in the original construction. -/
def shapiroG (sched : CausalSchedule D hb) : CRDTSig where
  State := EmulatorState D
  dec_state := inferInstance
  init := { materialized := D.init, known := ∅, delivered := ∅ }
  AppOp := D.AppOp
  dec_op := D.dec_op
  Query := D.Query
  Value := D.Value
  update := fun x e => x.prepare e.rep e.op
  merge := fun x y => x.drain sched (x.known ∪ y.known)
  query := fun x q => D.query x.materialized q
  rc := D.rc

/-- Compatibility name used by the transfer scaffold. -/
abbrev canonicalG (sched : CausalSchedule D hb) : CRDTSig := shapiroG D sched

theorem shapiroG_update_wellFormed (sched : CausalSchedule D hb)
    {x : EmulatorState D} (hx : x.WellFormed) (e : Op D.AppOp) :
    ((shapiroG D sched).update x e).WellFormed :=
  EmulatorState.wellFormed_prepare hx e.rep e.op

theorem shapiroG_merge_wellFormed (sched : CausalSchedule D hb)
    (x y : EmulatorState D) :
    ((shapiroG D sched).merge x y).WellFormed :=
  EmulatorState.wellFormed_drain sched x _

theorem shapiroG_merge_known (sched : CausalSchedule D hb)
    (x y : EmulatorState D) :
    ((shapiroG D sched).merge x y).known = x.known ∪ y.known := rfl

theorem shapiroG_merge_fully_delivered (sched : CausalSchedule D hb)
    (x y : EmulatorState D) :
    ((shapiroG D sched).merge x y).delivered = x.known ∪ y.known := rfl

end

end Sal.Emulation
