import Sal.MRDTs.Metatheory.Correctness

/-!
# The mergeable queue, Peepul's case study, through the one framework

The queue of *Certified Mergeable Replicated Data Types* (Soundarapandian,
Kamath, Nagar, Sivaramakrishnan; PLDI 2022), re-proved here. Enqueue mints a
timestamped element; dequeue removes a **named** element, the head its issuer
observed (the op carries the tag; the client API is unchanged, and the replica
captures its generation context). The three-way merge first computes Peepul's
survivor set and then sorts the result by the enqueue key selected by `rc`.
This normalization makes concurrent enqueue order independent of merge-operand
position.

Concurrent enqueues genuinely do not commute (queue order is arrival order)
and they conflict with their own class, a clique. The former `no_rc_chain`
contract therefore forced this instance out of the flat engine. The current
`rc_acyclic` contract removes that particular obstruction: a total order may
orient a clique acyclically. This file retains its independent route and proves
the ternary **Join Lemma directly** (`q_join_at`): the canonical ordering of
Peepul's survivor set is the linearization witness, and the framework's
`CanonicalConfig` induction (`canonicalConfig_merge_at`) does the rest.

The Join holds under an honest-history contract (`QHonest`): every dequeue
names an element its issuer had observed (a `vis`-prior enqueue with that
tag). This is the queue's `HonestDelivery`; without it a dequeue can precede
its enqueue in some enumerations and fold contents become enumeration-
dependent. Headline:

    queue_replay_witness :
      QHonest C → reachable C → HasReplayWitness C

This is a per-version replay theorem for the raw system, with no quotient (the state is
kept in canonical single-list form; Peepul's two-list balancing is an `≈`-away
representation refinement, deferred).
-/

set_option maxHeartbeats 1000000

namespace Sal.MRDTs.Instances.Queue

open Sal.MRDTs.Foundation
open Classical

/-! ## §1  The datatype -/

inductive QOp : Type where
  | enq (v : ℕ)
  | deq (t : ℕ)
deriving DecidableEq

/-- Queue state: `(tag, value)` pairs, head first. Canonical single-list form. -/
abbrev QState : Type := List (ℕ × ℕ)

def qTags (s : QState) : List ℕ := s.map Prod.fst

/-- Enqueue appends a fresh-tagged element (the tag is the event's own
timestamp); dequeue removes the named element wherever it sits: strictness
about *which* element lives in `applicable`, not in the effect. -/
def qUpdate (s : QState) (o : Op QOp) : QState :=
  match o.2.2 with
  | .enq v => if o.1 ∈ qTags s then s else s ++ [(o.1, v)]
  | .deq t => s.filter (fun x => decide (x.1 ≠ t))

/-- Lexicographic queue-entry order. Reachable states have unique tags, so its
first component is the enqueue timestamp and the value is only a total-order
tie breaker for malformed equal-timestamp inputs. -/
def qEntryLE (a b : ℕ × ℕ) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

def qEntryLEB (a b : ℕ × ℕ) : Bool :=
  if a.1 < b.1 then true
  else if a.1 = b.1 then decide (a.2 ≤ b.2)
  else false

theorem qEntryLEB_eq_true (a b : ℕ × ℕ) :
    qEntryLEB a b = true ↔ qEntryLE a b := by
  simp [qEntryLEB, qEntryLE]

theorem qEntryLE_trans : Transitive qEntryLE := by
  intro a b c hab hbc
  unfold qEntryLE at *
  omega

theorem qEntryLE_total (a b : ℕ × ℕ) : qEntryLE a b ∨ qEntryLE b a := by
  unfold qEntryLE
  omega

theorem qEntryLE_antisymm {a b : ℕ × ℕ} :
    qEntryLE a b → qEntryLE b a → a = b := by
  rintro hab hba
  unfold qEntryLE at hab hba
  apply Prod.ext <;> omega

theorem qEntry_mergeSort_sorted (s : QState) :
    (s.mergeSort qEntryLEB).Pairwise qEntryLE := by
  simpa [qEntryLEB_eq_true] using List.pairwise_mergeSort
    (le := qEntryLEB)
    (fun a b c hab hbc => by
      apply (qEntryLEB_eq_true _ _).2
      exact qEntryLE_trans ((qEntryLEB_eq_true _ _).1 hab)
        ((qEntryLEB_eq_true _ _).1 hbc))
    (fun a b => by
      rcases qEntryLE_total a b with h | h
      · simp [h, qEntryLEB_eq_true]
      · simp [h, qEntryLEB_eq_true]) s

/-- Peepul's survivor calculation before canonical queue ordering. -/
def qMergeRaw (l a b : QState) : QState :=
  l.filter (fun x => decide (x.1 ∈ qTags a ∧ x.1 ∈ qTags b))
    ++ a.filter (fun x => decide (x.1 ∉ qTags l))
    ++ b.filter (fun x => decide (x.1 ∉ qTags l))

/-- Merge keeps the Peepul survivor set and resolves concurrent enqueue order
canonically by enqueue key, independently of merge-operand position. -/
def qMerge (l a b : QState) : QState :=
  (qMergeRaw l a b).mergeSort qEntryLEB

def Q : MRDTSig where
  State := QState
  dec_state := inferInstance
  init := []
  AppOp := QOp
  dec_op := inferInstance
  Query := Unit
  Value := Option (ℕ × ℕ)
  update := qUpdate
  query := fun s _ => s.head?
  merge := qMerge

theorem Q_core_update (s : QState) (o : Op QOp) :
    Q.toUpdateSig.update s o = qUpdate s o := rfl

def qEnqLt (a b : Op QOp) : Prop :=
  match a.2.2, b.2.2 with
  | .enq av, .enq bv => a.1 < b.1 ∨ (a.1 = b.1 ∧ av < bv)
  | _, _ => False

def qEnqLTB (a b : Op QOp) : Bool :=
  match a.2.2, b.2.2 with
  | .enq av, .enq bv =>
      if a.1 < b.1 then true
      else if a.1 = b.1 then decide (av < bv)
      else false
  | _, _ => false

theorem qEnqLTB_eq_true (a b : Op QOp) :
    qEnqLTB a b = true ↔ qEnqLt a b := by
  obtain ⟨ats, ar, ao⟩ := a
  obtain ⟨bt, br, bo⟩ := b
  cases ao <;> cases bo <;>
    simp [qEnqLTB, qEnqLt]

def qRcOrder (a b : Op QOp) : RcRes :=
  match a.2.2, b.2.2 with
  | .enq _, .enq _ =>
      if qEnqLTB a b then .Fst_then_snd
      else if qEnqLTB b a then .Snd_then_fst else .Either
  | .enq _, .deq target =>
      if a.1 = target then .Fst_then_snd else .Either
  | .deq target, .enq _ =>
      if b.1 = target then .Snd_then_fst else .Either
  | .deq _, .deq _ => .Either

/-- Queue resolve-conflict policy: enqueue/enqueue conflicts use enqueue-key
order, and an enqueue precedes a dequeue of its tag. -/
def rc : ReplayPolicy Q.toUpdateSig where
  order := qRcOrder

instance QReplayPolicy : ReplayPolicy Q.toUpdateSig := rc

/-! ## §2  Event helpers -/

def qIsEnq (e : Op QOp) : Bool :=
  match e.2.2 with
  | .enq _ => true
  | .deq _ => false

/-- The tag an event concerns: an enqueue's own timestamp; a dequeue's target. -/
def qTag (e : Op QOp) : ℕ :=
  match e.2.2 with
  | .enq _ => e.1
  | .deq t => t

def qVal (e : Op QOp) : ℕ :=
  match e.2.2 with
  | .enq v => v
  | .deq _ => 0

/-- Canonical replay order: enqueues precede dequeues; enqueues use the same
key order as `rc`; dequeue order is immaterial. -/
def qWitnessLEB (a b : Op QOp) : Bool :=
  match a.2.2, b.2.2 with
  | .enq av, .enq bv => qEntryLEB (a.1, av) (b.1, bv)
  | .enq _, .deq _ => true
  | .deq _, .enq _ => false
  | .deq _, .deq _ => true

def QWitnessLE (a b : Op QOp) : Prop := qWitnessLEB a b = true

def qCanonical (ops : List (Op QOp)) : List (Op QOp) :=
  ops.mergeSort qWitnessLEB

theorem qCanonical_perm (ops : List (Op QOp)) :
    ops.Perm (qCanonical ops) :=
  (List.mergeSort_perm ops qWitnessLEB).symm

theorem qCanonical_listPermOf {ops : List (Op QOp)}
    {E : Set (Op QOp)} (h : listPermOf ops E) :
    listPermOf (qCanonical ops) E := by
  have hp := qCanonical_perm ops
  exact ⟨hp.nodup h.1, fun e => (hp.mem_iff (a := e)).symm.trans (h.2 e)⟩

theorem qCanonical_ordered (ops : List (Op QOp)) :
    (qCanonical ops).Pairwise QWitnessLE := by
  unfold qCanonical QWitnessLE
  apply List.pairwise_mergeSort
  · rintro ⟨ta, ra, oa⟩ ⟨tb, rb, ob⟩ ⟨tc, rc', oc⟩ hab hbc
    cases oa <;> cases ob <;> cases oc <;>
      simp [qWitnessLEB, qEntryLEB_eq_true] at *
    exact qEntryLE_trans hab hbc
  · rintro ⟨ta, ra, oa⟩ ⟨tb, rb, ob⟩
    cases oa <;> cases ob <;> simp [qWitnessLEB, qEntryLEB_eq_true]
    exact qEntryLE_total _ _

def qDeqTags (ρ : List (Op QOp)) : List ℕ :=
  ρ.filterMap (fun e => match e.2.2 with | .deq t => some t | .enq _ => none)

/-- The canonical content of an event list: its enqueues, in order, minus the
dequeued tags. -/
def qCanonList (ρ : List (Op QOp)) : QState :=
  (ρ.filter (fun e => qIsEnq e && !(decide (qTag e ∈ qDeqTags ρ)))).map
    (fun e => (e.1, qVal e))

theorem qDeqTags_append (ρ σ : List (Op QOp)) :
    qDeqTags (ρ ++ σ) = qDeqTags ρ ++ qDeqTags σ :=
  List.filterMap_append

theorem mem_qDeqTags {ρ : List (Op QOp)} {t : ℕ} :
    t ∈ qDeqTags ρ ↔ ∃ d ∈ ρ, qIsEnq d = false ∧ qTag d = t := by
  unfold qDeqTags
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨d, hd, hmatch⟩
    obtain ⟨ts, r, op⟩ := d
    cases op with
    | enq v => exact absurd hmatch (by simp)
    | deq t' =>
      refine ⟨(ts, r, QOp.deq t'), hd, rfl, ?_⟩
      simp only [Option.some.injEq] at hmatch
      simpa [qTag] using hmatch
  · rintro ⟨d, hd, hden, htag⟩
    obtain ⟨ts, r, op⟩ := d
    cases op with
    | enq v => exact absurd hden (by simp [qIsEnq])
    | deq t' =>
      refine ⟨(ts, r, QOp.deq t'), hd, ?_⟩
      simpa [qTag] using htag

theorem qTags_qCanonList {ρ : List (Op QOp)} {t : ℕ} :
    t ∈ qTags (qCanonList ρ)
      ↔ (∃ e ∈ ρ, qIsEnq e = true ∧ e.1 = t) ∧ t ∉ qDeqTags ρ := by
  unfold qCanonList qTags
  rw [List.map_map, List.mem_map]
  constructor
  · rintro ⟨e, he, hfst⟩
    rw [List.mem_filter] at he
    have h12 : qIsEnq e = true ∧ ¬(qTag e ∈ qDeqTags ρ) := by
      simpa using he.2
    have htag : qTag e = e.1 := by
      obtain ⟨ts, r, op⟩ := e
      cases op with
      | enq v => rfl
      | deq t' => exact absurd h12.1 (by simp [qIsEnq])
    have het : e.1 = t := by simpa using hfst
    refine ⟨⟨e, he.1, h12.1, het⟩, ?_⟩
    have h2 := h12.2
    rw [htag, het] at h2
    exact h2
  · rintro ⟨⟨e, he, hen, hfst⟩, hnd⟩
    have htag : qTag e = e.1 := by
      obtain ⟨ts, r, op⟩ := e
      cases op with
      | enq v => rfl
      | deq t' => exact absurd hen (by simp [qIsEnq])
    refine ⟨e, ?_, by simpa using hfst⟩
    rw [List.mem_filter]
    refine ⟨he, ?_⟩
    have hne : ¬(qTag e ∈ qDeqTags ρ) := by
      rw [htag, hfst]; exact hnd
    simp [hen, hne]

/-! ## §3  Well-formed event lists and the fold formula -/

/-- Well-formedness of an enumeration: distinct events, enqueue tags unique,
and no dequeue precedes the enqueue of its tag (in honest closed sets this is
forced by `respects`: the enqueue is `vis`-before the dequeue and they do
not commute). -/
structure QWf (ρ : List (Op QOp)) : Prop where
  nd : ρ.Nodup
  enq_uniq : ∀ a ∈ ρ, ∀ b ∈ ρ, qIsEnq a = true → qIsEnq b = true →
    a.1 = b.1 → a = b
  deq_before : ∀ (l₁ l₂ : List (Op QOp)), ρ = l₁ ++ l₂ →
    ∀ d ∈ l₁, qIsEnq d = false → ∀ a ∈ l₂, qIsEnq a = true →
      a.1 = qTag d → False

theorem QWf.prefix {ρ : List (Op QOp)} {e : Op QOp}
    (h : QWf (ρ ++ [e])) : QWf ρ := by
  refine ⟨(List.nodup_append.mp h.nd).1, ?_, ?_⟩
  · intro a ha b hb
    exact h.enq_uniq a (List.mem_append_left _ ha) b (List.mem_append_left _ hb)
  · intro l₁ l₂ hsplit d hd hdd a ha hae htag
    exact h.deq_before l₁ (l₂ ++ [e]) (by rw [hsplit, List.append_assoc])
      d hd hdd a (List.mem_append_left _ ha) hae htag

/-- Tags of the canonical content come from enqueue events. -/
theorem qTags_canon_sub {ρ : List (Op QOp)} {t : ℕ}
    (h : t ∈ qTags (qCanonList ρ)) :
    ∃ e ∈ ρ, qIsEnq e = true ∧ e.1 = t :=
  (qTags_qCanonList.mp h).1

theorem qCanonList_snoc_enq {ρ : List (Op QOp)} {ts r v : ℕ}
    (hnodeq : ts ∉ qDeqTags ρ) :
    qCanonList (ρ ++ [(ts, r, QOp.enq v)]) = qCanonList ρ ++ [(ts, v)] := by
  unfold qCanonList
  have hdt : qDeqTags (ρ ++ [(ts, r, QOp.enq v)]) = qDeqTags ρ := by
    rw [qDeqTags_append]
    rw [show qDeqTags [(ts, r, QOp.enq v)] = [] from rfl, List.append_nil]
  rw [hdt, List.filter_append, List.map_append]
  congr 1
  rw [show List.filter
      (fun e => qIsEnq e && !(decide (qTag e ∈ qDeqTags ρ)))
      [(ts, r, QOp.enq v)]
      = [(ts, r, QOp.enq v)] from by simp [qIsEnq, qTag, hnodeq]]
  rfl

theorem qCanonList_snoc_deq (ρ : List (Op QOp)) (ts r t : ℕ) :
    qCanonList (ρ ++ [(ts, r, QOp.deq t)])
      = (qCanonList ρ).filter (fun x => decide (x.1 ≠ t)) := by
  unfold qCanonList
  rw [List.filter_map, List.filter_filter]
  have hdt : qDeqTags (ρ ++ [(ts, r, QOp.deq t)]) = qDeqTags ρ ++ [t] := by
    rw [qDeqTags_append]
    rw [show qDeqTags [(ts, r, QOp.deq t)] = [t] from rfl]
  rw [hdt, List.filter_append]
  rw [show List.filter
      (fun e => qIsEnq e && !(decide (qTag e ∈ qDeqTags ρ ++ [t])))
      [(ts, r, QOp.deq t)] = [] from by simp [qIsEnq]]
  rw [List.append_nil]
  congr 1
  apply List.filter_congr
  intro x hx
  obtain ⟨ts', r', op'⟩ := x
  cases op' with
  | deq t' => simp [qIsEnq]
  | enq v' =>
    simp only [qIsEnq, qTag, Function.comp, Bool.true_and,
      List.mem_append, List.mem_singleton]
    by_cases h1 : ts' ∈ qDeqTags ρ <;> by_cases h2 : ts' = t <;>
      simp [h1, h2]

/-- **The fold formula**: over a well-formed enumeration, the fold from the
empty queue is the canonical content: the enqueues, in enumeration order,
minus the dequeued tags. -/
theorem q_fold_canon : ∀ (ρ : List (Op QOp)), QWf ρ →
    applySeq Q.toUpdateSig Q.init ρ = qCanonList ρ := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton ρ e ih =>
    intro h
    have hpre := h.prefix
    have hstep : applySeq Q.toUpdateSig Q.init (ρ ++ [e])
        = qUpdate (applySeq Q.toUpdateSig Q.init ρ) e := by
      unfold applySeq
      rw [List.foldl_append]
      rfl
    rw [hstep, ih hpre]
    obtain ⟨ts, r, op⟩ := e
    cases op with
    | enq v =>
      have hnodeq : ts ∉ qDeqTags ρ := by
        intro hmem
        obtain ⟨d, hd, hdd, htag⟩ := mem_qDeqTags.mp hmem
        exact h.deq_before ρ [(ts, r, QOp.enq v)] rfl d hd hdd
          (ts, r, QOp.enq v) (by simp) (by simp [qIsEnq]) htag.symm
      have hfresh : ts ∉ qTags (qCanonList ρ) := by
        intro hmem
        obtain ⟨a, ha, hae, hat⟩ := qTags_canon_sub hmem
        have heq : a = (ts, r, QOp.enq v) :=
          h.enq_uniq a (List.mem_append_left _ ha)
            (ts, r, QOp.enq v) (List.mem_append_right _ (by simp))
            hae (by simp [qIsEnq]) hat
        rw [heq] at ha
        exact (List.nodup_append.mp h.nd).2.2 _ ha _ (List.mem_singleton_self _) rfl
      rw [qCanonList_snoc_enq hnodeq]
      show (if ts ∈ qTags (qCanonList ρ) then qCanonList ρ
        else qCanonList ρ ++ [(ts, v)]) = qCanonList ρ ++ [(ts, v)]
      rw [if_neg hfresh]
    | deq t =>
      rw [qCanonList_snoc_deq]
      rfl

/-! ## §4  From canonicity premises to well-formedness -/

/-- Same-tag enqueue/dequeue do not commute (witness: the empty queue). -/
theorem q_enq_deq_not_comm (ts r v ts' r' : ℕ) :
    ¬ Q.toUpdateSig.commutes (ts, r, QOp.enq v) (ts', r', QOp.deq ts) := by
  intro h
  have := h []
  change qUpdate (qUpdate [] (ts, r, QOp.enq v))
      (ts', r', QOp.deq ts) =
    qUpdate (qUpdate [] (ts', r', QOp.deq ts))
      (ts, r, QOp.enq v) at this
  simp [qUpdate, qTags] at this

/-! ## §5  Honest histories, well-formedness of enumerations -/

/-- Honest histories: every dequeue names a tag its issuer had observed, a
`vis`-prior enqueue with that tag. The queue's `HonestDelivery`. -/
def QHonestCore (C : Sal.MRDTs.Foundation.ReplayContext Q.toUpdateSig) : Prop :=
  ∀ e ∈ C.events, ∀ t : ℕ, e.2.2 = QOp.deq t →
    ∃ a ∈ C.events, C.vis a e ∧ a.1 = t ∧ ∃ v, a.2.2 = QOp.enq v

/-- Queue replay additionally uses Lamport monotonicity to reconcile visible
enqueue/enqueue conflicts with the timestamp-directed `rc`. -/
def QGoodCore (C : Sal.MRDTs.Foundation.ReplayContext Q.toUpdateSig) : Prop :=
  QHonestCore C ∧ ∀ {a b}, C.vis a b → a.1 < b.1

variable {C : Sal.MRDTs.Foundation.ReplayContext Q.toUpdateSig}

/-- Timestamp uniqueness across the event universe (the generic
`Configuration.ts_unique`). -/
theorem q_ts_unique {a b : Op QOp}
    (ha : a ∈ C.events) (hb : b ∈ C.events) (h : a.1 = b.1) : a = b :=
  C.ts_unique ha hb h

/-- Non-commutation of the pair honesty and closure trade on. -/
theorem q_pair_not_comm {a d : Op QOp}
    (hae : ∃ v, a.2.2 = QOp.enq v) (hdd : ∃ t, d.2.2 = QOp.deq t)
    (htag : a.1 = qTag d) :
    ¬ Q.toUpdateSig.commutes a d := by
  obtain ⟨a1, a2, aop⟩ := a
  obtain ⟨d1, d2, dop⟩ := d
  obtain ⟨v, hv⟩ := hae
  obtain ⟨t, ht⟩ := hdd
  simp only at hv ht
  subst hv ht
  have h1 : a1 = t := htag
  subst h1
  exact q_enq_deq_not_comm a1 a2 v d1 d2

/-- Honesty + backward closure: a dequeue's enqueue lies in the same closed
event set, `vis`-before it. -/
theorem q_deq_enq_mem (hHon : QHonestCore C)
    {ev : Set (Op QOp)}
    (hin : ∀ a ∈ ev, a ∈ C.events)
    (hcl : ∀ a b, C.vis a b → ¬ Q.toUpdateSig.commutes a b → b ∈ ev → a ∈ ev) :
    ∀ d ∈ ev, qIsEnq d = false →
      ∃ a ∈ ev, qIsEnq a = true ∧ a.1 = qTag d ∧ C.vis a d := by
  intro d hd hdd
  obtain ⟨ts, r, op⟩ := d
  cases op with
  | enq v => exact absurd hdd (by simp [qIsEnq])
  | deq t =>
    obtain ⟨a, haev, hvis, hat, v, haenq⟩ :=
      hHon (ts, r, QOp.deq t) (hin _ hd) t rfl
    have hncomm : ¬ Q.toUpdateSig.commutes a (ts, r, QOp.deq t) :=
      q_pair_not_comm ⟨v, haenq⟩ ⟨t, rfl⟩ (by simpa [qTag] using hat)
    refine ⟨a, hcl a _ hvis hncomm hd, ?_, ?_, hvis⟩
    · obtain ⟨a1, a2, aop⟩ := a
      simp only at haenq
      subst haenq
      rfl
    · simpa [qTag] using hat

/-- A `loOn`-respecting enumeration of a closed honest set is well-formed. -/
theorem q_wf_of_enum (hHon : QHonestCore C)
    {ev : Set (Op QOp)} {ρ : List (Op QOp)}
    (hin : ∀ a ∈ ev, a ∈ C.events)
    (hcl : ∀ a b, C.vis a b → ¬ Q.toUpdateSig.commutes a b → b ∈ ev → a ∈ ev)
    (hperm : listPermOf ρ ev)
    (hresp : respects ρ (loOn C ev)) : QWf ρ := by
  refine ⟨hperm.1, ?_, ?_⟩
  · intro a ha b hb _ _ h1
    exact q_ts_unique (hin a ((hperm.2 a).mp ha)) (hin b ((hperm.2 b).mp hb)) h1
  · intro l₁ l₂ hsplit d hd hdd a ha hae htag
    have hdρ : d ∈ ρ := by rw [hsplit]; exact List.mem_append_left _ hd
    have haρ : a ∈ ρ := by rw [hsplit]; exact List.mem_append_right _ ha
    have hdev : d ∈ ev := (hperm.2 d).mp hdρ
    have haev : a ∈ ev := (hperm.2 a).mp haρ
    obtain ⟨a', ha'ev, ha'enq, ha't, hvis⟩ := q_deq_enq_mem hHon hin hcl d hdev hdd
    have haa' : a = a' :=
      q_ts_unique (hin a haev) (hin a' ha'ev) (htag.trans ha't.symm)
    -- respects: d before a' in ρ, yet loOn a' d
    have hpw := hresp
    unfold respects at hpw
    rw [hsplit] at hpw
    have hcross := (List.pairwise_append.mp hpw).2.2 d hd a' (haa' ▸ ha)
    apply hcross
    refine Or.inl ⟨hvis, Or.inl ?_⟩
    obtain ⟨ats, ar, aop⟩ := a'
    obtain ⟨dts, dr, dop⟩ := d
    cases aop with
    | deq t => simp [qIsEnq] at ha'enq
    | enq v =>
        cases dop with
        | enq w => simp [qIsEnq] at hdd
        | deq t =>
            simp [qTag] at ha't
            subst t
            change qRcOrder (ats, ar, QOp.enq v) (dts, dr, QOp.deq ats) =
              RcRes.Fst_then_snd
            simp [qRcOrder]

/-! ## §6  The Join: Peepul's merge is the linearization witness -/

/-- Set-level "some dequeue of `t`". -/
def qDeqIn (ev : Set (Op QOp)) (t : ℕ) : Prop :=
  ∃ d ∈ ev, qIsEnq d = false ∧ qTag d = t

/-- Set-level "some enqueue of `t`". -/
def qEnqIn (ev : Set (Op QOp)) (t : ℕ) : Prop :=
  ∃ e ∈ ev, qIsEnq e = true ∧ e.1 = t

theorem qDeqTags_perm {ρ : List (Op QOp)} {ev : Set (Op QOp)}
    (hperm : listPermOf ρ ev) {t : ℕ} :
    t ∈ qDeqTags ρ ↔ qDeqIn ev t := by
  rw [mem_qDeqTags]
  constructor
  · rintro ⟨d, hd, h1, h2⟩
    exact ⟨d, (hperm.2 d).mp hd, h1, h2⟩
  · rintro ⟨d, hd, h1, h2⟩
    exact ⟨d, (hperm.2 d).mpr hd, h1, h2⟩

theorem qTags_canon_perm {ρ : List (Op QOp)} {ev : Set (Op QOp)}
    (hperm : listPermOf ρ ev) {t : ℕ} :
    t ∈ qTags (qCanonList ρ) ↔ qEnqIn ev t ∧ ¬ qDeqIn ev t := by
  rw [qTags_qCanonList]
  constructor
  · rintro ⟨⟨e, he, h1, h2⟩, hnd⟩
    exact ⟨⟨e, (hperm.2 e).mp he, h1, h2⟩, fun hdin =>
      hnd ((qDeqTags_perm hperm).mpr hdin)⟩
  · rintro ⟨⟨e, he, h1, h2⟩, hnd⟩
    exact ⟨⟨e, (hperm.2 e).mpr he, h1, h2⟩, fun hmem =>
      hnd ((qDeqTags_perm hperm).mp hmem)⟩

theorem qDeqTags_mem_of_perm {ρ σ : List (Op QOp)}
    (h : ρ.Perm σ) (t : ℕ) : t ∈ qDeqTags ρ ↔ t ∈ qDeqTags σ := by
  rw [mem_qDeqTags, mem_qDeqTags]
  constructor <;> rintro ⟨d, hd, hdi, hdt⟩
  · exact ⟨d, h.mem_iff.mp hd, hdi, hdt⟩
  · exact ⟨d, h.mem_iff.mpr hd, hdi, hdt⟩

theorem qCanonList_perm_of_perm {ρ σ : List (Op QOp)}
    (h : ρ.Perm σ) : (qCanonList ρ).Perm (qCanonList σ) := by
  unfold qCanonList
  let pρ := fun e : Op QOp => qIsEnq e && !(decide (qTag e ∈ qDeqTags ρ))
  let pσ := fun e : Op QOp => qIsEnq e && !(decide (qTag e ∈ qDeqTags σ))
  have hp : ∀ e, pρ e = pσ e := by
    intro e
    simp only [pρ, pσ]
    congr 2
    exact decide_eq_decide.mpr (qDeqTags_mem_of_perm h (qTag e))
  have hf : ρ.filter pρ = ρ.filter pσ := by
    apply List.filter_congr
    intro e _
    exact hp e
  rw [show (fun e => qIsEnq e && !(decide (qTag e ∈ qDeqTags ρ))) = pρ from rfl,
      show (fun e => qIsEnq e && !(decide (qTag e ∈ qDeqTags σ))) = pσ from rfl,
      hf]
  exact (h.filter pσ).map _

theorem qCanonList_nodup (h : QWf ρ) : (qCanonList ρ).Nodup := by
  apply List.Nodup.of_map Prod.fst
  unfold qCanonList
  rw [List.map_map]
  apply List.Nodup.map_on _ (h.nd.filter _)
  intro a ha b hb hab
  rw [List.mem_filter] at ha hb
  have hai : qIsEnq a = true := by
    cases hx : qIsEnq a <;> simp [hx] at ha ⊢
  have hbi : qIsEnq b = true := by
    cases hx : qIsEnq b <;> simp [hx] at hb ⊢
  exact h.enq_uniq a ha.1 b hb.1 hai hbi (by simpa using hab)

theorem qCanonList_sorted_of_ordered {ρ : List (Op QOp)}
    (h : ρ.Pairwise QWitnessLE) : (qCanonList ρ).Pairwise qEntryLE := by
  unfold qCanonList
  let p := fun e : Op QOp => qIsEnq e && !(decide (qTag e ∈ qDeqTags ρ))
  change ((ρ.filter p).map (fun e => (e.1, qVal e))).Pairwise qEntryLE
  have hf : (ρ.filter p).Pairwise QWitnessLE :=
    h.sublist (List.filter_sublist (p := p))
  have hf' : (ρ.filter p).Pairwise
      (fun a b => qEntryLE (a.1, qVal a) (b.1, qVal b)) := by
    apply hf.imp_of_mem
    intro a b ha hb hab
    rw [List.mem_filter] at ha hb
    obtain ⟨ats, ar, aop⟩ := a
    obtain ⟨bts, br, bop⟩ := b
    cases aop <;> cases bop <;>
      simp [p, qIsEnq, QWitnessLE, qWitnessLEB, qVal,
        qEntryLEB_eq_true] at *
    assumption
  exact hf'.map _ (fun _ _ hab => hab)

theorem qCanonList_canonical {ρ : List (Op QOp)} :
    qCanonList (qCanonical ρ) = (qCanonList ρ).mergeSort qEntryLEB := by
  have hp : (qCanonList (qCanonical ρ)).Perm (qCanonList ρ) :=
    qCanonList_perm_of_perm (qCanonical_perm ρ).symm
  have hpc : (qCanonList (qCanonical ρ)).Perm
      ((qCanonList ρ).mergeSort qEntryLEB) :=
    hp.trans (List.mergeSort_perm _ _).symm
  apply hpc.eq_of_pairwise (fun a b _ _ => qEntryLE_antisymm)
  · exact qCanonList_sorted_of_ordered (qCanonical_ordered ρ)
  · exact qEntry_mergeSort_sorted _

theorem qCanonical_respects (hGood : QGoodCore C)
    {ev : Set (Op QOp)} {ops : List (Op QOp)}
    (hin : ∀ a ∈ ev, a ∈ C.events) (hperm : listPermOf ops ev) :
    respects (qCanonical ops) (loOn C ev) := by
  have hcan := qCanonical_listPermOf hperm
  have hall : ∀ e ∈ qCanonical ops, e ∈ C.events := by
    intro e he
    exact hin e ((hcan.2 e).mp he)
  have hordered := qCanonical_ordered ops
  generalize hwhole : qCanonical ops = whole at hall hordered
  clear hwhole
  induction whole with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
      unfold respects
      rw [List.pairwise_cons] at hordered ⊢
      refine ⟨?_, ih (fun e he => hall e (List.mem_cons_of_mem _ he)) hordered.2⟩
      intro b hb hba
      have hab := hordered.1 b hb
      have haC := hall a List.mem_cons_self
      have hbC := hall b (List.mem_cons_of_mem _ hb)
      obtain ⟨ats, ar, aop⟩ := a
      obtain ⟨bts, br, bop⟩ := b
      cases aop with
      | enq av =>
          cases bop with
          | enq bv =>
              have hle : qEntryLE (ats, av) (bts, bv) := by
                simpa [QWitnessLE, qWitnessLEB, qEntryLEB_eq_true] using hab
              rcases hba with hvis | hrc
              · exact (Nat.not_lt_of_ge (by rcases hle with h | ⟨h, _⟩ <;> omega))
                  (hGood.2 hvis.1)
              · have hlt : qEnqLt (bts, br, .enq bv) (ats, ar, .enq av) := by
                  have hbefore := hrc.2.2.1
                  change qRcOrder (bts, br, .enq bv) (ats, ar, .enq av) =
                    .Fst_then_snd at hbefore
                  by_cases hltB : qEnqLTB (bts, br, .enq bv) (ats, ar, .enq av) = true
                  · exact (qEnqLTB_eq_true _ _).mp hltB
                  · simp [qRcOrder, hltB] at hbefore
                    split at hbefore <;> contradiction
                change bts < ats ∨ (bts = ats ∧ bv < av) at hlt
                change ats < bts ∨ (ats = bts ∧ av ≤ bv) at hle
                rcases hlt with hts | ⟨hts, hval⟩
                · rcases hle with hts' | ⟨hts', _⟩
                  · exact (Nat.lt_asymm hts hts').elim
                  · exact (Nat.ne_of_lt hts) hts'.symm
                · rcases hle with hts' | ⟨_, hval'⟩
                  · exact (Nat.ne_of_lt hts') hts.symm
                  · exact (Nat.not_lt_of_ge hval') hval
          | deq target =>
              rcases hba with hvis | hrc
              · rcases hvis.2 with hback | hforward
                · change (if ats = target then RcRes.Snd_then_fst else RcRes.Either) =
                    RcRes.Fst_then_snd at hback
                  split at hback <;> contradiction
                · have hat : ats = target := by
                    simpa [UpdateSig.rc, ReplayPolicy.Before, rc, QReplayPolicy,
                      qRcOrder] using hforward
                  obtain ⟨c, hc, hcb, hct, _⟩ :=
                    hGood.1 (bts, br, .deq target) hbC target rfl
                  have hca : c = (ats, ar, .enq av) :=
                    C.ts_unique hc haC (hct.trans hat.symm)
                  have habvis : C.vis (ats, ar, .enq av) (bts, br, .deq target) := by
                    simpa [hca] using hcb
                  exact (Nat.lt_asymm (hGood.2 habvis) (hGood.2 hvis.1))
              · have hbefore := hrc.2.2.1
                change (if ats = target then RcRes.Snd_then_fst else RcRes.Either) =
                  RcRes.Fst_then_snd at hbefore
                split at hbefore <;> contradiction
      | deq atarget =>
          cases bop with
          | enq bv => simp [QWitnessLE, qWitnessLEB] at hab
          | deq btarget =>
              simp [loOn, UpdateSig.rc, ReplayPolicy.Before, rc, QReplayPolicy,
                qRcOrder] at hba

open LabeledTS in
/-- **The queue's ternary Join Lemma.** Peepul's survivor calculation is
normalized by the queue `rc`; the witness is the corresponding canonical
ordering of the union event set. -/
theorem q_join_at (hGood : QGoodCore C) : JoinAt Q C := by
  intro ev₁ ev₂ s₀ s₁ s₂ htr hir hin₁ hin₂ hcl₁ hcl₂ h₀ h₁ h₂
  classical
  have hHon := hGood.1
  obtain ⟨ρ₀, hp₀, hr₀, hf₀⟩ := h₀
  obtain ⟨ρ₁, hp₁, hr₁, hf₁⟩ := h₁
  obtain ⟨ρ₂, hp₂, hr₂, hf₂⟩ := h₂
  set ev₀ := ev₁ ∩ ev₂ with hev₀
  have hin₀ : ∀ a ∈ ev₀, a ∈ C.events := fun a ha => hin₁ a ha.1
  have hcl₀ : ∀ a b, C.vis a b → ¬ Q.toUpdateSig.commutes a b →
      b ∈ ev₀ → a ∈ ev₀ :=
    fun a b hv hc hb => ⟨hcl₁ a b hv hc hb.1, hcl₂ a b hv hc hb.2⟩
  have hinU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events := by
    rintro a (ha | ha)
    · exact hin₁ a ha
    · exact hin₂ a ha
  have hclU : ∀ a b, C.vis a b → ¬ Q.toUpdateSig.commutes a b →
      b ∈ ev₁ ∪ ev₂ → a ∈ ev₁ ∪ ev₂ := by
    rintro a b hv hc (hb | hb)
    · exact Or.inl (hcl₁ a b hv hc hb)
    · exact Or.inr (hcl₂ a b hv hc hb)
  -- well-formedness of the given enumerations, and their folds
  have hwf₀ := q_wf_of_enum hHon hin₀ hcl₀ hp₀ hr₀
  have hwf₁ := q_wf_of_enum hHon hin₁ hcl₁ hp₁ hr₁
  have hwf₂ := q_wf_of_enum hHon hin₂ hcl₂ hp₂ hr₂
  have hs₀ : s₀ = qCanonList ρ₀ := by rw [← hf₀, q_fold_canon ρ₀ hwf₀]
  have hs₁ : s₁ = qCanonList ρ₁ := by rw [← hf₁, q_fold_canon ρ₁ hwf₁]
  have hs₂ : s₂ = qCanonList ρ₂ := by rw [← hf₂, q_fold_canon ρ₂ hwf₂]
  -- the witness enumeration
  set Δ₁ := ρ₁.filter (fun e => decide (e ∉ ev₀)) with hΔ₁
  set Δ₂ := ρ₂.filter (fun e => decide (e ∉ ev₀)) with hΔ₂
  -- memberships
  have hmem₀ : ∀ x ∈ ρ₀, x ∈ ev₀ := fun x hx => (hp₀.2 x).mp hx
  have hmemΔ₁ : ∀ x ∈ Δ₁, x ∈ ev₁ ∧ x ∉ ev₀ := by
    intro x hx
    rw [hΔ₁, List.mem_filter] at hx
    exact ⟨(hp₁.2 x).mp hx.1, by simpa using hx.2⟩
  have hmemΔ₂ : ∀ x ∈ Δ₂, x ∈ ev₂ ∧ x ∉ ev₀ := by
    intro x hx
    rw [hΔ₂, List.mem_filter] at hx
    exact ⟨(hp₂.2 x).mp hx.1, by simpa using hx.2⟩
  have hΔ₂ev₁ : ∀ x ∈ Δ₂, x ∉ ev₁ := by
    intro x hx hx1
    exact (hmemΔ₂ x hx).2 ⟨hx1, (hmemΔ₂ x hx).1⟩
  -- the union permutation
  have hpermU : listPermOf (ρ₀ ++ Δ₁ ++ Δ₂) (ev₁ ∪ ev₂) := by
    constructor
    · rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hp₀.1, hp₁.1.filter _, ?_⟩
        intro a ha b hb hab
        exact (hmemΔ₁ b hb).2 (hab ▸ hmem₀ a ha)
      · exact hp₂.1.filter _
      · intro a ha b hb hab
        rcases List.mem_append.mp ha with ha | ha
        · exact (hmemΔ₂ b hb).2 (hab ▸ hmem₀ a ha)
        · exact hΔ₂ev₁ b hb (hab ▸ (hmemΔ₁ a ha).1)
    · intro x
      constructor
      · intro hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · exact Or.inl (hmem₀ x hx).1
          · exact Or.inl (hmemΔ₁ x hx).1
        · exact Or.inr (hmemΔ₂ x hx).1
      · intro hx
        by_cases hx0 : x ∈ ev₀
        · exact List.mem_append_left _
            (List.mem_append_left _ ((hp₀.2 x).mpr hx0))
        · rcases hx with hx | hx
          · refine List.mem_append_left _ (List.mem_append_right _ ?_)
            rw [hΔ₁, List.mem_filter]
            exact ⟨(hp₁.2 x).mpr hx, by simpa using hx0⟩
          · by_cases hx1 : x ∈ ev₁
            · exact absurd ⟨hx1, hx⟩ hx0
            · refine List.mem_append_right _ ?_
              rw [hΔ₂, List.mem_filter]
              exact ⟨(hp₂.2 x).mpr hx, by simpa using hx0⟩
  -- set-level characterizations
  have htags₀ : ∀ t, t ∈ qTags s₀ ↔ qEnqIn ev₀ t ∧ ¬ qDeqIn ev₀ t := by
    intro t; rw [hs₀]; exact qTags_canon_perm hp₀
  have htags₁ : ∀ t, t ∈ qTags s₁ ↔ qEnqIn ev₁ t ∧ ¬ qDeqIn ev₁ t := by
    intro t; rw [hs₁]; exact qTags_canon_perm hp₁
  have htags₂ : ∀ t, t ∈ qTags s₂ ↔ qEnqIn ev₂ t ∧ ¬ qDeqIn ev₂ t := by
    intro t; rw [hs₂]; exact qTags_canon_perm hp₂
  have hdeqU : ∀ t, t ∈ qDeqTags (ρ₀ ++ Δ₁ ++ Δ₂) ↔ qDeqIn (ev₁ ∪ ev₂) t :=
    fun t => qDeqTags_perm hpermU
  have hdeq₀ : ∀ t, t ∈ qDeqTags ρ₀ ↔ qDeqIn ev₀ t := fun t => qDeqTags_perm hp₀
  have hdeq₁ : ∀ t, t ∈ qDeqTags ρ₁ ↔ qDeqIn ev₁ t := fun t => qDeqTags_perm hp₁
  have hdeq₂ : ∀ t, t ∈ qDeqTags ρ₂ ↔ qDeqIn ev₂ t := fun t => qDeqTags_perm hp₂
  -- deq-set embeddings
  have hd01 : ∀ t, qDeqIn ev₀ t → qDeqIn ev₁ t := by
    rintro t ⟨d, hd, h1, h2⟩; exact ⟨d, hd.1, h1, h2⟩
  have hd02 : ∀ t, qDeqIn ev₀ t → qDeqIn ev₂ t := by
    rintro t ⟨d, hd, h1, h2⟩; exact ⟨d, hd.2, h1, h2⟩
  have hdU : ∀ t, qDeqIn (ev₁ ∪ ev₂) t ↔ qDeqIn ev₁ t ∨ qDeqIn ev₂ t := by
    intro t
    constructor
    · rintro ⟨d, (hd | hd), h1, h2⟩
      · exact Or.inl ⟨d, hd, h1, h2⟩
      · exact Or.inr ⟨d, hd, h1, h2⟩
    · rintro (⟨d, hd, h1, h2⟩ | ⟨d, hd, h1, h2⟩)
      · exact ⟨d, Or.inl hd, h1, h2⟩
      · exact ⟨d, Or.inr hd, h1, h2⟩
  -- cross-branch dequeues are impossible for a delta enqueue (its enqueue
  -- would be pulled into both branches, contradicting delta-ness)
  have hK₁ : ∀ e, e ∈ ev₁ → qIsEnq e = true → e ∉ ev₀ → ¬ qDeqIn ev₂ e.1 := by
    intro e he hen h0 hdin
    obtain ⟨d, hdev, hdd, hdt⟩ := hdin
    obtain ⟨a', ha'ev, _, ha't, _⟩ := q_deq_enq_mem hHon hin₂ hcl₂ d hdev hdd
    have heq : a' = e :=
      q_ts_unique (hin₂ a' ha'ev) (hin₁ e he) (by rw [ha't, hdt])
    rw [heq] at ha'ev
    exact h0 ⟨he, ha'ev⟩
  have hK₂ : ∀ e, e ∈ ev₂ → qIsEnq e = true → e ∉ ev₀ → ¬ qDeqIn ev₁ e.1 := by
    intro e he hen h0 hdin
    obtain ⟨d, hdev, hdd, hdt⟩ := hdin
    obtain ⟨a', ha'ev, _, ha't, _⟩ := q_deq_enq_mem hHon hin₁ hcl₁ d hdev hdd
    have heq : a' = e :=
      q_ts_unique (hin₁ a' ha'ev) (hin₂ e he) (by rw [ha't, hdt])
    rw [heq] at ha'ev
    exact h0 ⟨ha'ev, he⟩
  -- an GCA enqueue-tag can only be enqueued by the GCA event (ts-uniqueness)
  have hEnq₀ : ∀ e, e ∈ C.events → qEnqIn ev₀ e.1 → e ∈ ev₀ := by
    rintro e he ⟨a, ha, _, hat⟩
    have : a = e := q_ts_unique (hin₀ a ha) he hat
    rw [← this]; exact ha
  -- the list identity: Peepul's merge, segment by segment
  have hmain : qCanonList (ρ₀ ++ Δ₁ ++ Δ₂) = qMergeRaw s₀ s₁ s₂ := by
    unfold qCanonList qMergeRaw
    rw [List.filter_append, List.filter_append, List.map_append, List.map_append]
    congr 1
    · congr 1
      · -- GCA segment ↔ l-part
        rw [hs₀]
        unfold qCanonList
        rw [List.filter_map, List.filter_filter]
        congr 1
        apply List.filter_congr
        intro e he
        obtain ⟨ts', r', op'⟩ := e
        cases op' with
        | deq t' => simp [qIsEnq]
        | enq v' =>
          have heev : (ts', r', QOp.enq v') ∈ ev₀ := hmem₀ _ he
          simp only [qIsEnq, qTag, Function.comp, Bool.true_and]
          rw [← decide_not, ← decide_not, ← Bool.decide_and]
          apply decide_eq_decide.mpr
          constructor
          · intro hnd
            have hnd' : ¬ qDeqIn (ev₁ ∪ ev₂) ts' := fun h => hnd ((hdeqU ts').mpr h)
            have hnd₁ : ¬ qDeqIn ev₁ ts' := fun h => hnd' ((hdU ts').mpr (Or.inl h))
            have hnd₂ : ¬ qDeqIn ev₂ ts' := fun h => hnd' ((hdU ts').mpr (Or.inr h))
            refine ⟨⟨(htags₁ ts').mpr ⟨⟨_, heev.1, rfl, rfl⟩, hnd₁⟩,
                    (htags₂ ts').mpr ⟨⟨_, heev.2, rfl, rfl⟩, hnd₂⟩⟩, ?_⟩
            intro h
            exact hnd₁ (hd01 ts' ((hdeq₀ ts').mp h))
          · rintro ⟨⟨ht₁, ht₂⟩, _⟩
            intro hd
            rcases (hdU ts').mp ((hdeqU ts').mp hd) with h | h
            · exact ((htags₁ ts').mp ht₁).2 h
            · exact ((htags₂ ts').mp ht₂).2 h
      · -- Δ₁ segment ↔ a-part
        rw [hΔ₁, hs₁]
        unfold qCanonList
        rw [List.filter_filter, List.filter_map, List.filter_filter]
        congr 1
        apply List.filter_congr
        intro e he
        obtain ⟨ts', r', op'⟩ := e
        cases op' with
        | deq t' => simp [qIsEnq]
        | enq v' =>
          have heev : (ts', r', QOp.enq v') ∈ ev₁ := (hp₁.2 _).mp he
          simp only [qIsEnq, qTag, Function.comp, Bool.true_and]
          rw [← decide_not, ← decide_not, ← Bool.decide_and, ← Bool.decide_and]
          apply decide_eq_decide.mpr
          constructor
          · rintro ⟨hnd, h0⟩
            have hnd' : ¬ qDeqIn (ev₁ ∪ ev₂) ts' := fun h => hnd ((hdeqU ts').mpr h)
            have hnd₁ : ¬ qDeqIn ev₁ ts' := fun h => hnd' ((hdU ts').mpr (Or.inl h))
            refine ⟨?_, fun h => hnd₁ ((hdeq₁ ts').mp h)⟩
            intro hin0
            exact h0 (hEnq₀ _ (hin₁ _ heev) ((htags₀ ts').mp hin0).1)
          · rintro ⟨h0, hnd₁'⟩
            have hnd₁ : ¬ qDeqIn ev₁ ts' := fun h => hnd₁' ((hdeq₁ ts').mpr h)
            have hnot0 : (ts', r', QOp.enq v') ∉ ev₀ := by
              intro hin0
              exact h0 ((htags₀ ts').mpr
                ⟨⟨_, hin0, rfl, rfl⟩, fun h => hnd₁ (hd01 ts' h)⟩)
            refine ⟨?_, hnot0⟩
            intro hd
            rcases (hdU ts').mp ((hdeqU ts').mp hd) with h | h
            · exact hnd₁ h
            · exact hK₁ _ heev rfl hnot0 h
      -- Δ₂ segment ↔ b-part
    · rw [hΔ₂, hs₂]
      unfold qCanonList
      rw [List.filter_filter, List.filter_map, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro e he
      obtain ⟨ts', r', op'⟩ := e
      cases op' with
      | deq t' => simp [qIsEnq]
      | enq v' =>
        have heev : (ts', r', QOp.enq v') ∈ ev₂ := (hp₂.2 _).mp he
        simp only [qIsEnq, qTag, Function.comp, Bool.true_and]
        rw [← decide_not, ← decide_not, ← Bool.decide_and, ← Bool.decide_and]
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨hnd, h0⟩
          have hnd' : ¬ qDeqIn (ev₁ ∪ ev₂) ts' := fun h => hnd ((hdeqU ts').mpr h)
          have hnd₂ : ¬ qDeqIn ev₂ ts' := fun h => hnd' ((hdU ts').mpr (Or.inr h))
          refine ⟨?_, fun h => hnd₂ ((hdeq₂ ts').mp h)⟩
          intro hin0
          exact h0 (hEnq₀ _ (hin₂ _ heev) ((htags₀ ts').mp hin0).1)
        · rintro ⟨h0, hnd₂'⟩
          have hnd₂ : ¬ qDeqIn ev₂ ts' := fun h => hnd₂' ((hdeq₂ ts').mpr h)
          have hnot0 : (ts', r', QOp.enq v') ∉ ev₀ := by
            intro hin0
            exact h0 ((htags₀ ts').mpr
              ⟨⟨_, hin0, rfl, rfl⟩, fun h => hnd₂ (hd02 ts' h)⟩)
          refine ⟨?_, hnot0⟩
          intro hd
          rcases (hdU ts').mp ((hdeqU ts').mp hd) with h | h
          · exact hK₂ _ heev rfl hnot0 h
          · exact hnd₂ h
  let raw := ρ₀ ++ Δ₁ ++ Δ₂
  let ρU := qCanonical raw
  have hpCan : listPermOf ρU (ev₁ ∪ ev₂) :=
    qCanonical_listPermOf hpermU
  have hrCan : respects ρU (loOn C (ev₁ ∪ ev₂)) :=
    qCanonical_respects hGood hinU hpermU
  have hwfCan : QWf ρU := q_wf_of_enum hHon hinU hclU hpCan hrCan
  have hfoldCan : applySeq Q.toUpdateSig Q.init ρU = qCanonList ρU :=
    q_fold_canon _ hwfCan
  refine ⟨ρU, hpCan, hrCan, ?_⟩
  rw [hfoldCan]
  change qCanonList (qCanonical raw) = qMerge s₀ s₁ s₂
  rw [qCanonList_canonical]
  change (qCanonList raw).mergeSort qEntryLEB =
    (qMergeRaw s₀ s₁ s₂).mergeSort qEntryLEB
  rw [hmain]


end Sal.MRDTs.Instances.Queue
