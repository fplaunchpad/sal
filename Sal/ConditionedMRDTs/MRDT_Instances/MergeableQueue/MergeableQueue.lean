import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.HonestReach
import Sal.ConditionedMRDTs.Metatheory.GenHonest

/-!
# The mergeable queue, Peepul's case study, through the one framework

The queue of *Certified Mergeable Replicated Data Types* (Soundarapandian,
Kamath, Nagar, Sivaramakrishnan; PLDI 2022), re-proved here. Enqueue mints a
timestamped element; dequeue removes a **named** element, the head its issuer
observed (the op carries the tag; the client API is unchanged, the replica
captures its generation context, and this is what Peepul's `max(i,j)` merge
was implicitly doing). The three-way merge is Peepul's: the LCA's survivors
(elements still present in both branches) in LCA order, then each branch's
new arrivals in branch order.

Why this instance is structurally forced OUT of the flat engine: concurrent
enqueues genuinely do not commute (queue order is arrival order) and they
conflict with their own class, a clique, so no `rc` assignment satisfies
`rc_non_comm_directional` + `no_rc_chain`. The route here instead proves the
ternary **Join Lemma directly** (`q_join_at`): Peepul's merge *is* the
linearization witness (LCA-enumeration ++ branch-one news ++ branch-two news,
no reordering), and the framework's `GoodConfig3` induction
(`goodConfig3_merge_at`) does the rest.

The Join holds under an honest-history contract (`QHonest`): every dequeue
names an element its issuer had observed (a `vis`-prior enqueue with that
tag). This is the queue's `HonestDelivery`; without it a dequeue can precede
its enqueue in some enumerations and fold contents become enumeration-
dependent. Headline:

    queue_ra_linearizable3 :
      QHonest C → reachable C → IsRALinearizable3 C

Per-version RA-linearizability of the raw system, no quotient (the state is
kept in canonical single-list form; Peepul's two-list balancing is an `≈`-away
representation refinement, deferred).
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
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

/-- Peepul's merge: LCA elements surviving in both branches (LCA order), then
branch-one's news (branch order), then branch-two's. -/
def qMergeL (l a b : QState) : QState :=
  l.filter (fun x => decide (x.1 ∈ qTags a ∧ x.1 ∈ qTags b))
    ++ a.filter (fun x => decide (x.1 ∉ qTags l))
    ++ b.filter (fun x => decide (x.1 ∉ qTags l))

def Q : ConditionedMRDTSig where
  State := QState
  dec_state := inferInstance
  init := []
  AppOp := QOp
  dec_op := inferInstance
  Query := Unit
  Value := Option (ℕ × ℕ)
  update := qUpdate
  merge := fun a b => qMergeL [] a b
  query := fun s _ => s.head?
  rc := fun _ _ => RcRes.Either
  mergeL := qMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem Q_core_update (s : QState) (o : Op QOp) :
    Q.toCRDTSig.update s o = qUpdate s o := rfl

theorem Q_rc_either (o₁ o₂ : Op QOp) :
    Q.toCRDTSig.rc o₁ o₂ = RcRes.Either := rfl

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
    applySeq Q.toCRDTSig Q.init ρ = qCanonList ρ := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton ρ e ih =>
    intro h
    have hpre := h.prefix
    have hstep : applySeq Q.toCRDTSig Q.init (ρ ++ [e])
        = qUpdate (applySeq Q.toCRDTSig Q.init ρ) e := by
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
    ¬ Q.toCRDTSig.commutes (ts, r, QOp.enq v) (ts', r', QOp.deq ts) := by
  intro h
  have := h []
  simp only [Q_core_update, qUpdate, qTags] at this
  simp at this

/-- For the queue, `loOn` collapses to its `vis` arm (`rc` is `Either`;
the generic `loOn_iff_of_rc_either`). -/
theorem q_loOn_iff (C : Sal.Emulation.Configuration Q.toCRDTSig)
    (ev : Set (Op QOp)) (e₁ e₂ : Op QOp) :
    loOn C ev e₁ e₂ ↔ C.vis e₁ e₂ ∧ ¬ Q.toCRDTSig.commutes e₁ e₂ :=
  loOn_iff_of_rc_either Q_rc_either C ev e₁ e₂


/-! ## §5  Honest histories, well-formedness of enumerations -/

/-- Honest histories: every dequeue names a tag its issuer had observed, a
`vis`-prior enqueue with that tag. The queue's `HonestDelivery`. -/
def QHonestCore (C : Sal.Emulation.Configuration Q.toCRDTSig) : Prop :=
  ∀ e ∈ C.events, ∀ t : ℕ, e.2.2 = QOp.deq t →
    ∃ a ∈ C.events, C.vis a e ∧ a.1 = t ∧ ∃ v, a.2.2 = QOp.enq v

variable {C : Sal.Emulation.Configuration Q.toCRDTSig}

/-- Timestamp uniqueness across the event universe (the generic
`Configuration.ts_unique`). -/
theorem q_ts_unique {a b : Op QOp}
    (ha : a ∈ C.events) (hb : b ∈ C.events) (h : a.1 = b.1) : a = b :=
  C.ts_unique ha hb h

/-- Non-commutation of the pair honesty and closure trade on. -/
theorem q_pair_not_comm {a d : Op QOp}
    (hae : ∃ v, a.2.2 = QOp.enq v) (hdd : ∃ t, d.2.2 = QOp.deq t)
    (htag : a.1 = qTag d) :
    ¬ Q.toCRDTSig.commutes a d := by
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
    (hcl : ∀ a b, C.vis a b → ¬ Q.toCRDTSig.commutes a b → b ∈ ev → a ∈ ev) :
    ∀ d ∈ ev, qIsEnq d = false →
      ∃ a ∈ ev, qIsEnq a = true ∧ a.1 = qTag d ∧ C.vis a d := by
  intro d hd hdd
  obtain ⟨ts, r, op⟩ := d
  cases op with
  | enq v => exact absurd hdd (by simp [qIsEnq])
  | deq t =>
    obtain ⟨a, haev, hvis, hat, v, haenq⟩ :=
      hHon (ts, r, QOp.deq t) (hin _ hd) t rfl
    have hncomm : ¬ Q.toCRDTSig.commutes a (ts, r, QOp.deq t) :=
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
    (hcl : ∀ a b, C.vis a b → ¬ Q.toCRDTSig.commutes a b → b ∈ ev → a ∈ ev)
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
    rw [q_loOn_iff]
    have hae' : ∃ v, a'.2.2 = QOp.enq v := by
      obtain ⟨a1, a2, aop⟩ := a'
      cases aop with
      | enq v => exact ⟨v, rfl⟩
      | deq t' => exact absurd ha'enq (by simp [qIsEnq])
    have hdd' : ∃ t', d.2.2 = QOp.deq t' := by
      obtain ⟨d1, d2, dop⟩ := d
      cases dop with
      | enq v => exact absurd hdd (by simp [qIsEnq])
      | deq t' => exact ⟨t', rfl⟩
    exact ⟨hvis, q_pair_not_comm hae' hdd' ha't⟩

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

/-- `respects` is `ev`-independent for the queue (`loOn`'s `rc` arm is dead;
the generic `respects_transfer_of_rc_either`). -/
theorem q_respects_transfer {ev ev' : Set (Op QOp)} {ρ : List (Op QOp)}
    (h : respects ρ (loOn C ev)) : respects ρ (loOn C ev') :=
  respects_transfer_of_rc_either (D' := Q.toCRDTSig) Q_rc_either h

open LabeledTS in
/-- **The queue's ternary Join Lemma, at any honest configuration.** The
witness enumeration is Peepul's merge itself: the LCA's enumeration, then
branch one's delta in branch order, then branch two's. -/
theorem q_join_at (hHon : QHonestCore C) : JoinLemma3At Q C := by
  intro ev₁ ev₂ s₀ s₁ s₂ htr hir hin₁ hin₂ hcl₁ hcl₂ h₀ h₁ h₂
  classical
  obtain ⟨ρ₀, hp₀, hr₀, hf₀⟩ := h₀
  obtain ⟨ρ₁, hp₁, hr₁, hf₁⟩ := h₁
  obtain ⟨ρ₂, hp₂, hr₂, hf₂⟩ := h₂
  set ev₀ := ev₁ ∩ ev₂ with hev₀
  have hin₀ : ∀ a ∈ ev₀, a ∈ C.events := fun a ha => hin₁ a ha.1
  have hcl₀ : ∀ a b, C.vis a b → ¬ Q.toCRDTSig.commutes a b →
      b ∈ ev₀ → a ∈ ev₀ :=
    fun a b hv hc hb => ⟨hcl₁ a b hv hc hb.1, hcl₂ a b hv hc hb.2⟩
  have hinU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events := by
    rintro a (ha | ha)
    · exact hin₁ a ha
    · exact hin₂ a ha
  have hclU : ∀ a b, C.vis a b → ¬ Q.toCRDTSig.commutes a b →
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
  -- respects over the union: within-block from the given enumerations
  -- (`loOn` is `ev`-independent), cross-block back-edges killed by closure
  have hrespU : respects (ρ₀ ++ Δ₁ ++ Δ₂) (loOn C (ev₁ ∪ ev₂)) := by
    unfold respects
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨q_respects_transfer hr₀, ?_, ?_⟩
      · rw [hΔ₁]
        exact q_respects_transfer
          (List.Pairwise.sublist List.filter_sublist hr₁)
      · intro x hx y hy hlo
        rw [q_loOn_iff] at hlo
        have hyev : y ∈ ev₂ := hcl₂ y x hlo.1 hlo.2 (hmem₀ x hx).2
        exact (hmemΔ₁ y hy).2 ⟨(hmemΔ₁ y hy).1, hyev⟩
    · rw [hΔ₂]
      exact q_respects_transfer
        (List.Pairwise.sublist List.filter_sublist hr₂)
    · intro x hx y hy hlo
      rw [q_loOn_iff] at hlo
      rcases List.mem_append.mp hx with hx | hx
      · have hyev : y ∈ ev₁ := hcl₁ y x hlo.1 hlo.2 (hmem₀ x hx).1
        exact hΔ₂ev₁ y hy hyev
      · have hyev : y ∈ ev₁ := hcl₁ y x hlo.1 hlo.2 (hmemΔ₁ x hx).1
        exact hΔ₂ev₁ y hy hyev
  -- the fold of the witness
  have hwfU : QWf (ρ₀ ++ Δ₁ ++ Δ₂) := q_wf_of_enum hHon hinU hclU hpermU hrespU
  have hfoldU : applySeq Q.toCRDTSig Q.init (ρ₀ ++ Δ₁ ++ Δ₂)
      = qCanonList (ρ₀ ++ Δ₁ ++ Δ₂) := q_fold_canon _ hwfU
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
  -- an LCA enqueue-tag can only be enqueued by the LCA event (ts-uniqueness)
  have hEnq₀ : ∀ e, e ∈ C.events → qEnqIn ev₀ e.1 → e ∈ ev₀ := by
    rintro e he ⟨a, ha, _, hat⟩
    have : a = e := q_ts_unique (hin₀ a ha) he hat
    rw [← this]; exact ha
  -- the list identity: Peepul's merge, segment by segment
  have hmain : qCanonList (ρ₀ ++ Δ₁ ++ Δ₂) = qMergeL s₀ s₁ s₂ := by
    unfold qCanonList qMergeL
    rw [List.filter_append, List.filter_append, List.map_append, List.map_append]
    congr 1
    · congr 1
      · -- LCA segment ↔ l-part
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
  exact ⟨ρ₀ ++ Δ₁ ++ Δ₂, hpermU, hrespU, by rw [hfoldU, hmain]; rfl⟩

/-! ## §7  Honest reachability and the capstone -/

/-- Honest histories, at the ternary configuration: every dequeue names a tag
its issuer had observed: a `vis`-prior enqueue with that tag exists. -/
def QHonest (C : Configuration Q) : Prop :=
  ∀ e ∈ C.events, ∀ t : ℕ, e.2.2 = QOp.deq t →
    ∃ a ∈ C.events, C.vis a e ∧ a.1 = t ∧ ∃ v, a.2.2 = QOp.enq v

theorem qHonest_core {C : Configuration Q} (h : QHonest C) :
    QHonestCore (Configuration.core C) := by
  intro e he t ht
  rw [core_events] at he
  obtain ⟨a, ha, hv, hat, w, haw⟩ := h e he t ht
  refine ⟨a, ?_, hv, hat, w, haw⟩
  rw [core_events]
  exact ha

/-- **Honest reachability**: LTS reachability where every step is taken from
a configuration with an honest history. This is the queue's `HonestDelivery`
(the per-step contract under which the Join Lemma is available at each
merge), instantiating the generic `HonestReach`. -/
def QReach : Configuration Q → Prop := HonestReach Q QHonest trivial

/-- The generic honest-reachability induction
(`goodConfig3_of_honest_reach`), with the queue's per-configuration Join
supplied at each merge step from honesty of the pre-merge configuration. -/
theorem q_goodConfig3 {C : Configuration Q} (hReach : QReach C) :
    GoodConfig3 C :=
  goodConfig3_of_honest_reach (fun _ hHon => q_join_at (qHonest_core hHon))
    hReach

/-- **The mergeable queue is RA-linearizable, per version, at every honestly
reachable configuration**: every version the store ever registers is the fold
of a linearization of its event set that respects delivery order. Peepul's
PLDI'22 queue, in the one framework: the specification is the generic
RA-linearizability statement, with no bespoke partial-order spec language and
no head-recovery clause. -/
theorem queue_ra_linearizable3 {C : Configuration Q} (hReach : QReach C) :
    IsRALinearizable3 C :=
  isRALinearizable3_of_good (q_goodConfig3 hReach)

#print axioms queue_ra_linearizable3

/-! ## §8  The generation discipline: `applicable` implies honesty -/

/-- What a well-behaved replica checks before issuing `deq t`: the element
tagged `t` is the **head** of the queue it currently sees. (Enqueues are
unconditional.) The dequeue carries the tag of the head its issuer observed:
the client-facing API is still argumentless `dequeue`; the replica records
which element that call removed. -/
def qApplicable (o : Op QOp) (s : QState) : Prop :=
  match o.2.2 with
  | .enq _ => True
  | .deq t => ∃ v, s.head? = some (t, v)

/-- Every tag in a fold from the empty queue was put there by an enqueue
event of the sequence (no well-formedness needed). -/
theorem qTags_fold_sub : ∀ (π : List (Op QOp)) (t : ℕ),
    t ∈ qTags (applySeq Q.toCRDTSig Q.init π) →
    ∃ a ∈ π, qIsEnq a = true ∧ a.1 = t := by
  intro π
  induction π using List.reverseRecOn with
  | nil =>
    intro t ht
    rw [show applySeq Q.toCRDTSig Q.init ([] : List (Op QOp))
        = ([] : QState) from rfl] at ht
    simp [qTags] at ht
  | append_singleton π e ih =>
    intro t ht
    have hstep : applySeq Q.toCRDTSig Q.init (π ++ [e])
        = qUpdate (applySeq Q.toCRDTSig Q.init π) e := by
      unfold applySeq
      rw [List.foldl_append]
      rfl
    rw [hstep] at ht
    set s : QState := applySeq Q.toCRDTSig Q.init π with hs
    obtain ⟨ts, r, op⟩ := e
    cases op with
    | enq v =>
      by_cases hmem : ts ∈ qTags s
      · rw [show qUpdate s (ts, r, QOp.enq v) = s from by
          unfold qUpdate; simp [hmem]] at ht
        obtain ⟨a, ha, h1, h2⟩ := ih t ht
        exact ⟨a, List.mem_append_left _ ha, h1, h2⟩
      · rw [show qUpdate s (ts, r, QOp.enq v) = s ++ [(ts, v)] from by
          unfold qUpdate; simp [hmem]] at ht
        unfold qTags at ht
        rw [List.map_append, List.mem_append] at ht
        rcases ht with ht | ht
        · obtain ⟨a, ha, h1, h2⟩ := ih t ht
          exact ⟨a, List.mem_append_left _ ha, h1, h2⟩
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at ht
          exact ⟨(ts, r, QOp.enq v), List.mem_append_right _ (by simp),
            by simp [qIsEnq], by simpa using ht.symm⟩
    | deq t' =>
      have hsub : qTags (qUpdate s (ts, r, QOp.deq t')) ⊆ qTags s := by
        intro x hx
        unfold qUpdate at hx
        unfold qTags at hx ⊢
        rw [List.mem_map] at hx ⊢
        obtain ⟨p, hp, hpx⟩ := hx
        exact ⟨p, List.mem_of_mem_filter hp, hpx⟩
      obtain ⟨a, ha, h1, h2⟩ := ih t (hsub ht)
      exact ⟨a, List.mem_append_left _ ha, h1, h2⟩

/-- **The `applicable` discipline discharges honesty.** If every dequeue was
applicable at SOME fold of its issuer's causal past (the issuer's own
materialized state is such a fold, so this is exactly what an honest client
witnesses), then the history is honest: the head's tag can only have entered
that fold through a `vis`-prior enqueue. This is the queue's analogue of the
RGA's applicable-delivery layer, and the formal content of "dequeue names
the head its issuer observed". (Existential form: quantifying over ALL
enumerations of the causal past would be unsatisfiable once a past holds two
surviving enqueues: different orders materialize different heads.) -/
theorem qHonest_of_applicable (C : Configuration Q)
    (hApp : ∀ e ∈ C.events, ∀ t : ℕ, e.2.2 = QOp.deq t →
      ∃ π : List (Op QOp),
        listPermOf π {e' ∈ C.events | C.vis e' e} ∧
        qApplicable e (applySeq Q.toCRDTSig Q.init π)) :
    QHonest C := by
  intro e he t ht
  obtain ⟨π, hπ, happ⟩ := hApp e he t ht
  obtain ⟨ts, r, op⟩ := e
  simp only at ht
  subst ht
  obtain ⟨v, hv⟩ := happ
  have htag : t ∈ qTags (applySeq Q.toCRDTSig Q.init π) := by
    unfold qTags
    rw [List.mem_map]
    exact ⟨(t, v), List.mem_of_mem_head? hv, rfl⟩
  obtain ⟨a, ha, h1, h2⟩ := qTags_fold_sub π t htag
  have haev := (hπ.2 a).mp ha
  obtain ⟨a1, a2, aop⟩ := a
  cases aop with
  | deq t' => exact absurd h1 (by simp [qIsEnq])
  | enq w =>
    exact ⟨(a1, a2, QOp.enq w), haev.1, haev.2, h2, w, rfl⟩

#print axioms qHonest_of_applicable

/-- The queue's honesty contract from the generic honesty shape at
`P := qApplicable`: since `qApplicable` is `True` on enqueues,
`GenHonest Q qApplicable` supplies exactly the dequeue-guarded hypothesis of
`qHonest_of_applicable`. -/
theorem qHonest_of_genHonest (C : Configuration Q)
    (hEnum : CausalPastEnumerable Q C)
    (hApp : GenHonest Q qApplicable C) : QHonest C :=
  qHonest_of_applicable C
    (fun _ he _t _ht => hApp.exists_causalFold hEnum he)

#print axioms qHonest_of_genHonest

/-! ## The widened LTS: the queue over virtual merges

The queue rides the PLAIN `JoinLemma3At`, supplied per honest
configuration by `q_join_at`; the virtual-LCA fold induction
(`virtualLCAState_canonical`) consumes exactly that hook, so lifting the
criss-cross gate costs the queue nothing beyond restating reachability.
No witness-class obligation arises: the queue's honest-history content
lives inside `QHonestCore`, which is per-configuration, not
per-registered-version. -/

/-- Honest reachability over the widened LTS (virtual merges enabled). -/
def QReachV : Configuration Q → Prop := HonestReachV Q QHonest trivial

/-- `GoodConfig3` at every honestly reachable configuration of the widened
LTS: the same per-configuration Join, fed to the V induction. -/
theorem q_goodConfig3V {C : Configuration Q} (hReach : QReachV C) :
    GoodConfig3 C :=
  goodConfig3_of_honest_reachV
    (fun _ hHon => q_join_at (qHonest_core hHon)) hReach

/-- **The mergeable queue is RA-linearizable over the widened LTS**:
per-version RA-linearizability at every honestly reachable configuration
with the criss-cross gate lifted (virtual merges enabled). -/
theorem queue_ra_linearizable3_V {C : Configuration Q} (hReach : QReachV C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_honest_reachV
    (fun _ hHon => q_join_at (qHonest_core hHon)) hReach

#print axioms queue_ra_linearizable3_V

end Sal.ConditionedMRDTs
