import Sal.MRDTs.Instances.QueueCertificates

/-! Queue client-contract obligations derived from certified executions.
The public legalization and certificate are in `QueueLegalization`; the
combined concurrent FIFO contract is in `QueueCorrectness`. -/

namespace Sal.MRDTs.Instances.Queue

open Sal.MRDTs.Foundation
open Classical

/-- Abstract dequeue only removes the named head. It never removes a live
element from the middle of the queue. Legality separately rejects that case. -/
def clientStep (s : List (ℕ × ℕ)) (e : Op QOp) : List (ℕ × ℕ) :=
  match e.2.2 with
  | .enq value => s ++ [(e.1, value)]
  | .deq target =>
    match s with
    | [] => []
    | (tag, _) :: rest => if tag = target then rest else s

/-- Prefix legality tracks previously enqueued identities in the history,
not in the abstract queue state. A repeated removal is permitted only for a
previously enqueued target that is now absent. -/
def clientLegalAux (born : List ℕ) (s : List (ℕ × ℕ)) : List (Op QOp) → Bool
  | [] => true
  | e :: rest =>
    let next := clientStep s e
    match e.2.2 with
    | .enq _ => !(born.contains e.1) && clientLegalAux (e.1 :: born) next rest
    | .deq target =>
      born.contains target &&
        ((s.head?.map Prod.fst == some target) || !(s.map Prod.fst).contains target) &&
        clientLegalAux born next rest

/-- Client specification certified by `Queue.verified`. Concurrent duplicate
targets are reconciled by legality together with head-checked issuance. -/
def clientSpec : SequentialSpec Q where
  State := List (ℕ × ℕ)
  init := []
  step := clientStep
  Legal := fun ops => clientLegalAux [] [] ops = true
  query := fun s _ => s.head?

/-- At a legal origin, abstract head removal agrees with the implementation's
named removal. The no-middle-deletion requirement is supplied by the guard. -/
theorem clientStep_eq_update {s : QState} {e : Op QOp}
    (hnd : (qTags s).Nodup) (hg : qApplicable e s) :
    clientStep s e = qUpdate s e := by
  obtain ⟨ts, replica, op⟩ := e
  cases op with
  | enq value =>
    change ts ∉ qTags s at hg
    simp [clientStep, qUpdate, hg]
  | deq target =>
    obtain ⟨value, rest, rfl⟩ := hg
    have hnot : target ∉ qTags rest := (List.nodup_cons.mp hnd).1
    have hfilter : rest.filter (fun p => decide (p.1 ≠ target)) = rest := by
      apply List.filter_eq_self.mpr
      intro p hp
      simp only [decide_eq_true_eq]
      intro heq
      exact hnot (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
    simpa [clientStep, qUpdate] using hfilter.symm

/-- The abstract machine preserves the existing ordinary FIFO
theorem on linear, head-checked histories. No concurrency assumption is
smuggled into the ordinary sequential transition. -/
theorem client_run_eq_of_qOK {ops : List (Op QOp)} (h : qOK ops) :
    clientSpec.run ops = applySeq Q.toUpdateSig Q.init ops := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton pre e ih =>
    rw [SequentialSpec.run_append_single, applySeq_append_single]
    change clientStep (clientSpec.run pre) e =
      qUpdate (applySeq Q.toUpdateSig Q.init pre) e
    rw [ih (qOK_prefix h)]
    apply clientStep_eq_update (q_tags_nodup (qOK_prefix h))
    have hg := h pre e [] (by simp)
    obtain ⟨ts, replica, op⟩ := e
    cases op with
    | enq value => exact hg.1 value rfl
    | deq target => exact hg.2 target rfl

theorem client_linear_fifo {ops : List (Op QOp)}
    (h : LinearMintHistory Q generation.CanIssue ops) :
    (clientSpec.run ops).map Prod.snd = qSpecFold ops := by
  rw [client_run_eq_of_qOK (qOK_of_linear h)]
  exact queue_seq_sound (qOK_of_linear h)

/-- A causal enumeration cannot put a dequeue before its own enqueue.
Unlike the replay-order lemma, this applies directly to mint-time histories. -/
theorem q_wf_of_causal_enum {C : Configuration Q} (hHon : QHonest C)
    {E : Set (Op QOp)} {ops : List (Op QOp)}
    (hin : ∀ e ∈ E, e ∈ C.events)
    (hp : listPermOf ops E) (hr : respects ops C.vis) : QWf ops := by
  refine ⟨hp.1, ?_, ?_⟩
  · intro a ha b hb _ _ ht
    exact C.replayContext.ts_unique (hin a ((hp.2 a).mp ha))
      (hin b ((hp.2 b).mp hb)) ht
  · intro pre post hsplit d hd hdeq a ha henq htag
    have hdops : d ∈ ops := by rw [hsplit]; exact List.mem_append_left _ hd
    have haops : a ∈ ops := by rw [hsplit]; exact List.mem_append_right _ ha
    obtain ⟨dt, dr, dop⟩ := d
    cases dop with
    | enq v => simp [qIsEnq] at hdeq
    | deq target =>
      obtain ⟨birth, hbirth, hv, ht, _⟩ :=
        hHon (dt, dr, .deq target) (hin _ ((hp.2 _).mp hdops)) target rfl
      have heq : a = birth := C.replayContext.ts_unique
        (hin a ((hp.2 a).mp haops)) hbirth
        ((by simpa [qTag] using htag : a.1 = target).trans ht.symm)
      have hcross := (List.pairwise_append.mp (hsplit ▸ hr)).2.2
      exact hcross _ hd a ha (heq ▸ hv)

/-- A dequeue's target was not dequeued anywhere in its visible past.
The statement uses the strong origin guard, not the weaker replay honesty. -/
theorem issued_dequeue_no_visible_dequeue {C : Configuration Q}
    (exec : CertifiedExecution Q generation C)
    {d : Op QOp} (hd : d ∈ C.events) {target : ℕ}
    (hop : d.2.2 = .deq target) :
    ¬ qDeqIn {e ∈ C.events | C.vis e d} target := by
  have hm := exec.mintHonest
  obtain ⟨ops, hp, hr, hg⟩ := hm d hd
  have hwf := q_wf_of_causal_enum (qHonest_of_mint C hm)
    (fun _ he => he.1) hp hr
  change qApplicable d (applySeq Q.toUpdateSig Q.init ops) at hg
  unfold qApplicable at hg
  rw [hop] at hg
  obtain ⟨v, rest, hs⟩ := hg
  have htag : target ∈ qTags (qCanonList ops) := by
    rw [← q_fold_canon ops hwf, hs]
    simp [qTags]
  exact ((qTags_canon_perm hp).mp htag).2

/-- Concurrent duplicate dequeues are permitted; causally ordered duplicate
dequeues are excluded by issuance, independently of the chosen replay. -/
theorem duplicate_dequeues_concurrent {C : Configuration Q}
    (exec : CertifiedExecution Q generation C)
    {a b : Op QOp} (ha : a ∈ C.events) (hb : b ∈ C.events)
    {target : ℕ} (hoa : a.2.2 = .deq target) (hob : b.2.2 = .deq target) :
    ¬ C.vis a b ∧ ¬ C.vis b a := by
  constructor
  · intro hvis
    apply issued_dequeue_no_visible_dequeue exec hb hob
    exact ⟨a, ⟨ha, hvis⟩, by simp [qIsEnq, hoa], by simp [qTag, hoa]⟩
  · intro hvis
    apply issued_dequeue_no_visible_dequeue exec ha hoa
    exact ⟨b, ⟨hb, hvis⟩, by simp [qIsEnq, hob], by simp [qTag, hob]⟩

/-- Exact surviving identities, for every stored version in either execution
mode. Duplicate dequeue events remove one identity, not an additional head. -/
theorem queue_version_contents {C : Configuration Q}
    (exec : CertifiedExecution Q generation C)
    {v : Version} {s : QState} {E : Set (Op QOp)}
    (hver : C.ver v = some (s, E)) (target : ℕ) :
    target ∈ qTags s ↔ qEnqIn E target ∧ ¬ qDeqIn E target := by
  have hgood : QGoodCore C.replayContext :=
    qGood_core (qHonest_of_mint C exec.mintHonest)
  have hcanonical : CanonicalConfig C :=
    exec.canonicalConfig (fun C hm => q_join_at (qGood_core (qHonest_of_mint C hm)))
  have hreplay : @HasReplayWitness Q rc C := by
    cases exec with
    | ordinary h => exact replayAdequacy.sound h
    | virtual h => exact replayAdequacy.soundV h
  obtain ⟨ops, hp, hr, hf⟩ := hreplay v s E hver
  have hwf := q_wf_of_enum hgood.1
    (hcanonical.version_events_supported v s E hver)
    (fun a b hv _ hb => hcanonical.version_events_causal v s E hver a b hv hb)
    hp hr
  rw [← hf, q_fold_canon ops hwf]
  exact qTags_canon_perm hp

#print axioms issued_dequeue_no_visible_dequeue
#print axioms duplicate_dequeues_concurrent
#print axioms queue_version_contents
#print axioms client_linear_fifo

end Sal.MRDTs.Instances.Queue
