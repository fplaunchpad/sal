import Sal.MRDTs.Paper1.RGAStrict
import Sal.MRDTs.Paper1.RGAConflict

/-!
# Full operation-only strict-list crossed-delete investigation

Candidate: no ordering of the six crossed-delete events can both preserve the
independent specification-visible local orders and explain the final [4,6]
read in the live-anchor language. The proof quantifies every allocation choice.
The key invariant is physical-list membership: absent a later deletion, a live
anchor stays visible. Final absence of anchors 1 and 2 therefore requires each
anchor-dependent insertion before that anchor's unique deletion.
-/
namespace Sal.MRDTs.Paper1.RGA.Strict.Investigation
open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.RGA
open Sal.MRDTs.Paper1.RGA.Strict

private theorem old_mem_insertAfter {x anchor id : ℕ} {xs : List ℕ}
    (hx : x ∈ xs) : x ∈ insertAfter anchor id xs := by
  induction xs with
  | nil => cases hx
  | cons a xs ih =>
      unfold insertAfter
      split
      · simp only [List.mem_cons] at hx ⊢
        exact Or.inr hx
      · split
        · simp only [List.mem_cons] at hx ⊢
          rcases hx with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · simp only [List.mem_cons] at hx ⊢
          exact hx.elim Or.inl (fun h => Or.inr (ih h))

private theorem step_preserves_mem {s t : List ℕ × List ℕ}
    {e : Op RGAOp} {id : ℕ}
    (step : machine.transition s (.update e.op) t)
    (hne : e.op ≠ .remove id) (hm : id ∈ s.1) : id ∈ t.1 := by
  obtain ⟨ts, replica, op⟩ := e
  cases op with
  | addAfter anchor =>
      obtain ⟨_, fresh, _, rfl⟩ := step
      exact old_mem_insertAfter hm
  | remove target =>
      change t = (s.1.filter (· ≠ target), s.2) at step
      subst t
      have ht : id ≠ target := by intro h; subst target; exact hne rfl
      exact List.mem_filter.mpr ⟨hm, by simp [ht]⟩

/-- A live identifier survives a suffix with no deletion targeting it. -/
theorem run_preserves_mem (ops : List (Op RGAOp))
    {s t : List ℕ × List ℕ} {answer : List ℕ} {id : ℕ}
    (run : Runs machine.transition s
      (projectedUpdates (D := RGAM) ops ++ [.query () answer]) t)
    (hremove : ∀ e ∈ ops, e.op ≠ .remove id) (hm : id ∈ s.1) :
    id ∈ answer := by
  induction ops generalizing s with
  | nil =>
      cases run with
      | cons hquery _ =>
          have heq : answer = s.1 := hquery.2
          exact heq ▸ hm
  | cons e rest ih =>
      cases run with
      | cons hstep hrest =>
          exact ih hrest (fun e he => hremove e (List.mem_cons_of_mem _ he))
            (step_preserves_mem hstep (hremove e List.mem_cons_self) hm)

/-- If a live-anchor insertion is followed by a query omitting the anchor,
the suffix must contain a deletion of that anchor. This does not bound or
preselect the allocator's choices. -/
theorem insertion_requires_future_delete
    (pre post : List (Op RGAOp)) (e : Op RGAOp) (id : ℕ)
    (hpositive : id ≠ 0) (hop : e.op = .addAfter id) (answer : List ℕ)
    (habsent : id ∉ answer)
    (accepted : spec.admits
      (projectedUpdates (D := RGAM) (pre ++ e :: post) ++ [.query () answer])) :
    ∃ d ∈ post, d.op = .remove id := by
  classical
  obtain ⟨final, run⟩ := accepted
  have grouped : Runs machine.transition machine.initial
      (projectedUpdates (D := RGAM) pre ++
        (.update e.op :: (projectedUpdates (D := RGAM) post ++ [.query () answer]))) final := by
    simpa only [projectedUpdates, List.map_append, List.map_cons, List.append_assoc,
      List.cons_append] using run
  obtain ⟨mid, _, rest⟩ := grouped.split (projectedUpdates (D := RGAM) pre) _
  cases rest with
  | cons hstep hrest =>
      have guard : id = 0 ∨ id ∈ mid.1 := by
        rw [hop] at hstep
        exact hstep.1
      have hlive : id ∈ mid.1 := guard.resolve_left hpositive
      have hnext := step_preserves_mem hstep (by rw [hop]; exact RGAOp.noConfusion) hlive
      by_contra hnone
      have hremove : ∀ d ∈ post, d.op ≠ .remove id := by
        intro d hd he
        exact hnone ⟨d, hd, he⟩
      exact habsent (run_preserves_mem post hrest hremove hnext)

private theorem idxOf_before_of_suffix {α : Type} [BEq α] [LawfulBEq α]
    {pre post : List α} {e d : α}
    (hn : (pre ++ e :: post).Nodup) (hd : d ∈ post) :
    (pre ++ e :: post).idxOf e < (pre ++ e :: post).idxOf d := by
  have hsplit := List.nodup_append.mp hn
  have hepre : e ∉ pre := fun h => hsplit.2.2 e h e List.mem_cons_self rfl
  have hdpre : d ∉ pre := fun h => hsplit.2.2 d h d
    (List.mem_cons_of_mem _ hd) rfl
  have hde : d ≠ e := by
    intro h
    subst d
    exact (List.nodup_cons.mp hsplit.2.1).1 hd
  rw [List.idxOf_append_of_notMem hepre, List.idxOf_append_of_notMem hdpre]
  simp [hde.symm]

/-- Any relation edge in a respected duplicate-free enumeration points to a
strictly later index. -/
theorem respects_idxOf {α : Type} [BEq α] [LawfulBEq α] {ops : List α}
    {R : α → α → Prop} {a b : α} (hr : respects ops R)
    (ha : a ∈ ops) (hb : b ∈ ops) (hne : a ≠ b) (hab : R a b) :
    ops.idxOf a < ops.idxOf b := by
  have hia := List.idxOf_lt_length_of_mem ha
  have hib := List.idxOf_lt_length_of_mem hb
  by_contra h
  have hneq : ops.idxOf a ≠ ops.idxOf b := by
    intro he
    exact hne ((List.idxOf_inj ha).mp he)
  have hlt : ops.idxOf b < ops.idxOf a := by omega
  have hback := (List.pairwise_iff_getElem.mp hr)
    (ops.idxOf b) (ops.idxOf a) hib hia hlt
  apply hback
  simpa only [List.getElem_idxOf hib, List.getElem_idxOf hia] using hab

/-- Abstract query inversion for the strict language. -/
theorem after_delete_not_mem (pre : List (SeqLabel RGAOp Unit (List ℕ)))
    (id : ℕ) (answer : List ℕ)
    (accepted : spec.admits (pre ++ [.update (.remove id), .query () answer])) :
    id ∉ answer := by
  obtain ⟨final, run⟩ := accepted
  obtain ⟨mid, _, rest⟩ := run.split pre [.update (.remove id), .query () answer]
  cases rest with
  | cons hu rest =>
      cases rest with
      | cons hq _ =>
          change _ = (mid.1.filter (· ≠ id), mid.2) at hu
          subst hu
          have hanswer : answer = mid.1.filter (· ≠ id) := hq.2
          rw [hanswer]
          simp

/-- The prefix query fixes a live anchor independently of event metadata. -/
theorem pinned_context_admitted (anchor target : ℕ)
    (hroot : anchor ≠ 0) (hne : target ≠ anchor) :
    spec.admits
      [.update (.addAfter 0), .query () [anchor], .update (.remove target),
       .update (.addAfter anchor), .query () [anchor, target]] := by
  refine ⟨([anchor, target], [anchor, target]),
    .cons (m := ([anchor], [anchor])) ?_
      (.cons (m := ([anchor], [anchor])) ⟨rfl, rfl⟩
        (.cons (m := ([anchor], [anchor])) ?_
          (.cons (m := ([anchor, target], [anchor, target])) ?_
            (.cons ⟨rfl, rfl⟩ (.nil _)))))⟩
  · refine ⟨Or.inl rfl, anchor, ?_⟩
    exact ⟨by simp [machine], rfl⟩
  · change ([anchor], [anchor]) =
      (([anchor] : List ℕ).filter (· ≠ target), [anchor])
    simp [hne.symm]
  · refine ⟨Or.inr (by simp), target, ?_, ?_⟩
    · simp [hne]
    · simp [insertAfter, hroot]

/-- Globally contextual conflict includes a deletion of any different
identifier, because allocation can choose precisely that identifier. -/
theorem insert_remove_not_commute (anchor target : ℕ)
    (hroot : anchor ≠ 0) (hne : target ≠ anchor) :
    ¬ spec.Commutes (.addAfter anchor) (.remove target) := by
  intro commute
  have swapped := (commute [.update (.addAfter 0), .query () [anchor]]
    [.query () [anchor, target]]).mpr (pinned_context_admitted anchor target hroot hne)
  exact after_delete_not_mem
    [.update (.addAfter 0), .query () [anchor], .update (.addAfter anchor)]
    target [anchor, target] swapped (by simp)

/-- A live-anchor insertion whose anchor is absent at the final query must
precede that anchor's unique deletion. -/
theorem anchor_insertion_idxOf (ops : List (Op RGAOp))
    (ins deletion : Op RGAOp) (id : ℕ) (answer : List ℕ)
    (hnodup : ops.Nodup) (hins : ins ∈ ops)
    (hpositive : id ≠ 0) (hop : ins.op = .addAfter id)
    (hunique : ∀ d ∈ ops, d.op = .remove id → d = deletion)
    (habsent : id ∉ answer)
    (accepted : spec.admits
      (projectedUpdates (D := RGAM) ops ++ [.query () answer])) :
    ops.idxOf ins < ops.idxOf deletion := by
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hins
  obtain ⟨d, hd, hdop⟩ := insertion_requires_future_delete pre post ins id
    hpositive hop answer habsent (by simpa only [hsplit] using accepted)
  have hdops : d ∈ ops := by rw [hsplit]; simp [hd]
  have heq := hunique d hdops hdop
  subst d
  have hnodup' : (pre ++ ins :: post).Nodup := by simpa only [hsplit] using hnodup
  simpa only [hsplit] using idxOf_before_of_suffix hnodup' hd

/-- Full all-choice and all-order exclusion. The history starts from the
language's empty initial state; roots may allocate any permitted identifiers.
Only the two specified deletion events can remove the absent final anchors. -/
theorem crossed_no_history (ops : List (Op RGAOp))
    (insOne deleteOne insTwo deleteTwo : Op RGAOp) (one two : ℕ)
    (answer : List ℕ) (hnodup : ops.Nodup)
    (hiOne : insOne ∈ ops) (hiTwo : insTwo ∈ ops)
    (hpOne : one ≠ 0) (hpTwo : two ≠ 0)
    (hoOne : insOne.op = .addAfter one) (hoTwo : insTwo.op = .addAfter two)
    (hdOne : ∀ d ∈ ops, d.op = .remove one → d = deleteOne)
    (hdTwo : ∀ d ∈ ops, d.op = .remove two → d = deleteTwo)
    (haOne : one ∉ answer) (haTwo : two ∉ answer)
    (hcross : ops.idxOf deleteOne < ops.idxOf insTwo ∧
      ops.idxOf deleteTwo < ops.idxOf insOne) :
    ¬ spec.admits (projectedUpdates (D := RGAM) ops ++ [.query () answer]) := by
  intro accepted
  have hOne := anchor_insertion_idxOf ops insOne deleteOne one answer
    hnodup hiOne hpOne hoOne hdOne haOne accepted
  have hTwo := anchor_insertion_idxOf ops insTwo deleteTwo two answer
    hnodup hiTwo hpTwo hoTwo hdTwo haTwo accepted
  omega

/-- The original six-event strict scenario is excluded from the empty initial
state, independently of all allocations made by the two genesis labels. -/
theorem six_event_no_history (ops : List (Op RGAOp))
    (hperm : listPermOf ops {e | e ∈ Trace.all})
    (hcross : ops.idxOf Trace.deleteOne < ops.idxOf Trace.afterTwo ∧
      ops.idxOf Trace.deleteTwo < ops.idxOf Trace.afterOne) :
    ¬ spec.admits (projectedUpdates (D := RGAM) ops ++ [.query () [4, 6]]) := by
  apply crossed_no_history ops Trace.afterOne Trace.deleteOne Trace.afterTwo
    Trace.deleteTwo 1 2 [4, 6] hperm.1
  · apply (hperm.2 _).mpr
    simp [Trace.all, Trace.genesis]
  · apply (hperm.2 _).mpr
    simp [Trace.all, Trace.genesis]
  · decide
  · decide
  · rfl
  · rfl
  · intro d hd hop
    have hmem := (hperm.2 d).mp hd
    simp only [Set.mem_setOf_eq, Trace.all, Trace.genesis, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with (rfl | rfl) | rfl | rfl | rfl | rfl <;>
      first | rfl | (simp [Op.op, Trace.rootOne, Trace.rootTwo,
        Trace.deleteOne, Trace.afterTwo, Trace.deleteTwo, Trace.afterOne] at hop)
  · intro d hd hop
    have hmem := (hperm.2 d).mp hd
    simp only [Set.mem_setOf_eq, Trace.all, Trace.genesis, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with (rfl | rfl) | rfl | rfl | rfl | rfl <;>
      first | rfl | (simp [Op.op, Trace.rootOne, Trace.rootTwo,
        Trace.deleteOne, Trace.afterTwo, Trace.deleteTwo, Trace.afterOne] at hop)
  · decide
  · decide
  · exact hcross

/-- Positive control: an admitted history exists when the two crossed local
orders are dropped. It starts from the same empty specification state. -/
theorem six_event_unconstrained_admitted :
    spec.admits
      [.update (.addAfter 0), .update (.addAfter 0),
       .update (.addAfter 2), .update (.addAfter 1),
       .update (.remove 1), .update (.remove 2), .query () [4, 6]] := by
  have genesisRun : Runs machine.transition ([], [])
      [.update (.addAfter 0), .update (.addAfter 0)] ([2, 1], [1, 2]) := by
    refine .cons (m := ([1], [1])) ?_ (.cons ?_ (.nil _))
    · exact ⟨Or.inl rfl, 1, by simp, rfl⟩
    · exact ⟨Or.inl rfl, 2, by decide, rfl⟩
  exact ⟨_, genesisRun.append (Trace.unconstrained_suffix.append
    (.cons ⟨rfl, rfl⟩ (.nil _)))⟩

/-- PASS+FAIL: empty-state acceptance is nonvacuous, while the natural local
serialization cannot explain the final answer. -/
example : spec.admits
      [.update (.addAfter 0), .update (.addAfter 0),
       .update (.addAfter 2), .update (.addAfter 1),
       .update (.remove 1), .update (.remove 2), .query () [4, 6]] ∧
    ¬ spec.admits
      (projectedUpdates (D := RGAM) Trace.all ++ [.query () [4, 6]]) := by
  refine ⟨six_event_unconstrained_admitted, six_event_no_history Trace.all ?_ ?_⟩
  · exact ⟨by decide, fun _ => Iff.rfl⟩
  · decide

/-- Boundary control: the permissive language DOES admit the natural six-event
serialization. Its root allocations display the final child IDs, while the two
missing-anchor insertions allocate unrelated reserved IDs and become no-ops.
Thus the strict six-event refutation cannot be relabelled as a refutation of the
primary missing-anchor-no-op specification. -/
theorem six_event_primary_escape :
    Sal.MRDTs.Paper1.RGA.listHistorySpec.admits
      (projectedUpdates (D := RGAM) Trace.all ++ [.query () [4, 6]]) := by
  refine ⟨([4, 6], [6, 4, 10, 11]),
    .cons (m := ([6], [6])) ?_
      (.cons (m := ([4, 6], [6, 4])) ?_
        (.cons (m := ([4, 6], [6, 4])) rfl
          (.cons (m := ([4, 6], [6, 4, 10])) ?_
            (.cons (m := ([4, 6], [6, 4, 10])) rfl
              (.cons (m := ([4, 6], [6, 4, 10, 11])) ?_
                (.cons ⟨rfl, rfl⟩ (.nil _)))))))⟩
  · refine ⟨6, ?_⟩
    exact ⟨by simp [Sal.MRDTs.Paper1.RGA.allocationMachine], rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨10, by decide, rfl⟩
  · exact ⟨11, by decide, rfl⟩

/-- Configuration-level full refutation. Reachability and honest issuance are
separate concrete execution obligations; no prescribed prefix or allocation
choices occur in this predicate-level theorem. -/
theorem crossed_not_specificationRA
    (P : OperationPolicy RGAOp) (C : Configuration RGAM)
    (r v : ℕ) (state : RGAM.State) (E : Set (Op RGAOp))
    (insOne deleteOne insTwo deleteTwo : Op RGAOp) (one two : ℕ)
    (answer : List ℕ)
    (hhead : C.head r = some v) (hver : C.ver v = some (state, E))
    (hread : RGAM.query state () = answer)
    (hiOne : insOne ∈ E) (hiTwo : insTwo ∈ E)
    (hdOneMem : deleteOne ∈ E) (hdTwoMem : deleteTwo ∈ E)
    (hpOne : one ≠ 0) (hpTwo : two ≠ 0) (hne : one ≠ two)
    (hoOne : insOne.op = .addAfter one) (hoTwo : insTwo.op = .addAfter two)
    (hdoOne : deleteOne.op = .remove one) (hdoTwo : deleteTwo.op = .remove two)
    (hdOne : ∀ d ∈ E, d.op = .remove one → d = deleteOne)
    (hdTwo : ∀ d ∈ E, d.op = .remove two → d = deleteTwo)
    (haOne : one ∉ answer) (haTwo : two ∉ answer)
    (hvisOne : C.vis deleteOne insTwo) (hvisTwo : C.vis deleteTwo insOne) :
    ¬ SpecificationRALinearizable RGAM P spec C := by
  intro criterion
  obtain ⟨ops, hperm, _, hspec, accepted⟩ :=
    criterion r v state E hhead hver ()
  have hmOne : insOne ∈ ops := (hperm.2 _).mpr hiOne
  have hmTwo : insTwo ∈ ops := (hperm.2 _).mpr hiTwo
  have hmdOne : deleteOne ∈ ops := (hperm.2 _).mpr hdOneMem
  have hmdTwo : deleteTwo ∈ ops := (hperm.2 _).mpr hdTwoMem
  have hedgeOne : specVisibility spec C.replayContext deleteOne insTwo := by
    refine ⟨hvisOne, ?_⟩
    rw [hdoOne, hoTwo]
    intro hc
    exact insert_remove_not_commute two one hpTwo hne
      (HistorySpec.commutes_symm hc)
  have hedgeTwo : specVisibility spec C.replayContext deleteTwo insOne := by
    refine ⟨hvisTwo, ?_⟩
    rw [hdoTwo, hoOne]
    intro hc
    exact insert_remove_not_commute one two hpOne hne.symm
      (HistorySpec.commutes_symm hc)
  have hcrossOne := respects_idxOf hspec hmdOne hmTwo
    (by intro he; have hop := congrArg Op.op he; rw [hdoOne, hoTwo] at hop; cases hop)
    hedgeOne
  have hcrossTwo := respects_idxOf hspec hmdTwo hmOne
    (by intro he; have hop := congrArg Op.op he; rw [hdoTwo, hoOne] at hop; cases hop)
    hedgeTwo
  have reject := crossed_no_history ops insOne deleteOne insTwo deleteTwo one two
    answer hperm.1 hmOne hmTwo hpOne hpTwo hoOne hoTwo
    (fun d hd => hdOne d ((hperm.2 d).mp hd))
    (fun d hd => hdTwo d ((hperm.2 d).mp hd)) haOne haTwo ⟨hcrossOne, hcrossTwo⟩
  exact reject (by simpa only [hread] using accepted)

#print axioms insert_remove_not_commute
#print axioms crossed_no_history
#print axioms crossed_not_specificationRA
end Sal.MRDTs.Paper1.RGA.Strict.Investigation
