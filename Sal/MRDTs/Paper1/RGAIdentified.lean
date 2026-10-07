import Sal.MRDTs.Paper1.RGAActive
import Sal.MRDTs.Paper1.ProjectedCriterion

/-! Explicit insertion identifiers change the application labels, while preserving
RGAM and its generation policy. The abstract state is an ordinary list and an
allocation registry. Strict live-anchor and missing-anchor-no-op languages are
separate choices. Neither machine reads timestamps or replicas. -/
namespace Sal.MRDTs.Paper1.RGA.Identified
open Foundation
open Sal.MRDTs.Instances.RGA

inductive Update where
  | addAfter (id anchor : ℕ)
  | remove (id : ℕ)
  deriving DecidableEq, Repr

def project (e : Op RGAOp) : Update := match e.op with
  | .addAfter anchor => .addAfter e.time anchor
  | .remove id => .remove id

def machine (strict : Bool) : HistoryMachine Update Unit (List ℕ) where
  State := List ℕ × Finset ℕ
  initial := ([], ∅)
  transition state label next := match label with
    | .update (.addAfter id anchor) =>
        id ∉ state.2 ∧ (strict = false ∨ anchor = 0 ∨ anchor ∈ state.1) ∧
          next = (insertAfter anchor id state.1, insert id state.2)
    | .update (.remove id) => next = (state.1.filter (· ≠ id), state.2)
    | .query _ answer => next = state ∧ answer = state.1

def strictSpec := (machine true).toSpec
def missingNoopSpec := (machine false).toSpec

def labels (ops : List (Op RGAOp)) : List (SeqLabel Update Unit (List ℕ)) :=
  ops.map (fun e => .update (project e))

def registry (ops : List (Op RGAOp)) : Finset ℕ :=
  ((insertEntries ops).map Prod.fst).toFinset

private theorem mem_registry {ops : List (Op RGAOp)} {id : ℕ}
    (h : id ∈ registry ops) : id ∈ ops.map Op.time := by
  simp only [registry, List.mem_toFinset, List.mem_map] at h
  obtain ⟨⟨i, a⟩, he, hi⟩ := h
  subst id
  obtain ⟨r, hr⟩ := mem_insertEntries.mp he
  exact List.mem_map.mpr ⟨(i, r, .addAfter a), hr, rfl⟩

private theorem mem_insert_preserved (anchor id x : ℕ) (xs : List ℕ)
    (h : x ∈ xs) : x ∈ insertAfter anchor id xs := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
      simp only [insertAfter]
      split
      · simp_all
      · split
        · simp only [List.mem_cons] at h ⊢
          exact h.elim Or.inl (fun h => Or.inr (Or.inr h))
        · simp only [List.mem_cons] at h ⊢
          exact h.elim Or.inl (fun h => Or.inr (ih h))

private theorem inserted_mem (anchor id : ℕ) (xs : List ℕ)
    (h : anchor = 0 ∨ anchor ∈ xs) : id ∈ insertAfter anchor id xs := by
  induction xs with
  | nil => simp_all [insertAfter]
  | cons y ys ih =>
      simp only [insertAfter]
      split
      · simp
      · split
        · simp
        · simp only [List.mem_cons]
          exact Or.inr (ih (by
            simp only [List.mem_cons] at h
            simp_all [eq_comm]))

private theorem legal_prefix {ops : List (Op RGAOp)} {e : Op RGAOp}
    (h : listLegal (ops ++ [e])) : listLegal ops := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb ht
    exact h.1 a (List.mem_append_left _ ha) b (List.mem_append_left _ hb) ht
  · intro pre x post hs
    exact h.2 pre x (post ++ [e]) (by simp [hs, List.append_assoc])

/-- Ordered legal event lists run in the strict independent machine. The extra
invariant records that before the deletion block every inserted ID is live. -/
private theorem strict_run_aux (ops : List (Op RGAOp))
    (fresh : (ops.map Op.time).Nodup) (ordered : ops.Pairwise WitnessLE)
    (legal : listLegal ops) :
    Runs (machine true).transition ([], ∅) (labels ops)
      (listSpec.run ops, registry ops) ∧
    (removedIds ops = [] → ∀ ts r a, (ts, r, .addAfter a) ∈ ops →
      List.Mem ts (listSpec.run ops)) := by
  induction ops using List.reverseRecOn with
  | nil => exact ⟨.nil _, by simp⟩
  | append_singleton ops e ih =>
      have hn : (ops.map Op.time).Nodup ∧ e.time ∉ ops.map Op.time := by
        have hf : (ops.map Op.time ++ [e.time]).Nodup := by simpa using fresh
        rw [List.nodup_append_comm] at hf
        simpa [and_comm] using hf
      have hp := (List.pairwise_append.mp ordered).1
      obtain ⟨run, live⟩ := ih hn.1 hp (legal_prefix legal)
      obtain ⟨ts, r, op⟩ := e
      cases op with
      | addAfter anchor =>
          have norem : removedIds ops = [] := removedIds_eq_nil_of_before_add ordered
          have guard : anchor = 0 ∨ List.Mem anchor (listSpec.run ops) := by
            have hl := legal.2 ops (ts, r, .addAfter anchor) [] (by simp)
            rcases hl with root | ⟨pr, pa, birth⟩
            · exact Or.inl root
            · exact Or.inr (live norem anchor pr pa birth)
          constructor
          · have hf : ts ∉ registry ops := fun h => hn.2 (mem_registry h)
            have next : registry (ops ++ [(ts, r, .addAfter anchor)]) =
                insert ts (registry ops) := by
              simp [registry, insertEntries, List.toFinset_append]
            rw [show labels (ops ++ [(ts, r, .addAfter anchor)]) =
                labels ops ++ [.update (.addAfter ts anchor)] by simp [labels, project, Op.op, Op.time]]
            rw [SequentialSpec.run_append_single, next]
            exact run.append (.cons ⟨hf, Or.inr guard, rfl⟩ (.nil _))
          · intro _ i ri ai h
            rw [SequentialSpec.run_append_single]
            change i ∈ insertAfter anchor ts (listSpec.run ops)
            rw [List.mem_append] at h
            rcases h with h | h
            · exact mem_insert_preserved _ _ _ _ (live norem i ri ai h)
            · simp only [List.mem_singleton] at h
              cases h
              exact inserted_mem _ _ _ guard
      | remove id =>
          constructor
          · have next : registry (ops ++ [(ts, r, .remove id)]) = registry ops := by
              simp [registry, insertEntries]
            rw [show labels (ops ++ [(ts, r, .remove id)]) =
                labels ops ++ [.update (.remove id)] by simp [labels, project, Op.op, Op.time]]
            rw [SequentialSpec.run_append_single, next]
            exact run.append (.cons rfl (.nil _))
          · simp [removedIds]

/-- One hand-selected canonical history is accepted with a strict live anchor
and globally fresh explicit insertion IDs. -/
theorem strict_canonical_admitted {ops : List (Op RGAOp)} {E : Set (Op RGAOp)}
    (hperm : listPermOf ops E) (hwf : VersionWellFormed E) :
    strictSpec.admits (labels (canonical ops) ++
      [.query () (listSpec.run (canonical ops))]) := by
  have hcan := canonical_listPermOf hperm
  have hfresh : ((canonical ops).map Op.time).Nodup :=
    List.Nodup.map_on (fun a ha b hb he =>
      hwf.time_unique ((hcan.2 a).mp ha) ((hcan.2 b).mp hb) he) hcan.1
  exact ⟨_, (strict_run_aux _ hfresh (canonical_ordered ops)
    (canonical_legal hperm hwf)).1.append (.cons ⟨rfl, rfl⟩ (.nil _))⟩


def advance (s : List ℕ × Finset ℕ) : Update → List ℕ × Finset ℕ
  | .addAfter id anchor => (insertAfter anchor id s.1, insert id s.2)
  | .remove id => (s.1.filter (· ≠ id), s.2)

def guard (strict : Bool) (s : List ℕ × Finset ℕ) : Update → Prop
  | .addAfter id anchor => id ∉ s.2 ∧
      (strict = false ∨ anchor = 0 ∨ anchor ∈ s.1)
  | .remove _ => True

private theorem transition_update (strict : Bool) (s t : List ℕ × Finset ℕ)
    (u : Update) : (machine strict).transition s (.update u) t ↔
      guard strict s u ∧ t = advance s u := by
  cases u <;> simp [machine, guard, advance, and_assoc]

private theorem pair_run_iff (strict : Bool) (s t : List ℕ × Finset ℕ)
    (a b : Update) :
    Runs (machine strict).transition s [.update a, .update b] t ↔
      guard strict s a ∧ guard strict (advance s a) b ∧
      t = advance (advance s a) b := by
  constructor
  · intro h
    cases h with
    | cons ha rest =>
      cases rest with
      | cons hb rest =>
        cases rest
        obtain ⟨ga, rfl⟩ := (transition_update _ _ _ _).mp ha
        obtain ⟨gb, rfl⟩ := (transition_update _ _ _ _).mp hb
        exact ⟨ga, gb, rfl⟩
  · rintro ⟨ga, gb, rfl⟩
    exact .cons ((transition_update _ _ _ _).mpr ⟨ga, rfl⟩)
      (.cons ((transition_update _ _ _ _).mpr ⟨gb, rfl⟩) (.nil _))

@[simp] theorem insertAfter_zero (id : ℕ) (xs : List ℕ) :
    insertAfter 0 id xs = id :: xs := by cases xs <;> rfl

private theorem filter_insert (xs : List ℕ) (id anchor target : ℕ)
    (hi : target ≠ id) (ha : anchor = 0 ∨ target ≠ anchor) :
    (insertAfter anchor id xs).filter (· ≠ target) =
      insertAfter anchor id (xs.filter (· ≠ target)) := by
  simp only [decide_not]
  induction xs with
  | nil => simp [insertAfter, Ne.symm hi]
  | cons x xs ih =>
      by_cases root : anchor = 0
      · simp [insertAfter, root, Ne.symm hi]
      · have hat : anchor ≠ target := Ne.symm (ha.resolve_left root)
        by_cases hit : x = anchor
        · subst x
          simp [insertAfter, root, hat, Ne.symm hi]
        · by_cases deleted : x = target
          · subst x
            simp [insertAfter, root, hit, ih]
          · simp [insertAfter, root, hit, deleted, ih]

/-- Physical deletions commute in either independent list language. -/
theorem deletes_commute (strict : Bool) (i j : ℕ) :
    (machine strict).toSpec.Commutes (.remove i) (.remove j) := by
  apply HistoryMachine.commutes_of_diamond
  intro s t
  rw [pair_run_iff, pair_run_iff]
  have filters : (s.1.filter (· ≠ i)).filter (· ≠ j) =
      (s.1.filter (· ≠ j)).filter (· ≠ i) := by
    simp only [List.filter_filter]
    congr 1
    funext x
    exact Bool.and_comm _ _
  simp only [guard, true_and]
  change t = ((s.1.filter (· ≠ i)).filter (· ≠ j), s.2) ↔
    t = ((s.1.filter (· ≠ j)).filter (· ≠ i), s.2)
  rw [filters]

/-- Explicit insertion ID removes the allocator's spurious conflicts with
unrelated deletion targets. This is a contextual-language theorem, including
all prefixes and suffixes, rather than a fixed initial-state observation. -/
theorem insert_delete_commute (strict : Bool) (id anchor target : ℕ)
    (outside : ¬ insertDeleteConflict anchor id target) :
    (machine strict).toSpec.Commutes (.addAfter id anchor) (.remove target) := by
  have hi : target ≠ id := fun h => outside (Or.inl h)
  have ha : anchor = 0 ∨ target ≠ anchor := by
    by_cases h : anchor = 0
    · exact Or.inl h
    · exact Or.inr (fun eq => outside (Or.inr ⟨h, eq⟩))
  apply HistoryMachine.commutes_of_diamond
  intro s t
  rw [pair_run_iff, pair_run_iff]
  have hg : guard strict (advance s (.remove target)) (.addAfter id anchor) ↔
      guard strict s (.addAfter id anchor) := by
    rcases ha with root | h
    · simp [guard, advance, root]
    · simp [guard, advance, List.mem_filter, Ne.symm h]
  have eq : advance (advance s (.addAfter id anchor)) (.remove target) =
      advance (advance s (.remove target)) (.addAfter id anchor) := by
    exact Prod.ext (filter_insert _ _ _ _ hi ha) rfl
  change (guard strict s (.addAfter id anchor) ∧ True ∧
      t = advance (advance s (.addAfter id anchor)) (.remove target)) ↔
    (True ∧ guard strict (advance s (.remove target)) (.addAfter id anchor) ∧
      t = advance (advance s (.remove target)) (.addAfter id anchor))
  rw [hg, eq]
  simp only [true_and]


/-- Honest issuance supplies precisely the conflict exclusions needed by the
canonical witness; global concrete/specification commutation agreement is not
assumed (and is false for this grow-only implementation). -/
theorem canonical_respects_specVisibility (strict : Bool)
    {C : Configuration RGAM} (exec : CertifiedExecution RGAM generation C)
    {v : Version} {s : RGAM.State} {E : Set (Op RGAOp)}
    (hver : C.ver v = some (s, E)) {ops : List (Op RGAOp)}
    (hperm : listPermOf ops E) :
    respects (canonical ops)
      (projectedSpecVisibility project (machine strict).toSpec C.replayContext) := by
  have combined := (canonical_ordered ops).and (canonical_respects_rc exec hver hperm)
  apply combined.imp
  intro a b h hspec
  obtain ⟨ats, ar, aop⟩ := a
  obtain ⟨bts, br, bop⟩ := b
  cases aop with
  | addAfter anchor =>
      cases bop with
      | addAfter ba =>
          have hle : ats ≤ bts := by
            simpa [WitnessLE, witnessLEBool] using h.1
          exact (Nat.not_lt_of_ge hle) (C.causal_mono hspec.1)
      | remove target =>
          have conflict : insertDeleteConflict anchor ats target := by
            by_contra outside
            exact hspec.2 (by
              simpa only [project, Op.op, Op.time] using
                HistorySpec.commutes_symm (insert_delete_commute strict ats anchor target outside))
          apply h.2
          exact Or.inl ⟨hspec.1, Or.inr (by simpa [rc, rcOrder] using conflict)⟩
  | remove target =>
      cases bop with
      | addAfter anchor => simp [WitnessLE, witnessLEBool] at h
      | remove other =>
          exact hspec.2 (by
            simpa only [project, Op.op] using deletes_commute strict other target)

private theorem strict_runs_missing {s t : List ℕ × Finset ℕ} {ls}
    (h : Runs (machine true).transition s ls t) :
    Runs (machine false).transition s ls t := by
  induction h with
  | nil => exact .nil _
  | @cons s m t label ls trans rest ih =>
      apply Runs.cons (m := m) _ ih
      cases label with
      | update u =>
          cases u with
          | addAfter id anchor => exact ⟨trans.1, Or.inl rfl, trans.2.2⟩
          | remove id => exact trans
      | query q answer => exact trans

theorem strict_admits_missing {ls : List (SeqLabel Update Unit (List ℕ))}
    (h : strictSpec.admits ls) : missingNoopSpec.admits ls := by
  obtain ⟨t, run⟩ := h
  exact ⟨t, strict_runs_missing run⟩

/-- The explicit-ID strict language explains every stored version under the
stronger projected criterion, with the concrete RGAM and issuer unchanged. -/
theorem versions_of_execution (strict : Bool) {C : Configuration RGAM}
    (exec : CertifiedExecution RGAM generation C) :
    ∀ v s E, C.ver v = some (s, E) → ∀ q,
      ∃ π : List (Op RGAOp), listPermOf π E ∧
        respects π (paperOrder emptyPolicy C.replayContext E) ∧
        respects π (projectedSpecVisibility project (machine strict).toSpec C.replayContext) ∧
        (machine strict).toSpec.admits
          (projectedLabels (D := RGAM) project π ++ [.query q (RGAM.query s q)]) := by
  have replay : HasReplayWitness C := by
    cases exec with
    | ordinary reach => exact replayAdequacy.sound reach
    | virtual reach => exact replayAdequacy.soundV reach
  intro v s E hver q
  cases q
  obtain ⟨ops, hperm, _, hfold⟩ := replay v s E hver
  have hwf := versionWellFormed_of_execution exec hver
  have href := canonical_refines_list hperm hwf
  have hstate := (canonical_fold ops).trans hfold
  change read (applySeq RGAM.toUpdateSig RGAM.init (canonical ops)) =
    listSpec.run (canonical ops) at href
  rw [hstate] at href
  refine ⟨canonical ops, canonical_listPermOf hperm,
    (canonical_ordered ops).imp (fun {_ _} _ => paperOrder_empty _ _ _ _),
    canonical_respects_specVisibility strict exec hver hperm, ?_⟩
  change (machine strict).toSpec.admits
    (labels (canonical ops) ++ [.query () (read s)])
  rw [href]
  have accepted := strict_canonical_admitted hperm hwf
  cases strict with
  | false => exact strict_admits_missing accepted
  | true => exact accepted

theorem certified_strict {C : Configuration RGAM}
    (exec : CertifiedExecution RGAM generation C) :
    ProjectedSpecificationRALinearizable RGAM emptyPolicy project strictSpec C := by
  intro r v s E _ hver q
  exact versions_of_execution true exec v s E hver q

theorem certified_missingNoop {C : Configuration RGAM}
    (exec : CertifiedExecution RGAM generation C) :
    ProjectedSpecificationRALinearizable RGAM emptyPolicy project missingNoopSpec C := by
  intro r v s E _ hver q
  exact versions_of_execution false exec v s E hver q

theorem certifiedStrictRA (C : Configuration RGAM) (reach : MintCertifiedReach RGAM generation C) :
    ProjectedSpecificationRALinearizable RGAM emptyPolicy project strictSpec C :=
  certified_strict (.ordinary reach)

theorem certifiedStrictRAV (C : Configuration RGAM)
    (reach : MintCertifiedReachV RGAM (canonicalVirtualMergeBase RGAM) generation C) :
    ProjectedSpecificationRALinearizable RGAM emptyPolicy project strictSpec C :=
  certified_strict (.virtual reach)


theorem certifiedMissingNoopRA (C : Configuration RGAM)
    (reach : MintCertifiedReach RGAM generation C) :
    ProjectedSpecificationRALinearizable RGAM emptyPolicy project missingNoopSpec C :=
  certified_missingNoop (.ordinary reach)

theorem certifiedMissingNoopRAV (C : Configuration RGAM)
    (reach : MintCertifiedReachV RGAM (canonicalVirtualMergeBase RGAM) generation C) :
    ProjectedSpecificationRALinearizable RGAM emptyPolicy project missingNoopSpec C :=
  certified_missingNoop (.virtual reach)


theorem certifiedStrictExecutions (trace : List (Label RGAM × Configuration RGAM))
    (execution : (certifiedTS RGAM generation).Execution (initConfig RGAM) trace) :
    ProjectedSpecificationExecution RGAM emptyPolicy project strictSpec (initConfig RGAM) trace :=
  projected_certified_executions certifiedStrictRA trace execution

theorem certifiedStrictExecutionsV (trace : List (Label RGAM × Configuration RGAM))
    (execution : (certifiedTSV RGAM generation).Execution (initConfig RGAM) trace) :
    ProjectedSpecificationExecution RGAM emptyPolicy project strictSpec (initConfig RGAM) trace :=
  projected_certified_executionsV certifiedStrictRAV trace execution

/-- PASS: explicit IDs determine ordinary list contents, including physical deletion. -/
theorem two_insertions_admitted : strictSpec.admits
    [.update (.addAfter 1 0), .update (.addAfter 2 1), .query () [1, 2]] := by
  refine ⟨(([1, 2], {1, 2}) : List ℕ × Finset ℕ), .cons (m := ([1], {1})) ?_ (.cons (m := ([1, 2], {1, 2})) ?_ (.cons ?_ (.nil _)))⟩
  · exact ⟨by simp [machine], Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨by simp, Or.inr (Or.inr (by simp)), by
            apply Prod.ext
            · rfl
            · decide⟩
  · exact ⟨rfl, rfl⟩

namespace ReadSide

/-- FAIL: sibling reversal is not an alternative answer to the same identified labels. -/
theorem two_insertions_not_reversed : ¬ strictSpec.admits
    [.update (.addAfter 1 0), .update (.addAfter 2 1), .query () [2, 1]] := by
  rintro ⟨t, h⟩
  cases h with
  | cons h1 rest =>
      obtain ⟨_, _, rfl⟩ := h1
      cases rest with
      | cons h2 rest =>
          obtain ⟨_, _, rfl⟩ := h2
          cases rest with
          | cons hq _ =>
              have eq : ([2, 1] : List ℕ) = [1, 2] := hq.2
              cases eq


end ReadSide

theorem missing_anchor_noop_admitted : missingNoopSpec.admits
    [.update (.addAfter 2 1), .query () []] := by
  refine ⟨(([], {2}) : List ℕ × Finset ℕ), .cons (m := ([], {2})) ?_ (.cons ⟨rfl, rfl⟩ (.nil _))⟩
  exact ⟨by simp [machine], Or.inl rfl, rfl⟩

namespace ReadSide

theorem missing_anchor_strict_rejected : ¬ strictSpec.admits
    [.update (.addAfter 2 1), .query () []] := by
  rintro ⟨t, h⟩
  cases h with
  | cons h _ => simpa [machine] using h.2.1


end ReadSide

theorem delete_admitted : strictSpec.admits
    [.update (.addAfter 1 0), .update (.remove 1), .query () []] := by
  refine ⟨(([], {1}) : List ℕ × Finset ℕ), .cons (m := ([1], {1})) ?_ (.cons (m := ([], {1})) (by simp [machine]) (.cons ⟨rfl, rfl⟩ (.nil _)))⟩
  exact ⟨by simp [machine], Or.inr (Or.inl rfl), rfl⟩

namespace ReadSide

theorem delete_not_noop : ¬ strictSpec.admits
    [.update (.addAfter 1 0), .update (.remove 1), .query () [1]] := by
  rintro ⟨t, h⟩
  cases h with
  | cons ha rest =>
      obtain ⟨_, _, rfl⟩ := ha
      cases rest with
      | cons hd rest =>
          change _ = _ at hd
          subst hd
          cases rest with
          | cons hq _ =>
              have eq : ([1] : List ℕ) = [] := hq.2
              cases eq


end ReadSide

theorem registry_blocks_reuse : ¬ (machine true).transition
    (([], {1}) : List ℕ × Finset ℕ) (.update (.addAfter 1 0)) ([1], {1}) := by
  intro h
  exact h.1 (by simp)

namespace ReadSide

/-- The stronger result is substantive: even the explicit-ID language has an
independent add/delete conflict although RGAM's concrete updates all commute. -/
theorem strict_add_delete_not_commute :
    ¬ strictSpec.Commutes (.addAfter 1 0) (.remove 1) := by
  intro h
  have accepted : strictSpec.admits
      [.update (.remove 1), .update (.addAfter 1 0), .query () [1]] := by
    refine ⟨(([1], {1}) : List ℕ × Finset ℕ),
      .cons (m := ([], ∅)) rfl (.cons (m := ([1], {1})) ?_
        (.cons ⟨rfl, rfl⟩ (.nil _)))⟩
    exact ⟨by simp, Or.inr (Or.inl rfl), rfl⟩
  exact ReadSide.delete_not_noop ((h [] [.query () [1]]).mpr accepted)


end ReadSide

/-- The projection genuinely exposes insertion identity: it cannot be
recovered from the old anchor-only application operation. -/
theorem projection_does_not_factor :
    ¬ ∃ f : RGAOp → Update, ∀ e : Op RGAOp, f e.op = project e := by
  rintro ⟨f, hf⟩
  have h1 := hf (1, 0, .addAfter 0)
  have h2 := hf (2, 0, .addAfter 0)
  have eq : Update.addAfter 1 0 = .addAfter 2 0 := h1.symm.trans h2
  cases eq

/-- The unchanged issuer accepts a nontrivial local prefix: a root insertion
and its child are applicable. Its guard rejects insertion at a deleted anchor. -/
theorem honest_prefix_control :
    applicable (1, 0, .addAfter 0) RGAM.init ∧
    applicable (2, 0, .addAfter 1)
      (applySeq RGAM.toUpdateSig RGAM.init [(1, 0, .addAfter 0)]) ∧
    ¬ applicable (3, 0, .addAfter 1)
      (applySeq RGAM.toUpdateSig RGAM.init [(1, 0, .addAfter 0), (2, 0, .remove 1)]) := by
  simp [applicable, RGAM, applySeq, rgaUpdate]

/-- Paired semantic controls: explicit IDs fix the visible answer, strictness
rejects missing anchors, and deletion removes data without freeing its ID. -/
example : strictSpec.admits
      [.update (.addAfter 1 0), .update (.addAfter 2 1), .query () [1, 2]] ∧
    ¬ strictSpec.admits
      [.update (.addAfter 1 0), .update (.addAfter 2 1), .query () [2, 1]] :=
  ⟨two_insertions_admitted, ReadSide.two_insertions_not_reversed⟩

example : missingNoopSpec.admits [.update (.addAfter 2 1), .query () []] ∧
    ¬ strictSpec.admits [.update (.addAfter 2 1), .query () []] :=
  ⟨missing_anchor_noop_admitted, ReadSide.missing_anchor_strict_rejected⟩

example : strictSpec.admits [.update (.addAfter 1 0), .update (.remove 1), .query () []] ∧
    ¬ strictSpec.admits [.update (.addAfter 1 0), .update (.remove 1), .query () [1]] ∧
    ¬ (machine true).transition (([], {1}) : List ℕ × Finset ℕ)
      (.update (.addAfter 1 0)) ([1], {1}) :=
  ⟨delete_admitted, ReadSide.delete_not_noop, registry_blocks_reuse⟩

#print axioms certifiedStrictRA
#print axioms certifiedStrictRAV
#print axioms certifiedMissingNoopRA
#print axioms certifiedMissingNoopRAV
#print axioms certifiedStrictExecutions
#print axioms certifiedStrictExecutionsV
end Sal.MRDTs.Paper1.RGA.Identified
