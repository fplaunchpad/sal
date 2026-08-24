import Sal.MRDTs.Instances.RGA
import Sal.MRDTs.Metatheory.Safety

/-!
# Plain RGA sequential specification

The independent state is an ordinary list of identifiers. It contains no
timestamps, insertion edges, or tombstones. Insertion after a missing anchor
is an explicit no-op; generation-certified histories supply fresh identifiers.
Deletion physically removes the identifier and is idempotent.
-/

namespace Sal.MRDTs.Instances.RGA

open Sal.MRDTs.Foundation

def listStep (xs : List ℕ) (e : Op RGAOp) : List ℕ :=
  match e.2.2 with
  | .addAfter anchor id => insertAfter anchor id xs
  | .remove id => xs.filter (· ≠ id)

/-- Legal RGA histories are stated only over abstract events.  Inserted IDs
match their Lamport timestamps, timestamps are unique, and every referenced
anchor or deletion target was introduced earlier in the same history.
Repeated deletion remains legal. -/
def listLegal (ops : List (Op RGAOp)) : Prop :=
  (∀ a ∈ ops, ∀ b ∈ ops, a.1 = b.1 → a = b) ∧
  ∀ pre e post, ops = pre ++ e :: post →
    match e.2.2 with
    | .addAfter anchor id =>
        id = e.1 ∧ (anchor = 0 ∨
          ∃ ts replica parent,
            (ts, replica, .addAfter parent anchor) ∈ pre)
    | .remove id =>
        ∃ ts replica anchor,
          (ts, replica, .addAfter anchor id) ∈ pre

def listSpec : SequentialSpec RGAM where
  State := List ℕ
  init := []
  step := listStep
  Legal := listLegal
  query := fun xs _ => xs

def isInsert (e : Op RGAOp) : Bool :=
  match e.2.2 with
  | .addAfter _ _ => true
  | .remove _ => false

/-- Witness order: insertions precede deletions; insertions are ordered by
Lamport timestamp; deletion order is immaterial. -/
def witnessLEBool (a b : Op RGAOp) : Bool :=
  match a.2.2, b.2.2 with
  | .addAfter _ _, .addAfter _ _ => decide (a.1 ≤ b.1)
  | .addAfter _ _, .remove _ => true
  | .remove _, .addAfter _ _ => false
  | .remove _, .remove _ => true

/-- Candidate global witness selected only from the version's actual events. -/
def canonical (ops : List (Op RGAOp)) : List (Op RGAOp) :=
  ops.mergeSort witnessLEBool

/-- The grow-only implementation contains an insertion record exactly when
the history contains the corresponding insertion event. -/
theorem add_true_iff : ∀ (ops : List (Op RGAOp)) (ts anchor id : ℕ),
    (applySeq RGAM.toCRDTSig RGAM.init ops).1 (ts, anchor, id) = true ↔
      ∃ replica, (ts, replica, .addAfter anchor id) ∈ ops := by
  intro ops
  induction ops using List.reverseRecOn with
  | nil => simp [applySeq, RGAM]
  | append_singleton ops e ih =>
      rcases e with ⟨ets, replica, op⟩
      cases op with
      | addAfter eanchor eid =>
          intro ts anchor id
          rw [applySeq_append_single]
          change
            ((applySeq RGAM.toCRDTSig RGAM.init ops).1 (ts, anchor, id) ||
              decide ((ts, anchor, id) = (ets, eanchor, eid))) = true ↔ _
          rw [Bool.or_eq_true, decide_eq_true_eq]
          rw [ih]
          constructor
          · rintro (⟨r, hr⟩ | h)
            · exact ⟨r, List.mem_append_left _ hr⟩
            · obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨replica, by simp⟩
          · rintro ⟨r, hr⟩
            rw [List.mem_append] at hr
            rcases hr with hr | hr
            · exact Or.inl ⟨r, hr⟩
            · simp only [List.mem_singleton] at hr
              cases hr
              exact Or.inr rfl
      | remove eid =>
          intro ts anchor id
          rw [applySeq_append_single]
          simpa [rgaUpdate] using ih ts anchor id

/-- The grow-only graveyard contains an identifier exactly when the history
contains a deletion of that identifier. -/
theorem grave_true_iff : ∀ (ops : List (Op RGAOp)) (id : ℕ),
    (applySeq RGAM.toCRDTSig RGAM.init ops).2 id = true ↔
      ∃ ts replica, (ts, replica, .remove id) ∈ ops := by
  intro ops
  induction ops using List.reverseRecOn with
  | nil => simp [applySeq, RGAM]
  | append_singleton ops e ih =>
      rcases e with ⟨ets, replica, op⟩
      cases op with
      | addAfter anchor eid =>
          intro id
          rw [applySeq_append_single]
          simpa [rgaUpdate] using ih id
      | remove eid =>
          intro id
          rw [applySeq_append_single]
          change
            ((applySeq RGAM.toCRDTSig RGAM.init ops).2 id ||
              decide (id = eid)) = true ↔ _
          rw [Bool.or_eq_true, decide_eq_true_eq]
          rw [ih]
          constructor
          · rintro (⟨ts, r, hr⟩ | h)
            · exact ⟨ts, r, List.mem_append_left _ hr⟩
            · subst id
              exact ⟨ets, replica, by simp⟩
          · rintro ⟨ts, r, hr⟩
            rw [List.mem_append] at hr
            rcases hr with hr | hr
            · exact Or.inl ⟨ts, r, hr⟩
            · simp only [List.mem_singleton] at hr
              cases hr
              exact Or.inr rfl

theorem partition_perm (p : Op RGAOp → Bool) : ∀ ops : List (Op RGAOp),
    ops.Perm (ops.filter p ++ ops.filter (!p ·)) := by
  intro ops
  induction ops with
  | nil => simp
  | cons e rest ih =>
      cases h : p e
      · simpa [h] using List.perm_cons_append_cons e ih
      · simpa [h] using ih.cons e

theorem canonical_perm (ops : List (Op RGAOp)) :
    ops.Perm (canonical ops) := by
  exact (List.mergeSort_perm ops witnessLEBool).symm

theorem canonical_listPermOf {ops : List (Op RGAOp)}
    {E : Set (Op RGAOp)} (h : listPermOf ops E) :
    listPermOf (canonical ops) E := by
  have hp := canonical_perm ops
  exact ⟨hp.nodup h.1, fun e => (hp.mem_iff (a := e)).symm.trans (h.2 e)⟩

theorem canonical_fold (ops : List (Op RGAOp)) :
    applySeq RGAM.toCRDTSig RGAM.init (canonical ops) =
      applySeq RGAM.toCRDTSig RGAM.init ops :=
  applySeq_perm_of_all_comm RGAM_all_comm (canonical_perm ops).symm RGAM.init

def insertBlock (ops : List (Op RGAOp)) : List (Op RGAOp) :=
  (ops.filter isInsert).mergeSort (fun a b => a.1 ≤ b.1)

def removeBlock (ops : List (Op RGAOp)) : List (Op RGAOp) :=
  ops.filter (!isInsert ·)

theorem insertBlock_sorted (ops : List (Op RGAOp)) :
    (insertBlock ops).Pairwise (fun a b => a.1 ≤ b.1) := by
  unfold insertBlock
  simpa using List.pairwise_mergeSort
    (le := fun a b : Op RGAOp => a.1 ≤ b.1)
    (by
      intro a b c hab hbc
      exact decide_eq_true (Nat.le_trans (of_decide_eq_true hab)
        (of_decide_eq_true hbc)))
    (by
      intro a b
      by_cases h : a.1 ≤ b.1
      · simp [h]
      · simp [h, Nat.le_of_lt (Nat.lt_of_not_ge h)])
    (ops.filter isInsert)

theorem mem_insertBlock {ops : List (Op RGAOp)} {e : Op RGAOp} :
    e ∈ insertBlock ops ↔ e ∈ ops ∧ isInsert e = true := by
  unfold insertBlock
  rw [List.Perm.mem_iff (List.mergeSort_perm _ _)]
  simp

theorem mem_removeBlock {ops : List (Op RGAOp)} {e : Op RGAOp} :
    e ∈ removeBlock ops ↔ e ∈ ops ∧ isInsert e = false := by
  simp [removeBlock]

theorem mem_prefix_of_time_lt {whole pre suffix : List (Op RGAOp)}
    {e parent : Op RGAOp}
    (hsorted : whole.Pairwise (fun a b => a.1 ≤ b.1))
    (hsplit : whole = pre ++ e :: suffix)
    (hparent : parent ∈ whole) (hlt : parent.1 < e.1) :
    parent ∈ pre := by
  subst whole
  rw [List.mem_append] at hparent
  rcases hparent with hpre | hrest
  · exact hpre
  · simp only [List.mem_cons] at hrest
    rcases hrest with rfl | hsuf
    · exact (Nat.lt_irrefl _ hlt).elim
    · have htail := (List.pairwise_append.mp hsorted).2.1
      have hele := (List.pairwise_cons.mp htail).1 parent hsuf
      exact (Nat.not_le_of_lt hlt hele).elim

/-- Propositional view of the executable witness comparator. -/
def WitnessLE (a b : Op RGAOp) : Prop := witnessLEBool a b = true

theorem canonical_ordered (ops : List (Op RGAOp)) :
    (canonical ops).Pairwise WitnessLE := by
  unfold canonical WitnessLE
  apply List.pairwise_mergeSort
  · rintro ⟨ta, ra, oa⟩ ⟨tb, rb, ob⟩ ⟨tc, rc, oc⟩ hab hbc
    cases oa <;> cases ob <;> cases oc <;>
      simp [witnessLEBool] at *
    exact Nat.le_trans hab hbc
  · rintro ⟨ta, ra, oa⟩ ⟨tb, rb, ob⟩
    cases oa <;> cases ob <;>
      simp [witnessLEBool]
    exact Nat.le_total ta tb

theorem creator_mem_prefix {whole pre suffix : List (Op RGAOp)}
    {ts replica id creatorTs creatorReplica creatorAnchor : ℕ}
    (hordered : whole.Pairwise WitnessLE)
    (hsplit : whole = pre ++ (ts, replica, .remove id) :: suffix)
    (hcreator : (creatorTs, creatorReplica,
      .addAfter creatorAnchor id) ∈ whole) :
    (creatorTs, creatorReplica, .addAfter creatorAnchor id) ∈ pre := by
  subst whole
  rw [List.mem_append] at hcreator
  rcases hcreator with hpre | hrest
  · exact hpre
  · simp only [List.mem_cons] at hrest
    rcases hrest with heq | hsuf
    · cases heq
    · have htail := (List.pairwise_append.mp hordered).2.1
      have hrel := (List.pairwise_cons.mp htail).1 _ hsuf
      simp [WitnessLE, witnessLEBool] at hrel

theorem anchor_mem_prefix {whole pre suffix : List (Op RGAOp)}
    {ts replica anchor id anchorTs anchorReplica anchorParent : ℕ}
    (hordered : whole.Pairwise WitnessLE)
    (hsplit : whole = pre ++ (ts, replica, .addAfter anchor id) :: suffix)
    (hanchor : (anchorTs, anchorReplica,
      .addAfter anchorParent anchor) ∈ whole)
    (hlt : anchorTs < ts) :
    (anchorTs, anchorReplica, .addAfter anchorParent anchor) ∈ pre := by
  subst whole
  rw [List.mem_append] at hanchor
  rcases hanchor with hpre | hrest
  · exact hpre
  · simp only [List.mem_cons] at hrest
    rcases hrest with heq | hsuf
    · have htime := congrArg Op.time heq
      change anchorTs = ts at htime
      omega
    · have htail := (List.pairwise_append.mp hordered).2.1
      have hrel := (List.pairwise_cons.mp htail).1 _ hsuf
      simp only [WitnessLE, witnessLEBool, decide_eq_true_eq] at hrel
      exact (Nat.not_le_of_lt hlt hrel).elim

theorem lo_false (C : Configuration RGAM) (a b : Op RGAOp) :
    ¬ Sal.MRDTs.Foundation.lo C.core a b := by
  rintro (⟨_, hnoncomm⟩ | ⟨_, _, hrc, _⟩)
  · exact hnoncomm (RGAM_all_comm a b)
  · rw [RGAM_rc_either] at hrc
    exact RcRes.noConfusion hrc

theorem respects_lo (C : Configuration RGAM) :
    ∀ ops : List (Op RGAOp),
      respects ops (Sal.MRDTs.Foundation.lo C.core) := by
  intro ops
  induction ops with
  | nil => exact List.Pairwise.nil
  | cons e rest ih =>
      exact List.pairwise_cons.mpr ⟨fun b _ => lo_false C b e, ih⟩

/-- Static facts about one causally closed RGA version.  They are the small
interface between the operational semantics and the ordinary-list proof. -/
structure VersionWellFormed (E : Set (Op RGAOp)) : Prop where
  time_unique : ∀ {a b}, a ∈ E → b ∈ E → a.1 = b.1 → a = b
  add : ∀ {ts replica anchor id},
    (ts, replica, .addAfter anchor id) ∈ E →
      id = ts ∧ (anchor = 0 ∨
        ∃ parentTs parentReplica parentAnchor,
          (parentTs, parentReplica, .addAfter parentAnchor anchor) ∈ E ∧
          parentTs < ts)
  remove : ∀ {ts replica id},
    (ts, replica, .remove id) ∈ E →
      ∃ parentTs parentReplica parentAnchor,
        (parentTs, parentReplica, .addAfter parentAnchor id) ∈ E

/-- Generation honesty plus the framework's causal closure invariant imply
the static facts used by the sequential proof. -/
theorem versionWellFormed_of_execution {C : Configuration RGAM}
    (exec : CertifiedExecution RGAM generation C)
    {v : Version} {s : RGAM.State} {E : Set (Op RGAOp)}
    (hver : C.ver v = some (s, E)) : VersionWellFormed E := by
  have hgood : GoodConfig3 C :=
    exec.goodConfig (fun _ _ => join _)
  have hsub := hgood.ver_events_sub v s E hver
  have hclosed := hgood.ver_causal v s E hver
  have hmint : MintHonest RGAM applicable C := exec.mintHonest
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb htime
    exact C.core.ts_unique (hsub a ha) (hsub b hb) htime
  · intro ts replica anchor id he
    obtain ⟨past, hpast, _, hguard⟩ := hmint _ (hsub _ he)
    rcases hguard with ⟨hid, hanchor, _, _, _⟩
    refine ⟨hid, ?_⟩
    rcases hanchor with rfl | ⟨parentTs, parentAnchor, hlt, hpresent⟩
    · exact Or.inl rfl
    · rw [add_true_iff] at hpresent
      obtain ⟨parentReplica, hmem⟩ := hpresent
      have hpastSet := (hpast.2 _).mp hmem
      exact Or.inr ⟨parentTs, parentReplica, parentAnchor,
        hclosed _ _ hpastSet.2 he, hlt⟩
  · intro ts replica id he
    obtain ⟨past, hpast, _, hguard⟩ := hmint _ (hsub _ he)
    obtain ⟨⟨parentTs, parentAnchor, hpresent⟩, _⟩ := hguard
    rw [add_true_iff] at hpresent
    obtain ⟨parentReplica, hmem⟩ := hpresent
    have hpastSet := (hpast.2 _).mp hmem
    exact ⟨parentTs, parentReplica, parentAnchor,
      hclosed _ _ hpastSet.2 he⟩

theorem canonical_legal {ops : List (Op RGAOp)}
    {E : Set (Op RGAOp)} (hperm : listPermOf ops E)
    (hwf : VersionWellFormed E) : listSpec.Legal (canonical ops) := by
  unfold listSpec listLegal
  constructor
  · intro a ha b hb htime
    have hcan := canonical_listPermOf hperm
    exact hwf.time_unique ((hcan.2 a).mp ha) ((hcan.2 b).mp hb) htime
  · intro pre e post hsplit
    have hcan := canonical_listPermOf hperm
    have heList : e ∈ canonical ops := by rw [hsplit]; simp
    have heE : e ∈ E := (hcan.2 e).mp heList
    obtain ⟨ts, replica, op⟩ := e
    cases op with
    | addAfter anchor id =>
      obtain ⟨hid, hanchor⟩ := hwf.add heE
      refine ⟨hid, ?_⟩
      rcases hanchor with rfl | ⟨anchorTs, anchorReplica, anchorParent,
          hanchorE, hlt⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨anchorTs, anchorReplica, anchorParent,
          anchor_mem_prefix (canonical_ordered ops) hsplit
            ((hcan.2 _).mpr hanchorE) hlt⟩
    | remove id =>
      obtain ⟨creatorTs, creatorReplica, creatorAnchor, hcreatorE⟩ :=
        hwf.remove heE
      exact ⟨creatorTs, creatorReplica, creatorAnchor,
        creator_mem_prefix (canonical_ordered ops) hsplit
          ((hcan.2 _).mpr hcreatorE)⟩

/-! The following implementation-state lemma is retained as an internal proof
aid for correspondence checks.  It is not part of the public specification. -/
theorem canonical_prefix_allocated {ops : List (Op RGAOp)}
    {E : Set (Op RGAOp)} (hperm : listPermOf ops E)
    (hwf : VersionWellFormed E) :
    ∀ (pre : List (Op RGAOp)) (e : Op RGAOp) (post : List (Op RGAOp)),
      canonical ops = pre ++ e :: post →
      match e.2.2 with
      | .addAfter anchor _ =>
          anchor = 0 ∨ ∃ ts parent,
            (applySeq RGAM.toCRDTSig RGAM.init pre).1
              (ts, parent, anchor) = true
      | .remove id =>
          ∃ ts anchor,
            (applySeq RGAM.toCRDTSig RGAM.init pre).1
              (ts, anchor, id) = true := by
  intro pre e post hsplit
  have hcan := canonical_listPermOf hperm
  have heList : e ∈ canonical ops := by rw [hsplit]; simp
  have heE : e ∈ E := (hcan.2 e).mp heList
  obtain ⟨ts, replica, op⟩ := e
  cases op with
  | addAfter anchor id =>
      obtain ⟨_, hanchor⟩ := hwf.add heE
      rcases hanchor with rfl | ⟨anchorTs, anchorReplica, anchorParent,
          hanchorE, hlt⟩
      · exact Or.inl rfl
      · apply Or.inr
        refine ⟨anchorTs, anchorParent, ?_⟩
        rw [add_true_iff]
        refine ⟨anchorReplica, anchor_mem_prefix (canonical_ordered ops)
          hsplit ?_ hlt⟩
        exact (hcan.2 _).mpr hanchorE
  | remove id =>
      obtain ⟨creatorTs, creatorReplica, creatorAnchor, hcreatorE⟩ :=
        hwf.remove heE
      refine ⟨creatorTs, creatorAnchor, ?_⟩
      rw [add_true_iff]
      refine ⟨creatorReplica, creator_mem_prefix (canonical_ordered ops)
        hsplit ?_⟩
      exact (hcan.2 _).mpr hcreatorE

def insertEntries : List (Op RGAOp) → List RGAEntry
  | [] => []
  | (ts, _, .addAfter anchor id) :: rest =>
      (ts, anchor, id) :: insertEntries rest
  | (_, _, .remove _) :: rest => insertEntries rest

def removedIds : List (Op RGAOp) → List ℕ
  | [] => []
  | (_, _, .addAfter _ _) :: rest => removedIds rest
  | (_, _, .remove id) :: rest => id :: removedIds rest

@[simp] theorem insertEntries_append (xs ys : List (Op RGAOp)) :
    insertEntries (xs ++ ys) = insertEntries xs ++ insertEntries ys := by
  induction xs with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨ts, replica, op⟩ := e
      cases op <;> simp [insertEntries, ih]

@[simp] theorem removedIds_append (xs ys : List (Op RGAOp)) :
    removedIds (xs ++ ys) = removedIds xs ++ removedIds ys := by
  induction xs with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨ts, replica, op⟩ := e
      cases op <;> simp [removedIds, ih]

theorem spec_run_sets (ops : List (Op RGAOp)) :
    (spec.run ops).adds = (insertEntries ops).toFinset ∧
    (spec.run ops).grave = (removedIds ops).toFinset := by
  induction ops using List.reverseRecOn with
  | nil => simp [SequentialMachine.run, spec, insertEntries, removedIds]
  | append_singleton ops e ih =>
      rw [SequentialMachine.run_append_single]
      obtain ⟨ts, replica, op⟩ := e
      cases op with
      | addAfter anchor id =>
          constructor
          · change insert (ts, anchor, id) (spec.run ops).adds = _
            rw [ih.1]
            simp [insertEntries]
          · change (spec.run ops).grave = _
            simpa [removedIds] using ih.2
      | remove id =>
          constructor
          · change (spec.run ops).adds = _
            simpa [insertEntries] using ih.1
          · change insert id (spec.run ops).grave = _
            rw [ih.2]
            simp [removedIds]

theorem mem_insertEntries : ∀ {ops : List (Op RGAOp)} {ts anchor id : ℕ},
    (ts, anchor, id) ∈ insertEntries ops ↔
      ∃ replica, (ts, replica, .addAfter anchor id) ∈ ops := by
  intro ops
  induction ops with
  | nil => simp [insertEntries]
  | cons e rest ih =>
      obtain ⟨ets, replica, op⟩ := e
      cases op with
      | addAfter eanchor eid =>
          intro ts anchor id
          simp only [insertEntries, List.mem_cons, ih]
          constructor
          · rintro (heq | ⟨r, hr⟩)
            · obtain ⟨rfl, rfl, rfl⟩ := heq
              exact ⟨replica, by simp⟩
            · exact ⟨r, by simp [hr]⟩
          · rintro ⟨r, hr⟩
            rcases hr with heq | hr
            · cases heq
              exact Or.inl rfl
            · exact Or.inr ⟨r, hr⟩
      | remove eid =>
          intro ts anchor id
          simpa [insertEntries] using ih (ts := ts) (anchor := anchor) (id := id)

theorem insertEntries_sorted {ops : List (Op RGAOp)}
    (h : ops.Pairwise WitnessLE) :
    (insertEntries ops).Pairwise (fun a b => a.1 ≤ b.1) := by
  induction ops with
  | nil => exact List.Pairwise.nil
  | cons e rest ih =>
      have hp := List.pairwise_cons.mp h
      obtain ⟨ts, replica, op⟩ := e
      cases op with
      | remove id => exact ih hp.2
      | addAfter anchor id =>
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih hp.2⟩
          intro entry hentry
          obtain ⟨otherReplica, hother⟩ := mem_insertEntries.mp hentry
          have hrel := hp.1 (entry.1, otherReplica,
            .addAfter entry.2.1 entry.2.2) hother
          simpa [WitnessLE, witnessLEBool] using hrel

theorem insertEntries_time_injective {ops : List (Op RGAOp)}
    {E : Set (Op RGAOp)} (hperm : listPermOf ops E)
    (hwf : VersionWellFormed E) :
    ∀ {a b}, a ∈ insertEntries ops → b ∈ insertEntries ops →
      a.1 = b.1 → a = b := by
  intro a b ha hb htime
  obtain ⟨ra, hea⟩ := mem_insertEntries.mp ha
  obtain ⟨rb, heb⟩ := mem_insertEntries.mp hb
  have hop := hwf.time_unique ((hperm.2 _).mp hea) ((hperm.2 _).mp heb) htime
  have := congrArg (fun e : Op RGAOp => match e.2.2 with
    | .addAfter anchor id => (e.1, anchor, id)
    | .remove id => (e.1, 0, id)) hop
  simpa using this

theorem insertEntries_nodup {ops : List (Op RGAOp)}
    {E : Set (Op RGAOp)} (hperm : listPermOf ops E)
    (hwf : VersionWellFormed E) : (insertEntries ops).Nodup := by
  have aux : ∀ (xs : List (Op RGAOp)), xs.Nodup →
      (∀ e ∈ xs, e ∈ E) → (insertEntries xs).Nodup := by
    intro xs hnd hmem
    induction xs with
    | nil => exact List.nodup_nil
    | cons e rest ih =>
        have hndParts := List.nodup_cons.mp hnd
        obtain ⟨ts, replica, op⟩ := e
        cases op with
        | remove id =>
            exact ih hndParts.2 (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
        | addAfter anchor id =>
            apply List.nodup_cons.mpr
            refine ⟨?_, ih hndParts.2
              (fun x hx => hmem x (List.mem_cons_of_mem _ hx))⟩
            intro hentry
            obtain ⟨otherReplica, hother⟩ := mem_insertEntries.mp hentry
            have heq := hwf.time_unique
              (hmem _ List.mem_cons_self)
              (hmem _ (List.mem_cons_of_mem _ hother)) rfl
            exact hndParts.1 (heq ▸ hother)
  exact aux ops hperm.1 (fun e he => (hperm.2 e).mp he)

theorem canonical_entries_are_finset_order
    {ops : List (Op RGAOp)} {E : Set (Op RGAOp)}
    (hperm : listPermOf ops E) (hwf : VersionWellFormed E) :
    ((insertEntries (canonical ops)).toFinset.toList.mergeSort
      (fun a b => a.1 ≤ b.1)) = insertEntries (canonical ops) := by
  let entries := insertEntries (canonical ops)
  have hcan := canonical_listPermOf hperm
  have hnd : entries.Nodup := insertEntries_nodup hcan hwf
  have hright : entries.Pairwise (fun a b => a.1 ≤ b.1) :=
    insertEntries_sorted (canonical_ordered ops)
  have hleft : (entries.toFinset.toList.mergeSort
      (fun a b => a.1 ≤ b.1)).Pairwise (fun a b => a.1 ≤ b.1) := by
    simpa using List.pairwise_mergeSort
      (le := fun a b : RGAEntry => a.1 ≤ b.1)
      (by
        intro a b c hab hbc
        exact decide_eq_true (Nat.le_trans (of_decide_eq_true hab)
          (of_decide_eq_true hbc)))
      (by
        intro a b
        by_cases h : a.1 ≤ b.1
        · simp [h]
        · simp [h, Nat.le_of_lt (Nat.lt_of_not_ge h)])
      entries.toFinset.toList
  apply List.eq_of_perm_of_sorted
  · intro a b ha hb hab hba
    apply insertEntries_time_injective hcan hwf
    · have hp := List.mergeSort_perm entries.toFinset.toList
          (fun a b : RGAEntry => a.1 ≤ b.1)
      have : a ∈ entries.toFinset.toList := (hp.mem_iff).mp ha
      simpa using this
    · exact hb
    · exact Nat.le_antisymm hab hba
  · exact hleft
  · exact hright
  · exact (List.mergeSort_perm entries.toFinset.toList
      (fun a b : RGAEntry => a.1 ≤ b.1)).trans
        (List.toFinset_toList hnd)

def render (ops : List (Op RGAOp)) : List ℕ :=
  ((insertEntries ops).foldl
    (fun xs entry => insertAfter entry.2.1 entry.2.2 xs) []).filter
      (fun id => id ∉ (removedIds ops).toFinset)

theorem removedIds_eq_nil_of_all_add {ops : List (Op RGAOp)}
    (h : ∀ e ∈ ops, isInsert e = true) : removedIds ops = [] := by
  induction ops with
  | nil => rfl
  | cons e rest ih =>
      have he := h e List.mem_cons_self
      obtain ⟨ts, replica, op⟩ := e
      cases op with
      | addAfter anchor id =>
          simp only [removedIds]
          exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      | remove id => simp [isInsert] at he

theorem removedIds_eq_nil_of_before_add
    {ops : List (Op RGAOp)} {ts replica anchor id : ℕ}
    (h : (ops ++ [(ts, replica, RGAOp.addAfter anchor id)]).Pairwise WitnessLE) :
    removedIds ops = [] := by
  have hcross := (List.pairwise_append.mp h).2.2
  apply removedIds_eq_nil_of_all_add
  intro e he
  have hrel := hcross e he
    (ts, replica, RGAOp.addAfter anchor id) (by simp)
  obtain ⟨ets, ereplica, op⟩ := e
  cases op with
  | addAfter eanchor eid => rfl
  | remove eid => simp [WitnessLE, witnessLEBool] at hrel

theorem list_run_eq_render {ops : List (Op RGAOp)}
    (hordered : ops.Pairwise WitnessLE) : listSpec.run ops = render ops := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops e ih =>
      have hpre := (List.pairwise_append.mp hordered).1
      rw [SequentialSpec.run_append_single, ih hpre]
      obtain ⟨ts, replica, op⟩ := e
      cases op with
      | addAfter anchor id =>
          have hdead := removedIds_eq_nil_of_before_add hordered
          change insertAfter anchor id (render ops) = _
          simp [render, insertEntries, removedIds, hdead]
      | remove id =>
          change (render ops).filter (· ≠ id) = _
          simp only [render, insertEntries_append,
            removedIds_append, insertEntries, removedIds, List.foldl_append,
            List.foldl_nil]
          rw [List.filter_filter]
          apply List.filter_congr
          intro x hx
          simp

theorem sequence_run_canonical {ops : List (Op RGAOp)}
    {E : Set (Op RGAOp)} (hperm : listPermOf ops E)
    (hwf : VersionWellFormed E) :
    sequence (spec.run (canonical ops)) = render (canonical ops) := by
  have hsets := spec_run_sets (canonical ops)
  unfold sequence render
  rw [hsets.1, hsets.2, canonical_entries_are_finset_order hperm hwf]

theorem list_run_eq_sequence {ops : List (Op RGAOp)}
    {E : Set (Op RGAOp)} (hperm : listPermOf ops E)
    (hwf : VersionWellFormed E) :
    listSpec.run (canonical ops) = sequence (spec.run (canonical ops)) := by
  rw [list_run_eq_render (canonical_ordered ops),
    sequence_run_canonical hperm hwf]

def listRel (s : RGAM.State) (xs : List ℕ) : Prop := read s = xs

theorem canonical_refines_list {ops : List (Op RGAOp)}
    {E : Set (Op RGAOp)} (hperm : listPermOf ops E)
    (hwf : VersionWellFormed E) :
    listRel (applySeq RGAM.toCRDTSig RGAM.init (canonical ops))
      (listSpec.run (canonical ops)) := by
  unfold listRel
  rw [read_eq_sequence_of_stateRel (sequentialSound (canonical ops)),
    list_run_eq_sequence hperm hwf]

noncomputable def listLegalization : LegalizationCertificate RGAM generation
    (ArbitrationSpec.raw RGAM)
    listSpec listRel where
  sound C exec replay := by
    intro v s E hver
    obtain ⟨ops, hperm, _, hfold⟩ := replay v s E hver
    have hwf := versionWellFormed_of_execution exec hver
    have hstate : applySeq RGAM.toCRDTSig RGAM.init (canonical ops) = s :=
      (canonical_fold ops).trans hfold
    have href := canonical_refines_list hperm hwf
    have hrel : listRel s (listSpec.run (canonical ops)) := by
      rw [← hstate]
      exact href
    refine ⟨canonical ops, canonical_listPermOf hperm, respects_lo C _,
      canonical_legal hperm hwf, hrel, ?_⟩
    intro query
    cases query
    exact hrel

/-- Public tombstone-RGA package: internal convergence is joined to a legal
ordinary-list witness and exact query agreement. -/
noncomputable def verified : VerifiedMRDT RGAM where
  issuance := generation
  arbitration := ArbitrationSpec.raw RGAM
  convergence := convergence
  Spec := listSpec
  Rel := listRel
  legalization := listLegalization

theorem rga_spec_linearizable {C : Configuration RGAM}
    (h : MintCertifiedReach RGAM generation C) :
    IsSpecRALinearizable RGAM (ArbitrationSpec.raw RGAM)
      listSpec listRel C :=
  verified.converges h

theorem rga_spec_linearizableV {C : Configuration RGAM}
    (h : MintCertifiedReachV RGAM (canonicalVirtualLCA RGAM) generation C) :
    IsSpecRALinearizable RGAM (ArbitrationSpec.raw RGAM)
      listSpec listRel C :=
  verified.convergesV h

#print axioms rga_spec_linearizable
#print axioms rga_spec_linearizableV

namespace ListSpecSPOT

def parent : Op RGAOp := (1, 0, .addAfter 0 1)
def child : Op RGAOp := (4, 1, .addAfter 1 4)
def deleteParentA : Op RGAOp := (2, 1, .remove 1)
def deleteParentB : Op RGAOp := (3, 2, .remove 1)
def sibling : Op RGAOp := (5, 2, .addAfter 0 5)

/-- PASS: deletion removes the entry rather than retaining a tombstone. -/
example : listSpec.run [parent, deleteParentA] = [] := by rfl

/-- PASS: repeated deletion is an idempotent sequential operation. -/
example : listSpec.run [parent, deleteParentA, deleteParentB] = [] := by rfl

/-- PASS: inserting the child before the concurrent parent delete preserves
the child in the visible sequence. -/
example : listSpec.run [parent, child, deleteParentA] = [4] := by rfl

/-- FAIL control: replaying the parent delete first loses the insertion
anchor. The legalization theorem must select the former order. -/
example : listSpec.run [parent, deleteParentA, child] = [] := by rfl

/-- Timestamp-ascending root insertions produce the RGA sibling order because
each new root child is inserted at the front. -/
example : listSpec.run [parent, sibling] = [5, 1] := by rfl

end ListSpecSPOT

end Sal.MRDTs.Instances.RGA
