import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_M2

/-! # Shesha — honest branch evolution

The delivery contract and the invariants it buys. A branch evolves from
the LCA by honest steps: inserts carry globally fresh nonzero ids (Lamport
freshness: never an id of the current state nor of the LCA) and live
anchors; deletes target live nodes. Under `HReach`:

- `WF` is preserved (`hreach_WF`);
- L-nodes never end up under born parents (`hreach_LRowsOK`) — the
  branch-structure hypothesis of the M0/M2 lemmas, discharged;
- with cross-branch Lamport uniqueness (`ids A ∩ ids B ⊆ ids L`, the one
  irreducibly global contract), the full `ModelOK`, so every merge lemma
  applies at every honestly-reached merge (`merge_WF_honest`,
  `merge_ids_honest`, `merge_comm_honest`, `merge_extends_L_honest`).
-/

namespace Shesha

open List

/-- Honest applicability of one op. -/
def OpHonest (L s : St) : Op → Prop
  | .ins x a => x ∉ read s ∧ x ∉ read L ∧ x ≠ 0 ∧ (a = 0 ∨ a ∈ read s)
  | .del d => d ∈ read s

/-- Honest reachability of a branch from its LCA. -/
inductive HReach (L : St) : St → Prop
  | refl : HReach L L
  | step {t : St} {o : Op} : HReach L t → OpHonest L t o →
      HReach L (applyOp t o)

/-! ## WF preservation -/

theorem seqInsAt_count {x a c : Nat} (hcx : c ≠ x) (u : Nat) :
    (seqInsAt x a u).count c = if u == c then 1 else 0 := by
  rw [seqInsAt]
  by_cases hu : u = a
  · rw [if_pos hu, List.count_cons, List.count_cons, List.count_nil,
      if_neg (show ¬ ((x == c) = true) from by
        simp only [beq_iff_eq]
        exact fun e => hcx e.symm)]
    omega
  · rw [if_neg hu, List.count_cons, List.count_nil]
    omega

theorem seqInsAt_count_ne {x a c : Nat} (hcx : c ≠ x) :
    ∀ l : List Nat, (l.flatMap (seqInsAt x a)).count c = l.count c
  | [] => rfl
  | u :: l => by
      rw [List.flatMap_cons, List.count_append, seqInsAt_count hcx u,
        seqInsAt_count_ne hcx l, List.count_cons]
      omega

theorem seqInsAt_count_x' {x a : Nat} (u : Nat) (hux : u ≠ x) :
    (seqInsAt x a u).count x = if u == a then 1 else 0 := by
  rw [seqInsAt]
  by_cases hu : u = a
  · rw [if_pos hu, if_pos (by simp [hu]), List.count_cons, List.count_cons,
      List.count_nil, if_pos (show ((x == x) = true) by simp),
      if_neg (show ¬ ((u == x) = true) from by
        simp only [beq_iff_eq]
        exact hux)]
  · rw [if_neg hu, if_neg (by simp [hu]), List.count_cons, List.count_nil,
      if_neg (show ¬ ((u == x) = true) from by
        simp only [beq_iff_eq]
        exact hux)]

theorem seqInsAt_count_x {x a : Nat} :
    ∀ l : List Nat, x ∉ l →
      (l.flatMap (seqInsAt x a)).count x = l.count a
  | [], _ => rfl
  | u :: l, hx => by
      have hxl : x ∉ l := fun hm => hx (List.mem_cons_of_mem _ hm)
      have hux : u ≠ x := fun e => hx (by
        rw [← e]
        exact List.mem_cons_self ..)
      rw [List.flatMap_cons, List.count_append, seqInsAt_count_x' u hux,
        seqInsAt_count_x l hxl, List.count_cons]
      omega

theorem seqIns_nodup {l : List Nat} (hnd : l.Nodup) {x a : Nat}
    (hx : x ∉ l) : (seqIns l x a).Nodup := by
  rw [seqIns]
  by_cases ha : a = 0
  · rw [if_pos ha]
    exact List.nodup_cons.mpr ⟨hx, hnd⟩
  · rw [if_neg ha]
    refine nodup_of_count_le_one fun c => ?_
    by_cases hcx : c = x
    · rw [hcx, seqInsAt_count_x l hx]
      exact count_le_one_of_nodup hnd a
    · rw [seqInsAt_count_ne hcx l]
      exact count_le_one_of_nodup hnd c

theorem seqIns_mem {l : List Nat} {x a c : Nat}
    (h : c ∈ seqIns l x a) : c = x ∨ c ∈ l := by
  rw [seqIns] at h
  by_cases ha : a = 0
  · rw [if_pos ha] at h
    rcases List.mem_cons.mp h with he | h
    · exact Or.inl he
    · exact Or.inr h
  · rw [if_neg ha] at h
    rw [List.mem_flatMap] at h
    obtain ⟨u, hu, hc⟩ := h
    rw [seqInsAt] at hc
    by_cases hua : u = a
    · rw [if_pos hua] at hc
      rcases List.mem_cons.mp hc with he | hc
      · exact Or.inr (he ▸ hu)
      · rcases List.mem_singleton.mp hc with rfl
        exact Or.inl rfl
    · rw [if_neg hua] at hc
      rcases List.mem_singleton.mp hc with rfl
      exact Or.inr hu

/-- One honest step preserves well-formedness. -/
theorem step_WF {L t : St} {o : Op} (hwf : WF t) (ho : OpHonest L t o) :
    WF (applyOp t o) := by
  cases o with
  | ins x a =>
      obtain ⟨hx, -, hx0, ha⟩ := ho
      constructor
      · show (read (Shesha.insert t x a)).Nodup
        rw [read_insert]
        exact seqIns_nodup hwf.1 hx
      · show 0 ∉ read (Shesha.insert t x a)
        rw [read_insert]
        intro hc
        rcases seqIns_mem hc with he | hm
        · exact hx0 he.symm
        · exact hwf.2 hm
  | del d =>
      constructor
      · show (read (Shesha.delete t d)).Nodup
        rw [read_delete, seqDel]
        exact hwf.1.filter _
      · show 0 ∉ read (Shesha.delete t d)
        rw [read_delete, seqDel]
        intro hc
        exact hwf.2 (List.mem_filter.mp hc).1

theorem hreach_WF {L X : St} (hwfL : WF L) (h : HReach L X) : WF X := by
  induction h with
  | refl => exact hwfL
  | step _ ho ih => exact step_WF ih ho

/-! ## Row membership through the ops -/

mutual
  theorem insT_topId (x a : Nat) :
      ∀ t : Tree, topId (insT x a t) = topId t
    | .node i cs => by
        rw [insT]
        by_cases h : i = a
        · rw [if_pos h]
          rfl
        · rw [if_neg h]
          rfl
  theorem insF_topIds (x a : Nat) :
      ∀ F : List Tree, (insF x a F).map topId = F.map topId
    | [] => rfl
    | t :: ts => by
        rw [insF, List.map_cons, List.map_cons, insT_topId x a t,
          insF_topIds x a ts]
end

mutual
  theorem mem_rowT_insT {x a w q : Nat} :
      ∀ {t : Tree}, w ∈ rowT q (insT x a t) → w = x ∨ w ∈ rowT q t
    | .node i cs, h => by
        rw [insT] at h
        by_cases hia : i = a
        · rw [if_pos hia] at h
          rw [rowT] at h ⊢
          by_cases hiq : i = q
          · rw [if_pos hiq] at h ⊢
            rw [List.map_cons] at h
            rcases List.mem_cons.mp h with he | h
            · exact Or.inl he
            · rw [insF_topIds] at h
              exact Or.inr h
          · rw [if_neg hiq] at h ⊢
            rw [rowF, List.mem_append] at h
            rcases h with h | h
            · rw [rowT] at h
              by_cases hxq : x = q
              · rw [if_pos hxq] at h
                simp at h
              · rw [if_neg hxq, rowF] at h
                simp at h
            · exact mem_rowF_insF h
        · rw [if_neg hia] at h
          rw [rowT] at h ⊢
          by_cases hiq : i = q
          · rw [if_pos hiq] at h ⊢
            rw [insF_topIds] at h
            exact Or.inr h
          · rw [if_neg hiq] at h ⊢
            exact mem_rowF_insF h
  theorem mem_rowF_insF {x a w q : Nat} :
      ∀ {F : List Tree}, w ∈ rowF q (insF x a F) → w = x ∨ w ∈ rowF q F
    | [], h => by
        rw [insF, rowF] at h
        simp at h
    | t :: ts, h => by
        rw [insF, rowF, List.mem_append] at h
        rw [rowF, List.mem_append]
        rcases h with h | h
        · rcases mem_rowT_insT h with he | h
          · exact Or.inl he
          · exact Or.inr (Or.inl h)
        · rcases mem_rowF_insF h with he | h
          · exact Or.inl he
          · exact Or.inr (Or.inr h)
end

/-- Row membership after an insert: the new node, or an old member. -/
theorem mem_row_insert {X : St} {x a w q : Nat}
    (h : w ∈ row (Shesha.insert X x a) q) : w = x ∨ w ∈ row X q := by
  rw [Shesha.insert] at h
  by_cases ha : a = 0
  · rw [if_pos ha] at h
    rw [row] at h ⊢
    by_cases hq : q = 0
    · rw [if_pos hq] at h ⊢
      rw [List.map_cons] at h
      rcases List.mem_cons.mp h with he | h
      · exact Or.inl he
      · exact Or.inr h
    · rw [if_neg hq] at h ⊢
      rw [rowF, List.mem_append] at h
      rcases h with h | h
      · rw [rowT] at h
        by_cases hxq : x = q
        · rw [if_pos hxq] at h
          simp at h
        · rw [if_neg hxq, rowF] at h
          simp at h
      · exact Or.inr h
  · rw [if_neg ha] at h
    rw [row] at h ⊢
    by_cases hq : q = 0
    · rw [if_pos hq] at h ⊢
      rw [insF_topIds] at h
      exact Or.inr h
    · rw [if_neg hq] at h ⊢
      exact mem_rowF_insF h

theorem rowF_append (q : Nat) :
    ∀ (G H : List Tree), rowF q (G ++ H) = rowF q G ++ rowF q H
  | [], H => rfl
  | t :: ts, H => by
      rw [List.cons_append, rowF, rowF, rowF_append q ts H,
        List.append_assoc]

/-- The deleted node's row is gone. -/
theorem row_delete_self {X : St} (d : Nat) (hd0 : d ≠ 0) :
    row (Shesha.delete X d) d = [] := by
  rcases hemp : row (Shesha.delete X d) d with _ | ⟨a, l⟩
  · rfl
  · have hm : d ∈ read (Shesha.delete X d) :=
      row_parent_mem hd0 (by rw [hemp]; exact List.mem_cons_self ..)
    rw [read_delete, seqDel, List.mem_filter] at hm
    simp at hm

mutual
  theorem tops_delT {d w : Nat} :
      ∀ {t : Tree}, (readT t).Nodup → w ∈ (delT d t).map topId →
        w = topId t ∨ (topId t = d ∧ w ∈ rowT d t)
    | .node i cs, hnd, h => by
        rw [delT] at h
        rw [readT] at hnd
        by_cases hid : i = d
        · rw [if_pos hid] at h
          rcases tops_delF (List.nodup_cons.mp hnd).2 h with h | ⟨h1, -⟩
          · refine Or.inr ⟨hid, ?_⟩
            rw [rowT, if_pos hid]
            exact h
          · exact absurd (mem_topIds_readF h1)
              (hid ▸ (List.nodup_cons.mp hnd).1)
        · rw [if_neg hid] at h
          rw [List.map_cons] at h
          rcases List.mem_cons.mp h with he | h
          · exact Or.inl he
          · simp at h
  theorem tops_delF {d w : Nat} :
      ∀ {F : List Tree}, (readF F).Nodup → w ∈ (delF d F).map topId →
        w ∈ F.map topId ∨ (d ∈ F.map topId ∧ w ∈ rowF d F)
    | [], _, h => by
        rw [delF] at h
        simp at h
    | t :: ts, hnd, h => by
        rw [readF] at hnd
        rw [delF, List.map_append, List.mem_append] at h
        rw [List.map_cons, rowF]
        rcases h with h | h
        · rcases tops_delT (nodup_append_left hnd) h with he | ⟨h1, h2⟩
          · rw [he]
            exact Or.inl (List.mem_cons_self ..)
          · exact Or.inr ⟨by rw [← h1]; exact List.mem_cons_self ..,
              List.mem_append.mpr (Or.inl h2)⟩
        · rcases tops_delF (nodup_append_right hnd) h with h | ⟨h1, h2⟩
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr ⟨List.mem_cons_of_mem _ h1,
              List.mem_append.mpr (Or.inr h2)⟩
end

mutual
  theorem rows_delT {d w q : Nat} (hq : q ≠ d) :
      ∀ {t : Tree}, (readT t).Nodup → w ∈ rowF q (delT d t) →
        w ∈ rowT q t ∨ (d ∈ rowT q t ∧ w ∈ rowT d t)
    | .node i cs, hnd, h => by
        rw [delT] at h
        rw [readT] at hnd
        by_cases hid : i = d
        · rw [if_pos hid] at h
          rcases rows_delF hq (List.nodup_cons.mp hnd).2 h with h | ⟨h1, -⟩
          · rw [rowT, if_neg (fun e : i = q => hq (e.symm.trans hid))]
            exact Or.inl h
          · exact absurd (mem_rowF_readF h1)
              (hid ▸ (List.nodup_cons.mp hnd).1)
        · rw [if_neg hid] at h
          rw [rowF, rowF, List.append_nil] at h
          rw [rowT] at h
          by_cases hiq : i = q
          · rw [if_pos hiq] at h
            rw [rowT, if_pos hiq, rowT,
              if_neg (fun e : i = d => hid e)]
            rcases tops_delF (List.nodup_cons.mp hnd).2 h with h |
              ⟨h1, h2⟩
            · exact Or.inl h
            · exact Or.inr ⟨h1, h2⟩
          · rw [if_neg hiq] at h
            rw [rowT, if_neg hiq, rowT,
              if_neg (fun e : i = d => hid e)]
            rcases rows_delF hq (List.nodup_cons.mp hnd).2 h with h |
              ⟨h1, h2⟩
            · exact Or.inl h
            · exact Or.inr ⟨h1, h2⟩
  theorem rows_delF {d w q : Nat} (hq : q ≠ d) :
      ∀ {F : List Tree}, (readF F).Nodup → w ∈ rowF q (delF d F) →
        w ∈ rowF q F ∨ (d ∈ rowF q F ∧ w ∈ rowF d F)
    | [], _, h => by
        rw [delF, rowF] at h
        simp at h
    | t :: ts, hnd, h => by
        rw [readF] at hnd
        rw [delF, rowF_append, List.mem_append] at h
        rcases h with h | h
        · rcases rows_delT hq (nodup_append_left hnd) h with h | ⟨h1, h2⟩
          · exact Or.inl (by
              rw [rowF, List.mem_append]
              exact Or.inl h)
          · exact Or.inr ⟨by
              rw [rowF, List.mem_append]
              exact Or.inl h1,
              by
                rw [rowF, List.mem_append]
                exact Or.inl h2⟩
        · rcases rows_delF hq (nodup_append_right hnd) h with h | ⟨h1, h2⟩
          · exact Or.inl (by
              rw [rowF, List.mem_append]
              exact Or.inr h)
          · exact Or.inr ⟨by
              rw [rowF, List.mem_append]
              exact Or.inr h1,
              by
                rw [rowF, List.mem_append]
                exact Or.inr h2⟩
end

/-- Row membership after a delete: unchanged, or spliced up from the
deleted node's row into the deleted node's slot. -/
theorem mem_row_delete {X : St} (hwf : WF X) {d w q : Nat} (hd0 : d ≠ 0)
    (hq : q ≠ d) (h : w ∈ row (Shesha.delete X d) q) :
    w ∈ row X q ∨ (d ∈ row X q ∧ w ∈ row X d) := by
  rw [Shesha.delete] at h
  rw [row] at h ⊢
  by_cases hq0 : q = 0
  · rw [if_pos hq0] at h ⊢
    rcases tops_delF hwf.1 h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_⟩
      rw [row, if_neg hd0]
      exact h2
  · rw [if_neg hq0] at h ⊢
    rcases rows_delF hq hwf.1 h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_⟩
      rw [row, if_neg hd0]
      exact h2

/-! ## The branch-structure invariant, discharged -/

theorem step_LRowsOK {L t : St} {o : Op} (hwf : WF t)
    (hok : LRowsOK L t) (ho : OpHonest L t o) :
    LRowsOK L (applyOp t o) := by
  cases o with
  | ins x a =>
      obtain ⟨-, hxL, -, -⟩ := ho
      intro w q hwL hw
      rcases mem_row_insert hw with he | hw'
      · exact absurd (he ▸ hwL) hxL
      · exact hok w q hwL hw'
  | del d =>
      have hd : d ∈ read t := ho
      have hd0 : d ≠ 0 := fun h0 => hwf.2 (h0 ▸ hd)
      intro w q hwL hw
      have hw2 : w ∈ row (Shesha.delete t d) q := hw
      by_cases hqd : q = d
      · rw [hqd, row_delete_self d hd0] at hw2
        exact absurd hw2 (by simp)
      · rcases mem_row_delete hwf hd0 hqd hw2 with hw' | ⟨h1, h2⟩
        · exact hok w q hwL hw'
        · rcases hok w d hwL h2 with h0 | hdL
          · exact absurd h0 hd0
          · rcases hok d q hdL h1 with h0 | hqL
            · exact Or.inl h0
            · exact Or.inr hqL

theorem hreach_LRowsOK {L X : St} (hwfL : WF L) (h : HReach L X) :
    LRowsOK L X := by
  induction h with
  | refl =>
      intro w q hwL hw
      by_cases hq : q = 0
      · exact Or.inl hq
      · exact Or.inr (row_parent_mem hq hw)
  | step hr ho ih => exact step_LRowsOK (hreach_WF hwfL hr) ih ho

/-! ## The honest-merge capstones -/

/-- Both branches evolved honestly from a WF LCA, with cross-branch
Lamport uniqueness (an id live in both branches is common past) — the one
irreducibly global contract. -/
structure HonestMerge (L A B : St) : Prop where
  wfL : WF L
  reachA : HReach L A
  reachB : HReach L B
  fresh : ∀ u, u ∈ read A → u ∈ read B → u ∈ read L

theorem HonestMerge.modelOK {L A B : St} (h : HonestMerge L A B) :
    ModelOK L A B :=
  ⟨h.wfL, hreach_WF h.wfL h.reachA, hreach_WF h.wfL h.reachB, h.fresh⟩

/-- Every honestly-reached merge is well-formed. -/
theorem merge_WF_honest {L A B : St} (h : HonestMerge L A B) :
    WF (merge L A B) :=
  merge_WF h.modelOK (hreach_LRowsOK h.wfL h.reachA)
    (hreach_LRowsOK h.wfL h.reachB)

/-- Every honestly-reached merge displays exactly the merge-live ids. -/
theorem merge_ids_honest {L A B : St} (h : HonestMerge L A B) (u : Nat) :
    u ∈ ids (merge L A B) ↔ liveMp L A B u = true :=
  merge_ids h.modelOK (hreach_LRowsOK h.wfL h.reachA)
    (hreach_LRowsOK h.wfL h.reachB) u

/-- Every honestly-reached merge is branch-symmetric. -/
theorem merge_comm_honest {L A B : St} (h : HonestMerge L A B) :
    merge L A B = merge L B A :=
  merge_comm h.modelOK

/-- Every honestly-reached merge extends the LCA's display order. -/
theorem merge_extends_L_honest {L A B : St} (h : HonestMerge L A B)
    {u v : Nat} (hu : u ∈ ids (merge L A B)) (hv : v ∈ ids (merge L A B))
    (huL : u ∈ ids L) (hvL : v ∈ ids L) :
    precedes (read (merge L A B)) u v ↔ precedes (read L) u v :=
  merge_extends_L h.modelOK (hreach_LRowsOK h.wfL h.reachA)
    (hreach_LRowsOK h.wfL h.reachB) hu hv huL hvL

end Shesha

section AxiomAuditEvolution
/-! Axiom audit: the honest-merge capstones are kernel-clean. -/
#print axioms Shesha.hreach_WF
#print axioms Shesha.hreach_LRowsOK
#print axioms Shesha.merge_WF_honest
#print axioms Shesha.merge_ids_honest
#print axioms Shesha.merge_comm_honest
#print axioms Shesha.merge_extends_L_honest
end AxiomAuditEvolution
