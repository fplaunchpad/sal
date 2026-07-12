import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Skel

/-! # Shesha — M0: the placed-exactly-once accounting (phase 2b, block 2)

Closes the survivor-set identity (`merge_ids`) and the `Nodup` half of
`merge_WF` (`merge_read_nodup`) — the two obligations
`Shesha_Merge_Lemmas.lean` documents as owed to the parent-chain layer.

Structure:
- §1 counting plumbing (`count_flatMap`, `runsGo_count`);
- §2 `outRows` rows, exactly (`outRows_alGet_of_skel` / `_of_bornA` /
  `_of_bornB` / `_none`);
- §3 base accounting: every id sits in at most one merged row, at most once;
- §4 the marker splice: fuel adequacy (`expandRow` output is marker-free)
  and expanded-row accounting;
- §5 the generic DFS-count lemma (emissions ≤ visits of the unique emitter)
  and `merge_read_nodup`;
- §6 placement/coverage and `merge_ids`.
-/

namespace Shesha

open List

/-! ## §1 Counting plumbing -/

theorem count_flatMap (g : Nat → List Nat) (u : Nat) :
    ∀ l : List Nat,
      (l.flatMap g).count u = (l.map (fun c => (g c).count u)).sum
  | [] => rfl
  | c :: l => by
      rw [List.flatMap_cons, List.count_append, List.map_cons, List.sum_cons,
        count_flatMap g u l]

theorem length_dropWhile_le' (p : Nat → Bool) :
    ∀ l : List Nat, (l.dropWhile p).length ≤ l.length
  | [] => Nat.le_refl _
  | a :: l => by
      rw [List.dropWhile_cons]
      by_cases h : p a = true
      · rw [if_pos h]
        exact Nat.le_trans (length_dropWhile_le' p l) (by simp)
      · rw [if_neg h]
        exact Nat.le_refl _

/-- The runs of a row carry exactly its non-L elements (with multiplicity):
segments partition the filtered row. -/
theorem runsGo_count (isL : Nat → Bool) (u : Nat) :
    ∀ (fuel : Nat) (pre : Option Nat) (l : List Nat), l.length < fuel →
      ((runsGo isL fuel pre l).map (fun pr => pr.2.1.count u)).sum =
        (l.filter (fun v => !isL v)).count u
  | 0, _, l, h => ((Nat.not_lt_zero _) h).elim
  | fuel + 1, pre, [], _ => by simp [runsGo]
  | fuel + 1, pre, u' :: rest, h => by
      simp only [runsGo]
      by_cases hL : isL u' = true
      · rw [if_pos hL, List.filter_cons_of_neg (by simp [hL])]
        refine runsGo_count isL u fuel (some u') rest ?_
        simp only [List.length_cons] at h
        omega
      · rw [if_neg hL, List.map_cons, List.sum_cons]
        have hdw : (u' :: rest).dropWhile (fun v => !isL v) =
            rest.dropWhile (fun v => !isL v) := by
          rw [List.dropWhile_cons, if_pos (by simp [hL])]
        have hlen : ((u' :: rest).dropWhile (fun v => !isL v)).length
            < fuel := by
          rw [hdw]
          have := length_dropWhile_le' (fun v => !isL v) rest
          simp only [List.length_cons] at h
          omega
        rw [runsGo_count isL u fuel pre _ hlen]
        have hsplit : (u' :: rest).filter (fun v => !isL v) =
            ((u' :: rest).takeWhile (fun v => !isL v)).filter
                (fun v => !isL v) ++
              ((u' :: rest).dropWhile (fun v => !isL v)).filter
                (fun v => !isL v) := by
          rw [← List.filter_append, List.takeWhile_append_dropWhile]
        rw [hsplit, List.count_append,
          List.filter_eq_self.mpr fun a ha => mem_takeWhile_pred ha]

/-! ## §2 `outRows` rows, exactly -/

theorem alHas_append (al₁ al₂ : List (Nat × List Nat)) (k : Nat) :
    alHas (al₁ ++ al₂) k = (alHas al₁ k || alHas al₂ k) := by
  simp [alHas, List.any_append]

/-- The assembly map preserves keys. -/
theorem assemble_keys (g : Nat → List Nat → List Nat)
    (al : List (Nat × List Nat)) :
    (al.map (fun kv => (kv.1, g kv.1 kv.2))).map (·.1) = al.map (·.1) := by
  rw [List.map_map]
  exact List.map_congr_left fun kv _ => rfl

theorem alHas_assemble (g : Nat → List Nat → List Nat)
    (al : List (Nat × List Nat)) (k : Nat) :
    alHas (al.map (fun kv => (kv.1, g kv.1 kv.2))) k = alHas al k := by
  by_cases hh : alHas al k = true
  · rw [hh]
    exact alHas_iff_mem_keys.mpr (by
      rw [assemble_keys]
      exact alHas_iff_mem_keys.mp hh)
  · have h2 : ¬ alHas (al.map (fun kv => (kv.1, g kv.1 kv.2))) k = true :=
      fun hc => hh (alHas_iff_mem_keys.mpr (by
        rw [← assemble_keys g al]
        exact alHas_iff_mem_keys.mp hc))
    rw [Bool.eq_false_iff.mpr hh, Bool.eq_false_iff.mpr h2]

theorem alGet_map_assemble (g : Nat → List Nat → List Nat) :
    ∀ (al : List (Nat × List Nat)) (k : Nat),
      alGet (al.map (fun kv => (kv.1, g kv.1 kv.2))) k =
        if alHas al k = true then g k (alGet al k) else []
  | [], k => by simp [alGet, alHas]
  | kv :: al, k => by
      by_cases hk : kv.1 = k
      · rw [List.map_cons, alGet_cons,
          if_pos (show ((kv.1, g kv.1 kv.2).1 == k) = true by simp [hk]),
          if_pos (show alHas (kv :: al) k = true by
            rw [alHas_cons]; simp [hk]),
          alGet_cons, if_pos (show (kv.1 == k) = true by simp [hk]), hk]
      · rw [List.map_cons, alGet_cons,
          if_neg (show ¬ ((kv.1, g kv.1 kv.2).1 == k) = true by simp [hk]),
          alGet_map_assemble g al k, alHas_cons]
        by_cases hh : alHas al k = true
        · rw [if_pos hh, if_pos (by simp [hh]), alGet_cons,
            if_neg (show ¬ ((kv.1 == k) = true) by simp [hk])]
        · rw [if_neg hh,
            if_neg (show ¬ (((kv.1 == k) || alHas al k) = true) by
              simp [hk, hh])]

/-- The merge's command list (both branches, in order). -/
def mergeCmds (L A B : St) : List Cmd :=
  branchCmds L A (skelOf L A B) (markerp L A B) ++
    branchCmds L B (skelOf L A B) (markerp L A B)

/-- A skeleton key's merged row is its assembled skeleton row. -/
theorem outRows_alGet_of_skel {L A B : St} {k : Nat}
    (hk : alHas (skelOf L A B).rows k = true) :
    alGet (outRows L A B) k =
      rowAssemble (mergeCmds L A B) k (alGet (skelOf L A B).rows k) := by
  simp only [outRows, mergeCmds]
  rw [alGet_append, if_pos (by
    rw [alHas_append, alHas_assemble, hk]
    rfl),
    alGet_append, if_pos (by rw [alHas_assemble]; exact hk),
    alGet_map_assemble, if_pos hk]

/-- `bbrows` has a key exactly for born nodes with nonempty rows. -/
theorem bbrows_alHas_of_nonempty {L X : St} {q : Nat}
    (hq : q ∈ bornIds L X) (hne : ¬ (row X q).isEmpty = true) :
    alHas (bbrows L X) q = true := by
  rw [alHas, List.any_eq_true]
  refine ⟨(q, row X q), ?_, by simp⟩
  unfold bbrows
  rw [List.mem_filterMap]
  exact ⟨q, hq, by rw [if_neg hne]⟩

/-- A non-skeleton key outside both born sets has no merged row. -/
theorem outRows_alGet_none {L A B : St} {k : Nat}
    (h1 : ¬ alHas (skelOf L A B).rows k = true)
    (h2 : k ∉ bornIds L A) (h3 : k ∉ bornIds L B) :
    alGet (outRows L A B) k = [] := by
  simp only [outRows]
  have hbbA : ¬ alHas (bbrows L A) k = true := fun hc =>
    h2 ((filterMapRow_keys_sublist A (bornIds L A)).subset
      (alHas_iff_mem_keys.mp hc))
  have hbbB : ¬ alHas (bbrows L B) k = true := fun hc =>
    h3 ((filterMapRow_keys_sublist B (bornIds L B)).subset
      (alHas_iff_mem_keys.mp hc))
  have hmap : ¬ alHas ((skelOf L A B).rows.map (fun kv =>
      (kv.1, rowAssemble (branchCmds L A (skelOf L A B) (markerp L A B) ++
        branchCmds L B (skelOf L A B) (markerp L A B)) kv.1 kv.2))) k
      = true := by
    rw [alHas_assemble (fun a b => rowAssemble _ a b)]
    exact h1
  refine alGet_eq_nil_of_not_has ?_
  rw [alHas_append, alHas_append, Bool.eq_false_iff.mpr hmap,
    Bool.eq_false_iff.mpr hbbA, Bool.eq_false_iff.mpr hbbB]
  simp

theorem bool_eq_false {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- Born ids are live in their branch, absent from `L`, and nonzero. -/
theorem bornIds_spec {L X : St} (hwf : WF X) {q : Nat}
    (hq : q ∈ bornIds L X) : q ∈ read X ∧ q ∉ read L ∧ q ≠ 0 := by
  rw [bornIds, List.mem_filter] at hq
  refine ⟨hq.1, contains_eq_false.mp ?_, fun h0 => hwf.2 (h0 ▸ hq.1)⟩
  have := hq.2
  simp only [Bool.not_eq_true'] at this
  exact this

/-- An A-born key's merged row is its wholesale A-row. -/
theorem outRows_alGet_of_bornA {L A B : St} (mok : ModelOK L A B) {q : Nat}
    (hq : q ∈ bornIds L A) :
    alGet (outRows L A B) q = row A q := by
  obtain ⟨hqA, hqL, hq0⟩ := bornIds_spec mok.wfA hq
  have hskel : ¬ alHas (skelOf L A B).rows q = true := by
    intro hc
    rcases skelOf_keys_spec mok.wfL (alHas_iff_mem_keys.mp hc) with
      h0 | ⟨hm, -⟩
    · exact hq0 h0
    · exact hqL hm
  have hbbB : ¬ alHas (bbrows L B) q = true := fun hc =>
    hqL (mok.common q hqA (alHas_bbrows_key hc).1)
  simp only [outRows]
  have hmap : ¬ alHas ((skelOf L A B).rows.map (fun kv =>
      (kv.1, rowAssemble (branchCmds L A (skelOf L A B) (markerp L A B) ++
        branchCmds L B (skelOf L A B) (markerp L A B)) kv.1 kv.2))) q
      = true := by
    rw [alHas_assemble (fun a b => rowAssemble _ a b)]
    exact hskel
  rw [alGet_append]
  by_cases hbbA : alHas (bbrows L A) q = true
  · rw [if_pos (by rw [alHas_append, bool_eq_false hmap, hbbA]; rfl),
      alGet_append, if_neg (by rw [bool_eq_false hmap]; simp)]
    exact bbrows_alGet mok.wfA.1 hq
  · rw [if_neg (by
      rw [alHas_append, bool_eq_false hmap, bool_eq_false hbbA]
      simp),
      alGet_eq_nil_of_not_has hbbB]
    by_cases hem : (row A q).isEmpty = true
    · exact (List.isEmpty_iff.mp hem).symm
    · exact absurd (bbrows_alHas_of_nonempty hq hem) hbbA

/-- A B-born key's merged row is its wholesale B-row. -/
theorem outRows_alGet_of_bornB {L A B : St} (mok : ModelOK L A B) {q : Nat}
    (hq : q ∈ bornIds L B) :
    alGet (outRows L A B) q = row B q := by
  obtain ⟨hqB, hqL, hq0⟩ := bornIds_spec mok.wfB hq
  have hskel : ¬ alHas (skelOf L A B).rows q = true := by
    intro hc
    rcases skelOf_keys_spec mok.wfL (alHas_iff_mem_keys.mp hc) with
      h0 | ⟨hm, -⟩
    · exact hq0 h0
    · exact hqL hm
  have hbbA : ¬ alHas (bbrows L A) q = true := fun hc =>
    hqL (mok.common q (alHas_bbrows_key hc).1 hqB)
  simp only [outRows]
  have hmap : ¬ alHas ((skelOf L A B).rows.map (fun kv =>
      (kv.1, rowAssemble (branchCmds L A (skelOf L A B) (markerp L A B) ++
        branchCmds L B (skelOf L A B) (markerp L A B)) kv.1 kv.2))) q
      = true := by
    rw [alHas_assemble (fun a b => rowAssemble _ a b)]
    exact hskel
  rw [alGet_append,
    if_neg (by
      rw [alHas_append, bool_eq_false hmap, bool_eq_false hbbA]
      simp)]
  by_cases hbbB : alHas (bbrows L B) q = true
  · exact bbrows_alGet mok.wfB.1 hq
  · rw [alGet_eq_nil_of_not_has hbbB]
    by_cases hem : (row B q).isEmpty = true
    · exact (List.isEmpty_iff.mp hem).symm
    · exact absurd (bbrows_alHas_of_nonempty hq hem) hbbB

/-! ## §3 Base accounting: every id in at most one merged row, at most once

Sum plumbing is hand-rolled (this import closure is Lean-core only). -/

theorem sum_map_add (f g : Nat → Nat) :
    ∀ l : List Nat,
      (l.map (fun k => f k + g k)).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | a :: l => by
      rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons,
        List.sum_cons, List.sum_cons, sum_map_add f g l]
      omega

theorem sum_le_sum' {f g : Nat → Nat} :
    ∀ {l : List Nat}, (∀ x ∈ l, f x ≤ g x) →
      (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl _
  | a :: l, h => by
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      have h1 := h a (by simp)
      have h2 := sum_le_sum' fun x hx => h x (List.mem_cons_of_mem a hx)
      omega

theorem perm_sum_eq : ∀ {l₁ l₂ : List Nat}, l₁.Perm l₂ → l₁.sum = l₂.sum := by
  intro l₁ l₂ h
  induction h with
  | nil => rfl
  | cons x _ ih => rw [List.sum_cons, List.sum_cons, ih]
  | swap x y l => rw [List.sum_cons, List.sum_cons, List.sum_cons,
      List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem count_flatten (u : Nat) :
    ∀ rs : List (List Nat),
      rs.flatten.count u = (rs.map (fun r => r.count u)).sum
  | [] => rfl
  | r :: rs => by
      rw [List.flatten_cons, List.count_append, List.map_cons, List.sum_cons,
        count_flatten u rs]

/-- Sorting same-slot runs never changes what is counted. -/
theorem count_sortRunsDesc (rs : List (List Nat)) (u : Nat) :
    ((sortRunsDesc rs).flatten).count u = (rs.map (fun r => r.count u)).sum := by
  rw [count_flatten]
  exact perm_sum_eq ((List.mergeSort_perm rs _).map _)

/-- Counting through a filter. -/
theorem count_filter' (p : Nat → Bool) (u : Nat) :
    ∀ l : List Nat,
      (l.filter p).count u = if p u = true then l.count u else 0
  | [] => by by_cases h : p u = true <;> simp [h]
  | a :: l => by
      by_cases hu : p u = true
      · rw [if_pos hu]
        by_cases ha : p a = true
        · rw [List.filter_cons_of_pos ha, List.count_cons, List.count_cons,
            count_filter' p u l, if_pos hu]
        · rw [List.filter_cons_of_neg ha, List.count_cons,
            count_filter' p u l, if_pos hu]
          have hne : ¬ a = u := fun e => ha (e ▸ hu)
          have hne' : ¬ u = a := fun e => hne e.symm
          simp [hne, hne']
      · rw [if_neg hu]
        by_cases ha : p a = true
        · rw [List.filter_cons_of_pos ha, List.count_cons,
            count_filter' p u l, if_neg hu]
          have hne : ¬ a = u := fun e => hu (e ▸ ha)
          have hne' : ¬ u = a := fun e => hne e.symm
          simp [hne, hne']
        · rw [List.filter_cons_of_neg ha, count_filter' p u l, if_neg hu]

theorem sum_eq_zero' : ∀ {l : List Nat}, (∀ x ∈ l, x = 0) → l.sum = 0
  | [], _ => rfl
  | a :: l, h => by
      rw [List.sum_cons, h a (by simp),
        sum_eq_zero' fun x hx => h x (List.mem_cons_of_mem a hx)]

/-- Indicator sums over duplicate-free index lists collapse. -/
theorem sum_ite_le (a k' : Nat) :
    ∀ l : List Nat, l.Nodup →
      ((l.map (fun k => if k' == k then a else 0)).sum) ≤ a
  | [], _ => Nat.zero_le _
  | k :: l, hnd => by
      rw [List.map_cons, List.sum_cons]
      by_cases hk : (k' == k) = true
      · rw [if_pos hk]
        have hk' : k' = k := by simpa using hk
        have hz : (l.map (fun k'' => if k' == k'' then a else 0)).sum = 0 := by
          refine sum_eq_zero' fun x hx => ?_
          rw [List.mem_map] at hx
          obtain ⟨k'', hk'', he⟩ := hx
          have hne : ¬ (k' == k'') = true := fun hc => by
            have heq : k' = k'' := by simpa using hc
            rw [← heq] at hk''
            exact (List.nodup_cons.mp hnd).1 (hk' ▸ hk'')
          rw [if_neg hne] at he
          exact he.symm
        omega
      · rw [if_neg hk]
        have := sum_ite_le a k' l (List.nodup_cons.mp hnd).2
        omega

/-- A single member's contribution bounds below the mapped sum. -/
theorem single_mem_le {α : Type} (f : α → Nat) :
    ∀ {l : List α} {c : α}, c ∈ l → f c ≤ (l.map f).sum
  | a :: l, c, h => by
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := single_mem_le f h
        omega

/-- Two members at distinct positions (distinct values suffice) contribute
independently. -/
theorem two_mem_le {α : Type} (f : α → Nat) :
    ∀ {l : List α} {c₁ c₂ : α}, c₁ ∈ l → c₂ ∈ l → c₁ ≠ c₂ →
      f c₁ + f c₂ ≤ (l.map f).sum
  | a :: l, c₁, c₂, h₁, h₂, hne => by
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp h₁ with he₁ | h₁'
      · have h₂' : c₂ ∈ l := by
          rcases List.mem_cons.mp h₂ with he₂ | h
          · exact absurd (he₁.trans he₂.symm) hne
          · exact h
        have hb := single_mem_le f h₂'
        rw [he₁]
        omega
      · rcases List.mem_cons.mp h₂ with he₂ | h₂'
        · have hb := single_mem_le f h₁'
          rw [he₂]
          omega
        · have hb := two_mem_le f h₁' h₂' hne
          omega

/-- **Disjoint rows, counted.** On a WF state, the rows of any duplicate-free
list of parents jointly hold each id at most once. -/
theorem rows_count_sum {X : St} (hwf : WF X) (u : Nat) :
    ∀ (ps : List Nat), ps.Nodup →
      ((ps.map (fun p => (row X p).count u)).sum) ≤ 1 := by
  intro ps hnd
  have hpt : ∀ p ∈ ps, (row X p).count u ≤
      if parOf X u == p then 1 else 0 := by
    intro p _
    by_cases hz : (row X p).count u = 0
    · rw [hz]
      exact Nat.zero_le _
    · have hmem : u ∈ row X p := List.count_pos_iff.mp (Nat.pos_of_ne_zero hz)
      have hp : parOf X u = p := row_mem_parOf hwf hmem
      rw [if_pos (by simp [hp])]
      exact Nat.le_trans (row_count_le X p u) (count_le_one_of_nodup hwf.1 u)
  exact Nat.le_trans (sum_le_sum' hpt) (sum_ite_le 1 (parOf X u) ps hnd)

/-! ### Buckets: how commands land in an assembled row -/

theorem slotRuns_cons_slot (tr k' : Nat) (run : List Nat) (cmds : List Cmd)
    (p k : Nat) :
    slotRuns (Cmd.slot tr k' run :: cmds) p k =
      if (tr == p && k' == k) = true then run :: slotRuns cmds p k
      else slotRuns cmds p k := by
  by_cases hb : (tr == p && k' == k) = true
  · rw [if_pos hb]
    exact List.filterMap_cons_some (by
      show (if (tr == p && k' == k) = true then some run else none) = some run
      rw [if_pos hb])
  · rw [if_neg hb]
    exact List.filterMap_cons_none (by
      show (if (tr == p && k' == k) = true then some run else none) = none
      rw [if_neg hb])

theorem slotRuns_cons_atEnd (q : Nat) (run : List Nat) (cmds : List Cmd)
    (p k : Nat) :
    slotRuns (Cmd.atEnd q run :: cmds) p k = slotRuns cmds p k :=
  List.filterMap_cons_none rfl

theorem endRuns_cons_slot (tr k' : Nat) (run : List Nat) (cmds : List Cmd)
    (p : Nat) :
    endRuns (Cmd.slot tr k' run :: cmds) p = endRuns cmds p :=
  List.filterMap_cons_none rfl

theorem endRuns_cons_atEnd (q : Nat) (run : List Nat) (cmds : List Cmd)
    (p : Nat) :
    endRuns (Cmd.atEnd q run :: cmds) p =
      if (q == p) = true then run :: endRuns cmds p else endRuns cmds p := by
  by_cases hb : (q == p) = true
  · rw [if_pos hb]
    exact List.filterMap_cons_some (by
      show (if (q == p) = true then some run else none) = some run
      rw [if_pos hb])
  · rw [if_neg hb]
    exact List.filterMap_cons_none (by
      show (if (q == p) = true then some run else none) = none
      rw [if_neg hb])

/-- Each command's run lands in at most one bucket of row `p`. -/
theorem buckets_le (u p len : Nat) :
    ∀ cmds : List Cmd,
      ((List.range (len + 1)).map (fun k =>
        ((slotRuns cmds p k).map (fun r => r.count u)).sum)).sum
      + ((endRuns cmds p).map (fun r => r.count u)).sum
      ≤ (cmds.map (fun c => (cmdRun c).count u)).sum
  | [] => by
      have h1 : ((List.range (len + 1)).map (fun k =>
          ((slotRuns ([] : List Cmd) p k).map (fun r => r.count u)).sum)).sum
          = 0 :=
        sum_eq_zero' fun x hx => by
          rw [List.mem_map] at hx
          obtain ⟨k, -, he⟩ := hx
          exact he.symm
      rw [h1]
      simp [endRuns]
  | c :: cmds => by
      rw [List.map_cons, List.sum_cons]
      rcases c with ⟨tr, k', run⟩ | ⟨q, run⟩
      · have hpt : ∀ k ∈ List.range (len + 1),
            ((slotRuns (Cmd.slot tr k' run :: cmds) p k).map
              (fun r => r.count u)).sum =
            (if (tr == p && k' == k) = true then run.count u else 0)
              + ((slotRuns cmds p k).map (fun r => r.count u)).sum := by
          intro k _
          rw [slotRuns_cons_slot]
          by_cases hb : (tr == p && k' == k) = true
          · rw [if_pos hb, if_pos hb, List.map_cons, List.sum_cons]
          · rw [if_neg hb, if_neg hb, Nat.zero_add]
        rw [List.map_congr_left hpt,
          sum_map_add (fun k => if (tr == p && k' == k) = true
              then run.count u else 0)
            (fun k => ((slotRuns cmds p k).map (fun r => r.count u)).sum),
          endRuns_cons_slot]
        have hite : ((List.range (len + 1)).map
            (fun k => if (tr == p && k' == k) = true
              then run.count u else 0)).sum ≤ run.count u := by
          by_cases htr : (tr == p) = true
          · have hpt2 : ∀ k ∈ List.range (len + 1),
                (if (tr == p && k' == k) = true then run.count u else 0) =
                (if (k' == k) = true then run.count u else 0) := by
              intro k _
              rw [htr, Bool.true_and]
            rw [List.map_congr_left hpt2]
            exact sum_ite_le (run.count u) k' _ (List.nodup_range)
          · have hz : ((List.range (len + 1)).map
                (fun k => if (tr == p && k' == k) = true
                  then run.count u else 0)).sum = 0 :=
              sum_eq_zero' fun x hx => by
                rw [List.mem_map] at hx
                obtain ⟨k, -, he⟩ := hx
                rw [if_neg (by simp [htr])] at he
                exact he.symm
            omega
        have hrec := buckets_le u p len cmds
        show _ + _ ≤ run.count u + _
        omega
      · have hpt : ∀ k ∈ List.range (len + 1),
            ((slotRuns (Cmd.atEnd q run :: cmds) p k).map
              (fun r => r.count u)).sum =
            ((slotRuns cmds p k).map (fun r => r.count u)).sum := by
          intro k _
          rw [slotRuns_cons_atEnd]
        rw [List.map_congr_left hpt, endRuns_cons_atEnd]
        have hrec := buckets_le u p len cmds
        by_cases hb : (q == p) = true
        · rw [if_pos hb, List.map_cons, List.sum_cons]
          show _ + _ ≤ run.count u + _
          omega
        · rw [if_neg hb]
          show _ ≤ run.count u + _
          omega

/-- **Assembled-row count, decomposed**: skeleton entries plus bucketed
runs. -/
theorem rowAssemble_count (cmds : List Cmd) (p : Nat) (skelRow : List Nat)
    (u : Nat) :
    (rowAssemble cmds p skelRow).count u =
      ((List.range (skelRow.length + 1)).map (fun k =>
        ((slotRuns cmds p k).map (fun r => r.count u)).sum)).sum
      + skelRow.count u
      + ((endRuns cmds p).map (fun r => r.count u)).sum := by
  unfold rowAssemble
  rw [List.count_append, count_flatMap, count_sortRunsDesc]
  have hpt : ∀ k ∈ List.range (skelRow.length + 1),
      ((sortRunsDesc (slotRuns cmds p k)).flatten ++
        (skelRow.drop k).take 1).count u =
      ((slotRuns cmds p k).map (fun r => r.count u)).sum
        + ((skelRow.drop k).take 1).count u := by
    intro k _
    rw [List.count_append, count_sortRunsDesc]
  rw [List.map_congr_left hpt,
    sum_map_add (fun k => ((slotRuns cmds p k).map (fun r => r.count u)).sum)
      (fun k => ((skelRow.drop k).take 1).count u)]
  have hskel : ((List.range (skelRow.length + 1)).map (fun k =>
      ((skelRow.drop k).take 1).count u)).sum = skelRow.count u := by
    rw [← count_flatMap (fun k => (skelRow.drop k).take 1) u,
      flatMap_take_drop]
  rw [hskel]

/-- **Assembled-row count bound**: each id at most once per skeleton row
plus once per command. -/
theorem rowAssemble_count_le (cmds : List Cmd) (p : Nat) (skelRow : List Nat)
    (u : Nat) :
    (rowAssemble cmds p skelRow).count u ≤
      skelRow.count u + (cmds.map (fun c => (cmdRun c).count u)).sum := by
  rw [rowAssemble_count]
  have := buckets_le u p skelRow.length cmds
  omega

/-! ### Branch command totals -/

theorem sum_append' : ∀ (l₁ l₂ : List Nat), (l₁ ++ l₂).sum = l₁.sum + l₂.sum
  | [], l₂ => by rw [List.nil_append, List.sum_nil, Nat.zero_add]
  | a :: l₁, l₂ => by
      rw [List.cons_append, List.sum_cons, List.sum_cons, sum_append' l₁ l₂,
        Nat.add_assoc]

theorem sum_map_flatMap {α : Type} (f : α → Nat) (g : Nat → List α) :
    ∀ l : List Nat,
      ((l.flatMap g).map f).sum = (l.map (fun p => ((g p).map f).sum)).sum
  | [] => rfl
  | a :: l => by
      rw [List.flatMap_cons, List.map_append, sum_append', List.map_cons,
        List.sum_cons, sum_map_flatMap f g l]

/-- A branch's commands carry exactly the non-L content of its host rows. -/
theorem branchCmds_count_sum (L X : St) (sk : Skel) (mk : Nat → Bool)
    (u : Nat) :
    ((branchCmds L X sk mk).map (fun c => (cmdRun c).count u)).sum =
      ((hosts L X).map (fun p =>
        ((runsGo (contains L) ((row X p).length + 1) none (row X p)).map
          (fun pr => pr.2.1.count u)).sum)).sum := by
  unfold branchCmds
  rw [sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun pr _ => ?_)
  rcases pr with ⟨_ | pre, run, _ | s⟩ <;> rfl

/-- **Branch command bound**: a branch's commands mention an id at most
once, and only ids the branch holds outside `L`. -/
theorem branchCmds_count {L X : St} (hwf : WF X) (sk : Skel)
    (mk : Nat → Bool) (u : Nat) :
    ((branchCmds L X sk mk).map (fun c => (cmdRun c).count u)).sum ≤
      if (contains L u || !contains X u) = true then 0 else 1 := by
  rw [branchCmds_count_sum]
  by_cases hL : (contains L u || !contains X u) = true
  · rw [if_pos hL]
    refine Nat.le_of_eq (sum_eq_zero' fun x hx => ?_)
    rw [List.mem_map] at hx
    obtain ⟨p, -, he⟩ := hx
    rw [runsGo_count (contains L) u _ none (row X p) (Nat.lt_succ_self _),
      count_filter'] at he
    rcases Bool.or_eq_true_iff.mp hL with h | h
    · rw [if_neg (by simp [h])] at he
      exact he.symm
    · by_cases hf : (!contains L u) = true
      · rw [if_pos hf] at he
        rw [← he]
        refine List.count_eq_zero.mpr fun hc => ?_
        have hm := contains_iff.mpr (mem_row_read hc)
        simp [hm] at h
      · rw [if_neg hf] at he
        exact he.symm
  · rw [if_neg hL]
    have hnL : (!contains L u) = true := by
      by_cases h : contains L u = true
      · exact absurd (by simp [h]) hL
      · simp [bool_eq_false h]
    have hpt : ∀ p ∈ hosts L X,
        ((runsGo (contains L) ((row X p).length + 1) none
          (row X p)).map (fun pr => pr.2.1.count u)).sum =
        (row X p).count u := by
      intro p _
      rw [runsGo_count (contains L) u _ none (row X p) (Nat.lt_succ_self _),
        count_filter', if_pos hnL]
    rw [List.map_congr_left hpt]
    exact rows_count_sum hwf u (hosts L X) (hosts_nodup L X)

/-- **Global command bound** (pattern-8 across branches): the merge's
commands mention an id at most once, and never an L-id. -/
theorem mergeCmds_count {L A B : St} (mok : ModelOK L A B) (u : Nat) :
    ((mergeCmds L A B).map (fun c => (cmdRun c).count u)).sum ≤
      if contains L u = true then 0 else 1 := by
  unfold mergeCmds
  rw [List.map_append, sum_append']
  have hA := branchCmds_count (L := L) (X := A) mok.wfA (skelOf L A B)
    (markerp L A B) u
  have hB := branchCmds_count (L := L) (X := B) mok.wfB (skelOf L A B)
    (markerp L A B) u
  by_cases hL : contains L u = true
  · rw [if_pos hL]
    rw [if_pos (by simp [hL])] at hA hB
    omega
  · rw [if_neg hL]
    by_cases hXA : contains A u = true
    · have hXB : contains B u = false := by
        by_cases h : contains B u = true
        · exact absurd (contains_iff.mpr (mok.common u (contains_iff.mp hXA)
            (contains_iff.mp h))) hL
        · exact bool_eq_false h
      rw [if_neg (by simp [bool_eq_false hL, hXA])] at hA
      rw [if_pos (by simp [hXB])] at hB
      omega
    · rw [if_pos (by simp [bool_eq_false hXA])] at hA
      have hB1 : ((branchCmds L B (skelOf L A B) (markerp L A B)).map
          (fun c => (cmdRun c).count u)).sum ≤ 1 :=
        Nat.le_trans hB (by split <;> omega)
      omega

/-! ### Addresses: where a merged-row occurrence can come from -/

/-- The row a command targets. -/
def cmdTarget : Cmd → Nat
  | .slot tr _ _ => tr
  | .atEnd q _ => q

theorem slotRuns_mem_cmd {cmds : List Cmd} {p k : Nat} {r : List Nat}
    (h : r ∈ slotRuns cmds p k) : Cmd.slot p k r ∈ cmds := by
  unfold slotRuns at h
  rw [List.mem_filterMap] at h
  obtain ⟨c, hc, he⟩ := h
  rcases c with ⟨tr, k', run⟩ | ⟨q, run⟩
  · by_cases hb : (tr == p && k' == k) = true
    · simp only [hb, if_true] at he
      cases he
      have h1 : tr = p := by
        have := (Bool.and_eq_true_iff.mp hb).1
        simpa using this
      have h2 : k' = k := by
        have := (Bool.and_eq_true_iff.mp hb).2
        simpa using this
      rw [← h1, ← h2]
      exact hc
    · simp [hb] at he
  · simp at he

theorem endRuns_mem_cmd {cmds : List Cmd} {p : Nat} {r : List Nat}
    (h : r ∈ endRuns cmds p) : Cmd.atEnd p r ∈ cmds := by
  unfold endRuns at h
  rw [List.mem_filterMap] at h
  obtain ⟨c, hc, he⟩ := h
  rcases c with ⟨tr, k', run⟩ | ⟨q, run⟩
  · simp at he
  · by_cases hb : (q == p) = true
    · simp only [hb, if_true] at he
      cases he
      rw [← show q = p from by simpa using hb]
      exact hc
    · simp [hb] at he

/-- Every branch command's run is a segment of one of the branch's *host*
rows (host = root or an L-node). -/
theorem branchCmds_run_host {L X : St} {sk : Skel} {mk : Nat → Bool}
    {c : Cmd} (hc : c ∈ branchCmds L X sk mk) :
    ∃ p, (p = 0 ∨ contains L p = true) ∧
      ∃ x y, row X p = x ++ (cmdRun c ++ y) := by
  unfold branchCmds at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨p, hp, hc⟩ := hc
  rw [List.mem_map] at hc
  obtain ⟨pr, hpr, rfl⟩ := hc
  obtain ⟨x, y, e, -, -⟩ := runsGo_shape (contains L) _ none (row X p) pr hpr
  refine ⟨p, (hosts_mem hp).1, x, y, ?_⟩
  rcases pr with ⟨_ | pre, run, _ | s⟩ <;> exact e

/-- **The address of a merged-row occurrence**: a skeleton entry hosted at
its `wpar`, a command's run element targeted at the row, or a wholesale
born-row element. -/
theorem base_addr {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {u k : Nat}
    (h : u ∈ alGet (outRows L A B) k) :
    (u ∈ read L ∧ wp L A B u = true ∧ wpar L (wp L A B) u = k) ∨
    (contains L u = false ∧ alHas (skelOf L A B).rows k = true ∧
      ∃ c ∈ mergeCmds L A B, u ∈ cmdRun c ∧ cmdTarget c = k) ∨
    (contains L u = false ∧ k ∈ bornIds L A ∧ u ∈ row A k) ∨
    (contains L u = false ∧ k ∈ bornIds L B ∧ u ∈ row B k) := by
  by_cases hk : alHas (skelOf L A B).rows k = true
  · rw [outRows_alGet_of_skel hk] at h
    rcases rowAssemble_content h with hsk | ⟨r, k', hr, hur⟩ | ⟨r, hr, hur⟩
    · rw [skelOf_alGet, List.mem_filter] at hsk
      obtain ⟨hin, hw⟩ := hsk
      rw [List.mem_filter] at hin
      exact Or.inl ⟨hin.1, hin.2, by simpa using hw⟩
    · refine Or.inr (Or.inl ⟨?_, hk, Cmd.slot k k' r, slotRuns_mem_cmd hr,
        hur, rfl⟩)
      rcases List.mem_append.mp (slotRuns_mem_cmd hr) with hc | hc
      · exact (branchCmds_run hc).mem_notL hur
      · exact (branchCmds_run hc).mem_notL hur
    · refine Or.inr (Or.inl ⟨?_, hk, Cmd.atEnd k r, endRuns_mem_cmd hr,
        hur, rfl⟩)
      rcases List.mem_append.mp (endRuns_mem_cmd hr) with hc | hc
      · exact (branchCmds_run hc).mem_notL hur
      · exact (branchCmds_run hc).mem_notL hur
  · by_cases hbA : k ∈ bornIds L A
    · rw [outRows_alGet_of_bornA mok hbA] at h
      refine Or.inr (Or.inr (Or.inl ⟨?_, hbA, h⟩))
      rw [contains_eq_false]
      intro huL
      obtain ⟨-, hkL, hk0⟩ := bornIds_spec mok.wfA hbA
      rcases hA u k huL h with h0 | hL
      · exact hk0 h0
      · exact hkL hL
    · by_cases hbB : k ∈ bornIds L B
      · rw [outRows_alGet_of_bornB mok hbB] at h
        refine Or.inr (Or.inr (Or.inr ⟨?_, hbB, h⟩))
        rw [contains_eq_false]
        intro huL
        obtain ⟨-, hkL, hk0⟩ := bornIds_spec mok.wfB hbB
        rcases hB u k huL h with h0 | hL
        · exact hk0 h0
        · exact hkL hL
      · rw [outRows_alGet_none hk hbA hbB] at h
        exact absurd h (by simp)

/-- **Base count**: every merged row holds each id at most once. -/
theorem base_count1 {L A B : St} (mok : ModelOK L A B) (k u : Nat) :
    (alGet (outRows L A B) k).count u ≤ 1 := by
  by_cases hk : alHas (skelOf L A B).rows k = true
  · rw [outRows_alGet_of_skel hk]
    have hle := rowAssemble_count_le (mergeCmds L A B) k
      (alGet (skelOf L A B).rows k) u
    have hcm := mergeCmds_count mok u
    have hsk : (alGet (skelOf L A B).rows k).count u ≤
        if contains L u = true then 1 else 0 := by
      rw [skelOf_alGet, count_filter', count_filter']
      by_cases hL : contains L u = true
      · rw [if_pos hL]
        have h1 := count_le_one_of_nodup mok.wfL.1 u
        split
        · split
          · exact h1
          · exact Nat.zero_le _
        · exact Nat.zero_le _
      · rw [if_neg hL]
        have h0 : (read L).count u = 0 :=
          List.count_eq_zero.mpr fun hc => hL (contains_iff.mpr hc)
        rw [h0]
        split
        · split <;> exact Nat.le_refl 0
        · exact Nat.le_refl 0
    by_cases hL : contains L u = true
    · rw [if_pos hL] at hsk hcm
      omega
    · rw [if_neg hL] at hsk hcm
      omega
  · by_cases hbA : k ∈ bornIds L A
    · rw [outRows_alGet_of_bornA mok hbA]
      exact Nat.le_trans (row_count_le A k u)
        (count_le_one_of_nodup mok.wfA.1 u)
    · by_cases hbB : k ∈ bornIds L B
      · rw [outRows_alGet_of_bornB mok hbB]
        exact Nat.le_trans (row_count_le B k u)
          (count_le_one_of_nodup mok.wfB.1 u)
      · rw [outRows_alGet_none hk hbA hbB]
        exact Nat.zero_le _

/-- A command's run element lives in a host row of its own branch — packaged
for the uniqueness argument. -/
theorem mergeCmds_elem_row {L A B : St} (mok : ModelOK L A B) {c : Cmd}
    (hc : c ∈ mergeCmds L A B) {u : Nat} (hu : u ∈ cmdRun c)
    (hnL : contains L u = false) :
    (∃ p, (p = 0 ∨ contains L p = true) ∧ u ∈ row A p ∧ u ∈ read A) ∨
    (∃ p, (p = 0 ∨ contains L p = true) ∧ u ∈ row B p ∧ u ∈ read B) := by
  rcases List.mem_append.mp hc with hcA | hcB
  · obtain ⟨p, hp, x, y, e⟩ := branchCmds_run_host hcA
    have hrow : u ∈ row A p := by
      rw [e]
      simp [hu]
    exact Or.inl ⟨p, hp, hrow, mem_row_read hrow⟩
  · obtain ⟨p, hp, x, y, e⟩ := branchCmds_run_host hcB
    have hrow : u ∈ row B p := by
      rw [e]
      simp [hu]
    exact Or.inr ⟨p, hp, hrow, mem_row_read hrow⟩

/-- **Base uniqueness**: an id occurs in at most one merged row. -/
theorem base_unique {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {u k₁ k₂ : Nat}
    (h₁ : u ∈ alGet (outRows L A B) k₁)
    (h₂ : u ∈ alGet (outRows L A B) k₂) : k₁ = k₂ := by
  have hnLiff : ∀ {hL : contains L u = false}, u ∉ read L :=
    fun {hL} => contains_eq_false.mp hL
  -- the pattern-8 helper: a non-L id cannot be live in both branches
  have h8 : contains L u = false → u ∈ read A → u ∈ read B → False :=
    fun hnL hA' hB' => contains_eq_false.mp hnL (mok.common u hA' hB')
  rcases base_addr mok hA hB h₁ with
    ⟨hL₁, hw₁, hk₁⟩ | ⟨hnL₁, -, c₁, hc₁, hu₁, ht₁⟩ |
    ⟨hnL₁, hb₁, hr₁⟩ | ⟨hnL₁, hb₁, hr₁⟩ <;>
  rcases base_addr mok hA hB h₂ with
    ⟨hL₂, hw₂, hk₂⟩ | ⟨hnL₂, -, c₂, hc₂, hu₂, ht₂⟩ |
    ⟨hnL₂, hb₂, hr₂⟩ | ⟨hnL₂, hb₂, hr₂⟩
  -- (1,1): both skeleton entries — hosted at the same wpar
  · rw [← hk₁, ← hk₂]
  -- (1,2..4): u ∈ L vs u ∉ L
  · exact absurd hL₁ (contains_eq_false.mp hnL₂)
  · exact absurd hL₁ (contains_eq_false.mp hnL₂)
  · exact absurd hL₁ (contains_eq_false.mp hnL₂)
  · exact absurd hL₂ (contains_eq_false.mp hnL₁)
  -- (2,2): two command occurrences — same command, else the global count
  -- bound is violated
  · rcases Classical.em (c₁ = c₂) with he | hne
    · rw [← ht₁, ← ht₂, he]
    · have hcm := mergeCmds_count mok u
      rw [if_neg (by simp [hnL₁])] at hcm
      have h2le := two_mem_le (fun c => (cmdRun c).count u) hc₁ hc₂ hne
      dsimp only at h2le
      have hp₁ : 0 < (cmdRun c₁).count u := List.count_pos_iff.mpr hu₁
      have hp₂ : 0 < (cmdRun c₂).count u := List.count_pos_iff.mpr hu₂
      omega
  -- (2,3): a command occurrence vs an A-born wholesale row
  · obtain ⟨-, hkL₂, hk0₂⟩ := bornIds_spec mok.wfA hb₂
    rcases mergeCmds_elem_row mok hc₁ hu₁ hnL₁ with
      ⟨p, hp, hrow, -⟩ | ⟨p, hp, -, hmemB⟩
    · have hpk : p = k₂ := by
        by_cases hpe : p = k₂
        · exact hpe
        · exact (row_disjoint mok.wfA hpe hrow hr₂).elim
      rcases hpk ▸ hp with h0 | hL
      · exact absurd h0 hk0₂
      · exact absurd (contains_iff.mp hL) hkL₂
    · exact (h8 hnL₁ (mem_row_read hr₂) hmemB).elim
  -- (2,4): a command occurrence vs a B-born wholesale row
  · obtain ⟨-, hkL₂, hk0₂⟩ := bornIds_spec mok.wfB hb₂
    rcases mergeCmds_elem_row mok hc₁ hu₁ hnL₁ with
      ⟨p, hp, -, hmemA⟩ | ⟨p, hp, hrow, -⟩
    · exact (h8 hnL₁ hmemA (mem_row_read hr₂)).elim
    · have hpk : p = k₂ := by
        by_cases hpe : p = k₂
        · exact hpe
        · exact (row_disjoint mok.wfB hpe hrow hr₂).elim
      rcases hpk ▸ hp with h0 | hL
      · exact absurd h0 hk0₂
      · exact absurd (contains_iff.mp hL) hkL₂
  -- (3,1)
  · exact absurd hL₂ (contains_eq_false.mp hnL₁)
  -- (3,2): mirror of (2,3)
  · obtain ⟨-, hkL₁, hk0₁⟩ := bornIds_spec mok.wfA hb₁
    rcases mergeCmds_elem_row mok hc₂ hu₂ hnL₂ with
      ⟨p, hp, hrow, -⟩ | ⟨p, hp, -, hmemB⟩
    · have hpk : p = k₁ := by
        by_cases hpe : p = k₁
        · exact hpe
        · exact (row_disjoint mok.wfA hpe hrow hr₁).elim
      rcases hpk ▸ hp with h0 | hL
      · exact absurd h0 hk0₁
      · exact absurd (contains_iff.mp hL) hkL₁
    · exact (h8 hnL₁ (mem_row_read hr₁) hmemB).elim
  -- (3,3): two A-rows — disjointness
  · by_cases hpe : k₁ = k₂
    · exact hpe
    · exact (row_disjoint mok.wfA hpe hr₁ hr₂).elim
  -- (3,4): live in both branches
  · exact (h8 hnL₁ (mem_row_read hr₁) (mem_row_read hr₂)).elim
  -- (4,1)
  · exact absurd hL₂ (contains_eq_false.mp hnL₁)
  -- (4,2): mirror of (2,4)
  · obtain ⟨-, hkL₁, hk0₁⟩ := bornIds_spec mok.wfB hb₁
    rcases mergeCmds_elem_row mok hc₂ hu₂ hnL₂ with
      ⟨p, hp, -, hmemA⟩ | ⟨p, hp, hrow, -⟩
    · exact (h8 hnL₁ hmemA (mem_row_read hr₁)).elim
    · have hpk : p = k₁ := by
        by_cases hpe : p = k₁
        · exact hpe
        · exact (row_disjoint mok.wfB hpe hrow hr₁).elim
      rcases hpk ▸ hp with h0 | hL
      · exact absurd h0 hk0₁
      · exact absurd (contains_iff.mp hL) hkL₁
  -- (4,3): live in both branches
  · exact (h8 hnL₁ (mem_row_read hr₂) (mem_row_read hr₁)).elim
  -- (4,4): two B-rows — disjointness
  · by_cases hpe : k₁ = k₂
    · exact hpe
    · exact (row_disjoint mok.wfB hpe hr₁ hr₂).elim

/-! ## §4 The marker splice: placement, chains, fuel adequacy -/

/-- Markers are live L-nodes in the working set. -/
theorem marker_spec {L A B : St} {u : Nat} (h : markerp L A B u = true) :
    u ∈ read L ∧ wp L A B u = true := by
  rw [markerp, Bool.and_eq_true_iff] at h
  exact ⟨contains_iff.mp h.1, by rw [wp]; simp [markerp, h.1, h.2]⟩

theorem markerp_zero {L A B : St} (hwf : WF L) :
    markerp L A B 0 = false := by
  rw [markerp, bool_eq_false (fun hc => hwf.2 (contains_iff.mp hc))]
  rfl

theorem depthOf_absent {s : St} {u : Nat} (h : u ∉ read s) :
    depthOf s u = 0 := by
  rw [depthOf, depthF_eq_none h]
  rfl

mutual
  theorem parT_eq_none (u cur : Nat) :
      ∀ t : Tree, u ∉ readT t → parT cur u t = none
    | .node i cs, h => by
        rw [parT, if_neg (show ¬ i = u from fun e =>
          h (by rw [readT, e]; exact List.mem_cons_self ..))]
        exact parF_eq_none u i cs fun hm =>
          h (by rw [readT]; exact List.mem_cons_of_mem _ hm)
  theorem parF_eq_none (u cur : Nat) :
      ∀ ts : List Tree, u ∉ readF ts → parF cur u ts = none
    | [], _ => rfl
    | t :: ts, h => by
        rw [parF_cons_none (parT_eq_none u cur t fun hm =>
          h (by rw [readF, List.mem_append]; exact Or.inl hm))]
        exact parF_eq_none u cur ts fun hm =>
          h (by rw [readF, List.mem_append]; exact Or.inr hm)
end

theorem parOf_absent {s : St} {u : Nat} (h : u ∉ read s) : parOf s u = 0 := by
  rw [parOf, parF_eq_none u 0 s h]
  rfl

/-- `wpar` fixes the root. -/
theorem wpar_zero {L : St} (hwf : WF L) (W : Nat → Bool) :
    wpar L W 0 = 0 := by
  rw [wpar, parOf_absent hwf.2, wparGo_zero]

/-! ### Key existence: placed nodes and their hosts are skeleton keys -/

theorem alApp_keys_super {al : List (Nat × List Nat)} {k v x : Nat}
    (hx : x ∈ al.map (·.1)) : x ∈ (alApp al k v).map (·.1) := by
  rw [alApp_keys]
  split
  · exact hx
  · exact List.mem_append.mpr (Or.inl hx)

theorem alEnsure_keys_super {al : List (Nat × List Nat)} {k x : Nat}
    (hx : x ∈ al.map (·.1)) : x ∈ (alEnsure al k).map (·.1) := by
  rw [alEnsure_keys]
  split
  · exact hx
  · exact List.mem_append.mpr (Or.inl hx)

theorem alApp_keys_self (al : List (Nat × List Nat)) (k v : Nat) :
    k ∈ (alApp al k v).map (·.1) := by
  rw [alApp_keys]
  by_cases h : alHas al k = true
  · rw [if_pos h]
    exact alHas_iff_mem_keys.mp h
  · rw [if_neg h]
    exact List.mem_append.mpr (Or.inr (by simp))

theorem alEnsure_keys_self (al : List (Nat × List Nat)) (k : Nat) :
    k ∈ (alEnsure al k).map (·.1) := by
  rw [alEnsure_keys]
  by_cases h : alHas al k = true
  · rw [if_pos h]
    exact alHas_iff_mem_keys.mp h
  · rw [if_neg h]
    exact List.mem_append.mpr (Or.inr (by simp))

theorem skelFold_keys_super (h : Nat → Nat) :
    ∀ (l : List Nat) (sk : Skel) (x : Nat),
      (x ∈ sk.rows.map (·.1) ∨ x ∈ l ∨ x ∈ l.map h) →
      x ∈ ((l.foldl (fun sk u =>
          { rows := alEnsure (alApp sk.rows (h u) u) u
            rowof := sk.rowof ++ [(u, h u)] }) sk).rows).map (·.1)
  | [], sk, x, hx => by
      rcases hx with hx | hx | hx
      · exact hx
      · exact absurd hx (by simp)
      · exact absurd hx (by simp)
  | u :: l, sk, x, hx => by
      rw [List.foldl_cons]
      refine skelFold_keys_super h l _ x ?_
      dsimp only
      rcases hx with hx | hx | hx
      · exact Or.inl (alEnsure_keys_super (alApp_keys_super hx))
      · rcases List.mem_cons.mp hx with he | hx
        · rw [he]
          exact Or.inl (alEnsure_keys_self _ u)
        · exact Or.inr (Or.inl hx)
      · rw [List.map_cons] at hx
        rcases List.mem_cons.mp hx with he | hx
        · rw [he]
          exact Or.inl (alEnsure_keys_super
            (alApp_keys_self sk.rows (h u) u))
        · exact Or.inr (Or.inr hx)

/-- Every placed node is a skeleton key. -/
theorem skelOf_alHas_of_placed {L A B : St} {u : Nat}
    (hu : u ∈ (read L).filter (wp L A B)) :
    alHas (skelOf L A B).rows u = true := by
  rw [alHas_iff_mem_keys]
  simp only [skelOf]
  exact skelFold_keys_super _ _ _ u (Or.inr (Or.inl hu))

/-- Every placed node's host is a skeleton key. -/
theorem skelOf_alHas_host {L A B : St} {u : Nat}
    (hu : u ∈ (read L).filter (wp L A B)) :
    alHas (skelOf L A B).rows (wpar L (wp L A B) u) = true := by
  rw [alHas_iff_mem_keys]
  simp only [skelOf]
  exact skelFold_keys_super _ _ _ _
    (Or.inr (Or.inr (List.mem_map.mpr ⟨u, hu, rfl⟩)))

/-- Skeleton entries survive assembly (runs only interleave around them). -/
theorem mem_rowAssemble_of_skel {cmds : List Cmd} {p : Nat}
    {skelRow : List Nat} {u : Nat} (hu : u ∈ skelRow) :
    u ∈ rowAssemble cmds p skelRow := by
  have h1 : 0 < skelRow.count u := List.count_pos_iff.mpr hu
  have h2 := rowAssemble_count cmds p skelRow u
  exact List.count_pos_iff.mp (by omega)

/-- **Marker placement**: a marker occurs in its host's merged row… -/
theorem marker_in_host_row {L A B : St} (mok : ModelOK L A B) {m : Nat}
    (hm : markerp L A B m = true) :
    m ∈ alGet (outRows L A B) (wpar L (wp L A B) m) := by
  obtain ⟨hmL, hmw⟩ := marker_spec hm
  have hplaced : m ∈ (read L).filter (wp L A B) :=
    List.mem_filter.mpr ⟨hmL, hmw⟩
  rw [outRows_alGet_of_skel (skelOf_alHas_host hplaced)]
  refine mem_rowAssemble_of_skel ?_
  rw [skelOf_alGet]
  exact List.mem_filter.mpr ⟨hplaced, by simp⟩

/-- …and only there. -/
theorem marker_row_key {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {m k : Nat}
    (hm : markerp L A B m = true)
    (hk : m ∈ alGet (outRows L A B) k) : k = wpar L (wp L A B) m := by
  rcases base_addr mok hA hB hk with ⟨-, -, hw⟩ | ⟨hnL, -, -⟩ | ⟨hnL, -⟩ |
    ⟨hnL, -⟩
  · exact hw.symm
  all_goals simp [contains_iff.mpr (marker_spec hm).1] at hnL

/-- A marker in a merged row sits under its `wpar`, strictly shallower. -/
theorem marker_in_row_deeper {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {c k : Nat}
    (hcm : markerp L A B c = true) (hc : c ∈ alGet (outRows L A B) k) :
    k = 0 ∨ (k ∈ read L ∧ depthOf L k < depthOf L c) := by
  have hk := marker_row_key mok hA hB hcm hc
  rcases wpar_spec mok.wfL (wp L A B) (marker_spec hcm).1 with h0 | ⟨hm, -, hd⟩
  · exact Or.inl (hk.trans h0)
  · refine Or.inr ?_
    rw [hk]
    exact ⟨hm, hd⟩

/-- **Fuel adequacy**: with a depth's worth of fuel, the splice eliminates
every marker (splice chains descend strictly in L-depth). -/
theorem expandRow_marker_free {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) :
    ∀ (fuel d : Nat) (r : List Nat),
      (read L).length < fuel + d →
      (∀ m ∈ r, markerp L A B m = true → m ∈ read L ∧ d ≤ depthOf L m) →
      ∀ u ∈ expandRow (outRows L A B) (markerp L A B) fuel r,
        markerp L A B u = false
  | 0, d, r, hbud, hr, u, hu => by
      rw [expandRow] at hu
      by_cases hm : markerp L A B u = true
      · obtain ⟨hmem, hd⟩ := hr u hu hm
        have := depthOf_lt_length hmem
        omega
      · exact bool_eq_false hm
  | fuel + 1, d, r, hbud, hr, u, hu => by
      rw [expandRow, List.mem_flatMap] at hu
      obtain ⟨v, hv, hu⟩ := hu
      by_cases hmv : markerp L A B v = true
      · rw [if_pos hmv] at hu
        obtain ⟨hvL, hvd⟩ := hr v hv hmv
        refine expandRow_marker_free mok hA hB fuel (depthOf L v + 1)
          (alGet (outRows L A B) v) (by omega) ?_ u hu
        intro m hm hmm
        rcases marker_in_row_deeper mok hA hB hmm hm with h0 | ⟨-, hd⟩
        · rw [h0, markerp_zero mok.wfL] at hmv
          cases hmv
        · exact ⟨(marker_spec hmm).1, by omega⟩
      · rw [if_neg hmv] at hu
        rcases List.mem_singleton.mp hu with rfl
        exact bool_eq_false hmv

/-- The merged rows expand marker-free under the merge's own fuel. -/
theorem expandRow_out_marker_free {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {fuel : Nat}
    (hfuel : (read L).length < fuel) (k : Nat) :
    ∀ u ∈ expandRow (outRows L A B) (markerp L A B) fuel
        (alGet (outRows L A B) k),
      markerp L A B u = false :=
  expandRow_marker_free mok hA hB fuel 0 _ (by omega)
    (fun m _ hm => ⟨(marker_spec hm).1, Nat.zero_le _⟩)

/-! ### Splice chains: where an expanded occurrence comes from -/

/-- `u`'s row is reachable from key `k` through marker splices. -/
inductive SpliceReach (L A B : St) (u : Nat) : Nat → Prop where
  | base {k} : u ∈ alGet (outRows L A B) k → SpliceReach L A B u k
  | step {k m} : markerp L A B m = true → m ∈ alGet (outRows L A B) k →
      SpliceReach L A B u m → SpliceReach L A B u k

/-- Iterated attach-deep host. -/
def wparIter (L A B : St) : Nat → Nat → Nat
  | 0, b => b
  | j + 1, b => wpar L (wp L A B) (wparIter L A B j b)

theorem expandRow_spliceReach {L A B : St} {u : Nat} :
    ∀ (fuel : Nat) (k : Nat),
      u ∈ expandRow (outRows L A B) (markerp L A B) fuel
        (alGet (outRows L A B) k) →
      SpliceReach L A B u k
  | 0, k, hu => .base (by rwa [expandRow] at hu)
  | fuel + 1, k, hu => by
      rw [expandRow, List.mem_flatMap] at hu
      obtain ⟨v, hv, hu⟩ := hu
      by_cases hmv : markerp L A B v = true
      · rw [if_pos hmv] at hu
        exact .step hmv hv (expandRow_spliceReach fuel v hu)
      · rw [if_neg hmv] at hu
        rcases List.mem_singleton.mp hu with rfl
        exact .base hv

/-- Chain form: reachability is an iterated-`wpar` ascent from the base
row, through markers. -/
theorem spliceReach_chain {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {u k : Nat}
    (h : SpliceReach L A B u k) :
    ∃ b j, u ∈ alGet (outRows L A B) b ∧ k = wparIter L A B j b ∧
      ∀ i, i < j → markerp L A B (wparIter L A B i b) = true := by
  induction h with
  | base hb =>
      exact ⟨_, 0, hb, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | step hm hmk _ ih =>
      obtain ⟨b, j, hb, he, hint⟩ := ih
      refine ⟨b, j + 1, hb, ?_, ?_⟩
      · rw [wparIter, ← he]
        exact marker_row_key mok hA hB hm hmk
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · exact hint i hlt
        · rw [heq, ← he]
          exact hm

/-- One `wpar` step off a marker: the root, or strictly shallower. -/
theorem wpar_step' {L A B : St} (mok : ModelOK L A B) {b i : Nat}
    (hmi : markerp L A B (wparIter L A B i b) = true) :
    wparIter L A B (i + 1) b = 0 ∨
      (wparIter L A B (i + 1) b ∈ read L ∧
        depthOf L (wparIter L A B (i + 1) b) <
          depthOf L (wparIter L A B i b)) := by
  rcases wpar_spec mok.wfL (wp L A B) (marker_spec hmi).1 with h0 |
    ⟨hm, -, hd⟩
  · exact Or.inl (by rw [wparIter]; exact h0)
  · exact Or.inr (by rw [wparIter]; exact ⟨hm, hd⟩)

theorem chain_step_lt {L A B : St} (mok : ModelOK L A B) {b i : Nat}
    (hmi : markerp L A B (wparIter L A B i b) = true)
    (hmi1 : markerp L A B (wparIter L A B (i + 1) b) = true) :
    depthOf L (wparIter L A B (i + 1) b) <
      depthOf L (wparIter L A B i b) := by
  rcases wpar_step' mok hmi with h0 | ⟨-, hd⟩
  · rw [h0, markerp_zero mok.wfL] at hmi1
    cases hmi1
  · exact hd

/-- Along an all-marker stretch of the ascent, depth strictly decreases. -/
theorem chain_depth_lt {L A B : St} (mok : ModelOK L A B) (b : Nat) :
    ∀ (i₂ i₁ : Nat), i₁ < i₂ →
      (∀ i, i₁ ≤ i → i ≤ i₂ → markerp L A B (wparIter L A B i b) = true) →
      depthOf L (wparIter L A B i₂ b) < depthOf L (wparIter L A B i₁ b)
  | 0, i₁, h, _ => absurd h (Nat.not_lt_zero i₁)
  | i + 1, i₁, h, hm => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
      · have h1 := chain_depth_lt mok b i i₁ hlt
          (fun j hj1 hj2 => hm j hj1 (Nat.le_succ_of_le hj2))
        have h2 := chain_step_lt mok (b := b) (i := i)
          (hm i (Nat.le_of_lt hlt) (Nat.le_succ i))
          (hm (i + 1) (by omega) (Nat.le_refl _))
        omega
      · subst heq
        exact chain_step_lt mok (hm i₁ (Nat.le_refl _) (Nat.le_succ _))
          (hm (i₁ + 1) (Nat.le_succ _) (Nat.le_refl _))

/-- A marker never sits in its own merged row. -/
theorem marker_not_self_row {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {m : Nat}
    (hm : markerp L A B m = true)
    (hself : m ∈ alGet (outRows L A B) m) : False := by
  have hk := marker_row_key mok hA hB hm hself
  rcases wpar_spec mok.wfL (wp L A B) (marker_spec hm).1 with h0 | ⟨-, -, hd⟩
  · rw [hk, h0, markerp_zero mok.wfL] at hm
    cases hm
  · rw [← hk] at hd
    omega

/-- **Emitter uniqueness** (H2): a non-marker id's row is spliced into
exactly one non-marker key's expansion. -/
theorem spliceReach_nonmarker_unique {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {u q₁ q₂ : Nat}
    (h₁ : SpliceReach L A B u q₁) (h₂ : SpliceReach L A B u q₂)
    (hn₁ : markerp L A B q₁ = false) (hn₂ : markerp L A B q₂ = false) :
    q₁ = q₂ := by
  obtain ⟨b₁, j₁, hb₁, he₁, hint₁⟩ := spliceReach_chain mok hA hB h₁
  obtain ⟨b₂, j₂, hb₂, he₂, hint₂⟩ := spliceReach_chain mok hA hB h₂
  have hbb : b₁ = b₂ := base_unique mok hA hB hb₁ hb₂
  subst hbb
  rcases Nat.lt_trichotomy j₁ j₂ with hlt | heq | hgt
  · have hmark := hint₂ j₁ hlt
    rw [← he₁, hn₁] at hmark
    cases hmark
  · rw [he₁, he₂, heq]
  · have hmark := hint₁ j₂ hgt
    rw [← he₂, hn₂] at hmark
    cases hmark

/-- A marker with `SpliceReach` to `u` climbing back into its own row's
key is impossible: interior of a `wpar` cycle. -/
theorem chain_no_cycle {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {b : Nat} {j₁ j₂ : Nat}
    (hlt : j₁ < j₂)
    (hint : ∀ i, i < j₂ → markerp L A B (wparIter L A B i b) = true)
    (hj₂ : markerp L A B (wparIter L A B j₂ b) = true)
    (hkey : wparIter L A B (j₁ + 1) b =
      wpar L (wp L A B) (wparIter L A B j₂ b)) : False := by
  rcases Nat.lt_or_ge (j₁ + 1) j₂ with hlt2 | hge
  · -- strictly interior: depth of the top of the stretch beats its own wpar
    have hdlt : depthOf L (wparIter L A B j₂ b) <
        depthOf L (wparIter L A B (j₁ + 1) b) :=
      chain_depth_lt mok b j₂ (j₁ + 1) hlt2 (fun i h1 h2 => by
        rcases Nat.lt_or_ge i j₂ with h | h
        · exact hint i h
        · rw [Nat.le_antisymm h2 h]
          exact hj₂)
    rcases wpar_step' mok hj₂ with h0 | ⟨-, hd⟩
    · -- wpar of the j₂ marker is 0 = the (j₁+1) element, itself a marker
      rw [wparIter] at h0
      have hz : wparIter L A B (j₁ + 1) b = 0 := hkey.trans h0
      have hmk := hint (j₁ + 1) hlt2
      rw [hz, markerp_zero mok.wfL] at hmk
      cases hmk
    · rw [wparIter] at hd
      rw [← hkey] at hd
      omega
  · -- j₂ = j₁ + 1: the marker sits in its own row's key
    have he : j₂ = j₁ + 1 := Nat.le_antisymm hge (Nat.succ_le_of_lt hlt)
    subst he
    -- wparIter (j₁+1) b = wpar (wparIter (j₁+1) b): self-wpar
    rcases wpar_spec mok.wfL (wp L A B)
      (marker_spec hj₂).1 with h0 | ⟨-, -, hd⟩
    · rw [← hkey] at h0
      rw [h0, markerp_zero mok.wfL] at hj₂
      cases hj₂
    · rw [← hkey] at hd
      omega

/-- **Contributor uniqueness**: within one merged row, at most one element
carries `u` in its splice closure. -/
theorem contributor_unique {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {u k : Nat}
    {v₁ v₂ : Nat} (hv₁ : v₁ ∈ alGet (outRows L A B) k)
    (hv₂ : v₂ ∈ alGet (outRows L A B) k)
    (hc₁ : v₁ = u ∨ (markerp L A B v₁ = true ∧ SpliceReach L A B u v₁))
    (hc₂ : v₂ = u ∨ (markerp L A B v₂ = true ∧ SpliceReach L A B u v₂)) :
    v₁ = v₂ := by
  -- symmetric helper: a direct occurrence vs a spliced one is impossible
  have key : ∀ v w : Nat, v ∈ alGet (outRows L A B) k →
      w ∈ alGet (outRows L A B) k → v = u →
      markerp L A B w = true → SpliceReach L A B u w → False := by
    intro v w hv hw hvu hwm hwr
    obtain ⟨b, j, hb, he, hint⟩ := spliceReach_chain mok hA hB hwr
    have hbk : b = k := base_unique mok hA hB hb (hvu ▸ hv)
    subst hbk
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0] at he
      have hwb : w = b := he
      exact marker_not_self_row mok hA hB hwm (hwb.symm ▸ hw)
    · -- w's wpar closes a cycle back onto the base key b
      have hcyc : wparIter L A B (j + 1) b = b := by
        show wpar L (wp L A B) (wparIter L A B j b) = b
        rw [← he]
        exact (marker_row_key mok hA hB hwm hw).symm
      have hmall : ∀ i, 0 ≤ i → i ≤ j + 1 →
          markerp L A B (wparIter L A B i b) = true := by
        intro i _ hi
        rcases Nat.lt_or_ge i j with h | h
        · exact hint i h
        · rcases Nat.eq_or_lt_of_le h with hij | h2
          · rw [← hij, ← he]
            exact hwm
          · have hij1 : i = j + 1 := by omega
            rw [hij1, hcyc]
            exact hint 0 hjpos
      have hdlt := chain_depth_lt mok b (j + 1) 0 (Nat.succ_pos j)
        (fun i h1 h2 => hmall i h1 h2)
      rw [hcyc, show wparIter L A B 0 b = b from rfl] at hdlt
      omega
  rcases hc₁ with hvu₁ | ⟨hm₁, hr₁⟩
  · rcases hc₂ with hvu₂ | ⟨hm₂, hr₂⟩
    · rw [hvu₁, hvu₂]
    · exact (key v₁ v₂ hv₁ hv₂ hvu₁ hm₂ hr₂).elim
  · rcases hc₂ with hvu₂ | ⟨hm₂, hr₂⟩
    · exact (key v₂ v₁ hv₂ hv₁ hvu₂ hm₁ hr₁).elim
    · -- both markers: same base, same wpar target — same chain index
      obtain ⟨b₁, j₁, hb₁, he₁, hint₁⟩ := spliceReach_chain mok hA hB hr₁
      obtain ⟨b₂, j₂, hb₂, he₂, hint₂⟩ := spliceReach_chain mok hA hB hr₂
      have hbb : b₁ = b₂ := base_unique mok hA hB hb₁ hb₂
      subst hbb
      rcases Nat.lt_trichotomy j₁ j₂ with hlt | heq | hgt
      · -- v₁ deeper index: k = wpar v₁ closes a cycle against v₂'s stretch
        refine (chain_no_cycle mok hA hB (b := b₁) (j₁ := j₁) (j₂ := j₂)
          hlt ?_ (he₂ ▸ hm₂) ?_).elim
        · intro i hi
          exact hint₂ i hi
        · rw [show wparIter L A B (j₁ + 1) b₁ =
              wpar L (wp L A B) (wparIter L A B j₁ b₁) from rfl, ← he₁, ← he₂,
            (marker_row_key mok hA hB hm₁ hv₁ :
              k = wpar L (wp L A B) v₁).symm,
            (marker_row_key mok hA hB hm₂ hv₂ :
              k = wpar L (wp L A B) v₂)]
      · rw [he₁, he₂, heq]
      · refine (chain_no_cycle mok hA hB (b := b₁) (j₁ := j₂) (j₂ := j₁)
          hgt ?_ (he₁ ▸ hm₁) ?_).elim
        · intro i hi
          exact hint₁ i hi
        · rw [show wparIter L A B (j₂ + 1) b₁ =
              wpar L (wp L A B) (wparIter L A B j₂ b₁) from rfl, ← he₂, ← he₁,
            (marker_row_key mok hA hB hm₂ hv₂ :
              k = wpar L (wp L A B) v₂).symm,
            (marker_row_key mok hA hB hm₁ hv₁ :
              k = wpar L (wp L A B) v₁)]

theorem sum_ite_count (w : Nat) :
    ∀ l : List Nat,
      (l.map (fun v => if w == v then 1 else 0)).sum = l.count w
  | [] => rfl
  | a :: l => by
      rw [List.map_cons, List.sum_cons, sum_ite_count w l, List.count_cons]
      by_cases h : w = a
      · rw [if_pos (by simp [h]), if_pos (by simp [h])]
        omega
      · rw [if_neg (by simp [h]),
          if_neg (show ¬ ((a == w) = true) from by
            simp only [beq_iff_eq]
            exact fun e => h e.symm)]
        omega

/-- **H1**: a key's expansion holds each id at most once. -/
theorem expandRow_count_le_one {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) (u : Nat) :
    ∀ (fuel k : Nat),
      (expandRow (outRows L A B) (markerp L A B) fuel
        (alGet (outRows L A B) k)).count u ≤ 1
  | 0, k => by
      rw [expandRow]
      exact base_count1 mok k u
  | fuel + 1, k => by
      rw [expandRow, count_flatMap]
      by_cases hex : ∃ w, w ∈ alGet (outRows L A B) k ∧
          (w = u ∨ (markerp L A B w = true ∧ SpliceReach L A B u w))
      · obtain ⟨w, hwmem, hw⟩ := hex
        have hpt : ∀ v ∈ alGet (outRows L A B) k,
            ((if markerp L A B v = true then
                expandRow (outRows L A B) (markerp L A B) fuel
                  (alGet (outRows L A B) v)
              else [v]).count u) ≤ if w == v then 1 else 0 := by
          intro v hv
          by_cases hmv : markerp L A B v = true
          · rw [if_pos hmv]
            by_cases hz : (expandRow (outRows L A B) (markerp L A B) fuel
                (alGet (outRows L A B) v)).count u = 0
            · rw [hz]
              exact Nat.zero_le _
            · have hmem : u ∈ expandRow (outRows L A B) (markerp L A B) fuel
                  (alGet (outRows L A B) v) :=
                List.count_pos_iff.mp (Nat.pos_of_ne_zero hz)
              have hveq : v = w := contributor_unique mok hA hB hv hwmem
                (Or.inr ⟨hmv, expandRow_spliceReach fuel v hmem⟩) hw
              rw [if_pos (show (w == v) = true by simp [hveq])]
              exact expandRow_count_le_one mok hA hB u fuel v
          · rw [if_neg hmv]
            by_cases hvu : v = u
            · have hveq : v = w := contributor_unique mok hA hB hv hwmem
                (Or.inl hvu) hw
              rw [if_pos (show (w == v) = true by simp [hveq])]
              have := List.count_le_length (l := [v]) (a := u)
              simpa using this
            · have hz : ([v] : List Nat).count u = 0 := by
                rw [List.count_eq_zero]
                intro hc
                exact hvu (List.mem_singleton.mp hc).symm
              rw [hz]
              exact Nat.zero_le _
        exact Nat.le_trans (sum_le_sum' hpt)
          (Nat.le_trans (Nat.le_of_eq (sum_ite_count w _))
            (base_count1 mok k w))
      · refine Nat.le_trans (Nat.le_of_eq (sum_eq_zero' fun x hx => ?_))
          (by omega)
        rw [List.mem_map] at hx
        obtain ⟨v, hv, he⟩ := hx
        rw [← he]
        by_cases hmv : markerp L A B v = true
        · rw [if_pos hmv]
          by_cases hz : (expandRow (outRows L A B) (markerp L A B) fuel
              (alGet (outRows L A B) v)).count u = 0
          · exact hz
          · exact absurd ⟨v, hv, Or.inr ⟨hmv, expandRow_spliceReach fuel v
              (List.count_pos_iff.mp (Nat.pos_of_ne_zero hz))⟩⟩ hex
        · rw [if_neg hmv]
          by_cases hvu : v = u
          · exact absurd ⟨v, hv, Or.inl hvu⟩ hex
          · rw [List.count_eq_zero]
            intro hc
            exact hvu (List.mem_singleton.mp hc).symm

end Shesha
