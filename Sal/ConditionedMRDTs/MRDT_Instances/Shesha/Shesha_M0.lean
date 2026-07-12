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
    (contains L u = false ∧
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
    · refine Or.inr (Or.inl ⟨?_, Cmd.slot k k' r, slotRuns_mem_cmd hr,
        hur, rfl⟩)
      rcases List.mem_append.mp (slotRuns_mem_cmd hr) with hc | hc
      · exact (branchCmds_run hc).mem_notL hur
      · exact (branchCmds_run hc).mem_notL hur
    · refine Or.inr (Or.inl ⟨?_, Cmd.atEnd k r, endRuns_mem_cmd hr,
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
    ⟨hL₁, hw₁, hk₁⟩ | ⟨hnL₁, c₁, hc₁, hu₁, ht₁⟩ |
    ⟨hnL₁, hb₁, hr₁⟩ | ⟨hnL₁, hb₁, hr₁⟩ <;>
  rcases base_addr mok hA hB h₂ with
    ⟨hL₂, hw₂, hk₂⟩ | ⟨hnL₂, c₂, hc₂, hu₂, ht₂⟩ |
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

end Shesha
