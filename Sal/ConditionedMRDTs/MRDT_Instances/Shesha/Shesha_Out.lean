import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_EffFold

/-! # Shesha — output rows and the forest builder (phase 2g)

The two missing *generic* engines feeding the pre-splice obligation
(`shesha_presplice`, `Shesha_Cond.lean`):

* §1–§2 **the output row characterization**: in a duplicate-free built
  forest (`buildF`) with a level grading, every emitted key's row is the
  expansion of its stored row — instantiated to the ternary merge
  (`merge_row`): `row (merge L A B) q = expandRow … (alGet (outRows …) q)`
  at every displayed `q` (and the root). This converts obligation (d)'s
  RHS rows into the `outRows`/`expandRow` language of M0–M2.
* §4–§6 **the forest builder**: the pre-splice forest `T` is
  `buildF preRows … 0` over an id-graded row store (anchors precede
  children — Lamport). Its reads/rows are the store (`build_row_raw`),
  it is WF (`build_WF_raw`), and its delete-collapse rows are marker
  expansions of the store (`build_front_raw` + `expand_stable`): the
  state-level obligation (d) reduces to per-key row equations between
  two `expandRow`s. -/

namespace Shesha

/-! ## §1 plumbing: rows over built forests -/

theorem expandRow_nil {rows : List (Nat × List Nat)} {mk : Nat → Bool} :
    ∀ f : Nat, expandRow rows mk f [] = []
  | 0 => rfl
  | _ + 1 => rfl

theorem map_topId_node (g : Nat → List Tree) :
    ∀ l : List Nat, (l.map (fun c => Tree.node c (g c))).map topId = l
  | [] => rfl
  | c :: l => by
      rw [List.map_cons, List.map_cons, map_topId_node g l]
      rfl

/-- The top ids of a built forest are its key's expanded row. -/
theorem topIds_buildF (rows : List (Nat × List Nat)) (mk : Nat → Bool)
    (mf : Nat) (f p : Nat) :
    (buildF rows mk mf (f + 1) p).map topId
      = expandRow rows mk mf (alGet rows p) := by
  rw [buildF, map_topId_node]

/-- Each tree of a duplicate-free forest reads duplicate-free. -/
theorem nodup_readT_of_mem :
    ∀ {F : List Tree} {t : Tree}, (readF F).Nodup → t ∈ F →
      (readT t).Nodup
  | t' :: ts, t, hnd, ht => by
      rw [readF_cons] at hnd
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact nodup_append_left hnd
      · exact nodup_readT_of_mem (nodup_append_right hnd) ht'

/-- On a duplicate-free forest, a present id's row collapses to the
unique tree containing it. -/
theorem rowF_of_unique {q : Nat} :
    ∀ {F : List Tree}, (readF F).Nodup → q ∈ readF F →
      ∃ t, t ∈ F ∧ q ∈ readT t ∧ rowF q F = rowT q t
  | t :: ts, hnd, hq => by
      rw [readF_cons] at hnd hq
      rw [List.mem_append] at hq
      by_cases hqt : q ∈ readT t
      · have hqts : q ∉ readF ts := fun h => nodup_append_disj hnd hqt h
        refine ⟨t, List.mem_cons_self .., hqt, ?_⟩
        rw [rowF, rowF_absent hqts, List.append_nil]
      · rcases hq with h | hqts
        · exact absurd h hqt
        · obtain ⟨t', ht', hqt', hrow⟩ :=
            rowF_of_unique (nodup_append_right hnd) hqts
          refine ⟨t', List.mem_cons_of_mem _ ht', hqt', ?_⟩
          rw [rowF, rowT_absent hqt, List.nil_append, hrow]

/-- An absent id has no child forest (tree form). -/
theorem kidsT_absent {q : Nat} {t : Tree} (h : q ∉ readT t) :
    kidsT q t = [] := by
  have htop := topIds_kidsT (p := q) t
  rw [rowT_absent h] at htop
  rcases hk : kidsT q t with _ | ⟨s, l⟩
  · rfl
  · rw [hk, List.map_cons] at htop
    cases htop

/-- An absent id has no child forest (forest form). -/
theorem kidsF_absent {q : Nat} :
    ∀ {F : List Tree}, q ∉ readF F → kidsF q F = []
  | [], _ => rfl
  | t :: ts, h => by
      have ht : q ∉ readT t := fun hm =>
        h (by rw [readF_cons]; exact List.mem_append_left _ hm)
      have hts : q ∉ readF ts := fun hm =>
        h (by rw [readF_cons]; exact List.mem_append_right _ hm)
      rw [kidsF_cons, kidsT_absent ht, kidsF_absent hts]
      rfl

/-- On a duplicate-free forest, a present id's child forest collapses to
the unique tree containing it. -/
theorem kidsF_of_unique {q : Nat} :
    ∀ {F : List Tree}, (readF F).Nodup → q ∈ readF F →
      ∃ t, t ∈ F ∧ q ∈ readT t ∧ kidsF q F = kidsT q t
  | t :: ts, hnd, hq => by
      rw [readF_cons] at hnd hq
      rw [List.mem_append] at hq
      by_cases hqt : q ∈ readT t
      · have hqts : q ∉ readF ts := fun h => nodup_append_disj hnd hqt h
        refine ⟨t, List.mem_cons_self .., hqt, ?_⟩
        rw [kidsF_cons, kidsF_absent hqts, List.append_nil]
      · rcases hq with h | hqts
        · exact absurd h hqt
        · obtain ⟨t', ht', hqt', hk⟩ :=
            kidsF_of_unique (nodup_append_right hnd) hqts
          refine ⟨t', List.mem_cons_of_mem _ ht', hqt', ?_⟩
          rw [kidsF_cons, kidsT_absent hqt, List.nil_append, hk]

/-! ## §2 the row characterization of a built forest

The generic engine: with a level grading (expansion strictly raises the
level; expanded levels bounded by `n`) and fuel covering the grading
(`n ≤ lvl p + f` at each call), a duplicate-free build realizes every
emitted key's row as its expanded stored row — the fuel can never
truncate a nonempty expansion. -/

theorem buildF_row_char (rows : List (Nat × List Nat)) (mk : Nat → Bool)
    (mf : Nat) (lvl : Nat → Nat) (n : Nat)
    (hedge : ∀ p u, u ∈ expandRow rows mk mf (alGet rows p) →
      lvl p < lvl u)
    (hbound : ∀ p u, u ∈ expandRow rows mk mf (alGet rows p) →
      lvl u ≤ n) :
    ∀ (f p q : Nat), n ≤ lvl p + f →
      (readF (buildF rows mk mf f p)).Nodup →
      q ∈ readF (buildF rows mk mf f p) →
      rowF q (buildF rows mk mf f p)
        = expandRow rows mk mf (alGet rows q)
  | 0, p, q, hinv, hnd, hq => by
      rw [buildF, readF] at hq
      exact absurd hq (List.not_mem_nil)
  | f + 1, p, q, hinv, hnd, hq => by
      rw [buildF] at hnd hq ⊢
      obtain ⟨t, htF, hqt, hrow⟩ := rowF_of_unique hnd hq
      have hndt : (readT t).Nodup := nodup_readT_of_mem hnd htF
      obtain ⟨c, hcE, rfl⟩ := List.mem_map.mp htF
      rw [readT] at hqt hndt
      have hcnot : c ∉ readF (buildF rows mk mf f c) :=
        (List.nodup_cons.mp hndt).1
      rw [hrow, rowT]
      rcases List.mem_cons.mp hqt with rfl | hq'
      · rw [if_pos rfl]
        cases f with
        | zero =>
            rw [buildF, List.map_nil]
            rcases hE : expandRow rows mk mf (alGet rows q) with _ | ⟨u, l⟩
            · rfl
            · have huE : u ∈ expandRow rows mk mf (alGet rows q) := by
                rw [hE]
                exact List.mem_cons_self ..
              have h2 : lvl p < lvl q := hedge p q hcE
              have h3 : lvl q < lvl u := hedge q u huE
              have h4 : lvl u ≤ n := hbound q u huE
              omega
        | succ f' => rw [topIds_buildF]
      · have hqc : ¬ c = q := fun he => hcnot (he ▸ hq')
        rw [if_neg hqc]
        refine buildF_row_char rows mk mf lvl n hedge hbound f c q ?_
          (List.nodup_cons.mp hndt).2 hq'
        have := hedge p c hcE
        omega

/-- The companion child-forest locator: an emitted key's child forest in
the build is a build from that key, with graded fuel. -/
theorem buildF_kids_char (rows : List (Nat × List Nat)) (mk : Nat → Bool)
    (mf : Nat) (lvl : Nat → Nat) (n : Nat)
    (hedge : ∀ p u, u ∈ expandRow rows mk mf (alGet rows p) →
      lvl p < lvl u) :
    ∀ (f p q : Nat), n ≤ lvl p + f →
      (readF (buildF rows mk mf f p)).Nodup →
      q ∈ readF (buildF rows mk mf f p) →
      ∃ g, n ≤ lvl q + g ∧
        kidsF q (buildF rows mk mf f p) = buildF rows mk mf g q
  | 0, p, q, hinv, hnd, hq => by
      rw [buildF, readF] at hq
      exact absurd hq (List.not_mem_nil)
  | f + 1, p, q, hinv, hnd, hq => by
      rw [buildF] at hnd hq ⊢
      obtain ⟨t, htF, hqt, hk⟩ := kidsF_of_unique hnd hq
      have hndt : (readT t).Nodup := nodup_readT_of_mem hnd htF
      obtain ⟨c, hcE, rfl⟩ := List.mem_map.mp htF
      rw [readT] at hqt hndt
      have hcnot : c ∉ readF (buildF rows mk mf f c) :=
        (List.nodup_cons.mp hndt).1
      rw [hk, kidsT]
      rcases List.mem_cons.mp hqt with rfl | hq'
      · rw [if_pos rfl]
        refine ⟨f, ?_, rfl⟩
        have := hedge p q hcE
        omega
      · have hqc : ¬ c = q := fun he => hcnot (he ▸ hq')
        rw [if_neg hqc]
        refine buildF_kids_char rows mk mf lvl n hedge f c q ?_
          (List.nodup_cons.mp hndt).2 hq'
        have := hedge p c hcE
        omega

/-! ## §3 the merge instance -/

/-- The merge's fuel (both the descent fuel and the splice fuel). -/
def mergeFuel (L A B : St) : Nat :=
  (read L).length + (read A).length + (read B).length + 1

theorem merge_eq_buildF (L A B : St) :
    merge L A B = buildF (outRows L A B) (markerp L A B)
      (mergeFuel L A B) (mergeFuel L A B) 0 := rfl

/-- **The output rows, characterized**: at every displayed id (and the
root), the merge's row is the marker-expansion of its assembled
`outRows` entry — the missing RHS characterization of the pre-splice
obligation (d). -/
theorem merge_row {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {q : Nat}
    (hq : q ∈ read (merge L A B) ∨ q = 0) :
    row (merge L A B) q
      = expandRow (outRows L A B) (markerp L A B) (mergeFuel L A B)
          (alGet (outRows L A B) q) := by
  have hnd : (readF (buildF (outRows L A B) (markerp L A B)
      (mergeFuel L A B) (mergeFuel L A B) 0)).Nodup := by
    have h := merge_read_nodup mok hA hB
    rw [merge_eq_buildF] at h
    exact h
  rcases hq with hq | rfl
  · have hq0 : q ≠ 0 := fun h0 => zero_not_mem_merge mok (h0 ▸ hq)
    rw [merge_eq_buildF] at hq
    rw [row, if_neg hq0, merge_eq_buildF]
    exact buildF_row_char (outRows L A B) (markerp L A B)
      (mergeFuel L A B) (lvl L A B) (mergeFuel L A B)
      (fun p u hu => lvl_edge mok hA hB hu)
      (fun p u hu => lvl_le_fuel u)
      (mergeFuel L A B) 0 q (by rw [lvl_zero mok]; omega) hnd hq
  · rw [row, if_pos rfl, merge_eq_buildF]
    have hn : mergeFuel L A B = (mergeFuel L A B - 1) + 1 := by
      rw [mergeFuel]
      omega
    rw [hn, topIds_buildF]

end Shesha
