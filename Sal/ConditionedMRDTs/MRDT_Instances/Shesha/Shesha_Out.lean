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

/-! ## §4 the raw-graded store: expansion stability and the front bridge

For the pre-splice forest the store is consumed *raw* (`mfuel = 0`; no
marker splice at build time), and the grading is over raw rows —
concretely, anchors precede children in Lamport order. -/

theorem expandRow_zero {rows : List (Nat × List Nat)} {mk : Nat → Bool}
    {r : List Nat} : expandRow rows mk 0 r = r := rfl

/-- A key at the level ceiling stores an empty row. -/
theorem row_empty_of_level {rows : List (Nat × List Nat)}
    {lvl : Nat → Nat} {n : Nat}
    (hedge : ∀ p u, u ∈ alGet rows p → lvl p < lvl u)
    (hbound : ∀ p u, u ∈ alGet rows p → lvl u ≤ n)
    {p : Nat} (h : n ≤ lvl p) : alGet rows p = [] := by
  rcases hE : alGet rows p with _ | ⟨u, l⟩
  · rfl
  · have hu : u ∈ alGet rows p := by
      rw [hE]
      exact List.mem_cons_self ..
    have := hedge p u hu
    have := hbound p u hu
    omega

/-- **Expansion is fuel-stable** on a graded store: any two fuels
covering the grading expand a key's row identically. -/
theorem expand_stable (rows : List (Nat × List Nat)) (D : Nat → Bool)
    (lvl : Nat → Nat) (n : Nat)
    (hedge : ∀ p u, u ∈ alGet rows p → lvl p < lvl u)
    (hbound : ∀ p u, u ∈ alGet rows p → lvl u ≤ n) :
    ∀ (f g p : Nat), n ≤ lvl p + f → n ≤ lvl p + g →
      expandRow rows D f (alGet rows p)
        = expandRow rows D g (alGet rows p)
  | 0, g, p, hf, hg => by
      have hrow : alGet rows p = [] :=
        row_empty_of_level hedge hbound (by omega)
      rw [hrow, expandRow_nil, expandRow_nil]
  | f + 1, 0, p, hf, hg => by
      have hrow : alGet rows p = [] :=
        row_empty_of_level hedge hbound (by omega)
      rw [hrow, expandRow_nil, expandRow_nil]
  | f + 1, g + 1, p, hf, hg => by
      rw [expandRow, expandRow]
      refine flatMap_congr' (fun v hv => ?_)
      by_cases hDv : D v
      · rw [if_pos hDv, if_pos hDv]
        exact expand_stable rows D lvl n hedge hbound f g v
          (by have := hedge p v hv; omega)
          (by have := hedge p v hv; omega)
      · rw [if_neg hDv, if_neg hDv]

theorem frontF_map_node (D : Nat → Bool) (g : Nat → List Tree) :
    ∀ l : List Nat, frontF D (l.map (fun c => Tree.node c (g c)))
      = l.flatMap (fun c => if D c then frontF D (g c) else [c])
  | [] => rfl
  | c :: l => by
      rw [List.map_cons, frontF_cons, List.flatMap_cons, frontT,
        frontF_map_node D g l]

/-- **The front bridge**: the `D`-front of a raw build is the `D`-marker
expansion of its key's stored row — the collapse of the built forest is
computed by `expandRow` over the same store. -/
theorem build_front_raw (rows : List (Nat × List Nat))
    (mk D : Nat → Bool) (lvl : Nat → Nat) (n : Nat)
    (hedge : ∀ p u, u ∈ alGet rows p → lvl p < lvl u)
    (hbound : ∀ p u, u ∈ alGet rows p → lvl u ≤ n) :
    ∀ (f p : Nat), n ≤ lvl p + f →
      frontF D (buildF rows mk 0 f p)
        = expandRow rows D f (alGet rows p)
  | 0, p, hinv => by
      have hrow : alGet rows p = [] :=
        row_empty_of_level hedge hbound (by omega)
      rw [buildF, hrow]
      rfl
  | f + 1, p, hinv => by
      rw [buildF, expandRow_zero, frontF_map_node, expandRow]
      refine flatMap_congr' (fun c hc => ?_)
      by_cases hDc : D c
      · rw [if_pos hDc, if_pos hDc]
        exact build_front_raw rows mk D lvl n hedge hbound f c
          (by have := hedge p c hc; omega)
      · rw [if_neg hDc, if_neg hDc]

/-! ## §5 well-formedness, membership and coverage of raw builds -/

/-- Fuel weakening for emission. -/
theorem buildF_mem_le (rows : List (Nat × List Nat)) (mk : Nat → Bool)
    (mf : Nat) {u : Nat} :
    ∀ (k f p : Nat), u ∈ readF (buildF rows mk mf f p) →
      u ∈ readF (buildF rows mk mf (f + k) p)
  | 0, _, _, h => h
  | k + 1, f, p, h =>
      buildF_mem_mono rows mk mf (f + k) p (buildF_mem_le rows mk mf k f p h)

/-- Everything a raw build displays is stored somewhere. -/
theorem build_mem_raw (rows : List (Nat × List Nat)) (mk : Nat → Bool)
    (f p : Nat) {u : Nat} (h : u ∈ readF (buildF rows mk 0 f p)) :
    ∃ r, u ∈ alGet rows r := by
  obtain ⟨r, -, hur⟩ := buildF_emitted rows mk 0 (fun _ => True)
    (fun _ _ _ _ => trivial) f p trivial h
  exact ⟨r, hur⟩

/-- **Raw-build well-formedness**: duplicate-free graded store with
unique addresses and nonzero content builds a WF forest. -/
theorem build_WF_raw (rows : List (Nat × List Nat)) (mk : Nat → Bool)
    (lvl : Nat → Nat)
    (hedge : ∀ p u, u ∈ alGet rows p → lvl p < lvl u)
    (hcnt : ∀ p, (alGet rows p).Nodup)
    (huniq : ∀ v r₁ r₂, v ∈ alGet rows r₁ → v ∈ alGet rows r₂ → r₁ = r₂)
    (hnz : ∀ p u, u ∈ alGet rows p → u ≠ 0) (f : Nat) :
    WF (buildF rows mk 0 f 0) := by
  constructor
  · exact nodup_of_count_le_one fun u =>
      buildF_count_le_one rows mk 0 (fun _ => True) lvl
        (fun _ _ _ _ => trivial)
        (fun v r _ => count_le_one_of_nodup (hcnt r) v)
        (fun v r₁ r₂ _ _ h₁ h₂ => huniq v r₁ r₂ h₁ h₂)
        (fun r c _ hc => hedge r c hc)
        (fun r c _ hc => hnz r c hc)
        trivial u f
  · intro h0
    obtain ⟨r, hr⟩ := build_mem_raw rows mk f 0 h0
    exact hnz r 0 hr rfl

/-- **Coverage**: stored content whose key chain roots (every key is the
root or itself stored) is displayed, with fuel one past its level. -/
theorem build_cover_raw (rows : List (Nat × List Nat)) (mk : Nat → Bool)
    (lvl : Nat → Nat)
    (hedge : ∀ p u, u ∈ alGet rows p → lvl p < lvl u)
    (hanc : ∀ p u, u ∈ alGet rows p → p = 0 ∨ ∃ q, p ∈ alGet rows q) :
    ∀ (N u p : Nat), lvl u ≤ N → u ∈ alGet rows p →
      u ∈ readF (buildF rows mk 0 (N + 1) 0)
  | 0, u, p, hN, hu => by
      have := hedge p u hu
      omega
  | N + 1, u, p, hN, hu => by
      rcases hanc p u hu with rfl | ⟨q, hq⟩
      · exact buildF_mem_root rows mk 0 hu (N + 1)
      · have hpN : lvl p ≤ N := by
          have := hedge p u hu
          omega
        have hp := build_cover_raw rows mk lvl hedge hanc N p q hpN hq
        exact buildF_step_mem rows mk 0 hu (N + 1) 0 hp

/-- **Raw-build rows, state form**: at every displayed id (and the
root), the row is the stored row. -/
theorem build_row_raw (rows : List (Nat × List Nat)) (mk : Nat → Bool)
    (lvl : Nat → Nat) (n : Nat)
    (hedge : ∀ p u, u ∈ alGet rows p → lvl p < lvl u)
    (hbound : ∀ p u, u ∈ alGet rows p → lvl u ≤ n)
    (hnz : ∀ p u, u ∈ alGet rows p → u ≠ 0)
    (hlvl0 : lvl 0 = 0) (f : Nat) (hnf : n ≤ f + 1)
    (hnd : (readF (buildF rows mk 0 (f + 1) 0)).Nodup) {q : Nat}
    (hq : q ∈ read (buildF rows mk 0 (f + 1) 0) ∨ q = 0) :
    row (buildF rows mk 0 (f + 1) 0) q = alGet rows q := by
  rcases hq with hq | rfl
  · have hq0 : q ≠ 0 := by
      rintro rfl
      obtain ⟨r, hr⟩ := build_mem_raw rows mk (f + 1) 0 hq
      exact hnz r 0 hr rfl
    rw [row, if_neg hq0]
    have h := buildF_row_char rows mk 0 lvl n
      (fun p u hu => hedge p u hu) (fun p u hu => hbound p u hu)
      (f + 1) 0 q (by omega) hnd hq
    rw [expandRow_zero] at h
    exact h
  · rw [row, if_pos rfl, topIds_buildF, expandRow_zero]

/-! ## §6 the collapse rows of a raw build

The state-level composite: the delete-collapse of the built pre-splice
forest has, at every live key, exactly the `D`-expansion of the stored
row at the canonical fuel `n`. With `merge_row` (§3) this reduces the
pre-splice obligation (d) to per-key equations between two `expandRow`s. -/

theorem build_collapse_row_raw (rows : List (Nat × List Nat))
    (mk D : Nat → Bool) (lvl : Nat → Nat) (n : Nat)
    (hedge : ∀ p u, u ∈ alGet rows p → lvl p < lvl u)
    (hbound : ∀ p u, u ∈ alGet rows p → lvl u ≤ n)
    (hlvl0 : lvl 0 = 0) (f : Nat) (hnf : n ≤ f + 1)
    (hnd : (readF (buildF rows mk 0 (f + 1) 0)).Nodup) {q : Nat}
    (hq : q ∈ read (buildF rows mk 0 (f + 1) 0) ∨ q = 0)
    (hDq : D q = false) :
    row (dropF D (buildF rows mk 0 (f + 1) 0)) q
      = expandRow rows D n (alGet rows q) := by
  rw [row_dropF hDq, kids]
  rcases hq with hq | rfl
  · have hq0 : q ≠ 0 := by
      rintro rfl
      obtain ⟨r, hr⟩ := build_mem_raw rows mk (f + 1) 0 hq
      have := hedge r 0 hr
      have := hbound r 0 hr
      have h0 : lvl 0 = 0 := hlvl0
      omega
    rw [if_neg hq0]
    obtain ⟨g, hg, hk⟩ := buildF_kids_char rows mk 0 lvl n
      (fun p u hu => hedge p u hu) (f + 1) 0 q
      (by omega) hnd hq
    rw [hk, build_front_raw rows mk D lvl n hedge hbound g q hg]
    exact expand_stable rows D lvl n hedge hbound g n q hg (by omega)
  · rw [if_pos rfl,
      build_front_raw rows mk D lvl n hedge hbound (f + 1) 0
        (by omega)]
    exact expand_stable rows D lvl n hedge hbound (f + 1) n 0
      (by omega) (by omega)

end Shesha
