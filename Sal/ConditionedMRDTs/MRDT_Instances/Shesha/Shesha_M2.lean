import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_M0

/-! # Shesha — M2: the L-extension order theorem

Closes `merge_L_filter` (the skeleton-DFS-order = L-document-order core) and
hosts `merge_extends_L`, both stated as owed in
`Shesha_Merge_Lemmas.lean`.

Route: the L-filter of the merge's read computes, level by level, the DFS
of the *collapsed* skeleton (runs stripped by `rowAssemble_filter_L`,
markers spliced by `expandRow` = `collapseRow`); the collapsed skeleton is
the structural shallow-survivor forest of `L` (the `wpar` ↔ tree-structure
bridge); and that DFS is exactly `(read L).filter` survivors — the same
splice as `delete`, performed at merge time.

- §1 subtrees (`subF`), the row characterization, subtree uniqueness;
- §2 the `wpar` bridge: fuel stability, the climb lemma, `skelRowOf` =
  shallowest-W (structural);
- §3 collapse alignment: markers expand shallow-W to shallow-survivors,
  whose DFS is the survivor filter of `read L`;
- §4 output side: the L-filter of `buildF` is that DFS;
- §5 `merge_L_filter`, `merge_extends_L`.
-/

namespace Shesha

open List

/-! ## §1 Subtrees, structurally -/

mutual
  def subT : Tree → List Tree
    | .node i cs => .node i cs :: subF cs
  def subF : List Tree → List Tree
    | [] => []
    | t :: ts => subT t ++ subF ts
end

theorem subT_self (t : Tree) : t ∈ subT t := by
  cases t with
  | node i cs =>
      rw [subT]
      exact List.mem_cons_self ..

mutual
  theorem subT_closed : ∀ {t x : Tree}, x ∈ subT t →
      ∀ y ∈ subT x, y ∈ subT t
    | .node i cs, x, hx, y, hy => by
        rw [subT] at hx ⊢
        rcases List.mem_cons.mp hx with he | hx
        · rw [he] at hy
          rw [subT] at hy
          exact hy
        · exact List.mem_cons_of_mem _ (subF_closed hx y hy)
  theorem subF_closed : ∀ {F : List Tree} {x : Tree}, x ∈ subF F →
      ∀ y ∈ subT x, y ∈ subF F
    | t :: ts, x, hx, y, hy => by
        rw [subF] at hx ⊢
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append.mpr (Or.inl (subT_closed hx y hy))
        · exact List.mem_append.mpr (Or.inr (subF_closed hx y hy))
end

theorem mem_subF_of_mem : ∀ {ts : List Tree} {t : Tree}, t ∈ ts →
    t ∈ subF ts
  | t' :: ts, t, h => by
      rw [subF]
      rcases List.mem_cons.mp h with he | h
      · refine List.mem_append.mpr (Or.inl ?_)
        rw [he]
        exact subT_self t'
      · exact List.mem_append.mpr (Or.inr (mem_subF_of_mem h))

theorem child_mem_subF {F : List Tree} {i : Nat} {cs : List Tree}
    (h : Tree.node i cs ∈ subF F) {t : Tree} (ht : t ∈ cs) : t ∈ subF F :=
  subF_closed h t (by
    rw [subT]
    exact List.mem_cons_of_mem _ (mem_subF_of_mem ht))

mutual
  theorem subT_read : ∀ {t x : Tree}, x ∈ subT t →
      ∀ w ∈ readT x, w ∈ readT t
    | .node i cs, x, hx, w, hw => by
        rw [subT] at hx
        rcases List.mem_cons.mp hx with he | hx
        · rw [← he]
          exact hw
        · rw [readT]
          exact List.mem_cons_of_mem _ (subF_read hx w hw)
  theorem subF_read : ∀ {F : List Tree} {x : Tree}, x ∈ subF F →
      ∀ w ∈ readT x, w ∈ readF F
    | t :: ts, x, hx, w, hw => by
        rw [subF] at hx
        rw [readF, List.mem_append]
        rcases List.mem_append.mp hx with hx | hx
        · exact Or.inl (subT_read hx w hw)
        · exact Or.inr (subF_read hx w hw)
end

theorem subF_root_read {F : List Tree} {i : Nat} {cs : List Tree}
    (hx : Tree.node i cs ∈ subF F) : i ∈ readF F :=
  subF_read hx i (by rw [readT]; exact List.mem_cons_self ..)

mutual
  theorem subT_count : ∀ {t x : Tree}, x ∈ subT t →
      ∀ w, (readT x).count w ≤ (readT t).count w
    | .node i cs, x, hx, w => by
        rw [subT] at hx
        rcases List.mem_cons.mp hx with he | hx
        · rw [he]
          exact Nat.le_refl _
        · rw [readT, List.count_cons]
          have := subF_count hx w
          omega
  theorem subF_count : ∀ {F : List Tree} {x : Tree}, x ∈ subF F →
      ∀ w, (readT x).count w ≤ (readF F).count w
    | t :: ts, x, hx, w => by
        rw [subF] at hx
        rw [readF, List.count_append]
        rcases List.mem_append.mp hx with hx | hx
        · have := subT_count hx w
          omega
        · have := subF_count hx w
          omega
end

theorem subF_nodup {L : St} (hnd : (read L).Nodup) {x : Tree}
    (hx : x ∈ subF L) : (readT x).Nodup :=
  nodup_of_count_le_one fun c =>
    Nat.le_trans (subF_count hx c) (count_le_one_of_nodup hnd c)

/-! ### The row of a subtree node is its structural child list -/

mutual
  theorem rowT_subtree : ∀ {t : Tree} {i : Nat} {cs : List Tree},
      (readT t).Nodup → Tree.node i cs ∈ subT t →
      rowT i t = cs.map topId
    | .node j ds, i, cs, hnd, hx => by
        rw [subT] at hx
        rcases List.mem_cons.mp hx with he | hx
        · injection he with h1 h2
          rw [rowT, if_pos h1.symm, h2]
        · have hiF : i ∈ readF ds := subF_root_read hx
          rw [readT] at hnd
          have hij : ¬ j = i := fun e =>
            (List.nodup_cons.mp hnd).1 (e ▸ hiF)
          rw [rowT, if_neg hij]
          exact rowF_subtree (List.nodup_cons.mp hnd).2 hx
  theorem rowF_subtree : ∀ {F : List Tree} {i : Nat} {cs : List Tree},
      (readF F).Nodup → Tree.node i cs ∈ subF F →
      rowF i F = cs.map topId
    | t :: ts, i, cs, hnd, hx => by
        rw [subF] at hx
        rw [readF] at hnd
        rw [rowF]
        rcases List.mem_append.mp hx with hx | hx
        · have hiT : i ∈ readT t := subT_read hx i
            (by rw [readT]; exact List.mem_cons_self ..)
          have hits : rowF i ts = [] := by
            rcases hemp : rowF i ts with _ | ⟨a, l⟩
            · rfl
            · have him : i ∈ readF ts := rowF_parent_mem
                (by rw [hemp]; exact List.mem_cons_self ..)
              exact (nodup_append_disj hnd hiT him).elim
          rw [hits, rowT_subtree (nodup_append_left hnd) hx,
            List.append_nil]
        · have hiTs : i ∈ readF ts := subF_root_read hx
          have hT : rowT i t = [] := by
            rcases hemp : rowT i t with _ | ⟨a, l⟩
            · rfl
            · have him : i ∈ readT t := rowT_parent_mem
                (by rw [hemp]; exact List.mem_cons_self ..)
              exact (nodup_append_disj hnd him hiTs).elim
          rw [hT, rowF_subtree (nodup_append_right hnd) hx,
            List.nil_append]
end

theorem row_subtree {L : St} (hwf : WF L) {i : Nat} {cs : List Tree}
    (hx : Tree.node i cs ∈ subF L) : row L i = cs.map topId := by
  have hi0 : i ≠ 0 := fun h0 => hwf.2 (h0 ▸ subF_root_read hx)
  rw [row, if_neg hi0]
  exact rowF_subtree hwf.1 hx

/-- A structural child's parent is its structural parent. -/
theorem parOf_child {L : St} (hwf : WF L) {i : Nat} {cs : List Tree}
    (hx : Tree.node i cs ∈ subF L) {t : Tree} (ht : t ∈ cs) :
    parOf L (topId t) = i := by
  apply row_mem_parOf hwf
  rw [row_subtree hwf hx]
  exact List.mem_map.mpr ⟨t, ht, rfl⟩

/-! On a WF forest, a label determines its subtree. -/
mutual
  theorem subT_unique : ∀ {t : Tree} {i : Nat} {cs₁ cs₂ : List Tree},
      (readT t).Nodup → Tree.node i cs₁ ∈ subT t →
      Tree.node i cs₂ ∈ subT t → cs₁ = cs₂
    | .node j ds, i, cs₁, cs₂, hnd, h₁, h₂ => by
        rw [subT] at h₁ h₂
        rw [readT] at hnd
        rcases List.mem_cons.mp h₁ with he₁ | h₁ <;>
          rcases List.mem_cons.mp h₂ with he₂ | h₂
        · injection he₁ with e₁ e₂
          injection he₂ with e₃ e₄
          rw [e₂, e₄]
        · injection he₁ with e₁ e₂
          exact ((List.nodup_cons.mp hnd).1
            (e₁ ▸ subF_root_read h₂)).elim
        · injection he₂ with e₁ e₂
          exact ((List.nodup_cons.mp hnd).1
            (e₁ ▸ subF_root_read h₁)).elim
        · exact subF_unique (List.nodup_cons.mp hnd).2 h₁ h₂
  theorem subF_unique : ∀ {F : List Tree} {i : Nat} {cs₁ cs₂ : List Tree},
      (readF F).Nodup → Tree.node i cs₁ ∈ subF F →
      Tree.node i cs₂ ∈ subF F → cs₁ = cs₂
    | t :: ts, i, cs₁, cs₂, hnd, h₁, h₂ => by
        rw [subF] at h₁ h₂
        rw [readF] at hnd
        rcases List.mem_append.mp h₁ with h₁ | h₁ <;>
          rcases List.mem_append.mp h₂ with h₂ | h₂
        · exact subT_unique (nodup_append_left hnd) h₁ h₂
        · exact (nodup_append_disj hnd
            (subT_read h₁ i (by rw [readT]; exact List.mem_cons_self ..))
            (subF_root_read h₂)).elim
        · exact (nodup_append_disj hnd
            (subT_read h₂ i (by rw [readT]; exact List.mem_cons_self ..))
            (subF_root_read h₁)).elim
        · exact subF_unique (nodup_append_right hnd) h₁ h₂
end

/-! ## §2 The `wpar` bridge: fuel stability and the climb lemma -/

/-- `wparGo` is fuel-stable once the fuel covers the depth. -/
theorem wparGo_stable {L : St} (hwf : WF L) (W : Nat → Bool) :
    ∀ (f₁ f₂ p : Nat), (p = 0 ∨ p ∈ read L) →
      depthOf L p < f₁ → depthOf L p < f₂ →
      wparGo L W f₁ p = wparGo L W f₂ p
  | 0, _, p, _, h₁, _ => absurd h₁ (Nat.not_lt_zero _)
  | _ + 1, 0, p, _, _, h₂ => absurd h₂ (Nat.not_lt_zero _)
  | f₁ + 1, f₂ + 1, p, hp, h₁, h₂ => by
      rcases hp with rfl | hp
      · rw [wparGo_zero, wparGo_zero]
      · rw [wparGo, wparGo]
        by_cases hc : (p == 0 || W p) = true
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc]
          rcases parOf_step hwf hp with h0 | ⟨hm, hd⟩
          · rw [h0, wparGo_zero, wparGo_zero]
          · exact wparGo_stable hwf W f₁ f₂ (parOf L p) (Or.inr hm)
              (by omega) (by omega)

/-- The canonical climb, unfolded one node: stop at a `W`-node, else the
node's own host. -/
theorem wparGo_at_node {L : St} (hwf : WF L) (W : Nat → Bool) {y : Nat}
    (hy : y ∈ read L) :
    wparGo L W ((read L).length + 1) y =
      if W y = true then y else wpar L W y := by
  have hy0 : y ≠ 0 := fun h => hwf.2 (h ▸ hy)
  rw [wparGo]
  by_cases hW : W y = true
  · rw [if_pos (by simp [hW]), if_pos hW]
  · rw [if_neg (show ¬ ((y == 0 || W y) = true) by simp [hW, hy0]),
      if_neg hW, wpar]
    rcases parOf_step hwf hy with h0 | ⟨hm, -⟩
    · rw [h0, wparGo_zero, wparGo_zero]
    · have hd := depthOf_lt_length hm
      exact wparGo_stable hwf W _ _ (parOf L y) (Or.inr hm)
        (by omega) (by omega)

/-- The host of a node whose parent is `y`: `y` if `y` is a `W`-node, else
`y`'s own host. -/
theorem wpar_child_eq {L : St} (hwf : WF L) (W : Nat → Bool) {y w : Nat}
    (hpar : parOf L w = y) (hy : y ∈ read L) :
    wpar L W w = if W y = true then y else wpar L W y := by
  rw [wpar, hpar]
  exact wparGo_at_node hwf W hy

theorem wpar_of_parOf_zero {L : St} (W : Nat → Bool) {w : Nat}
    (hpar : parOf L w = 0) : wpar L W w = 0 := by
  rw [wpar, hpar, wparGo_zero]

theorem readF_mem_tree : ∀ {F : List Tree} {w : Nat}, w ∈ readF F →
    ∃ t ∈ F, w ∈ readT t
  | t :: ts, w, h => by
      rw [readF, List.mem_append] at h
      rcases h with h | h
      · exact ⟨t, List.mem_cons_self .., h⟩
      · obtain ⟨t', ht', hw⟩ := readF_mem_tree h
        exact ⟨t', List.mem_cons_of_mem _ ht', hw⟩

theorem mem_readF_of_tree {F : List Tree} {t : Tree} (ht : t ∈ F)
    {w : Nat} (hw : w ∈ readT t) : w ∈ readF F :=
  subF_read (mem_subF_of_mem ht) w hw

/-- **The climb lemma** (forest form): the host of any node of a child
forest is inside the forest, or is the shared parent's own host value. -/
theorem climb2F {L : St} (hwf : WF L) (W : Nat → Bool) :
    ∀ (F : List Tree) (y : Nat), (∀ t ∈ F, t ∈ subF L) →
      (∀ t ∈ F, parOf L (topId t) = y) → y ∈ read L →
      ∀ w ∈ readF F,
        wpar L W w ∈ readF F ∨
          wpar L W w = (if W y = true then y else wpar L W y)
  | .node z csz :: ts, y, hsub, hpar, hyL, w, hw => by
      rw [readF, List.mem_append] at hw
      have hzL : z ∈ read L :=
        subF_root_read (hsub _ (List.mem_cons_self ..))
      rcases hw with hw | hw
      · rw [readT, List.mem_cons] at hw
        rcases hw with he | hw
        · -- w = z: its parent is y
          have hp : parOf L w = y := by
            rw [he]
            exact hpar _ (List.mem_cons_self ..)
          rw [wpar_child_eq hwf W hp hyL]
          exact Or.inr rfl
        · -- w strictly below z: climb within z's forest
          have hzsub : Tree.node z csz ∈ subF L :=
            hsub _ (List.mem_cons_self ..)
          rcases climb2F hwf W csz z
            (fun t' ht' => child_mem_subF hzsub ht')
            (fun t' ht' => parOf_child hwf hzsub ht') hzL w hw with
            hin | he
          · refine Or.inl ?_
            rw [readF, List.mem_append]
            exact Or.inl (by rw [readT]; exact List.mem_cons_of_mem _ hin)
          · by_cases hWz : W z = true
            · rw [if_pos hWz] at he
              refine Or.inl ?_
              rw [he, readF, List.mem_append, readT]
              exact Or.inl (List.mem_cons_self ..)
            · rw [if_neg hWz] at he
              rw [he, wpar_child_eq hwf W
                (show parOf L z = y from hpar _ (List.mem_cons_self ..))
                hyL]
              exact Or.inr rfl
      · rcases climb2F hwf W ts y
          (fun t' ht' => hsub _ (List.mem_cons_of_mem _ ht'))
          (fun t' ht' => hpar _ (List.mem_cons_of_mem _ ht')) hyL w hw with
          hin | he
        · refine Or.inl ?_
          rw [readF, List.mem_append]
          exact Or.inr hin
        · exact Or.inr he

/-! ### Shallowest-`P` fronts -/

mutual
  def shallowWT (P : Nat → Bool) : Tree → List Nat
    | .node i cs => if P i then [i] else shallowWF P cs
  def shallowWF (P : Nat → Bool) : List Tree → List Nat
    | [] => []
    | t :: ts => shallowWT P t ++ shallowWF P ts
end

theorem filter_filter' (p q : Nat → Bool) :
    ∀ l : List Nat, (l.filter p).filter q = l.filter (fun a => p a && q a)
  | [] => rfl
  | a :: l => by
      rw [List.filter_cons]
      by_cases hp : p a = true
      · rw [if_pos hp, List.filter_cons, List.filter_cons]
        by_cases hq : q a = true
        · rw [if_pos hq, if_pos (by simp [hp, hq]), filter_filter' p q l]
        · rw [if_neg hq, if_neg (by simp [hp, hq]), filter_filter' p q l]
      · rw [if_neg hp, List.filter_cons, if_neg (by simp [hp]),
          filter_filter' p q l]

/-! ### The skeleton filter over a subtree -/

/-- Zero part: a subtree whose top is hosted elsewhere, and which does not
contain `h`, contributes nothing to `h`'s skeleton row. -/
theorem skelZ {L A B : St} (mok : ModelOK L A B) {t : Tree}
    (ht : t ∈ subF L) {h : Nat}
    (hne : wpar L (wp L A B) (topId t) ≠ h) (hnot : h ∉ readT t) :
    (readT t).filter (fun w => wp L A B w &&
      (wpar L (wp L A B) w == h)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro w hw hc
  obtain ⟨hwp, hwh⟩ := Bool.and_eq_true_iff.mp hc
  have hwpar : wpar L (wp L A B) w = h := by simpa using hwh
  cases t with
  | node z csz =>
      have hzL : z ∈ read L := subF_root_read ht
      rw [readT, List.mem_cons] at hw
      rcases hw with he | hw
      · exact hne (he ▸ hwpar)
      · rcases climb2F mok.wfL (wp L A B) csz z
          (fun t' ht' => child_mem_subF ht ht')
          (fun t' ht' => parOf_child mok.wfL ht ht') hzL w hw with
          hin | heq
        · rw [hwpar] at hin
          exact hnot (by rw [readT]; exact List.mem_cons_of_mem _ hin)
        · by_cases hWz : wp L A B z = true
          · rw [if_pos hWz] at heq
            rw [hwpar] at heq
            exact hnot (by
              rw [readT, ← heq]
              exact List.mem_cons_self ..)
          · rw [if_neg hWz] at heq
            rw [hwpar] at heq
            exact hne heq.symm

mutual
  /-- A subtree hosted at `h` contributes exactly its shallow-`W` front. -/
  theorem skelT {L A B : St} (mok : ModelOK L A B) :
      ∀ (t : Tree), t ∈ subF L → ∀ (h : Nat),
        wpar L (wp L A B) (topId t) = h → h ∉ readT t →
        (readT t).filter (fun w => wp L A B w &&
          (wpar L (wp L A B) w == h)) = shallowWT (wp L A B) t
    | .node z csz, ht, h, hup, hnot => by
        have hzL : z ∈ read L := subF_root_read ht
        have hupz : wpar L (wp L A B) z = h := hup
        rw [readT, List.filter_cons]
        by_cases hWz : wp L A B z = true
        · rw [if_pos (by simp [hWz, hupz]), shallowWT, if_pos hWz]
          have hdeep : (readF csz).filter (fun w => wp L A B w &&
              (wpar L (wp L A B) w == h)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro w hw hc
            obtain ⟨hwp, hwh⟩ := Bool.and_eq_true_iff.mp hc
            have hwpar : wpar L (wp L A B) w = h := by simpa using hwh
            rcases climb2F mok.wfL (wp L A B) csz z
              (fun t' ht' => child_mem_subF ht ht')
              (fun t' ht' => parOf_child mok.wfL ht ht') hzL w hw with
              hin | heq
            · rw [hwpar] at hin
              exact hnot (by rw [readT]; exact List.mem_cons_of_mem _ hin)
            · rw [if_pos hWz] at heq
              rw [hwpar] at heq
              exact hnot (by
                rw [readT, ← heq]
                exact List.mem_cons_self ..)
          rw [hdeep]
        · rw [if_neg (by simp [hWz]), shallowWT, if_neg hWz]
          refine skelF mok csz h ?_
          intro t' ht'
          have hnotin : h ∉ readT t' := fun hm => hnot (by
            rw [readT]
            exact List.mem_cons_of_mem _ (mem_readF_of_tree ht' hm))
          refine ⟨child_mem_subF ht ht', ?_, hnotin⟩
          rw [wpar_child_eq mok.wfL (wp L A B)
            (parOf_child mok.wfL ht ht') hzL, if_neg hWz]
          exact hupz
  /-- Forest form, hypotheses bundled per tree. -/
  theorem skelF {L A B : St} (mok : ModelOK L A B) :
      ∀ (F : List Tree) (h' : Nat),
        (∀ t ∈ F, t ∈ subF L ∧
          wpar L (wp L A B) (topId t) = h' ∧ h' ∉ readT t) →
        (readF F).filter (fun w => wp L A B w &&
          (wpar L (wp L A B) w == h')) = shallowWF (wp L A B) F
    | [], _, _ => rfl
    | t :: ts, h', hyp => by
        rw [readF, List.filter_append, shallowWF]
        obtain ⟨h1, h2, h3⟩ := hyp t (List.mem_cons_self ..)
        rw [skelT mok t h1 h' h2 h3,
          skelF mok ts h'
            (fun t' ht' => hyp t' (List.mem_cons_of_mem _ ht'))]
end

/-! Every live node has a subtree. -/
mutual
  theorem readT_subtree : ∀ {t : Tree} {w : Nat}, w ∈ readT t →
      ∃ cs, Tree.node w cs ∈ subT t
    | .node i cs, w, hw => by
        rw [readT, List.mem_cons] at hw
        rcases hw with he | hw
        · exact ⟨cs, by rw [he, subT]; exact List.mem_cons_self ..⟩
        · obtain ⟨cs', hcs'⟩ := readF_subtree hw
          rw [subT]
          exact ⟨cs', List.mem_cons_of_mem _ hcs'⟩
  theorem readF_subtree : ∀ {F : List Tree} {w : Nat}, w ∈ readF F →
      ∃ cs, Tree.node w cs ∈ subF F
    | t :: ts, w, hw => by
        rw [readF, List.mem_append] at hw
        rw [subF]
        rcases hw with hw | hw
        · obtain ⟨cs, hcs⟩ := readT_subtree hw
          exact ⟨cs, List.mem_append.mpr (Or.inl hcs)⟩
        · obtain ⟨cs, hcs⟩ := readF_subtree hw
          exact ⟨cs, List.mem_append.mpr (Or.inr hcs)⟩
end

/-! ### Locating the host's row: the find sweep -/

theorem skelZ_forest {L A B : St} (mok : ModelOK L A B) :
    ∀ (F : List Tree) (h : Nat),
      (∀ t ∈ F, t ∈ subF L ∧
        wpar L (wp L A B) (topId t) ≠ h ∧ h ∉ readT t) →
      (readF F).filter (fun w => wp L A B w &&
        (wpar L (wp L A B) w == h)) = []
  | [], _, _ => rfl
  | t :: ts, h, hyp => by
      rw [readF, List.filter_append]
      obtain ⟨h1, h2, h3⟩ := hyp t (List.mem_cons_self ..)
      rw [skelZ mok h1 h2 h3,
        skelZ_forest mok ts h
          (fun t' ht' => hyp t' (List.mem_cons_of_mem _ ht'))]
      rfl

mutual
  /-- Descend to `h`'s node: everything outside contributes nothing; at the
  node, `skelF` yields the shallow-`W` front of its child forest. -/
  theorem findT {L A B : St} (mok : ModelOK L A B) :
      ∀ (t : Tree), t ∈ subF L → ∀ (h : Nat) (csh : List Tree),
        Tree.node h csh ∈ subT t → wp L A B h = true →
        wpar L (wp L A B) (topId t) ≠ h →
        (readT t).filter (fun w => wp L A B w &&
          (wpar L (wp L A B) w == h)) = shallowWF (wp L A B) csh
    | .node z csz, ht, h, csh, hin, hWh, hne => by
        have hzL : z ∈ read L := subF_root_read ht
        have hndT : (readT (Tree.node z csz)).Nodup :=
          subF_nodup mok.wfL.1 ht
        rw [subT] at hin
        rcases List.mem_cons.mp hin with he | hin
        · injection he with e1 e2
          rw [readT, List.filter_cons,
            if_neg (show ¬ ((wp L A B z &&
                (wpar L (wp L A B) z == h)) = true) from by
              simp [show wpar L (wp L A B) z ≠ h from hne]),
            e2]
          refine skelF mok csz h ?_
          intro t' ht'
          have hz_notin : z ∉ readF csz := by
            rw [readT] at hndT
            exact (List.nodup_cons.mp hndT).1
          have hWz : wp L A B z = true := e1 ▸ hWh
          refine ⟨child_mem_subF ht ht', ?_, ?_⟩
          · rw [wpar_child_eq mok.wfL (wp L A B)
              (parOf_child mok.wfL ht ht') hzL, if_pos hWz]
            exact e1.symm
          · intro hm
            exact hz_notin (e1 ▸ mem_readF_of_tree ht' hm)
        · have hhz : h ∈ readF csz := subF_root_read hin
          rw [readT, List.filter_cons,
            if_neg (show ¬ ((wp L A B z &&
                (wpar L (wp L A B) z == h)) = true) from by
              simp [show wpar L (wp L A B) z ≠ h from hne])]
          have hz_ne : z ≠ h := by
            rw [readT] at hndT
            intro e
            exact (List.nodup_cons.mp hndT).1 (e ▸ hhz)
          refine findF mok csz (fun t' ht' => child_mem_subF ht ht') ?_
            h csh hin hWh ?_
          · rw [readT] at hndT
            exact (List.nodup_cons.mp hndT).2
          · intro t' ht'
            rw [wpar_child_eq mok.wfL (wp L A B)
              (parOf_child mok.wfL ht ht') hzL]
            by_cases hWz : wp L A B z = true
            · rw [if_pos hWz]
              exact hz_ne
            · rw [if_neg hWz]
              exact hne
  theorem findF {L A B : St} (mok : ModelOK L A B) :
      ∀ (F : List Tree), (∀ t ∈ F, t ∈ subF L) → (readF F).Nodup →
        ∀ (h : Nat) (csh : List Tree), Tree.node h csh ∈ subF F →
        wp L A B h = true →
        (∀ t ∈ F, wpar L (wp L A B) (topId t) ≠ h) →
        (readF F).filter (fun w => wp L A B w &&
          (wpar L (wp L A B) w == h)) = shallowWF (wp L A B) csh
    | t :: ts, hsub, hnd, h, csh, hin, hWh, hne => by
        rw [subF] at hin
        rw [readF] at hnd ⊢
        rw [List.filter_append]
        rcases List.mem_append.mp hin with hin | hin
        · have hhT : h ∈ readT t := subT_read hin h
            (by rw [readT]; exact List.mem_cons_self ..)
          have hts : (readF ts).filter (fun w => wp L A B w &&
              (wpar L (wp L A B) w == h)) = [] := by
            refine skelZ_forest mok ts h ?_
            intro t' ht'
            exact ⟨hsub _ (List.mem_cons_of_mem _ ht'),
              hne _ (List.mem_cons_of_mem _ ht'),
              fun hm => nodup_append_disj hnd hhT
                (mem_readF_of_tree ht' hm)⟩
          rw [hts, findT mok t (hsub _ (List.mem_cons_self ..)) h csh hin
            hWh (hne _ (List.mem_cons_self ..)), List.append_nil]
        · have hhTs : h ∈ readF ts := subF_root_read hin
          have htz : (readT t).filter (fun w => wp L A B w &&
              (wpar L (wp L A B) w == h)) = [] :=
            skelZ mok (hsub _ (List.mem_cons_self ..))
              (hne _ (List.mem_cons_self ..))
              (fun hm => nodup_append_disj hnd hm hhTs)
          rw [htz, findF mok ts
            (fun t' ht' => hsub _ (List.mem_cons_of_mem _ ht'))
            (nodup_append_right hnd) h csh hin hWh
            (fun t' ht' => hne _ (List.mem_cons_of_mem _ ht')),
            List.nil_append]
end

/-! ### The skeleton rows, structurally (Claim K) -/

/-- The root skeleton row is the shallow-`W` front of `L` itself. -/
theorem skelRowOf_root {L A B : St} (mok : ModelOK L A B) :
    alGet (skelOf L A B).rows 0 = shallowWF (wp L A B) L := by
  rw [skelOf_alGet, filter_filter']
  refine skelF mok L 0 ?_
  intro t ht
  have htop : topId t ∈ row L 0 := by
    rw [row, if_pos rfl]
    exact List.mem_map.mpr ⟨t, ht, rfl⟩
  have hpar : parOf L (topId t) = 0 := row_mem_parOf mok.wfL htop
  refine ⟨mem_subF_of_mem ht, wpar_of_parOf_zero _ hpar, ?_⟩
  intro hm
  exact mok.wfL.2 (mem_readF_of_tree ht hm)

/-- A `W`-node's skeleton row is the shallow-`W` front of its own child
forest. -/
theorem skelRowOf_node {L A B : St} (mok : ModelOK L A B) {h : Nat}
    {csh : List Tree} (hx : Tree.node h csh ∈ subF L)
    (hWh : wp L A B h = true) :
    alGet (skelOf L A B).rows h = shallowWF (wp L A B) csh := by
  have hh0 : h ≠ 0 := fun e => mok.wfL.2 (e ▸ subF_root_read hx)
  rw [skelOf_alGet, filter_filter']
  refine findF mok L (fun t ht => mem_subF_of_mem ht) mok.wfL.1 h csh hx
    hWh ?_
  intro t ht
  have htop : topId t ∈ row L 0 := by
    rw [row, if_pos rfl]
    exact List.mem_map.mpr ⟨t, ht, rfl⟩
  have hpar : parOf L (topId t) = 0 := row_mem_parOf mok.wfL htop
  rw [wpar_of_parOf_zero _ hpar]
  exact fun e => hh0 e.symm

/-! ## §3 Collapse alignment: markers expand shallow-W to
shallow-survivors, whose DFS is the survivor filter -/

mutual
  theorem subT_length : ∀ {t x : Tree}, x ∈ subT t →
      (readT x).length ≤ (readT t).length
    | .node i cs, x, hx => by
        rw [subT] at hx
        rcases List.mem_cons.mp hx with he | hx
        · rw [he]
          exact Nat.le_refl _
        · rw [readT, List.length_cons]
          have := subF_length hx
          omega
  theorem subF_length : ∀ {F : List Tree} {x : Tree}, x ∈ subF F →
      (readT x).length ≤ (readF F).length
    | t :: ts, x, hx => by
        rw [subF] at hx
        rw [readF, List.length_append]
        rcases List.mem_append.mp hx with hx | hx
        · have := subT_length hx
          omega
        · have := subF_length hx
          omega
end

theorem wp_of_liveM {L A B : St} {x : Nat} (h : liveMp L A B x = true) :
    wp L A B x = true := by
  rw [wp, h]
  rfl

/-- The (fueled) marker collapse of a skeleton row. -/
def collapseRow (L A B : St) : Nat → List Nat → List Nat
  | 0, cs => cs
  | f + 1, cs => cs.flatMap (fun v =>
      if markerp L A B v = true
      then collapseRow L A B f (alGet (skelOf L A B).rows v)
      else [v])

/-- DFS of the collapsed skeleton. -/
def survDFS (L A B : St) (mf : Nat) : Nat → List Nat → List Nat
  | 0, _ => []
  | f + 1, cs => cs.flatMap (fun c =>
      c :: survDFS L A B mf f
        (collapseRow L A B mf (alGet (skelOf L A B).rows c)))

theorem collapseRow_append (L A B : St) :
    ∀ (f : Nat) (a b : List Nat),
      collapseRow L A B f (a ++ b) =
        collapseRow L A B f a ++ collapseRow L A B f b
  | 0, a, b => rfl
  | f + 1, a, b => by
      rw [collapseRow, collapseRow, collapseRow, List.flatMap_append]

theorem survDFS_append (L A B : St) (mf : Nat) :
    ∀ (f : Nat) (a b : List Nat),
      survDFS L A B mf f (a ++ b) =
        survDFS L A B mf f a ++ survDFS L A B mf f b
  | 0, a, b => rfl
  | f + 1, a, b => by
      rw [survDFS, survDFS, survDFS, List.flatMap_append]

mutual
  /-- **J1 (tree)**: collapsing the shallow-`W` front of a subtree yields
  its shallow-survivor front. -/
  theorem collapseT {L A B : St} (mok : ModelOK L A B) :
      ∀ (t : Tree), t ∈ subF L → ∀ (f : Nat), (readT t).length < f →
        collapseRow L A B f (shallowWT (wp L A B) t) =
          shallowWT (fun w => liveMp L A B w) t
    | .node x csx, ht, f, hf => by
        rw [shallowWT]
        by_cases hWx : wp L A B x = true
        · rw [if_pos hWx]
          rcases f with _ | f
          · exact absurd hf (Nat.not_lt_zero _)
          rw [collapseRow, List.flatMap_cons, List.flatMap_nil,
            List.append_nil]
          by_cases hmx : markerp L A B x = true
          · rw [if_pos hmx, skelRowOf_node mok ht hWx,
              collapseF mok csx (fun t' ht' => child_mem_subF ht ht') f
                (by simp only [readT, List.length_cons] at hf; omega)]
            have hlive : ¬ (liveMp L A B x = true) := fun hl => by
              rw [liveM_not_marker hl] at hmx
              cases hmx
            rw [shallowWT, if_neg hlive]
          · rw [if_neg hmx]
            have hlive : liveMp L A B x = true := by
              rw [wp, Bool.or_eq_true_iff] at hWx
              rcases hWx with h | h
              · exact h
              · exact absurd h hmx
            rw [shallowWT, if_pos hlive]
        · rw [if_neg hWx,
            collapseF mok csx (fun t' ht' => child_mem_subF ht ht') f
              (by simp only [readT, List.length_cons] at hf; omega),
            shallowWT,
            if_neg (show ¬ (liveMp L A B x = true) from fun hl =>
              hWx (wp_of_liveM hl))]
  /-- **J1 (forest)**. -/
  theorem collapseF {L A B : St} (mok : ModelOK L A B) :
      ∀ (F : List Tree), (∀ t ∈ F, t ∈ subF L) →
        ∀ (f : Nat), (readF F).length < f →
        collapseRow L A B f (shallowWF (wp L A B) F) =
          shallowWF (fun w => liveMp L A B w) F
    | [], _, f, hf => by
        rcases f with _ | f
        · exact absurd hf (Nat.not_lt_zero _)
        · rw [shallowWF, shallowWF, collapseRow, List.flatMap_nil]
    | t :: ts, hsub, f, hf => by
        rw [shallowWF, shallowWF, collapseRow_append,
          collapseT mok t (hsub _ (List.mem_cons_self ..)) f
            (by simp only [readF, List.length_append] at hf; omega),
          collapseF mok ts
            (fun t' ht' => hsub _ (List.mem_cons_of_mem _ ht')) f
            (by simp only [readF, List.length_append] at hf; omega)]
end

mutual
  /-- **J2 (tree)**: the collapsed DFS from a subtree's shallow-survivor
  front reads out its survivor filter, in document order. -/
  theorem survDFST {L A B : St} (mok : ModelOK L A B) {mf : Nat}
      (hmf : (read L).length < mf) :
      ∀ (t : Tree), t ∈ subF L → ∀ (f : Nat), (readT t).length < f →
        survDFS L A B mf f (shallowWT (fun w => liveMp L A B w) t) =
          (readT t).filter (fun w => liveMp L A B w)
    | .node x csx, ht, f, hf => by
        rw [shallowWT, readT, List.filter_cons]
        by_cases hlx : liveMp L A B x = true
        · rw [if_pos hlx, if_pos hlx]
          rcases f with _ | f
          · exact absurd hf (Nat.not_lt_zero _)
          rw [survDFS, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, skelRowOf_node mok ht (wp_of_liveM hlx),
            collapseF mok csx (fun t' ht' => child_mem_subF ht ht') mf
              (by
                have h1 := subF_length ht
                simp only [readT, List.length_cons] at h1
                have h2 : (readF L).length = (read L).length := rfl
                omega),
            survDFSF mok hmf csx
              (fun t' ht' => child_mem_subF ht ht') f
              (by simp only [readT, List.length_cons] at hf; omega)]
        · rw [if_neg hlx, if_neg hlx]
          exact survDFSF mok hmf csx
            (fun t' ht' => child_mem_subF ht ht') f
            (by simp only [readT, List.length_cons] at hf; omega)
  /-- **J2 (forest)**. -/
  theorem survDFSF {L A B : St} (mok : ModelOK L A B) {mf : Nat}
      (hmf : (read L).length < mf) :
      ∀ (F : List Tree), (∀ t ∈ F, t ∈ subF L) →
        ∀ (f : Nat), (readF F).length < f →
        survDFS L A B mf f (shallowWF (fun w => liveMp L A B w) F) =
          (readF F).filter (fun w => liveMp L A B w)
    | [], _, f, hf => by
        rcases f with _ | f
        · exact absurd hf (Nat.not_lt_zero _)
        · rw [shallowWF, survDFS, List.flatMap_nil, readF]
          rfl
    | t :: ts, hsub, f, hf => by
        rw [shallowWF, readF, List.filter_append, survDFS_append,
          survDFST mok hmf t (hsub _ (List.mem_cons_self ..)) f
            (by simp only [readF, List.length_append] at hf; omega),
          survDFSF mok hmf ts
            (fun t' ht' => hsub _ (List.mem_cons_of_mem _ ht')) f
            (by simp only [readF, List.length_append] at hf; omega)]
end

/-! ## §4 The output side: the L-filter of the built forest is the
collapsed DFS -/

theorem flatMap_singleton' : ∀ l : List Nat, l.flatMap (fun v => [v]) = l
  | [] => rfl
  | a :: l => by
      rw [List.flatMap_cons, flatMap_singleton' l]
      rfl

theorem flatMap_congr' {f g : Nat → List Nat} :
    ∀ {l : List Nat}, (∀ v ∈ l, f v = g v) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
      rw [List.flatMap_cons, List.flatMap_cons,
        h a (List.mem_cons_self ..),
        flatMap_congr' fun v hv => h v (List.mem_cons_of_mem _ hv)]

theorem flatMap_eq_nil' {f : Nat → List Nat} :
    ∀ {l : List Nat}, (∀ v ∈ l, f v = []) → l.flatMap f = []
  | [], _ => rfl
  | a :: l, h => by
      rw [List.flatMap_cons, h a (List.mem_cons_self ..),
        flatMap_eq_nil' fun v hv => h v (List.mem_cons_of_mem _ hv)]
      rfl

/-- Support restriction: a `flatMap` whose function vanishes off `P` only
sees the `P`-filter. -/
theorem flatMap_filter_support {P : Nat → Bool} {h : Nat → List Nat}
    (hz : ∀ v, P v = false → h v = []) :
    ∀ l : List Nat, l.flatMap h = (l.filter P).flatMap h
  | [] => rfl
  | a :: l => by
      rw [List.flatMap_cons, List.filter_cons]
      by_cases hp : P a = true
      · rw [if_pos hp, List.flatMap_cons, flatMap_filter_support hz l]
      · rw [if_neg hp, hz a (bool_eq_false hp),
          flatMap_filter_support hz l]
        rfl

theorem expandRow_of_nonmarker {rows : List (Nat × List Nat)}
    {mk : Nat → Bool} :
    ∀ (f : Nat) (r : List Nat), (∀ v ∈ r, mk v = false) →
      expandRow rows mk f r = r
  | 0, r, _ => rfl
  | f + 1, r, h => by
      rw [expandRow,
        flatMap_congr' (fun v hv => by rw [if_neg (by simp [h v hv])]),
        flatMap_singleton']

/-- Elements of merged rows are nonzero and, off `L`, branch-live. -/
theorem outRows_mem_class {L A B : St} (mok : ModelOK L A B) {b u : Nat}
    (hu : u ∈ alGet (outRows L A B) b) :
    u ≠ 0 ∧ (contains L u = false → (u ∈ read A ∨ u ∈ read B)) := by
  refine ⟨fun h0 => zero_not_mem_outRows mok (h0 ▸ hu), fun hnL => ?_⟩
  rcases outRows_cases hu with ⟨hL, -⟩ | ⟨hAB, -⟩ | ⟨q, -, hr⟩ | ⟨q, -, hr⟩
  · rw [contains_iff.mpr hL] at hnL
    cases hnL
  · exact hAB
  · exact Or.inl (mem_row_read hr)
  · exact Or.inr (mem_row_read hr)

/-- **Born subtrees are L-free**: the output subtree under a born id never
displays an L-id. -/
theorem born_subtree_L_free {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {mf : Nat} :
    ∀ (f c : Nat), contains L c = false → c ≠ 0 →
      (readF (buildF (outRows L A B) (markerp L A B) mf f c)).filter
        (fun w => contains L w) = []
  | 0, c, _, _ => by
      rw [buildF]
      rfl
  | f + 1, c, hcL, hc0 => by
      rw [buildF, readF_map_node, filter_flatMap]
      refine flatMap_eq_nil' fun d hd => ?_
      -- the row of c is a wholesale born row (or empty), marker-free
      have hrow : ∀ w ∈ alGet (outRows L A B) c,
          contains L w = false ∧ markerp L A B w = false := by
        intro w hw
        by_cases hbA : c ∈ bornIds L A
        · rw [outRows_alGet_of_bornA mok hbA] at hw
          have hwL : contains L w = false := by
            rw [contains_eq_false]
            intro hwl
            obtain ⟨-, hcL', hc0'⟩ := bornIds_spec mok.wfA hbA
            rcases hA w c hwl hw with h0 | hL'
            · exact hc0' h0
            · exact hcL' hL'
          refine ⟨hwL, ?_⟩
          rw [markerp, hwL]
          rfl
        · by_cases hbB : c ∈ bornIds L B
          · rw [outRows_alGet_of_bornB mok hbB] at hw
            have hwL : contains L w = false := by
              rw [contains_eq_false]
              intro hwl
              obtain ⟨-, hcL', hc0'⟩ := bornIds_spec mok.wfB hbB
              rcases hB w c hwl hw with h0 | hL'
              · exact hc0' h0
              · exact hcL' hL'
            refine ⟨hwL, ?_⟩
            rw [markerp, hwL]
            rfl
          · have hskel : ¬ alHas (skelOf L A B).rows c = true := by
              intro hc
              rcases skelOf_keys_spec mok.wfL
                (alHas_iff_mem_keys.mp hc) with h0 | ⟨hm, -⟩
              · exact hc0 h0
              · exact (contains_eq_false.mp hcL) hm
            rw [outRows_alGet_none hskel hbA hbB] at hw
            exact absurd hw (by simp)
      have hexp : expandRow (outRows L A B) (markerp L A B) mf
          (alGet (outRows L A B) c) = alGet (outRows L A B) c :=
        expandRow_of_nonmarker mf _ (fun v hv => (hrow v hv).2)
      rw [hexp] at hd
      obtain ⟨hdL, -⟩ := hrow d hd
      have hd0 : d ≠ 0 := (outRows_mem_class mok hd).1
      rw [List.filter_cons, if_neg (by simp [hdL])]
      exact born_subtree_L_free mok hA hB f d hdL hd0

theorem skelRow_mem_L {L A B : St} {s v : Nat}
    (hv : v ∈ alGet (skelOf L A B).rows s) :
    v ∈ read L ∧ wp L A B v = true := by
  rw [skelOf_alGet, List.mem_filter] at hv
  obtain ⟨hv1, -⟩ := hv
  exact ⟨(List.mem_filter.mp hv1).1, (List.mem_filter.mp hv1).2⟩

theorem collapseRow_mem_L {L A B : St} :
    ∀ (f : Nat) (cs : List Nat), (∀ v ∈ cs, v ∈ read L) →
      ∀ u ∈ collapseRow L A B f cs, u ∈ read L
  | 0, cs, hcs, u, hu => hcs u hu
  | f + 1, cs, hcs, u, hu => by
      rw [collapseRow, List.mem_flatMap] at hu
      obtain ⟨v, hv, hu⟩ := hu
      by_cases hmv : markerp L A B v = true
      · rw [if_pos hmv] at hu
        exact collapseRow_mem_L f _
          (fun w hw => (skelRow_mem_L hw).1) u hu
      · rw [if_neg hmv] at hu
        rcases List.mem_singleton.mp hu with rfl
        exact hcs u hv

/-- **Claim C**: the L-filter of a skeleton key's expansion is its
collapsed skeleton row — the marker splice IS the collapse. -/
theorem expandRow_filter_L {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) :
    ∀ (f s : Nat), alHas (skelOf L A B).rows s = true →
      (expandRow (outRows L A B) (markerp L A B) f
        (alGet (outRows L A B) s)).filter (fun w => contains L w) =
      collapseRow L A B f (alGet (skelOf L A B).rows s)
  | 0, s, hs => by
      rw [expandRow, collapseRow, outRows_alGet_of_skel hs,
        show mergeCmds L A B =
          branchCmds L A (skelOf L A B) (markerp L A B) ++
            branchCmds L B (skelOf L A B) (markerp L A B) from rfl]
      exact rowAssemble_filter_L fun c hc =>
        contains_iff.mpr (skelRow_mem_L hc).1
  | f + 1, s, hs => by
      rw [expandRow, filter_flatMap]
      have hcongr : ∀ v ∈ alGet (outRows L A B) s,
          ((if markerp L A B v = true
            then expandRow (outRows L A B) (markerp L A B) f
              (alGet (outRows L A B) v)
            else [v]).filter (fun w => contains L w)) =
          (if contains L v = true
            then (if markerp L A B v = true
              then collapseRow L A B f (alGet (skelOf L A B).rows v)
              else [v])
            else []) := by
        intro v hv
        by_cases hLv : contains L v = true
        · rw [if_pos hLv]
          by_cases hmv : markerp L A B v = true
          · rw [if_pos hmv, if_pos hmv]
            have hplaced : v ∈ (read L).filter (wp L A B) :=
              List.mem_filter.mpr
                ⟨(marker_spec hmv).1, (marker_spec hmv).2⟩
            exact expandRow_filter_L mok hA hB f v
              (skelOf_alHas_of_placed hplaced)
          · rw [if_neg hmv, if_neg hmv, List.filter_cons, if_pos hLv]
            rfl
        · rw [if_neg hLv]
          by_cases hmv : markerp L A B v = true
          · rw [markerp, bool_eq_false hLv] at hmv
            simp at hmv
          · rw [if_neg hmv, List.filter_cons, if_neg (by simp [hLv])]
            rfl
      rw [flatMap_congr' hcongr,
        flatMap_filter_support (P := fun w => contains L w)
          (fun v hv => by rw [if_neg (by simp [hv])]) _,
        outRows_alGet_of_skel hs,
        show mergeCmds L A B =
          branchCmds L A (skelOf L A B) (markerp L A B) ++
            branchCmds L B (skelOf L A B) (markerp L A B) from rfl,
        rowAssemble_filter_L (fun c hc =>
          contains_iff.mpr (skelRow_mem_L hc).1),
        collapseRow]
      refine flatMap_congr' ?_
      intro v hv
      rw [if_pos (contains_iff.mpr (skelRow_mem_L hv).1)]

/-- **Claim D**: the L-filter of the built forest is the collapsed DFS. -/
theorem buildF_filter_L {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {mf : Nat}
    (hmf : (read L).length < mf) :
    ∀ (f s : Nat), alHas (skelOf L A B).rows s = true →
      (readF (buildF (outRows L A B) (markerp L A B) mf f s)).filter
        (fun w => contains L w) =
      survDFS L A B mf f
        (collapseRow L A B mf (alGet (skelOf L A B).rows s))
  | 0, s, hs => by
      rw [buildF, survDFS]
      rfl
  | f + 1, s, hs => by
      rw [buildF, readF_map_node, filter_flatMap, survDFS]
      have hcongr : ∀ c ∈ expandRow (outRows L A B) (markerp L A B) mf
          (alGet (outRows L A B) s),
          ((c :: readF (buildF (outRows L A B) (markerp L A B) mf f
            c)).filter (fun w => contains L w)) =
          (if contains L c = true
            then c :: survDFS L A B mf f
              (collapseRow L A B mf (alGet (skelOf L A B).rows c))
            else []) := by
        intro c hc
        obtain ⟨b, hb⟩ := (expandRow_spliceReach mf s hc).mem_base
        have hc0 : c ≠ 0 := (outRows_mem_class mok hb).1
        by_cases hLc : contains L c = true
        · rw [if_pos hLc, List.filter_cons, if_pos hLc]
          have hwpc : wp L A B c = true := by
            rcases base_addr mok hA hB hb with ⟨-, hw, -⟩ |
              ⟨hnL, -, -⟩ | ⟨hnL, -⟩ | ⟨hnL, -⟩
            · exact hw
            all_goals rw [hLc] at hnL
            all_goals cases hnL
          have hkey : alHas (skelOf L A B).rows c = true :=
            skelOf_alHas_of_placed (List.mem_filter.mpr
              ⟨contains_iff.mp hLc, hwpc⟩)
          rw [buildF_filter_L mok hA hB hmf f c hkey]
        · rw [if_neg hLc, List.filter_cons, if_neg (by simp [hLc])]
          exact born_subtree_L_free mok hA hB f c
            (bool_eq_false hLc) hc0
      rw [flatMap_congr' hcongr,
        flatMap_filter_support (P := fun w => contains L w)
          (fun v hv => by rw [if_neg (by simp [hv])]) _,
        expandRow_filter_L mok hA hB mf s hs]
      refine flatMap_congr' ?_
      intro c hc
      rw [if_pos (contains_iff.mpr (collapseRow_mem_L mf _
        (fun v hv => (skelRow_mem_L hv).1) c hc))]

/-! ## §5 The M2 theorems -/

theorem bool_eq_of_iff {a b : Bool} (h : (a = true) ↔ (b = true)) :
    a = b := by
  cases a <;> cases b <;> simp_all

theorem filter_congr'' {p q : Nat → Bool} :
    ∀ {l : List Nat}, (∀ x ∈ l, p x = q x) → l.filter p = l.filter q
  | [], _ => rfl
  | a :: l, h => by
      rw [List.filter_cons, List.filter_cons, h a (List.mem_cons_self ..),
        filter_congr'' fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **The M2 core identity, closed**: the merge read filtered to L-ids
equals the L read filtered to merge survivors — L-survivors appear in
L-document order. The marker splice at assembly is the delete splice
(`sibling-linked-proof.md` §4, Lemma M2). -/
theorem merge_L_filter {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) :
    (read (merge L A B)).filter (fun w => contains L w) =
      (read L).filter (fun w => contains (merge L A B) w) := by
  have hrhs : (read L).filter (fun w => contains (merge L A B) w) =
      (read L).filter (fun w => liveMp L A B w) :=
    filter_congr'' fun w _ => bool_eq_of_iff (by
      rw [contains_iff]
      exact merge_ids mok hA hB w)
  rw [hrhs]
  have hlen : (readF L).length = (read L).length := rfl
  have hn : (read L).length <
      (readF L).length + (readF A).length + (readF B).length + 1 := by
    omega
  simp only [merge, read]
  rw [buildF_filter_L mok hA hB hn _ 0 (skelOf_alHas_zero L A B),
    skelRowOf_root mok,
    collapseF mok L (fun t ht => mem_subF_of_mem ht) _ (by omega),
    survDFSF mok hn L (fun t ht => mem_subF_of_mem ht) _ (by omega)]

/-- **Lemma M2 (L-extension), closed**: for merge-surviving L-pairs, the
merge's display order is exactly L's. -/
theorem merge_extends_L {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {u v : Nat}
    (hu : u ∈ ids (merge L A B)) (hv : v ∈ ids (merge L A B))
    (huL : u ∈ ids L) (hvL : v ∈ ids L) :
    precedes (read (merge L A B)) u v ↔ precedes (read L) u v := by
  rw [← precedes_filter_iff (P := fun w => contains L w)
      (l := read (merge L A B))
      (contains_iff.mpr huL) (contains_iff.mpr hvL),
    merge_L_filter mok hA hB,
    precedes_filter_iff (P := fun w => contains (merge L A B) w)
      (l := read L) (contains_iff.mpr hu) (contains_iff.mpr hv)]

end Shesha

section AxiomAuditM2
/-! Axiom audit: the M2 obligations are closed kernel-clean. -/
#print axioms Shesha.skelRowOf_node
#print axioms Shesha.collapseF
#print axioms Shesha.survDFSF
#print axioms Shesha.expandRow_filter_L
#print axioms Shesha.buildF_filter_L
#print axioms Shesha.merge_L_filter
#print axioms Shesha.merge_extends_L
end AxiomAuditM2
