import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_M0

/-! # Shesha — M2: the L-extension order theorem (phase 2b, block 3)

Closes `merge_L_filter` (the skeleton-DFS-order = L-document-order core) and
hosts `merge_extends_L`, both previously owed in
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

end Shesha
