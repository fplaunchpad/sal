import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Merge_Lemmas

/-! # Shesha — forest layer: parent chains and depth (phase 2b, block 0)

The parent-chain/depth machinery shared by the M0/M2 merge lemmas
(`merge_ids`, `merge_read_nodup` — both closed in `Shesha_M0.lean` — and
`merge_L_filter`, the M2 core still owed in `Shesha_Merge_Lemmas.lean`):

- `depthF`/`depthOf` — structural depth of a node (first occurrence, like
  `parF`).
- Bridges: on a WF state a live node sits in exactly the row of its parent
  (`parOf_row_mem`, `row_mem_parOf`), and a child is one level deeper than
  its parent (`depth_row_succ`, `depth_row_root`).
- `wpar` analysis (`wpar_spec`): the attach-deep host of a live L-node is
  the root or a strictly shallower `W`-member — the measure that terminates
  marker chains.
-/

namespace Shesha

open List

/-! ## Structural depth (first occurrence, mirroring `parF`) -/

mutual
  def depthT (u : Nat) : Tree → Option Nat
    | .node i cs => if i = u then some 0 else (depthF u cs).map (· + 1)
  def depthF (u : Nat) : List Tree → Option Nat
    | [] => none
    | t :: ts =>
        match depthT u t with
        | some d => some d
        | none => depthF u ts
end

/-- Depth of `u` in `s` (root row = depth 0; junk `0` when absent). -/
def depthOf (s : St) (u : Nat) : Nat := (depthF u s).getD 0

/-! One-step reductions of `depthF` on a cons (the raw `eq_def` form leaves
an outer match `rw` cannot see into). -/

theorem depthF_cons_some {u d : Nat} {t : Tree} {ts : List Tree}
    (h : depthT u t = some d) : depthF u (t :: ts) = some d := by
  show (match depthT u t with
        | some d => some d
        | none => depthF u ts) = some d
  rw [h]

theorem depthF_cons_none {u : Nat} {t : Tree} {ts : List Tree}
    (h : depthT u t = none) : depthF u (t :: ts) = depthF u ts := by
  show (match depthT u t with
        | some d => some d
        | none => depthF u ts) = depthF u ts
  rw [h]

/-! ## Bridge: `depthF` is defined exactly on live nodes -/

mutual
  theorem depthT_isSome (u : Nat) :
      ∀ t : Tree, (depthT u t).isSome = true ↔ u ∈ readT t
    | .node i cs => by
        by_cases h : i = u
        · subst h; simp [depthT, readT]
        · rw [readT]
          simp only [depthT, if_neg h, List.mem_cons]
          cases hd : depthF u cs with
          | some d =>
              have h2 : u ∈ readF cs := (depthF_isSome u cs).mp (by rw [hd]; rfl)
              simp [hd, h2]
          | none =>
              have h2 : u ∉ readF cs := by rw [← depthF_isSome u cs, hd]; simp
              simp [hd, h2, Ne.symm h]
  theorem depthF_isSome (u : Nat) :
      ∀ ts : List Tree, (depthF u ts).isSome = true ↔ u ∈ readF ts
    | [] => by simp [depthF, readF]
    | t :: ts => by
        rw [depthF.eq_def, readF]
        cases hd : depthT u t with
        | some d =>
            have h1 : u ∈ readT t := (depthT_isSome u t).mp (by rw [hd]; rfl)
            simp [hd, List.mem_append, h1]
        | none =>
            have hnot : u ∉ readT t := by
              rw [← depthT_isSome u t, hd]; simp
            simp [hd, List.mem_append, hnot, depthF_isSome u ts]
end

/-! ## A nonempty row names a live parent -/

mutual
  theorem rowT_parent_mem {u p : Nat} :
      ∀ {t : Tree}, u ∈ rowT p t → p ∈ readT t
    | .node i cs, h => by
        rw [rowT] at h
        by_cases hip : i = p
        · rw [readT, hip]; exact List.mem_cons_self ..
        · rw [if_neg hip] at h
          rw [readT]
          exact List.mem_cons_of_mem _ (rowF_parent_mem h)
  theorem rowF_parent_mem {u p : Nat} :
      ∀ {ts : List Tree}, u ∈ rowF p ts → p ∈ readF ts
    | t :: ts, h => by
        rw [rowF, List.mem_append] at h
        rw [readF, List.mem_append]
        rcases h with h | h
        · exact Or.inl (rowT_parent_mem h)
        · exact Or.inr (rowF_parent_mem h)
end

/-- A member of a nonroot row is a live node's child: the parent is live. -/
theorem row_parent_mem {s : St} {u p : Nat} (hp : p ≠ 0)
    (h : u ∈ row s p) : p ∈ read s := by
  rw [row, if_neg hp] at h
  exact rowF_parent_mem h

/-! ## Small `Nodup`/membership helpers (count-based, name-stable) -/

theorem nodup_append_disj {l₁ l₂ : List Nat} (h : (l₁ ++ l₂).Nodup)
    {a : Nat} (h₁ : a ∈ l₁) (h₂ : a ∈ l₂) : False := by
  have c1 : 0 < l₁.count a := List.count_pos_iff.mpr h₁
  have c2 : 0 < l₂.count a := List.count_pos_iff.mpr h₂
  have hle := count_le_one_of_nodup h a
  rw [List.count_append] at hle
  omega

theorem nodup_append_left {l₁ l₂ : List Nat} (h : (l₁ ++ l₂).Nodup) :
    l₁.Nodup :=
  nodup_of_count_le_one fun c => by
    have := count_le_one_of_nodup h c
    rw [List.count_append] at this
    omega

theorem nodup_append_right {l₁ l₂ : List Nat} (h : (l₁ ++ l₂).Nodup) :
    l₂.Nodup :=
  nodup_of_count_le_one fun c => by
    have := count_le_one_of_nodup h c
    rw [List.count_append] at this
    omega

/-- Row members are live (forest form of `mem_row_read`). -/
theorem mem_rowF_readF {u p : Nat} {ts : List Tree} (h : u ∈ rowF p ts) :
    u ∈ readF ts := by
  have h1 : 0 < (rowF p ts).count u := List.count_pos_iff.mpr h
  have h2 := rowF_count p u ts
  exact List.count_pos_iff.mp (by omega)

/-- Top-level ids are live. -/
theorem mem_topIds_readF {u : Nat} {ts : List Tree} (h : u ∈ ts.map topId) :
    u ∈ readF ts :=
  (topIds_sublist_readF ts).subset h

theorem depthT_eq_none {u : Nat} {t : Tree} (h : u ∉ readT t) :
    depthT u t = none := by
  cases hd : depthT u t with
  | none => rfl
  | some d => exact absurd ((depthT_isSome u t).mp (by rw [hd]; rfl)) h

theorem depthF_eq_none {u : Nat} {ts : List Tree} (h : u ∉ readF ts) :
    depthF u ts = none := by
  cases hd : depthF u ts with
  | none => rfl
  | some d => exact absurd ((depthF_isSome u ts).mp (by rw [hd]; rfl)) h

/-! ## Depth of children: one more than the parent -/

/-- A top-level node has depth 0 (first occurrence pinned by `Nodup`). -/
theorem depthF_top {u : Nat} :
    ∀ {ts : List Tree}, (readF ts).Nodup → u ∈ ts.map topId →
      depthF u ts = some 0
  | t :: ts, hnd, h => by
      rw [readF] at hnd
      rw [List.map_cons, List.mem_cons] at h
      rcases h with hu | hu
      · cases t with
        | node i cs =>
            have hui : i = u := hu.symm
            exact depthF_cons_some (by rw [depthT, if_pos hui])
      · have hT : depthT u t = none :=
          depthT_eq_none fun hmem =>
            nodup_append_disj hnd hmem (mem_topIds_readF hu)
        rw [depthF_cons_none hT]
        exact depthF_top (nodup_append_right hnd) hu

mutual
  /-- Tree form: a row member is one level deeper than the row's owner. -/
  theorem depthT_row (u p : Nat) :
      ∀ t : Tree, (readT t).Nodup → u ∈ rowT p t →
        ∃ dp, depthT p t = some dp ∧ depthT u t = some (dp + 1)
    | .node i cs, hnd, h => by
        rw [readT] at hnd
        have hnd' : (readF cs).Nodup := hnd.of_cons
        rw [rowT] at h
        by_cases hip : i = p
        · rw [if_pos hip] at h
          have hu : u ∈ readF cs := mem_topIds_readF h
          have hui : ¬ i = u := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hu)
          refine ⟨0, by simp [depthT, hip], ?_⟩
          simp [depthT, hui, depthF_top hnd' h]
        · rw [if_neg hip] at h
          obtain ⟨dp, hdp, hdu⟩ := depthF_row u p cs hnd' h
          have hu : u ∈ readF cs := mem_rowF_readF h
          have hui : ¬ i = u := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hu)
          exact ⟨dp + 1, by simp [depthT, hip, hdp],
            by simp [depthT, hui, hdu]⟩
  /-- Forest form. -/
  theorem depthF_row (u p : Nat) :
      ∀ ts : List Tree, (readF ts).Nodup → u ∈ rowF p ts →
        ∃ dp, depthF p ts = some dp ∧ depthF u ts = some (dp + 1)
    | t :: ts, hnd, h => by
        rw [readF] at hnd
        rw [rowF, List.mem_append] at h
        rcases h with h | h
        · obtain ⟨dp, hdp, hdu⟩ := depthT_row u p t (nodup_append_left hnd) h
          exact ⟨dp, depthF_cons_some hdp, depthF_cons_some hdu⟩
        · have hndr : (readF ts).Nodup := nodup_append_right hnd
          obtain ⟨dp, hdp, hdu⟩ := depthF_row u p ts hndr h
          have hTu : depthT u t = none :=
            depthT_eq_none fun hm => nodup_append_disj hnd hm (mem_rowF_readF h)
          have hTp : depthT p t = none :=
            depthT_eq_none fun hm => nodup_append_disj hnd hm (rowF_parent_mem h)
          refine ⟨dp, ?_, ?_⟩
          · rw [depthF_cons_none hTp]; exact hdp
          · rw [depthF_cons_none hTu]; exact hdu
end

/-- **Child depth.** On a WF state, a member of a nonroot row sits one level
below the row's owner. -/
theorem depth_row_succ {s : St} (hwf : WF s) {u p : Nat} (hp : p ≠ 0)
    (h : u ∈ row s p) : depthOf s u = depthOf s p + 1 := by
  rw [row, if_neg hp] at h
  obtain ⟨dp, hdp, hdu⟩ := depthF_row u p s hwf.1 h
  rw [depthOf, depthOf, hdp, hdu]
  rfl

/-- Root-row members have depth 0. -/
theorem depth_row_root {s : St} (hnd : (read s).Nodup) {u : Nat}
    (h : u ∈ row s 0) : depthOf s u = 0 := by
  rw [row, if_pos rfl] at h
  rw [depthOf, depthF_top hnd h]
  rfl

/-! ## `parOf` bridges: a live node sits in its parent's row, and only there -/

theorem parF_cons_some {cur u q : Nat} {t : Tree} {ts : List Tree}
    (h : parT cur u t = some q) : parF cur u (t :: ts) = some q := by
  show (match parT cur u t with
        | some r => some r
        | none => parF cur u ts) = some q
  rw [h]

theorem parF_cons_none {cur u : Nat} {t : Tree} {ts : List Tree}
    (h : parT cur u t = none) : parF cur u (t :: ts) = parF cur u ts := by
  show (match parT cur u t with
        | some r => some r
        | none => parF cur u ts) = parF cur u ts
  rw [h]

mutual
  theorem parT_isSome (u cur : Nat) :
      ∀ t : Tree, u ∈ readT t → (parT cur u t).isSome = true
    | .node i cs, h => by
        rw [parT]
        by_cases hiu : i = u
        · rw [if_pos hiu]; rfl
        · rw [if_neg hiu]
          rw [readT, List.mem_cons] at h
          rcases h with h | h
          · exact absurd h.symm hiu
          · exact parF_isSome u i cs h
  theorem parF_isSome (u cur : Nat) :
      ∀ ts : List Tree, u ∈ readF ts → (parF cur u ts).isSome = true
    | [], h => by simp [readF] at h
    | t :: ts, h => by
        rw [readF, List.mem_append] at h
        cases hT : parT cur u t with
        | some q => rw [parF_cons_some hT]; rfl
        | none =>
            rw [parF_cons_none hT]
            rcases h with h | h
            · exact absurd (parT_isSome u cur t h) (by rw [hT]; simp)
            · exact parF_isSome u cur ts h
end

mutual
  /-- What a `parT` answer certifies: `u` is the top (parent = ambient), or a
  member of the answer's row. `Nodup` pins the first-occurrence search. -/
  theorem parT_spec (u cur : Nat) :
      ∀ (t : Tree) (p : Nat), (readT t).Nodup → parT cur u t = some p →
        (p = cur ∧ u = topId t) ∨ u ∈ rowT p t
    | .node i cs, p, hnd, h => by
        rw [parT] at h
        by_cases hiu : i = u
        · rw [if_pos hiu] at h
          exact Or.inl ⟨(Option.some.inj h).symm, hiu.symm⟩
        · rw [if_neg hiu] at h
          rw [readT] at hnd
          have hnd' : (readF cs).Nodup := hnd.of_cons
          rcases parF_spec u i cs p hnd' h with ⟨rfl, hu⟩ | hu
          · rw [rowT, if_pos rfl]
            exact Or.inr hu
          · rw [rowT]
            by_cases hip : i = p
            · exact absurd (hip ▸ rowF_parent_mem hu)
                (List.nodup_cons.mp hnd).1
            · rw [if_neg hip]
              exact Or.inr hu
  theorem parF_spec (u cur : Nat) :
      ∀ (ts : List Tree) (p : Nat), (readF ts).Nodup → parF cur u ts = some p →
        (p = cur ∧ u ∈ ts.map topId) ∨ u ∈ rowF p ts
    | [], p, _, h => by simp [parF] at h
    | t :: ts, p, hnd, h => by
        rw [readF] at hnd
        cases hT : parT cur u t with
        | some q =>
            rw [parF_cons_some hT] at h
            have hq : q = p := Option.some.inj h
            subst hq
            rcases parT_spec u cur t q (nodup_append_left hnd) hT with
              ⟨hc, ht⟩ | hu
            · exact Or.inl ⟨hc, by simp [ht]⟩
            · exact Or.inr (by rw [rowF, List.mem_append]; exact Or.inl hu)
        | none =>
            rw [parF_cons_none hT] at h
            rcases parF_spec u cur ts p (nodup_append_right hnd) h with
              ⟨hc, hu⟩ | hu
            · exact Or.inl ⟨hc, by simp [hu]⟩
            · exact Or.inr (by rw [rowF, List.mem_append]; exact Or.inr hu)
end

/-- A live node is a member of its parent's row. -/
theorem parOf_row_mem {s : St} (hwf : WF s) {u : Nat} (hu : u ∈ read s) :
    u ∈ row s (parOf s u) := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (parF_isSome u 0 s hu)
  rcases parF_spec u 0 s p hwf.1 hp with ⟨rfl, hu'⟩ | hu'
  · rw [parOf, hp]
    show u ∈ row s 0
    rw [row, if_pos rfl]
    exact hu'
  · rw [parOf, hp]
    show u ∈ row s p
    by_cases hp0 : p = 0
    · subst hp0
      exact absurd (rowF_parent_mem hu') hwf.2
    · rw [row, if_neg hp0]
      exact hu'

/-- Rows determine the parent: `u ∈ row s p` forces `parOf s u = p`. -/
theorem row_mem_parOf {s : St} (hwf : WF s) {u p : Nat}
    (h : u ∈ row s p) : parOf s u = p := by
  have h2 := parOf_row_mem hwf (mem_row_read h)
  by_cases hne : parOf s u = p
  · exact hne
  · exact (row_disjoint hwf hne h2 h).elim

/-- Parent step: the root, or a live node exactly one level up. -/
theorem parOf_step {s : St} (hwf : WF s) {u : Nat} (hu : u ∈ read s) :
    parOf s u = 0 ∨
      (parOf s u ∈ read s ∧ depthOf s u = depthOf s (parOf s u) + 1) := by
  have h := parOf_row_mem hwf hu
  by_cases hp : parOf s u = 0
  · exact Or.inl hp
  · exact Or.inr ⟨row_parent_mem hp h, depth_row_succ hwf hp h⟩

/-! ## Depth is bounded by the read length -/

mutual
  theorem depthT_lt (u : Nat) :
      ∀ (t : Tree) (d : Nat), depthT u t = some d → d < (readT t).length
    | .node i cs, d, h => by
        rw [depthT] at h
        by_cases hiu : i = u
        · rw [if_pos hiu] at h
          have hd : d = 0 := (Option.some.inj h).symm
          subst hd
          simp [readT]
        · rw [if_neg hiu] at h
          cases hd : depthF u cs with
          | none => rw [hd] at h; simp at h
          | some d' =>
              rw [hd] at h
              have he : d = d' + 1 := (Option.some.inj h).symm
              subst he
              have := depthF_lt u cs d' hd
              simp only [readT, List.length_cons]
              omega
  theorem depthF_lt (u : Nat) :
      ∀ (ts : List Tree) (d : Nat), depthF u ts = some d →
        d < (readF ts).length
    | [], d, h => by simp [depthF] at h
    | t :: ts, d, h => by
        cases hT : depthT u t with
        | some d' =>
            rw [depthF_cons_some hT] at h
            have he : d = d' := (Option.some.inj h).symm
            subst he
            have := depthT_lt u t d hT
            simp only [readF, List.length_append]
            omega
        | none =>
            rw [depthF_cons_none hT] at h
            have := depthF_lt u ts d h
            simp only [readF, List.length_append]
            omega
end

theorem depthOf_lt_length {s : St} {u : Nat} (hu : u ∈ read s) :
    depthOf s u < (read s).length := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp ((depthF_isSome u s).mpr hu)
  rw [depthOf, hd]
  exact depthF_lt u s d hd

/-! ## The attach-deep host: root or a strictly shallower `W`-member -/

theorem wparGo_zero (L : St) (W : Nat → Bool) :
    ∀ fuel, wparGo L W fuel 0 = 0
  | 0 => rfl
  | fuel + 1 => by simp [wparGo]

theorem wparGo_spec {L : St} (hwf : WF L) (W : Nat → Bool) :
    ∀ (fuel p : Nat), p ∈ read L → depthOf L p < fuel →
      wparGo L W fuel p = 0 ∨
        (wparGo L W fuel p ∈ read L ∧ W (wparGo L W fuel p) = true ∧
          depthOf L (wparGo L W fuel p) ≤ depthOf L p)
  | 0, p => fun _ hd => absurd hd (Nat.not_lt_zero _)
  | fuel + 1, p => fun hp hd => by
      rw [wparGo]
      by_cases hW : W p = true
      · rw [if_pos (by simp [hW])]
        exact Or.inr ⟨hp, hW, Nat.le_refl _⟩
      · have hp0 : p ≠ 0 := fun h0 => hwf.2 (h0 ▸ hp)
        rw [if_neg (show ¬ ((p == 0 || W p) = true) by simp [hW, hp0])]
        rcases parOf_step hwf hp with h0 | ⟨hmem, hdep⟩
        · rw [h0, wparGo_zero]
          exact Or.inl rfl
        · have hlt : depthOf L (parOf L p) < fuel := by omega
          rcases wparGo_spec hwf W fuel (parOf L p) hmem hlt with h | ⟨h1, h2, h3⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, h2, by omega⟩

/-- **Host spec.** On a WF LCA, the attach-deep host of a live node is the
root or a *strictly shallower* live `W`-member — the measure that terminates
marker-splice chains (`wpar` never descends or stalls). -/
theorem wpar_spec {L : St} (hwf : WF L) (W : Nat → Bool) {u : Nat}
    (hu : u ∈ read L) :
    wpar L W u = 0 ∨
      (wpar L W u ∈ read L ∧ W (wpar L W u) = true ∧
        depthOf L (wpar L W u) < depthOf L u) := by
  rw [wpar]
  rcases parOf_step hwf hu with h0 | ⟨hmem, hdep⟩
  · rw [h0, wparGo_zero]
    exact Or.inl rfl
  · have hlt : depthOf L (parOf L u) < (read L).length + 1 :=
      Nat.lt_succ_of_lt (depthOf_lt_length hmem)
    rcases wparGo_spec hwf W _ _ hmem hlt with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, by omega⟩

end Shesha
