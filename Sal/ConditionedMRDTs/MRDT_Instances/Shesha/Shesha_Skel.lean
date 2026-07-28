import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Forest

/-! # Shesha: skeleton layer

Exact characterization of `skelOf`:

- alist algebra: `alGet`/`alHas` through `alApp`/`alEnsure` (`alGet_alApp`,
  `alGet_alEnsure`, …), key preservation and key `Nodup`.
- `skelOf_alGet`, skeleton row `p` is exactly the `W`-members of `L` hosted
  at `p` (`wpar` = p), in L-document order.
- `rowofGet_skelOf`, the recorded host of a placed node is its `wpar`.
- `skelOf_keys_nodup`, no skeleton row key repeats (each row assembled
  exactly once by `outRows`).
- `bbrows_alGet`, a born node's wholesale row is its branch row.
-/

namespace Shesha

open List

/-! ## alist algebra -/

theorem alGet_nil (k : Nat) : alGet ([] : List (Nat × List Nat)) k = [] := rfl

theorem alGet_cons (kv : Nat × List Nat) (al : List (Nat × List Nat))
    (k : Nat) :
    alGet (kv :: al) k = if kv.1 == k then kv.2 else alGet al k := by
  by_cases h : (kv.1 == k) = true
  · simp [alGet, List.find?_cons_of_pos, h]
  · simp [alGet, List.find?_cons_of_neg, h]

theorem alGet_singleton (a k : Nat) (r : List Nat) :
    alGet [(a, r)] k = if a == k then r else [] := by
  rw [alGet_cons]
  split <;> rfl

theorem alHas_cons (kv : Nat × List Nat) (al : List (Nat × List Nat))
    (k : Nat) :
    alHas (kv :: al) k = ((kv.1 == k) || alHas al k) := by
  simp [alHas]

theorem alHas_iff_mem_keys {al : List (Nat × List Nat)} {k : Nat} :
    alHas al k = true ↔ k ∈ al.map (·.1) := by
  rw [alHas, List.any_eq_true]
  constructor
  · rintro ⟨kv, hm, hp⟩
    exact List.mem_map.mpr ⟨kv, hm, by simpa using hp⟩
  · rintro hm
    obtain ⟨kv, hkv, he⟩ := List.mem_map.mp hm
    exact ⟨kv, hkv, by simpa using he⟩

/-- `alGet` through the in-place update `alApp` performs when the key
exists. -/
theorem alGet_upd (k v : Nat) :
    ∀ (al : List (Nat × List Nat)) (k' : Nat),
      alGet (al.map (fun kv =>
          if kv.1 == k then (kv.1, kv.2 ++ [v]) else kv)) k'
        = if k' = k ∧ alHas al k = true then alGet al k ++ [v]
          else alGet al k'
  | [], k' => by simp [alGet, alHas]
  | kv :: al, k' => by
      obtain ⟨k₀, r₀⟩ := kv
      by_cases h0 : k₀ = k
      · by_cases h1 : k₀ = k'
        · have hk : k' = k := h1.symm.trans h0
          simp [List.map_cons, alGet_cons, alHas_cons, h0, hk]
        · have hk : ¬ k' = k := fun e => h1 (h0.trans e.symm)
          rw [List.map_cons, alGet_cons, alGet_upd k v al k']
          simp [alGet_cons, alHas_cons, h0, hk, Ne.symm hk]
      · by_cases h1 : k₀ = k'
        · have hk : ¬ k' = k := fun e => h0 (h1.trans e)
          simp [List.map_cons, alGet_cons, alHas_cons, h0, h1, hk]
        · rw [List.map_cons, alGet_cons, alGet_upd k v al k']
          simp [alGet_cons, alHas_cons, h0, h1]

/-- `alGet` through `alApp`: row `k` gains `v` at the end, others
unchanged. -/
theorem alGet_alApp (al : List (Nat × List Nat)) (k v k' : Nat) :
    alGet (alApp al k v) k' =
      if k' = k then alGet al k ++ [v] else alGet al k' := by
  rw [alApp]
  by_cases hh : alHas al k = true
  · rw [if_pos hh, alGet_upd]
    by_cases he : k' = k
    · rw [if_pos ⟨he, hh⟩, if_pos he]
    · rw [if_neg (fun hc => he hc.1), if_neg he]
  · rw [if_neg hh, alGet_append]
    by_cases he : k' = k
    · rw [if_pos he, he, if_neg hh, alGet_singleton,
        if_pos (show (k == k) = true by simp), alGet_eq_nil_of_not_has hh]
      rfl
    · rw [if_neg he]
      by_cases hh' : alHas al k' = true
      · rw [if_pos hh']
      · rw [if_neg hh', alGet_eq_nil_of_not_has hh', alGet_singleton,
          if_neg (show ¬ ((k == k') = true) by simp [Ne.symm he])]

/-- `alEnsure` never changes what `alGet` sees. -/
theorem alGet_alEnsure (al : List (Nat × List Nat)) (k k' : Nat) :
    alGet (alEnsure al k) k' = alGet al k' := by
  rw [alEnsure]
  by_cases hh : alHas al k = true
  · rw [if_pos hh]
  · rw [if_neg hh, alGet_append]
    by_cases hh' : alHas al k' = true
    · rw [if_pos hh']
    · rw [if_neg hh', alGet_eq_nil_of_not_has hh', alGet_singleton]
      split <;> rfl

/-! ## Key lists through `alApp`/`alEnsure` -/

theorem alApp_keys (al : List (Nat × List Nat)) (k v : Nat) :
    (alApp al k v).map (·.1) =
      if alHas al k = true then al.map (·.1) else al.map (·.1) ++ [k] := by
  rw [alApp]
  by_cases hh : alHas al k = true
  · rw [if_pos hh, if_pos hh, List.map_map]
    refine List.map_congr_left fun kv _ => ?_
    by_cases hk : kv.1 = k
    · simp [hk]
    · simp [hk]
  · rw [if_neg hh, if_neg hh]
    simp

theorem alEnsure_keys (al : List (Nat × List Nat)) (k : Nat) :
    (alEnsure al k).map (·.1) =
      if alHas al k = true then al.map (·.1) else al.map (·.1) ++ [k] := by
  rw [alEnsure]
  by_cases hh : alHas al k = true
  · rw [if_pos hh, if_pos hh]
  · rw [if_neg hh, if_neg hh]
    simp

theorem nodup_snoc {l : List Nat} {a : Nat} (hnd : l.Nodup) (ha : a ∉ l) :
    (l ++ [a]).Nodup :=
  nodup_of_count_le_one fun c => by
    have h1 := count_le_one_of_nodup hnd c
    rw [List.count_append]
    by_cases hc : c = a
    · have h0 : l.count c = 0 := List.count_eq_zero_of_not_mem (hc ▸ ha)
      have h2 : ([a] : List Nat).count c ≤ 1 := by
        have := List.count_le_length (l := [a]) (a := c)
        simpa using this
      omega
    · have h2 : ([a] : List Nat).count c = 0 := by
        rw [List.count_eq_zero]
        simp [hc]
      omega

/-! ## The skeleton fold, characterized

All statements are over the literal fold body `skelOf` uses (with the host
function `h` abstracted); `simp only [skelOf]` aligns them. -/

theorem skelFold_alGet (h : Nat → Nat) :
    ∀ (l : List Nat) (sk : Skel) (p : Nat),
      alGet (l.foldl (fun sk u =>
          { rows := alEnsure (alApp sk.rows (h u) u) u
            rowof := sk.rowof ++ [(u, h u)] }) sk).rows p
        = alGet sk.rows p ++ l.filter (fun u => h u == p)
  | [], sk, p => by simp
  | u :: l, sk, p => by
      rw [List.foldl_cons, skelFold_alGet h l _ p, List.filter_cons]
      dsimp only
      rw [alGet_alEnsure, alGet_alApp]
      by_cases he : p = h u
      · rw [if_pos he, if_pos (show (h u == p) = true by simp [he]), he]
        simp
      · rw [if_neg he,
          if_neg (show ¬ ((h u == p) = true) by
            simp only [beq_iff_eq]
            exact fun e => he e.symm)]

theorem skelFold_rowof (h : Nat → Nat) :
    ∀ (l : List Nat) (sk : Skel),
      (l.foldl (fun sk u =>
          { rows := alEnsure (alApp sk.rows (h u) u) u
            rowof := sk.rowof ++ [(u, h u)] }) sk).rowof
        = sk.rowof ++ l.map (fun u => (u, h u))
  | [], sk => by simp
  | u :: l, sk => by
      rw [List.foldl_cons, skelFold_rowof h l, List.map_cons]
      dsimp only
      rw [List.append_assoc]
      rfl

theorem skelFold_keys_nodup (h : Nat → Nat) :
    ∀ (l : List Nat) (sk : Skel), (sk.rows.map (·.1)).Nodup →
      (((l.foldl (fun sk u =>
          { rows := alEnsure (alApp sk.rows (h u) u) u
            rowof := sk.rowof ++ [(u, h u)] }) sk).rows).map (·.1)).Nodup
  | [], sk, hnd => hnd
  | u :: l, sk, hnd => by
      rw [List.foldl_cons]
      refine skelFold_keys_nodup h l _ ?_
      dsimp only
      rw [alEnsure_keys, alApp_keys]
      by_cases h1 : alHas sk.rows (h u) = true
      · rw [if_pos h1]
        by_cases h2 : alHas (alApp sk.rows (h u) u) u = true
        · rw [if_pos h2]
          exact hnd
        · rw [if_neg h2]
          refine nodup_snoc hnd fun hm => h2 ?_
          rw [alHas_iff_mem_keys, alApp_keys, if_pos h1]
          exact hm
      · rw [if_neg h1]
        have hnu : h u ∉ sk.rows.map (·.1) := fun hm =>
          h1 (alHas_iff_mem_keys.mpr hm)
        by_cases h2 : alHas (alApp sk.rows (h u) u) u = true
        · rw [if_pos h2]
          exact nodup_snoc hnd hnu
        · rw [if_neg h2]
          have hu2 : u ∉ sk.rows.map (·.1) ++ [h u] := fun hm => by
            refine h2 ?_
            rw [alHas_iff_mem_keys, alApp_keys, if_neg h1]
            exact hm
          exact nodup_snoc (nodup_snoc hnd hnu) hu2

/-- Every key the fold creates is an initial key, a placed node, or a host. -/
theorem skelFold_keys_sub (h : Nat → Nat) :
    ∀ (l : List Nat) (sk : Skel) (x : Nat),
      x ∈ ((l.foldl (fun sk u =>
          { rows := alEnsure (alApp sk.rows (h u) u) u
            rowof := sk.rowof ++ [(u, h u)] }) sk).rows).map (·.1) →
      x ∈ sk.rows.map (·.1) ∨ x ∈ l ∨ x ∈ l.map h
  | [], sk, x, hx => Or.inl hx
  | u :: l, sk, x, hx => by
      rw [List.foldl_cons] at hx
      rcases skelFold_keys_sub h l _ x hx with hx | hx | hx
      · dsimp only at hx
        rw [alEnsure_keys] at hx
        by_cases h2 : alHas (alApp sk.rows (h u) u) u = true
        · rw [if_pos h2, alApp_keys] at hx
          by_cases h1 : alHas sk.rows (h u) = true
          · rw [if_pos h1] at hx
            exact Or.inl hx
          · rw [if_neg h1] at hx
            rcases List.mem_append.mp hx with hx | hx
            · exact Or.inl hx
            · rcases List.mem_singleton.mp hx with rfl
              exact Or.inr (Or.inr (by simp))
        · rw [if_neg h2, alApp_keys] at hx
          rcases List.mem_append.mp hx with hx | hx
          · by_cases h1 : alHas sk.rows (h u) = true
            · rw [if_pos h1] at hx
              exact Or.inl hx
            · rw [if_neg h1] at hx
              rcases List.mem_append.mp hx with hx | hx
              · exact Or.inl hx
              · rcases List.mem_singleton.mp hx with rfl
                exact Or.inr (Or.inr (by simp))
          · rcases List.mem_singleton.mp hx with rfl
            exact Or.inr (Or.inl (by simp))
      · exact Or.inr (Or.inl (List.mem_cons_of_mem u hx))
      · rw [List.map_cons]
        exact Or.inr (Or.inr (List.mem_cons_of_mem _ hx))

/-! ## `skelOf`, characterized -/

/-- **Skeleton row `p`** = the `W`-members of `L` hosted at `p` (`wpar` = p),
in L-document order. -/
theorem skelOf_alGet (L A B : St) (p : Nat) :
    alGet (skelOf L A B).rows p =
      ((read L).filter (wp L A B)).filter
        (fun u => wpar L (wp L A B) u == p) := by
  simp only [skelOf]
  rw [skelFold_alGet]
  dsimp only
  rw [alGet_singleton]
  split <;> rfl

theorem find_map_pair (h : Nat → Nat) :
    ∀ (l : List Nat) (u : Nat), u ∈ l →
      (l.map (fun x => (x, h x))).find? (fun kv => kv.1 == u) = some (u, h u)
  | x :: l, u, hu => by
      rw [List.map_cons]
      by_cases hx : x = u
      · rw [List.find?_cons_of_pos (by simp [hx]), hx]
      · rw [List.find?_cons_of_neg (by simp [hx])]
        rcases List.mem_cons.mp hu with h' | h'
        · exact absurd h'.symm hx
        · exact find_map_pair h l u h'

/-- The recorded host of a placed node is its `wpar`. -/
theorem rowofGet_skelOf {L A B : St} {u : Nat}
    (hu : u ∈ (read L).filter (wp L A B)) :
    rowofGet (skelOf L A B) u = wpar L (wp L A B) u := by
  simp only [rowofGet, skelOf]
  rw [skelFold_rowof]
  dsimp only
  rw [List.nil_append,
    find_map_pair (fun u => wpar L (wp L A B) u) _ u hu]

/-- Skeleton row keys never repeat. -/
theorem skelOf_keys_nodup (L A B : St) :
    ((skelOf L A B).rows.map (·.1)).Nodup := by
  simp only [skelOf]
  refine skelFold_keys_nodup _ _ _ ?_
  simp

/-- Every skeleton key is the root or a live `W`-member of `L`. -/
theorem skelOf_keys_spec {L A B : St} (hwf : WF L) {x : Nat}
    (hx : x ∈ (skelOf L A B).rows.map (·.1)) :
    x = 0 ∨ (x ∈ read L ∧ wp L A B x = true) := by
  simp only [skelOf] at hx
  rcases skelFold_keys_sub _ _ _ x hx with hx | hx | hx
  · simp at hx
    exact Or.inl hx
  · rw [List.mem_filter] at hx
    exact Or.inr ⟨hx.1, hx.2⟩
  · rw [List.mem_map] at hx
    obtain ⟨u, hu, he⟩ := hx
    rw [List.mem_filter] at hu
    rcases wpar_spec hwf (wp L A B) hu.1 with h0 | ⟨hm, hw, -⟩
    · exact Or.inl (he ▸ h0)
    · exact Or.inr (he ▸ ⟨hm, hw⟩)

/-! ## `bbrows`, characterized -/

theorem bornIds_nodup {L X : St} (hnd : (read X).Nodup) :
    (bornIds L X).Nodup := hnd.filter _

theorem filterMapRow_keys_sublist (X : St) :
    ∀ l : List Nat,
      ((l.filterMap (fun q =>
        if (row X q).isEmpty then none
        else some (q, row X q))).map (·.1)) <+ l
  | [] => by simp
  | x :: l => by
      by_cases he : (row X x).isEmpty = true
      · rw [List.filterMap_cons_none (by rw [if_pos he])]
        exact (filterMapRow_keys_sublist X l).cons x
      · rw [List.filterMap_cons_some (by rw [if_neg he]), List.map_cons]
        exact (filterMapRow_keys_sublist X l).cons₂ x

theorem bbrows_keys_nodup {L X : St} (hnd : (read X).Nodup) :
    ((bbrows L X).map (·.1)).Nodup :=
  (bornIds_nodup hnd).sublist (filterMapRow_keys_sublist X (bornIds L X))

theorem alGet_filterMapRow (X : St) :
    ∀ (l : List Nat), l.Nodup → ∀ q ∈ l,
      alGet (l.filterMap (fun q' =>
        if (row X q').isEmpty then none
        else some (q', row X q'))) q = row X q
  | [], _, q, hq => by simp at hq
  | x :: l, hnd, q, hq => by
      rcases List.mem_cons.mp hq with he | hq'
      · by_cases hem : (row X x).isEmpty = true
        · rw [List.filterMap_cons_none (by rw [if_pos hem])]
          have hql : q ∉ l := by
            rw [he]
            exact (List.nodup_cons.mp hnd).1
          have hnh : ¬ alHas (l.filterMap (fun q' =>
              if (row X q').isEmpty then none
              else some (q', row X q'))) q = true := fun hh =>
            hql ((filterMapRow_keys_sublist X l).subset
              (alHas_iff_mem_keys.mp hh))
          rw [alGet_eq_nil_of_not_has hnh, he]
          exact (List.isEmpty_iff.mp hem).symm
        · rw [List.filterMap_cons_some (by rw [if_neg hem]), alGet_cons,
            if_pos (by simp [he.symm]), he]
      · have hxq : ¬ (x = q) := fun e =>
          (List.nodup_cons.mp hnd).1 (e ▸ hq')
        by_cases hem : (row X x).isEmpty = true
        · rw [List.filterMap_cons_none (by rw [if_pos hem])]
          exact alGet_filterMapRow X l (List.nodup_cons.mp hnd).2 q hq'
        · rw [List.filterMap_cons_some (by rw [if_neg hem]), alGet_cons,
            if_neg (by simp [hxq])]
          exact alGet_filterMapRow X l (List.nodup_cons.mp hnd).2 q hq'

/-- A born node's wholesale row is its branch row (empty rows simply have no
entry, and `alGet` defaults to `[]` = the row). -/
theorem bbrows_alGet {L X : St} (hnd : (read X).Nodup) {q : Nat}
    (hq : q ∈ bornIds L X) : alGet (bbrows L X) q = row X q := by
  unfold bbrows
  by_cases hem : (row X q).isEmpty = true
  · have hnh : ¬ alHas ((bornIds L X).filterMap (fun q' =>
        if (row X q').isEmpty then none
        else some (q', row X q'))) q = true := by
      intro hh
      obtain ⟨kv, hkv, hp⟩ := List.any_eq_true.mp hh
      obtain ⟨q', hq', hg⟩ := List.mem_filterMap.mp hkv
      by_cases he' : (row X q').isEmpty = true
      · rw [if_pos he'] at hg
        cases hg
      · rw [if_neg he'] at hg
        cases hg
        have heq : q' = q := by simpa using hp
        rw [heq] at he'
        exact he' hem
    rw [alGet_eq_nil_of_not_has hnh]
    exact (List.isEmpty_iff.mp hem).symm
  · exact alGet_filterMapRow X (bornIds L X) (bornIds_nodup hnd) q hq

/-! ## `dedupNat` and `hosts` -/

theorem dedupNat_mem : ∀ {l : List Nat} {x : Nat}, x ∈ dedupNat l ↔ x ∈ l
  | [], x => by simp [dedupNat]
  | a :: l, x => by
      rw [dedupNat]
      by_cases hc : l.contains a = true
      · rw [if_pos hc]
        rw [dedupNat_mem (l := l)]
        constructor
        · exact List.mem_cons_of_mem a
        · intro h
          rcases List.mem_cons.mp h with rfl | h
          · exact List.contains_iff_mem.mp hc
          · exact h
      · rw [if_neg hc, List.mem_cons, List.mem_cons,
          dedupNat_mem (l := l)]

theorem dedupNat_nodup : ∀ l : List Nat, (dedupNat l).Nodup
  | [] => by simp [dedupNat]
  | a :: l => by
      rw [dedupNat]
      by_cases hc : l.contains a = true
      · rw [if_pos hc]
        exact dedupNat_nodup l
      · rw [if_neg hc, List.nodup_cons]
        refine ⟨fun hm => ?_, dedupNat_nodup l⟩
        exact hc (List.contains_iff_mem.mpr (dedupNat_mem.mp hm))

theorem hosts_nodup (L X : St) : (hosts L X).Nodup := dedupNat_nodup _

theorem hosts_mem {L X : St} {p : Nat} (hp : p ∈ hosts L X) :
    (p = 0 ∨ contains L p = true) ∧
      ∃ u ∈ bornIds L X, parOf X u = p := by
  unfold hosts at hp
  rw [dedupNat_mem, List.mem_filter] at hp
  obtain ⟨hm, hcond⟩ := hp
  rw [List.mem_map] at hm
  obtain ⟨u, hu, he⟩ := hm
  refine ⟨?_, u, hu, he⟩
  rcases Bool.or_eq_true_iff.mp hcond with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr h

end Shesha
