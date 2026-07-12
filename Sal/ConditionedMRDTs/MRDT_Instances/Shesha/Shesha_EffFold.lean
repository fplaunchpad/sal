import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Replay

/-! # Shesha — effective-fold theory (phase 2e, piece i)

The structure theory of folds of **effective** enumerations, feeding the
join hook `shesha_join_at_eff` (`Shesha_Cond.lean`):

* §0 **read/steps bookkeeping** — live ids come only from inserts.
* §1 **the `drop` splice** — simultaneous splice-out of a *set* of ids
  (`dropF`); `delete` is the singleton instance, the delete-*fold* is the
  set instance (`steps_dels`): the delete phase of any enumeration is
  **order-free and set-determined**.
* §2 **delete postponement** — deletes bubble to the end of an enumeration
  past inserts they don't touch (`steps_postpone_deletes`); with §1 this
  puts every effective fold in the normal form
  `dropF (deleted) (insert-phase forest)`.
* §3 **insert-phase structure** — the fold of an effective, fresh
  insert-only list is the *anchored forest*: ids = the inserted ids,
  each row = that anchor's inserts, newest first (head-insertion).
* §4 **fronts** — the rows of a `dropF`-collapse: the row of a live node
  `p` is the *front* of `p`'s pre-splice row (each dead child replaced by
  its recursively-collapsed row, in place). -/

namespace Shesha

/-! ## §0 read/steps bookkeeping -/

/-- The inserted ids of an op list, in order. -/
def opInsIds : List Op → List Nat
  | [] => []
  | .ins x _ :: ρ => x :: opInsIds ρ
  | .del _ :: ρ => opInsIds ρ

/-- The deleted ids of an op list, in order. -/
def opDelIds : List Op → List Nat
  | [] => []
  | .ins _ _ :: ρ => opDelIds ρ
  | .del d :: ρ => d :: opDelIds ρ

/-- Live ids come only from the start state or from inserts. -/
theorem mem_read_steps :
    ∀ (ρ : List Op) (s : St) {u : Nat},
      u ∈ read (steps s ρ) → u ∈ read s ∨ u ∈ opInsIds ρ
  | [], _, _, h => Or.inl h
  | .ins x a :: ρ, s, u, h => by
      rcases mem_read_steps ρ (Shesha.insert s x a) h with h' | h'
      · rcases seqIns_mem (by rw [← read_insert]; exact h') with he | h''
        · exact Or.inr (by rw [opInsIds, he]; exact List.mem_cons_self ..)
        · exact Or.inl h''
      · exact Or.inr (by rw [opInsIds]; exact List.mem_cons_of_mem _ h')
  | .del d :: ρ, s, u, h => by
      rcases mem_read_steps ρ (Shesha.delete s d) h with h' | h'
      · rw [read_delete, seqDel, List.mem_filter] at h'
        exact Or.inl h'.1
      · exact Or.inr h'

/-- Dead stays dead: an id absent from the state with no insert in the
tail never reappears. -/
theorem not_mem_read_steps {ρ : List Op} {s : St} {u : Nat}
    (hs : u ∉ read s) (hρ : u ∉ opInsIds ρ) : u ∉ read (steps s ρ) :=
  fun h => (mem_read_steps ρ s h).elim hs hρ

/-! ## §1 the `drop` splice -/

mutual
  /-- Splice out every node whose id satisfies `D`, in one pass: a dead
  node's (recursively dropped) row replaces it in place. -/
  def dropT (D : Nat → Bool) : Tree → List Tree
    | .node i cs => if D i then dropF D cs else [.node i (dropF D cs)]
  def dropF (D : Nat → Bool) : List Tree → List Tree
    | [] => []
    | t :: ts => dropT D t ++ dropF D ts
end

theorem dropF_nil {D : Nat → Bool} : dropF D [] = [] := rfl

theorem dropF_cons {D : Nat → Bool} {t : Tree} {ts : List Tree} :
    dropF D (t :: ts) = dropT D t ++ dropF D ts := rfl

theorem dropF_append {D : Nat → Bool} :
    ∀ F G : List Tree, dropF D (F ++ G) = dropF D F ++ dropF D G
  | [], _ => rfl
  | t :: ts, G => by
      rw [List.cons_append, dropF_cons, dropF_cons, dropF_append ts G,
        List.append_assoc]

mutual
  /-- `drop` only reads the predicate pointwise. -/
  theorem dropT_congr {D D' : Nat → Bool} (h : ∀ u, D u = D' u) :
      ∀ t : Tree, dropT D t = dropT D' t
    | .node i cs => by
        rw [dropT, dropT, h i, dropF_congr h cs]
  theorem dropF_congr {D D' : Nat → Bool} (h : ∀ u, D u = D' u) :
      ∀ F : List Tree, dropF D F = dropF D' F
    | [] => rfl
    | t :: ts => by
        rw [dropF_cons, dropF_cons, dropT_congr h t, dropF_congr h ts]
end

mutual
  /-- `delete` is the singleton `drop`. -/
  theorem delT_eq_dropT (d : Nat) :
      ∀ t : Tree, delT d t = dropT (fun u => u == d) t
    | .node i cs => by
        rw [delT, dropT, delF_eq_dropF d cs]
        by_cases h : i = d
        · rw [if_pos h, if_pos (by simp [h])]
        · rw [if_neg h, if_neg (by simp [h])]
  theorem delF_eq_dropF (d : Nat) :
      ∀ F : List Tree, delF d F = dropF (fun u => u == d) F
    | [] => rfl
    | t :: ts => by
        rw [delF_cons, dropF_cons, delT_eq_dropT d t, delF_eq_dropF d ts]
end

mutual
  /-- Composition: successive drops fuse to the union. -/
  theorem dropF_dropT {D D' : Nat → Bool} :
      ∀ t : Tree, dropF D (dropT D' t) = dropT (fun u => D' u || D u) t
    | .node i cs => by
        rw [dropT, dropT]
        by_cases h' : D' i
        · rw [if_pos h', if_pos (by rw [h']; rfl), dropF_dropF cs]
        · rw [if_neg h']
          by_cases h : D i
          · rw [dropF_cons, dropF_nil, List.append_nil, dropT, if_pos h,
              if_pos (by rw [bool_eq_false h', h]; rfl), dropF_dropF cs]
          · rw [dropF_cons, dropF_nil, List.append_nil, dropT, if_neg h,
              if_neg (by rw [bool_eq_false h', bool_eq_false h]; simp),
              dropF_dropF cs]
  theorem dropF_dropF {D D' : Nat → Bool} :
      ∀ F : List Tree, dropF D (dropF D' F) = dropF (fun u => D' u || D u) F
    | [] => rfl
    | t :: ts => by
        rw [dropF_cons, dropF_append, dropF_cons, dropF_dropT t,
          dropF_dropF ts]
end

mutual
  /-- The read of a drop: the survivors, in order (set-instance of
  Corollary S1). -/
  theorem readF_dropT {D : Nat → Bool} :
      ∀ t : Tree, readF (dropT D t) = (readT t).filter (fun u => !D u)
    | .node i cs => by
        rw [dropT, readT]
        by_cases h : D i
        · rw [if_pos h, List.filter_cons, if_neg (by rw [h]; simp),
            readF_dropF cs]
        · rw [if_neg h, List.filter_cons,
            if_pos (by rw [bool_eq_false h]; simp)]
          show readT (.node i (dropF D cs)) ++ readF [] = _
          rw [readT, readF, List.append_nil, readF_dropF cs]
  theorem readF_dropF {D : Nat → Bool} :
      ∀ F : List Tree, readF (dropF D F) = (readF F).filter (fun u => !D u)
    | [] => rfl
    | t :: ts => by
        rw [dropF_cons, readF_append, readF, List.filter_append,
          readF_dropT t, readF_dropF ts]
end

/-- Drop with a never-true predicate is the identity. -/
theorem dropF_false : ∀ F : List Tree, dropF (fun _ => false) F = F
  | [] => rfl
  | .node i cs :: ts => by
      rw [dropF_cons, dropT, if_neg (by simp), dropF_false cs,
        dropF_false ts, List.singleton_append]

/-- **The delete phase is a set-drop** (order-free, set-determined): the
fold of any list of deletes is the simultaneous splice of their targets. -/
theorem steps_dels :
    ∀ (ds : List Nat) (s : St),
      steps s (ds.map .del) = dropF (fun u => ds.contains u) s
  | [], s => by
      show s = _
      rw [show (fun u => List.contains [] u) = (fun _ : Nat => false)
          from rfl, dropF_false s]
  | d :: ds, s => by
      rw [List.map_cons,
        show steps s (.del d :: ds.map .del)
          = steps (Shesha.delete s d) (ds.map .del) from rfl,
        steps_dels ds (Shesha.delete s d), Shesha.delete,
        delF_eq_dropF, dropF_dropF s]
      refine dropF_congr (fun u => ?_) s
      show ((u == d) || ds.contains u) = (d :: ds).contains u
      rw [List.contains_cons]

/-! ## §2 delete postponement -/

/-- The insert phase of an op list (inserts, in order). -/
def insPart : List Op → List Op
  | [] => []
  | .ins x a :: ρ => .ins x a :: insPart ρ
  | .del _ :: ρ => insPart ρ

/-- The delete phase of an op list (deletes, in order). -/
def delPart : List Op → List Op
  | [] => []
  | .ins _ _ :: ρ => delPart ρ
  | .del d :: ρ => .del d :: delPart ρ

theorem delPart_eq_map : ∀ ρ : List Op, delPart ρ = (opDelIds ρ).map .del
  | [] => rfl
  | .ins _ _ :: ρ => by rw [delPart, opDelIds, delPart_eq_map ρ]
  | .del d :: ρ => by
      rw [delPart, opDelIds, List.map_cons, delPart_eq_map ρ]

theorem opInsIds_insPart : ∀ ρ : List Op, opInsIds (insPart ρ) = opInsIds ρ
  | [] => rfl
  | .ins x a :: ρ => by rw [insPart, opInsIds, opInsIds, opInsIds_insPart ρ]
  | .del _ :: ρ => by rw [insPart, opInsIds, opInsIds_insPart ρ]

/-- An ordered delete–insert pair is *clean* if the delete touches neither
the inserted id nor its anchor. (`Pairwise DelBeforeOK` is exactly the
hypothesis under which deletes bubble to the end.) -/
def DelBeforeOK : Op → Op → Prop
  | .del d, .ins x a => d ≠ x ∧ d ≠ a
  | _, _ => True

/-- A clean delete commutes past the whole insert phase. -/
theorem steps_delete_comm {d : Nat} :
    ∀ (ρ : List Op) (s : St),
      (∀ x a, Op.ins x a ∈ ρ → d ≠ x ∧ d ≠ a) →
      steps (Shesha.delete s d) (insPart ρ)
        = Shesha.delete (steps s (insPart ρ)) d
  | [], _, _ => rfl
  | .ins x a :: ρ, s, h => by
      obtain ⟨hdx, hda⟩ := h x a (List.mem_cons_self ..)
      rw [insPart,
        show steps (Shesha.delete s d) (.ins x a :: insPart ρ)
          = steps (Shesha.insert (Shesha.delete s d) x a) (insPart ρ) from rfl,
        show steps s (.ins x a :: insPart ρ)
          = steps (Shesha.insert s x a) (insPart ρ) from rfl,
        ← delete_insert_comm hdx hda s,
        steps_delete_comm ρ (Shesha.insert s x a)
          (fun x' a' hm => h x' a' (List.mem_cons_of_mem _ hm))]
  | .del d' :: ρ, s, h => by
      rw [insPart]
      exact steps_delete_comm ρ s
        (fun x' a' hm => h x' a' (List.mem_cons_of_mem _ hm))

/-- **Delete postponement**: under clean ordered delete–insert pairs, the
fold factors into its insert phase followed by its delete phase. -/
theorem steps_postpone_deletes :
    ∀ (ρ : List Op) (s : St), ρ.Pairwise DelBeforeOK →
      steps s ρ = steps s (insPart ρ ++ delPart ρ)
  | [], _, _ => rfl
  | .ins x a :: ρ, s, hp => by
      rw [insPart, delPart,
        show steps s (.ins x a :: ρ)
          = steps (Shesha.insert s x a) ρ from rfl,
        List.cons_append,
        show steps s (.ins x a :: (insPart ρ ++ delPart ρ))
          = steps (Shesha.insert s x a) (insPart ρ ++ delPart ρ) from rfl]
      exact steps_postpone_deletes ρ _ (List.pairwise_cons.mp hp).2
  | .del d :: ρ, s, hp => by
      have hd := (List.pairwise_cons.mp hp).1
      rw [insPart, delPart,
        show steps s (.del d :: ρ)
          = steps (Shesha.delete s d) ρ from rfl,
        steps_postpone_deletes ρ (Shesha.delete s d)
          (List.pairwise_cons.mp hp).2,
        steps_append, steps_append,
        steps_delete_comm ρ s (fun x a hm => hd _ hm)]
      rfl

/-- **The effective normal form**: under clean pairs, a fold from `s` is
the set-drop of its delete ids over its insert-phase forest. -/
theorem steps_normal_form (ρ : List Op) (s : St)
    (hp : ρ.Pairwise DelBeforeOK) :
    steps s ρ
      = dropF (fun u => (opDelIds ρ).contains u) (steps s (insPart ρ)) := by
  rw [steps_postpone_deletes ρ s hp, steps_append, delPart_eq_map,
    steps_dels]

/-! ## §3 insert-phase structure -/

/-- An absent node's row is empty (tree form). -/
theorem rowT_absent {q : Nat} {t : Tree} (h : q ∉ readT t) :
    rowT q t = [] := by
  rcases hr : rowT q t with _ | ⟨w, l⟩
  · rfl
  · exact absurd (rowT_parent_mem (by rw [hr]; exact List.mem_cons_self ..)) h

/-- An absent node's row is empty (forest form). -/
theorem rowF_absent {q : Nat} {F : List Tree} (h : q ∉ readF F) :
    rowF q F = [] := by
  rcases hr : rowF q F with _ | ⟨w, l⟩
  · rfl
  · exact absurd (rowF_parent_mem (by rw [hr]; exact List.mem_cons_self ..)) h

theorem rowT_leaf (q x : Nat) : rowT q (.node x []) = [] := by
  rw [rowT]
  by_cases hxq : x = q
  · rw [if_pos hxq]
    rfl
  · rw [if_neg hxq]
    rfl

mutual
  /-- Head-insertion at a live anchor, tree form: the anchor's row gains
  the new node at its head. -/
  theorem rowT_insT_self {x a : Nat} :
      ∀ t : Tree, (readT t).Nodup → a ∈ readT t →
        rowT a (insT x a t) = x :: rowT a t
    | .node i cs, hnd, ha => by
        rw [readT] at hnd ha
        rw [insT]
        by_cases hia : i = a
        · rw [if_pos hia, rowT, if_pos hia, rowT, if_pos hia, List.map_cons,
            insF_topIds]
          rfl
        · rw [if_neg hia, rowT, if_neg hia, rowT, if_neg hia]
          have ha' : a ∈ readF cs := by
            rcases List.mem_cons.mp ha with he | h'
            · exact absurd he.symm hia
            · exact h'
          exact rowF_insF_self cs (List.nodup_cons.mp hnd).2 ha'
  theorem rowF_insF_self {x a : Nat} :
      ∀ F : List Tree, (readF F).Nodup → a ∈ readF F →
        rowF a (insF x a F) = x :: rowF a F
    | t :: ts, hnd, ha => by
        rw [readF] at hnd ha
        rw [insF_cons, rowF, rowF]
        rcases List.mem_append.mp ha with h | h
        · have hnotts : a ∉ readF ts := fun hm => nodup_append_disj hnd h hm
          rw [rowT_insT_self t (nodup_append_left hnd) h,
            insF_eq_graftF,
            graftF_no_op ts (bool_eq_false
              (fun hc => hnotts ((containsF_iff a ts).mp hc))),
            List.cons_append]
        · have hnott : a ∉ readT t := fun hm => nodup_append_disj hnd hm h
          rw [insT_eq_graftT,
            graftT_no_op t (bool_eq_false
              (fun hc => hnott ((containsT_iff a t).mp hc))),
            rowF_insF_self ts (nodup_append_right hnd) h,
            rowT_absent hnott]
          rfl
end

mutual
  /-- Other rows are untouched by an insert (tree form). -/
  theorem rowT_insT_other {x a q : Nat} (hqa : q ≠ a) :
      ∀ t : Tree, rowT q (insT x a t) = rowT q t
    | .node i cs => by
        rw [insT]
        by_cases hia : i = a
        · have hiq : ¬ i = q := fun h => hqa (h.symm.trans hia)
          rw [if_pos hia, rowT, if_neg hiq, rowT, if_neg hiq, rowF,
            rowT_leaf, rowF_insF_other hqa cs, List.nil_append]
        · rw [if_neg hia, rowT, rowT]
          by_cases hiq : i = q
          · rw [if_pos hiq, if_pos hiq, insF_topIds]
          · rw [if_neg hiq, if_neg hiq, rowF_insF_other hqa cs]
  theorem rowF_insF_other {x a q : Nat} (hqa : q ≠ a) :
      ∀ F : List Tree, rowF q (insF x a F) = rowF q F
    | [] => rfl
    | t :: ts => by
        rw [insF_cons, rowF, rowF, rowT_insT_other hqa t,
          rowF_insF_other hqa ts]
end

/-- **Head-insertion, state form**: an effective insert prepends the new
node to its anchor's row and touches no other row. -/
theorem row_insert_eff {X : St} {x a : Nat} (hwf : WF X)
    (ha : a = 0 ∨ a ∈ read X) (q : Nat) :
    row (Shesha.insert X x a) q
      = if a = q then x :: row X q else row X q := by
  rw [Shesha.insert]
  by_cases haq : a = q
  · rw [if_pos haq]
    by_cases ha0 : a = 0
    · rw [if_pos ha0, row, if_pos (haq ▸ ha0), row, if_pos (haq ▸ ha0),
        List.map_cons]
      rfl
    · have hq0 : ¬ q = 0 := fun h => ha0 (haq.trans h)
      rw [if_neg ha0, row, if_neg hq0, row, if_neg hq0, ← haq]
      exact rowF_insF_self X hwf.1
        (ha.elim (fun h => absurd h ha0) id)
  · rw [if_neg haq]
    by_cases ha0 : a = 0
    · rw [if_pos ha0, row, row]
      by_cases hq0 : q = 0
      · exact absurd (ha0.trans hq0.symm) haq
      · rw [if_neg hq0, if_neg hq0, rowF, rowT_leaf, List.nil_append]
    · rw [if_neg ha0, row, row]
      by_cases hq0 : q = 0
      · rw [if_pos hq0, if_pos hq0, insF_topIds]
      · rw [if_neg hq0, if_neg hq0,
          rowF_insF_other (fun h => haq h.symm) X]

/-- All-insert op lists. -/
def AllIns : List Op → Prop
  | [] => True
  | .ins _ _ :: ρ => AllIns ρ
  | .del _ :: ρ => False

/-- Effectiveness + freshness from a state: each insert's id is fresh and
nonzero, and its anchor live-or-root, at its point in the fold. -/
def EffFreshFrom : St → List Op → Prop
  | _, [] => True
  | s, .ins x a :: ρ =>
      x ∉ read s ∧ x ≠ 0 ∧ (a = 0 ∨ a ∈ read s) ∧
        EffFreshFrom (Shesha.insert s x a) ρ
  | s, .del d :: ρ => EffFreshFrom (Shesha.delete s d) ρ

/-- The `p`-anchored inserted ids of an op list, in order. -/
def anchIds : List Op → Nat → List Nat
  | [], _ => []
  | .ins x a :: ρ, p => if a = p then x :: anchIds ρ p else anchIds ρ p
  | .del _ :: ρ, p => anchIds ρ p

theorem opHonest_of_effFresh {s : St} {x a : Nat}
    (hx : x ∉ read s) (hx0 : x ≠ 0) (ha : a = 0 ∨ a ∈ read s) :
    OpHonest ([] : St) s (.ins x a) :=
  ⟨hx, fun h => absurd h (by rw [read]; exact List.not_mem_nil), hx0, ha⟩

/-- The insert phase preserves well-formedness. -/
theorem wf_steps_ins :
    ∀ (l : List Op) (s : St), WF s → AllIns l → EffFreshFrom s l →
      WF (steps s l)
  | [], _, hwf, _, _ => hwf
  | .ins x a :: l, s, hwf, hai, heff => by
      obtain ⟨hx, hx0, ha, hrest⟩ := heff
      show WF (steps (Shesha.insert s x a) l)
      exact wf_steps_ins l _
        (step_WF hwf (opHonest_of_effFresh hx hx0 ha)) hai hrest
  | .del _ :: _, _, _, hai, _ => absurd hai id

theorem mem_seqIns_of_mem {l : List Nat} {x a u : Nat} (h : u ∈ l) :
    u ∈ seqIns l x a := by
  rw [seqIns]
  by_cases ha : a = 0
  · rw [if_pos ha]
    exact List.mem_cons_of_mem _ h
  · rw [if_neg ha, List.mem_flatMap]
    refine ⟨u, h, ?_⟩
    rw [seqInsAt]
    by_cases hu : u = a
    · rw [if_pos hu]
      exact List.mem_cons_self ..
    · rw [if_neg hu]
      exact List.mem_singleton.mpr rfl

theorem self_mem_seqIns {l : List Nat} {x a : Nat} (ha : a = 0 ∨ a ∈ l) :
    x ∈ seqIns l x a := by
  by_cases ha0 : a = 0
  · rw [seqIns, if_pos ha0]
    exact List.mem_cons_self ..
  · rw [seqIns, if_neg ha0, List.mem_flatMap]
    refine ⟨a, ha.elim (fun h => absurd h ha0) id, ?_⟩
    rw [seqInsAt, if_pos rfl]
    exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)

/-- The live set of the insert phase: the start state plus every inserted
id (every insert applies). -/
theorem read_steps_ins :
    ∀ (l : List Op) (s : St), AllIns l → EffFreshFrom s l → ∀ u : Nat,
      (u ∈ read (steps s l) ↔ u ∈ read s ∨ u ∈ opInsIds l)
  | [], s, _, _, u =>
      ⟨Or.inl, fun h => h.elim id (fun h' => absurd h' (List.not_mem_nil))⟩
  | .ins x a :: l, s, hai, heff, u => by
      obtain ⟨hx, hx0, ha, hrest⟩ := heff
      rw [show steps s (.ins x a :: l) = steps (Shesha.insert s x a) l
          from rfl, opInsIds,
        read_steps_ins l _ hai hrest u, read_insert, List.mem_cons]
      constructor
      · rintro (h | h)
        · rcases seqIns_mem h with he | h'
          · exact Or.inr (Or.inl he)
          · exact Or.inl h'
        · exact Or.inr (Or.inr h)
      · rintro (h | he | h)
        · exact Or.inl (mem_seqIns_of_mem h)
        · exact Or.inl (he ▸ self_mem_seqIns ha)
        · exact Or.inr h
  | .del _ :: _, _, hai, _, _ => absurd hai id

/-- **The anchored-forest row characterization**: after the insert phase,
the row of `p` is `p`'s anchored inserts, newest first, atop `p`'s
starting row. -/
theorem row_steps_ins :
    ∀ (l : List Op) (s : St), WF s → AllIns l → EffFreshFrom s l →
      ∀ p, row (steps s l) p = (anchIds l p).reverse ++ row s p
  | [], s, _, _, _, p => by
      rw [anchIds, List.reverse_nil, List.nil_append]
      rfl
  | .ins x a :: l, s, hwf, hai, heff, p => by
      obtain ⟨hx, hx0, ha, hrest⟩ := heff
      rw [show steps s (.ins x a :: l) = steps (Shesha.insert s x a) l
          from rfl,
        row_steps_ins l (Shesha.insert s x a)
          (step_WF hwf (opHonest_of_effFresh hx hx0 ha))
          hai hrest p,
        row_insert_eff hwf ha p, anchIds]
      by_cases hap : a = p
      · rw [if_pos hap, if_pos hap, List.reverse_cons, List.append_assoc,
          List.singleton_append]
      · rw [if_neg hap, if_neg hap]
  | .del _ :: _, _, _, hai, _, _ => absurd hai id

end Shesha
