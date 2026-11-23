import LeanProofs1.Implementations.TreeMove.Raw

/-!
# Tree move: the delivery algorithm computes the canonical state

The one theorem this row turns on, and the two facts `Definition.lean` needs
to cut `Sigma` down to the coherent states. On a coherent state, `receive`
and `merge` return the `build` of a key-descending list, and that list is
determined by its **set** of moves. So delivery order does not matter, which
is the appendix's claim that complete deliveries commute on the coherent
state space, including their undo metadata.

The chain is

```
  undo_push        undo inverts push, recomputing the old parent
  applyRaw_build   applyRaw o (build E) = build (insertDesc o E)
  receive_eq       receive s o = build (ins o (events s))   on coherent s
  desc_unique      two descending lists with the same members are equal
  coh_ext          two coherent states with the same moves are equal
```

`applyRaw_build` needs no hypothesis at all: `build` keeps the log and the
tree in lockstep, so undoing the newest entry recovers the older tree
exactly.
-/

namespace LeanProofs1.Implementations.TreeMove

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-! ## The key -/

/-- The full key is the whole move, so it determines it. -/
theorem key_inj {o o' : AppOp} (h : key o = key o') : o = o' := by
  obtain ⟨t, r, p, m, c⟩ := o
  obtain ⟨t', r', p', m', c'⟩ := o'
  simp only [key, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  subst h1; subst h2; subst h3; subst h4; subst h5; rfl

/-- Distinct moves have distinct keys. -/
theorem key_ne {o o' : AppOp} (h : o ≠ o') : key o ≠ key o' :=
  fun hk => h (key_inj hk)

/-! ## `build` and its log -/

theorem ops_push (s : Raw) (o : AppOp) : ops (push s o) = o :: ops s := rfl

/-- `build` lays down exactly the list it is given. -/
theorem ops_build : ∀ E : List AppOp, ops (build E) = E
  | [] => rfl
  | o :: E => by rw [build, ops_push, ops_build E]

/-- **`undo` inverts `push`.** Both branches of `f` move only the child's
own entry, and the entry `push` records is that child's previous value. -/
theorem undo_push (T : Tree) (o : AppOp) :
    undo (o, T o.child) (f T o) = T := by
  simp only [undo, f]
  split_ifs with h
  · exact Function.update_eq_self _ _
  · rw [Function.update_idem, Function.update_eq_self]

/-- **`applyRaw` is descending insertion.** Undo, insert, redo on the state
`build E` returns the state of the list `E` with `o` inserted in key
order. -/
theorem applyRaw_build (o : AppOp) : ∀ E : List AppOp,
    applyRaw o (build E).1 (build E).2 = build (insertDesc o E)
  | [] => rfl
  | a :: E => by
      have hb : build (a :: E) = push (build E) a := rfl
      rw [hb]
      show applyRaw o ((a, (build E).2 a.child) :: (build E).1)
          (f (build E).2 a) = _
      rw [applyRaw, insertDesc]
      by_cases h : key o < key a
      · simp only [h, if_true, undo_push]
        rw [applyRaw_build o E]
        rfl
      · simp only [h, if_false]
        rfl

/-! ## Descending lists -/

theorem mem_insertDesc (o x : AppOp) : ∀ E : List AppOp,
    x ∈ insertDesc o E ↔ x = o ∨ x ∈ E
  | [] => by simp [insertDesc]
  | a :: E => by
      by_cases h : key o < key a
      · simp only [insertDesc, h, if_true, List.mem_cons, mem_insertDesc o x E]
        tauto
      · simp only [insertDesc, h, if_false, List.mem_cons]

/-- A head of a descending list does not recur in its tail. -/
theorem notMem_of_desc {a : AppOp} {E : List AppOp} (h : Desc (a :: E)) :
    a ∉ E := by
  intro hm
  exact absurd ((List.pairwise_cons.mp h).1 a hm) (lt_irrefl _)

/-- Descending insertion preserves the invariant. -/
theorem desc_insertDesc {o : AppOp} : ∀ {E : List AppOp}, Desc E → o ∉ E →
    Desc (insertDesc o E)
  | [], _, _ => by simp [insertDesc, Desc]
  | a :: E, hd, hne => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hd
      have hea : o ≠ a := fun hq => hne (hq ▸ List.mem_cons_self ..)
      have heE : o ∉ E := fun hm => hne (List.mem_cons_of_mem _ hm)
      by_cases h : key o < key a
      · simp only [insertDesc, h, if_true]
        refine List.pairwise_cons.mpr ⟨?_, desc_insertDesc htail heE⟩
        intro x hx
        rcases (mem_insertDesc o x E).mp hx with rfl | hx'
        · exact h
        · exact hhead x hx'
      · have hak : key a < key o :=
          lt_of_le_of_ne (not_lt.mp h) (key_ne (Ne.symm hea))
        simp only [insertDesc, h, if_false]
        refine List.pairwise_cons.mpr ⟨?_, hd⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hak
        · exact lt_trans (hhead x hx') hak

/-- **Two descending lists with the same members are equal.** -/
theorem desc_unique : ∀ {E₁ E₂ : List AppOp}, Desc E₁ → Desc E₂ →
    (∀ x, x ∈ E₁ ↔ x ∈ E₂) → E₁ = E₂
  | [], [], _, _, _ => rfl
  | [], b :: E₂, _, _, h => absurd ((h b).mpr (List.mem_cons_self ..)) (by simp)
  | a :: E₁, [], _, _, h => absurd ((h a).mp (List.mem_cons_self ..)) (by simp)
  | a :: E₁, b :: E₂, h₁, h₂, h => by
      obtain ⟨g₁, t₁⟩ := List.pairwise_cons.mp h₁
      obtain ⟨g₂, t₂⟩ := List.pairwise_cons.mp h₂
      have hab : a = b := by
        by_contra hne
        have ha2 : a ∈ E₂ :=
          (List.mem_cons.mp ((h a).mp (List.mem_cons_self ..))).resolve_left hne
        have hb1 : b ∈ E₁ :=
          (List.mem_cons.mp ((h b).mpr (List.mem_cons_self ..))).resolve_left
            (Ne.symm hne)
        exact absurd (lt_trans (g₂ a ha2) (g₁ b hb1)) (lt_irrefl _)
      subst hab
      have hmem : ∀ x, x ∈ E₁ ↔ x ∈ E₂ := by
        intro x
        constructor
        · intro hx
          rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with rfl | hx'
          · exact absurd hx (notMem_of_desc h₁)
          · exact hx'
        · intro hx
          rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with rfl | hx'
          · exact absurd hx (notMem_of_desc h₂)
          · exact hx'
      rw [desc_unique t₁ t₂ hmem]

/-! ## Duplicate-suppressing insertion -/

theorem mem_ins (o x : AppOp) (E : List AppOp) :
    x ∈ ins o E ↔ x = o ∨ x ∈ E := by
  unfold ins
  split_ifs with h
  · constructor
    · exact Or.inr
    · rintro (rfl | hx) <;> [exact h; exact hx]
  · exact mem_insertDesc o x E

theorem desc_ins {o : AppOp} {E : List AppOp} (hd : Desc E) : Desc (ins o E) := by
  unfold ins
  split_ifs with h
  · exact hd
  · exact desc_insertDesc hd h

theorem mem_insAll (x : AppOp) : ∀ (L E : List AppOp),
    x ∈ insAll L E ↔ x ∈ L ∨ x ∈ E
  | [], E => by simp [insAll]
  | o :: L, E => by
      show x ∈ insAll L (ins o E) ↔ _
      rw [mem_insAll x L (ins o E), mem_ins, List.mem_cons]
      tauto

theorem desc_insAll : ∀ (L : List AppOp) {E : List AppOp}, Desc E →
    Desc (insAll L E)
  | [], _, hd => hd
  | _ :: L, _, hd => desc_insAll L (desc_ins hd)

/-! ## Coherence -/

theorem coherent_build {E : List AppOp} (hd : Desc E) : Coherent (build E) :=
  ⟨by rw [ops_build]; exact hd, by rw [ops_build]⟩

theorem coherent_init : Coherent (([], T0) : Raw) :=
  ⟨by simp [ops, Desc], rfl⟩

/-- **The delivery equation.** -/
theorem receive_eq {s : Raw} (hc : Coherent s) (o : AppOp) :
    receive s o = build (ins o (ops s)) := by
  unfold receive ins
  split_ifs with h
  · exact hc.2
  · conv_lhs => rw [hc.2]
    exact applyRaw_build o (ops s)

/-- **`receive` lands in the coherent state space.** -/
theorem receive_coherent {s : Raw} (hc : Coherent s) (o : AppOp) :
    Coherent (receive s o) := by
  rw [receive_eq hc]; exact coherent_build (desc_ins hc.1)

theorem ops_receive {s : Raw} (hc : Coherent s) (o : AppOp) :
    ops (receive s o) = ins o (ops s) := by
  rw [receive_eq hc, ops_build]

/-- **The merge equation.** -/
theorem mergeRaw_eq : ∀ (L : List AppOp) {a : Raw}, Coherent a →
    L.foldl receive a = build (insAll L (ops a))
  | [], _, ha => ha.2
  | o :: L, a, ha => by
      show L.foldl receive (receive a o) = _
      rw [mergeRaw_eq L (receive_coherent ha o), ops_receive ha]
      rfl

/-- **`merge` lands in the coherent state space.** -/
theorem mergeRaw_coherent {a : Raw} (ha : Coherent a) (b : Raw) :
    Coherent (mergeRaw a b) := by
  rw [mergeRaw, mergeRaw_eq _ ha]
  exact coherent_build (desc_insAll _ ha.1)

theorem ops_mergeRaw {a : Raw} (ha : Coherent a) (b : Raw) (x : AppOp) :
    x ∈ ops (mergeRaw a b) ↔ x ∈ ops b ∨ x ∈ ops a := by
  rw [mergeRaw, mergeRaw_eq _ ha, ops_build, mem_insAll]

/-- **A coherent state is its move set.** -/
theorem coh_ext {s t : Raw} (hs : Coherent s) (ht : Coherent t)
    (h : ∀ x, x ∈ ops s ↔ x ∈ ops t) : s = t := by
  rw [hs.2, ht.2, desc_unique hs.1 ht.1 h]

end LeanProofs1.Implementations.TreeMove
