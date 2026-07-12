import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha

/-! # Shesha — merge lemmas, block 1 (phase 2a): M0, M1, M2

Pen-and-paper source: `whiteboard/sibling-linked-proof.md` §4 (Lemmas M0, M1,
M2); model hypotheses from `whiteboard/sibling-linked-rga-notes.md` §3 (the
membership table; pattern-8 exclusion). M3 and Theorem P are phase 2b and
deliberately absent.

Contents:

- **§0 Bridges** — `contains` ↔ `∈ read` (the Bool/Prop seam).
- **§1 Model** — `WF` (distinct, nonzero ids) and `ModelOK` (WF × 3 +
  pattern-8 exclusion `ids A ∩ ids B ⊆ ids L`).
- **§2 Row machinery** — count-based: a row never exceeds the read
  (`row_count_le`), two distinct rows never overlap (`row_count₂`), hence on
  WF states rows are `Nodup`, mutually disjoint, and contained in the read.
  This substrate serves M0, M1 and M2 alike.
- **§3 Run machinery** — every run placed by `branchCmds` is a maximal non-L
  segment of one row of its branch (`IsRunOf`, via `runsGo_shape`); on a WF
  branch a run is determined by its head id (`IsRunOf.head_det`).
- **§4 Lemma M1** (`merge_comm`) — state equality, kernel-clean. The only
  branch-asymmetric step of the construction is the newest-head-first
  same-slot sort; run heads are pairwise distinct (within a branch by WF,
  across branches by pattern-8), so the sort output is order-independent.
- **§5 Lemma M0** — the content bound (`merge_reads_bound`) and the nonzero
  half of `merge_WF` proved here; the `Nodup` half (`merge_read_nodup`,
  `merge_WF`) and the survivor-set identity (`merge_ids`) are discharged in
  `Shesha_M0.lean` on top of the parent-chain layer (`Shesha_Forest.lean`)
  and the skeleton characterization (`Shesha_Skel.lean`).
- **§6 Lemma M2** (`merge_extends_L`) — the proved plumbing
  (`precedes_filter_iff`, `rowAssemble_filter_L`) lives here; the core
  identity `merge_L_filter` (skeleton DFS order = L document order) and
  `merge_extends_L` itself are discharged in `Shesha_M2.lean`.

This file is `sorry`-free and kernel-clean throughout.
-/

namespace Shesha

open List

/-! ## §0 Bridges: `contains` ↔ membership in `read`

`read` is the preorder listing of ids, so `u ∈ read s` *is* "u is a live node
of s"; `contains` is its Bool twin used inside the merge. -/

theorem topId_mem_readT : ∀ t : Tree, topId t ∈ readT t
  | .node _ _ => by simp [topId, readT]

mutual
  theorem containsT_iff (u : Nat) :
      ∀ t : Tree, containsT u t = true ↔ u ∈ readT t
    | .node i cs => by
        simp only [containsT, readT, Bool.or_eq_true, beq_iff_eq,
          containsF_iff u cs, List.mem_cons]
        exact or_congr eq_comm Iff.rfl
  theorem containsF_iff (u : Nat) :
      ∀ ts : List Tree, containsF u ts = true ↔ u ∈ readF ts
    | [] => by simp [containsF, readF]
    | t :: ts => by
        simp [containsF, readF, containsT_iff u t, containsF_iff u ts]
end

theorem contains_iff {s : St} {u : Nat} : contains s u = true ↔ u ∈ read s :=
  containsF_iff u s

theorem contains_eq_false {s : St} {u : Nat} :
    contains s u = false ↔ u ∉ read s := by
  rw [← contains_iff]; cases contains s u <;> simp

/-! ## §1 The model: well-formedness and the merge-model hypotheses -/

/-- The id list of a state (ids double as elements): the preorder read. -/
abbrev ids : St → List Nat := read

/-- Well-formedness of the rose forest: every id occurs at most once (each
node has one parent and one row slot), and no node uses `0` — the code
reserves `0` for the implicit root `⌂` (`insert`'s front case, `parOf`'s root
answer, `wparGo`'s stop, the skeleton's root row). In the rose-forest
encoding the remaining design invariants (par is a forest, rows are chains)
hold by construction. -/
def WF (s : St) : Prop := (read s).Nodup ∧ 0 ∉ read s

/-- The merge-model hypotheses (design record §3, membership table): the
three inputs are well-formed, and — pattern-8 exclusion — an id live in both
branches is common past, i.e. in the LCA (`ids A ∩ ids B ⊆ ids L`; supplied
by the framework's LCA discipline plus global id uniqueness). -/
structure ModelOK (L A B : St) : Prop where
  wfL : WF L
  wfA : WF A
  wfB : WF B
  common : ∀ u, u ∈ ids A → u ∈ ids B → u ∈ ids L

/-! ## §2 Row machinery (count-based)

The whole section quantifies over raw forests; `WF` enters only at the end.
`rowF p ts` collects the child lists of *every* node labelled `p`; the count
lemmas say those collections (plus the root row `map topId`) sit inside the
read without double-counting, because every node lives in exactly one row. -/

theorem topIds_sublist_readF : ∀ ts : List Tree, ts.map topId <+ readF ts
  | [] => by simp [readF]
  | t :: ts =>
      match t with
      | .node i cs => by
          simp only [List.map_cons, readF, readT, topId, List.cons_append]
          exact ((topIds_sublist_readF ts).trans
            (List.sublist_append_right _ _)).cons₂ i

theorem count_le_one_of_nodup : ∀ {l : List Nat}, l.Nodup → ∀ c, l.count c ≤ 1
  | [], _, c => by simp
  | a :: t, h, c => by
      rw [List.nodup_cons] at h
      by_cases hc : a = c
      · subst hc
        simp [List.count_eq_zero_of_not_mem h.1]
      · have := count_le_one_of_nodup h.2 c
        simp [hc]
        omega

theorem nodup_of_count_le_one :
    ∀ {l : List Nat}, (∀ c, l.count c ≤ 1) → l.Nodup
  | [], _ => by simp
  | a :: t, h => by
      rw [List.nodup_cons]
      refine ⟨?_, nodup_of_count_le_one fun c =>
        Nat.le_trans List.count_le_count_cons (h c)⟩
      have := h a
      simp at this
      exact List.count_eq_zero.mp (by omega)

mutual
  /-- One row plus the node's own top-level occurrence fit inside the read
  (stated in cons form so every `if` atom arises from `count_cons`). -/
  theorem rowT_count (q c : Nat) :
      ∀ t : Tree, (topId t :: rowT q t).count c ≤ (readT t).count c
    | .node i cs => by
        have hf := rowF_count q c cs
        simp only [rowT, readT, topId, List.count_cons]
        split <;> omega
  /-- The root row (`map topId`) and any internal row fit side by side. -/
  theorem rowF_count (q c : Nat) :
      ∀ ts : List Tree,
        (ts.map topId).count c + (rowF q ts).count c ≤ (readF ts).count c
    | [] => by simp [rowF, readF]
    | t :: ts => by
        have h1 := rowT_count q c t
        have h2 := rowF_count q c ts
        simp only [List.count_cons] at h1
        simp only [List.map_cons, rowF, readF, List.count_cons,
          List.count_append]
        omega
end

mutual
  /-- Two rows of distinct parents fit side by side inside the read. -/
  theorem rowT_count₂ (p q c : Nat) (hpq : p ≠ q) :
      ∀ t : Tree, (rowT p t).count c + (rowT q t).count c ≤ (readT t).count c
    | .node i cs => by
        have hfp := rowF_count p c cs
        have hfq := rowF_count q c cs
        have hf2 := rowF_count₂ p q c hpq cs
        simp only [rowT, readT, List.count_cons]
        split <;> split <;> omega
  theorem rowF_count₂ (p q c : Nat) (hpq : p ≠ q) :
      ∀ ts : List Tree,
        (rowF p ts).count c + (rowF q ts).count c ≤ (readF ts).count c
    | [] => by simp [rowF, readF]
    | t :: ts => by
        have h1 := rowT_count₂ p q c hpq t
        have h2 := rowF_count₂ p q c hpq ts
        simp only [rowF, readF, List.count_append]
        omega
end

theorem row_count_le (s : St) (p c : Nat) :
    (row s p).count c ≤ (read s).count c := by
  by_cases h : p = 0
  · simpa [row, read, h] using (topIds_sublist_readF s).count_le c
  · have := rowF_count p c s
    simp [row, read, h]
    omega

theorem row_count₂ (s : St) {p q : Nat} (hpq : p ≠ q) (c : Nat) :
    (row s p).count c + (row s q).count c ≤ (read s).count c := by
  by_cases hp : p = 0
  · by_cases hq : q = 0
    · exact absurd (hp.trans hq.symm) hpq
    · have := rowF_count q c s
      simp [row, read, hp, hq]
      omega
  · by_cases hq : q = 0
    · have := rowF_count p c s
      simp [row, read, hp, hq]
      omega
    · have := rowF_count₂ p q c hpq s
      simp [row, read, hp, hq]
      omega

/-- Row contents are live nodes (no WF needed). -/
theorem mem_row_read {s : St} {p c : Nat} (h : c ∈ row s p) : c ∈ read s := by
  have h1 : 0 < (row s p).count c := List.count_pos_iff.mpr h
  exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le h1 (row_count_le s p c))

/-- On a WF state every row is duplicate-free. -/
theorem row_nodup {s : St} (hwf : WF s) (p : Nat) : (row s p).Nodup :=
  nodup_of_count_le_one fun c =>
    Nat.le_trans (row_count_le s p c) (count_le_one_of_nodup hwf.1 c)

/-- On a WF state rows of distinct parents are disjoint (one parent each). -/
theorem row_disjoint {s : St} (hwf : WF s) {p q c : Nat} (hpq : p ≠ q)
    (hp : c ∈ row s p) (hq : c ∈ row s q) : False := by
  have h1 : 0 < (row s p).count c := List.count_pos_iff.mpr hp
  have h2 : 0 < (row s q).count c := List.count_pos_iff.mpr hq
  have h3 := row_count₂ s hpq c
  have h4 := count_le_one_of_nodup hwf.1 c
  omega

/-! ## §3 Run machinery

`branchCmds` places, per host row of a branch, the maximal runs of non-L ids
computed by `runsGo`. The lemmas here recover, from a run's mere membership
in a placement command, its provenance as a *nonempty maximal non-L segment
of one branch row* (`IsRunOf`), and derive that on a WF branch **a run is
determined by its head id** (`IsRunOf.head_det`) — the fact that makes the
newest-head-first same-slot sort order-independent (M1), and that run
contents are branch ids outside L (M0/M2). -/

/-- Membership in a `takeWhile` certifies the predicate. -/
theorem mem_takeWhile_pred {p : Nat → Bool} :
    ∀ {l : List Nat} {a : Nat}, a ∈ l.takeWhile p → p a = true
  | [], _, h => by simp at h
  | b :: l, a, h => by
      rw [List.takeWhile_cons] at h
      by_cases hb : p b
      · rw [if_pos hb] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact hb
        · exact mem_takeWhile_pred h
      · rw [if_neg hb] at h
        simp at h

/-- In a duplicate-free list, the decomposition around an element is unique. -/
theorem nodup_middle_inj (h : Nat) :
    ∀ (x₁ x₂ y₁ y₂ : List Nat), (x₁ ++ h :: y₁).Nodup →
      x₁ ++ h :: y₁ = x₂ ++ h :: y₂ → x₁ = x₂ ∧ y₁ = y₂
  | [], [], y₁, y₂, _, e => by simp_all
  | [], a :: x₂, y₁, y₂, hn, e => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp only [List.nil_append, List.nodup_cons] at hn
      exact absurd (by simp) hn.1
  | a :: x₁, [], y₁, y₂, hn, e => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp only [List.cons_append, List.nodup_cons] at hn
      exact absurd (by simp) hn.1
  | a :: x₁, b :: x₂, y₁, y₂, hn, e => by
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      simp only [List.cons_append, List.nodup_cons] at hn
      obtain ⟨h1, h2⟩ := nodup_middle_inj h x₁ x₂ y₁ y₂ hn.2 e
      exact ⟨by rw [h1], h2⟩

/-- Every triple `runsGo` emits carries a *nonempty maximal non-L segment* of
the scanned list: the list splits as `x ++ run ++ y` with
`run = takeWhile (¬ isL) (run ++ y)`. -/
theorem runsGo_shape (isL : Nat → Bool) :
    ∀ (fuel : Nat) (pre₀ : Option Nat) (l : List Nat)
      (pr : Option Nat × List Nat × Option Nat),
      pr ∈ runsGo isL fuel pre₀ l →
      ∃ x y, l = x ++ (pr.2.1 ++ y) ∧ pr.2.1 ≠ [] ∧
        pr.2.1 = (pr.2.1 ++ y).takeWhile (fun v => !isL v)
  | 0, _, _, _, h => by simp [runsGo] at h
  | _ + 1, _, [], _, h => by simp [runsGo] at h
  | fuel + 1, pre₀, u :: rest, pr, h => by
      rw [runsGo] at h
      by_cases hu : isL u
      · rw [if_pos hu] at h
        obtain ⟨x, y, e, hne, htw⟩ := runsGo_shape isL fuel (some u) rest pr h
        exact ⟨u :: x, y, by rw [List.cons_append, ← e], hne, htw⟩
      · rw [if_neg hu] at h
        rcases List.mem_cons.mp h with rfl | h
        · refine ⟨[], (u :: rest).dropWhile (fun v => !isL v), ?_, ?_, ?_⟩
          · simp [List.takeWhile_append_dropWhile]
          · simp [hu]
          · rw [List.takeWhile_append_dropWhile]
        · obtain ⟨x, y, e, hne, htw⟩ :=
            runsGo_shape isL fuel pre₀ ((u :: rest).dropWhile (fun v => !isL v))
              pr h
          exact ⟨(u :: rest).takeWhile (fun v => !isL v) ++ x, y,
            by rw [List.append_assoc, ← e, List.takeWhile_append_dropWhile],
            hne, htw⟩

/-- `r` is one of the maximal non-L segments of some row of branch `X`. -/
def IsRunOf (L X : St) (r : List Nat) : Prop :=
  ∃ p x y, row X p = x ++ (r ++ y) ∧ r ≠ [] ∧
    r = (r ++ y).takeWhile (fun v => !contains L v)

theorem IsRunOf.ne_nil {L X : St} {r : List Nat} (h : IsRunOf L X r) :
    r ≠ [] := h.choose_spec.choose_spec.choose_spec.2.1

/-- Run contents live in the branch. -/
theorem IsRunOf.mem_read {L X : St} {r : List Nat} (h : IsRunOf L X r)
    {c : Nat} (hc : c ∈ r) : c ∈ read X := by
  obtain ⟨p, x, y, e, -, -⟩ := h
  exact mem_row_read (p := p) (by rw [e]; simp [hc])

/-- Run contents are outside L (they are the non-L segments). -/
theorem IsRunOf.mem_notL {L X : St} {r : List Nat} (h : IsRunOf L X r)
    {c : Nat} (hc : c ∈ r) : contains L c = false := by
  obtain ⟨-, -, y, -, -, htw⟩ := h
  have hm : c ∈ (r ++ y).takeWhile (fun v => !contains L v) := htw ▸ hc
  simpa using mem_takeWhile_pred hm

theorem IsRunOf.head_mem {L X : St} {r : List Nat} (h : IsRunOf L X r) :
    r.headD 0 ∈ read X := by
  obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
  exact h.mem_read (by simp)

theorem IsRunOf.head_notL {L X : St} {r : List Nat} (h : IsRunOf L X r) :
    contains L (r.headD 0) = false := by
  obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
  exact h.mem_notL (by simp)

/-- **Run determinism.** On a WF branch, a run is determined by its head id:
the head pins the row (rows are disjoint), the position in it (rows are
duplicate-free), and maximality pins the extent. -/
theorem IsRunOf.head_det {L X : St} (hwf : WF X) {r₁ r₂ : List Nat}
    (h₁ : IsRunOf L X r₁) (h₂ : IsRunOf L X r₂)
    (hh : r₁.headD 0 = r₂.headD 0) : r₁ = r₂ := by
  obtain ⟨p₁, x₁, y₁, e₁, hne₁, htw₁⟩ := h₁
  obtain ⟨p₂, x₂, y₂, e₂, hne₂, htw₂⟩ := h₂
  obtain ⟨hd₁, tl₁, rfl⟩ := List.exists_cons_of_ne_nil hne₁
  obtain ⟨hd₂, tl₂, rfl⟩ := List.exists_cons_of_ne_nil hne₂
  simp only [List.headD_cons] at hh
  subst hh
  by_cases hp : p₁ = p₂
  · subst hp
    have hnd : (row X p₁).Nodup := row_nodup hwf p₁
    have e₁' : row X p₁ = x₁ ++ hd₁ :: (tl₁ ++ y₁) := by simpa using e₁
    have e₂' : row X p₁ = x₂ ++ hd₁ :: (tl₂ ++ y₂) := by simpa using e₂
    obtain ⟨-, hz⟩ := nodup_middle_inj hd₁ x₁ x₂ (tl₁ ++ y₁) (tl₂ ++ y₂)
      (e₁' ▸ hnd) (e₁'.symm.trans e₂')
    calc hd₁ :: tl₁
        = ((hd₁ :: tl₁) ++ y₁).takeWhile (fun v => !contains L v) := htw₁
      _ = (hd₁ :: (tl₁ ++ y₁)).takeWhile (fun v => !contains L v) := by simp
      _ = (hd₁ :: (tl₂ ++ y₂)).takeWhile (fun v => !contains L v) := by rw [hz]
      _ = ((hd₁ :: tl₂) ++ y₂).takeWhile (fun v => !contains L v) := by simp
      _ = hd₁ :: tl₂ := htw₂.symm
  · exact (row_disjoint hwf hp
      (show hd₁ ∈ row X p₁ by rw [e₁]; simp)
      (show hd₁ ∈ row X p₂ by rw [e₂]; simp)).elim

/-- The run payload of a placement command. -/
def cmdRun : Cmd → List Nat
  | .slot _ _ r => r
  | .atEnd _ r => r

/-- Every command `branchCmds` emits carries a genuine run of its branch. -/
theorem branchCmds_run {L X : St} {sk : Skel} {mk : Nat → Bool} {c : Cmd}
    (hc : c ∈ branchCmds L X sk mk) : IsRunOf L X (cmdRun c) := by
  unfold branchCmds at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨p, -, hc⟩ := hc
  rw [List.mem_map] at hc
  obtain ⟨pr, hpr, rfl⟩ := hc
  obtain ⟨x, y, e, hne, htw⟩ :=
    runsGo_shape (contains L) _ none (row X p) pr hpr
  have hrun : IsRunOf L X pr.2.1 := ⟨p, x, y, e, hne, htw⟩
  rcases pr with ⟨_ | pre, run, _ | s⟩ <;> exact hrun

/-- Runs collected at a slot are runs of their branch. -/
theorem slotRuns_run {L X : St} {sk : Skel} {mk : Nat → Bool} {p k : Nat}
    {r : List Nat} (h : r ∈ slotRuns (branchCmds L X sk mk) p k) :
    IsRunOf L X r := by
  unfold slotRuns at h
  rw [List.mem_filterMap] at h
  obtain ⟨c, hc, hr⟩ := h
  have hrun := branchCmds_run hc
  rcases c with ⟨tr, k', run⟩ | ⟨q, run⟩
  · by_cases hb : (tr == p && k' == k) = true
    · simp [hb] at hr
      subst hr
      exact hrun
    · simp [hb] at hr
  · simp at hr

/-- Runs collected for end placement are runs of their branch. -/
theorem endRuns_run {L X : St} {sk : Skel} {mk : Nat → Bool} {p : Nat}
    {r : List Nat} (h : r ∈ endRuns (branchCmds L X sk mk) p) :
    IsRunOf L X r := by
  unfold endRuns at h
  rw [List.mem_filterMap] at h
  obtain ⟨c, hc, hr⟩ := h
  have hrun := branchCmds_run hc
  rcases c with ⟨tr, k', run⟩ | ⟨q, run⟩
  · simp at hr
  · by_cases hb : (q == p) = true
    · simp [hb] at hr
      subst hr
      exact hrun
    · simp [hb] at hr

/-- **Cross-branch head injectivity.** Two same-slot runs (from either
branch) with the same head are equal: within a branch by `head_det` (WF),
across branches because the head would be live in both branches yet outside
L — barred by the pattern-8 exclusion. -/
theorem runs_head_inj {L A B : St} (mok : ModelOK L A B) {r s : List Nat}
    (hr : IsRunOf L A r ∨ IsRunOf L B r)
    (hs : IsRunOf L A s ∨ IsRunOf L B s)
    (hh : r.headD 0 = s.headD 0) : r = s := by
  rcases hr with hr | hr <;> rcases hs with hs | hs
  · exact hr.head_det mok.wfA hs hh
  · exact absurd
      (mok.common _ hr.head_mem (by rw [hh]; exact hs.head_mem))
      (contains_eq_false.mp hr.head_notL)
  · exact absurd
      (mok.common _ hs.head_mem (by rw [← hh]; exact hr.head_mem))
      (contains_eq_false.mp hs.head_notL)
  · exact hr.head_det mok.wfB hs hh

/-! ## §4 Lemma M1 — merge symmetry (`merge_comm`), state equality

`sibling-linked-proof.md` §4, Lemma M1: "the construction is symmetric in
A, B: every rule is branch-agnostic except the newest-first tiebreak, which
is symmetric." Mechanized as *state* equality. The proof splits into
(i) pointwise Bool symmetry of the membership classifiers, (ii) canonicity
of the newest-head-first sort on run lists with injective heads
(`sortRunsDesc_swap`, fed by §3's `runs_head_inj`), and (iii) key-disjoint
association-list reordering (`bbrows L A` vs `bbrows L B` keys are disjoint
by pattern-8), transported through `buildF` by congruence. -/

theorem liveMp_comm (L A B : St) : liveMp L A B = liveMp L B A := by
  funext u
  simp only [liveMp]
  cases contains A u <;> cases contains B u <;> cases contains L u <;> rfl

theorem markerp_comm (L A B : St) : markerp L A B = markerp L B A := by
  funext u
  simp only [markerp]
  cases contains A u <;> cases contains B u <;> rfl

theorem wp_comm (L A B : St) : wp L A B = wp L B A := by
  unfold wp
  rw [liveMp_comm, markerp_comm]

theorem skelOf_comm (L A B : St) : skelOf L A B = skelOf L B A := by
  unfold skelOf
  rw [wp_comm]

/-- The newest-head-first sort is canonical on run lists whose heads are
injective: sorting `x ++ y` and `y ++ x` agree. (Both are sorted
permutations of each other; head-injectivity makes the comparator
antisymmetric on the members.) -/
theorem sortRunsDesc_swap {x y : List (List Nat)}
    (hinj : ∀ r ∈ x ++ y, ∀ s ∈ x ++ y, r.headD 0 = s.headD 0 → r = s) :
    sortRunsDesc (x ++ y) = sortRunsDesc (y ++ x) := by
  have htrans : ∀ (a b c : List Nat),
      Nat.ble (b.headD 0) (a.headD 0) = true →
      Nat.ble (c.headD 0) (b.headD 0) = true →
      Nat.ble (c.headD 0) (a.headD 0) = true := by
    intro a b c h1 h2
    simp only [Nat.ble_eq] at *
    omega
  have htotal : ∀ (a b : List Nat),
      (Nat.ble (b.headD 0) (a.headD 0) ||
        Nat.ble (a.headD 0) (b.headD 0)) = true := by
    intro a b
    simp only [Bool.or_eq_true, Nat.ble_eq]
    omega
  unfold sortRunsDesc
  apply List.Perm.eq_of_pairwise
  · intro a b ha hb hab hba
    rw [List.mem_mergeSort] at ha hb
    refine hinj a ha b (List.mem_append.mpr (Or.symm (List.mem_append.mp hb)))
      ?_
    have h1 : Nat.ble (b.headD 0) (a.headD 0) = true := hab
    have h2 : Nat.ble (a.headD 0) (b.headD 0) = true := hba
    simp only [Nat.ble_eq] at h1 h2
    omega
  · exact List.pairwise_mergeSort htrans htotal _
  · exact List.pairwise_mergeSort htrans htotal _
  · exact (List.mergeSort_perm _ _).trans
      (List.perm_append_comm.trans (List.mergeSort_perm _ _).symm)

theorem slotRuns_append (c₁ c₂ : List Cmd) (p k : Nat) :
    slotRuns (c₁ ++ c₂) p k = slotRuns c₁ p k ++ slotRuns c₂ p k := by
  unfold slotRuns
  exact List.filterMap_append

theorem endRuns_append (c₁ c₂ : List Cmd) (p : Nat) :
    endRuns (c₁ ++ c₂) p = endRuns c₁ p ++ endRuns c₂ p := by
  unfold endRuns
  exact List.filterMap_append

/-- Head-injectivity instantiated at a slot: any two runs gathered there
(from either branch) with equal heads are equal. -/
theorem slot_head_inj {L A B : St} (mok : ModelOK L A B) {sk : Skel}
    {mk : Nat → Bool} {p k : Nat} :
    ∀ r ∈ slotRuns (branchCmds L A sk mk) p k ++
          slotRuns (branchCmds L B sk mk) p k,
    ∀ s ∈ slotRuns (branchCmds L A sk mk) p k ++
          slotRuns (branchCmds L B sk mk) p k,
      r.headD 0 = s.headD 0 → r = s := by
  intro r hr s hs hh
  refine runs_head_inj mok ?_ ?_ hh
  · rcases List.mem_append.mp hr with h | h
    · exact Or.inl (slotRuns_run h)
    · exact Or.inr (slotRuns_run h)
  · rcases List.mem_append.mp hs with h | h
    · exact Or.inl (slotRuns_run h)
    · exact Or.inr (slotRuns_run h)

theorem end_head_inj {L A B : St} (mok : ModelOK L A B) {sk : Skel}
    {mk : Nat → Bool} {p : Nat} :
    ∀ r ∈ endRuns (branchCmds L A sk mk) p ++
          endRuns (branchCmds L B sk mk) p,
    ∀ s ∈ endRuns (branchCmds L A sk mk) p ++
          endRuns (branchCmds L B sk mk) p,
      r.headD 0 = s.headD 0 → r = s := by
  intro r hr s hs hh
  refine runs_head_inj mok ?_ ?_ hh
  · rcases List.mem_append.mp hr with h | h
    · exact Or.inl (endRuns_run h)
    · exact Or.inr (endRuns_run h)
  · rcases List.mem_append.mp hs with h | h
    · exact Or.inl (endRuns_run h)
    · exact Or.inr (endRuns_run h)

/-- Row assembly is branch-order-independent (the heart of M1). -/
theorem rowAssemble_comm {L A B : St} (mok : ModelOK L A B) (sk : Skel)
    (mk : Nat → Bool) (p : Nat) (skelRow : List Nat) :
    rowAssemble
        (branchCmds L A sk mk ++ branchCmds L B sk mk) p skelRow =
      rowAssemble
        (branchCmds L B sk mk ++ branchCmds L A sk mk) p skelRow := by
  have hslot : ∀ k,
      sortRunsDesc
          (slotRuns (branchCmds L A sk mk ++ branchCmds L B sk mk) p k) =
        sortRunsDesc
          (slotRuns (branchCmds L B sk mk ++ branchCmds L A sk mk) p k) := by
    intro k
    rw [slotRuns_append, slotRuns_append]
    exact sortRunsDesc_swap (slot_head_inj mok)
  have hend :
      sortRunsDesc
          (endRuns (branchCmds L A sk mk ++ branchCmds L B sk mk) p) =
        sortRunsDesc
          (endRuns (branchCmds L B sk mk ++ branchCmds L A sk mk) p) := by
    rw [endRuns_append, endRuns_append]
    exact sortRunsDesc_swap (end_head_inj mok)
  unfold rowAssemble
  rw [hend]
  have hfun :
      (fun k =>
        (sortRunsDesc
            (slotRuns (branchCmds L A sk mk ++ branchCmds L B sk mk) p
              k)).flatten ++
          (skelRow.drop k).take 1) =
      (fun k =>
        (sortRunsDesc
            (slotRuns (branchCmds L B sk mk ++ branchCmds L A sk mk) p
              k)).flatten ++
          (skelRow.drop k).take 1) :=
    funext fun k => by rw [hslot k]
  rw [hfun]

/-! ### Association-list plumbing for the `outRows` block swap -/

theorem alGet_append (al₁ al₂ : List (Nat × List Nat)) (k : Nat) :
    alGet (al₁ ++ al₂) k =
      if alHas al₁ k then alGet al₁ k else alGet al₂ k := by
  by_cases h : alHas al₁ k
  · rw [if_pos h]
    cases hf : al₁.find? (fun kv => kv.1 == k) with
    | none =>
        rw [List.find?_eq_none] at hf
        rw [alHas, List.any_eq_true] at h
        obtain ⟨kv, hm, hp⟩ := h
        exact absurd hp (hf kv hm)
    | some kv => simp [alGet, List.find?_append, hf]
  · rw [if_neg h]
    have hf : al₁.find? (fun kv => kv.1 == k) = none := by
      rw [List.find?_eq_none]
      intro kv hm hp
      exact h (by rw [alHas, List.any_eq_true]; exact ⟨kv, hm, hp⟩)
    simp [alGet, List.find?_append, hf]

theorem alGet_eq_nil_of_not_has {al : List (Nat × List Nat)} {k : Nat}
    (h : ¬ alHas al k = true) : alGet al k = [] := by
  have hf : al.find? (fun kv => kv.1 == k) = none := by
    rw [List.find?_eq_none]
    intro kv hm hp
    exact h (by rw [alHas, List.any_eq_true]; exact ⟨kv, hm, hp⟩)
  simp [alGet, hf]

/-- Keys of `bbrows L X` are branch-born: in `X`, outside `L`. -/
theorem alHas_bbrows_key {L X : St} {k : Nat}
    (h : alHas (bbrows L X) k = true) : k ∈ read X ∧ k ∉ read L := by
  rw [alHas, List.any_eq_true] at h
  obtain ⟨kv, hm, hp⟩ := h
  unfold bbrows at hm
  rw [List.mem_filterMap] at hm
  obtain ⟨q, hq, he⟩ := hm
  by_cases hr : (row X q).isEmpty
  · rw [if_pos hr] at he
    cases he
  · rw [if_neg hr] at he
    cases he
    have hqk : q = k := by simpa using hp
    subst hqk
    unfold bornIds at hq
    rw [List.mem_filter] at hq
    refine ⟨hq.1, ?_⟩
    have h2 := hq.2
    simp only [Bool.not_eq_true'] at h2
    exact contains_eq_false.mp h2

/-- `alGet` sees through a swap of key-disjoint alist blocks. -/
theorem alGet_swap_disjoint {m x y : List (Nat × List Nat)}
    (hd : ∀ k, alHas x k = true → alHas y k = true → False) (k : Nat) :
    alGet (m ++ (x ++ y)) k = alGet (m ++ (y ++ x)) k := by
  rw [alGet_append m (x ++ y), alGet_append m (y ++ x)]
  by_cases hm : alHas m k
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm, alGet_append x y, alGet_append y x]
    by_cases hx : alHas x k
    · have hy : ¬ alHas y k = true := fun hy => hd k hx hy
      rw [if_pos hx, if_neg hy]
    · by_cases hy : alHas y k
      · rw [if_neg hx, if_pos hy]
      · rw [if_neg hx, if_neg hy, alGet_eq_nil_of_not_has hx,
          alGet_eq_nil_of_not_has hy]

/-! ### `expandRow`/`buildF` consume rows only through `alGet` -/

theorem expandRow_congr {r₁ r₂ : List (Nat × List Nat)} {mk : Nat → Bool}
    (h : ∀ k, alGet r₁ k = alGet r₂ k) :
    ∀ (mf : Nat) (rw : List Nat),
      expandRow r₁ mk mf rw = expandRow r₂ mk mf rw
  | 0, _ => rfl
  | mf + 1, rw => by
      unfold expandRow
      exact congrArg (fun g => List.flatMap g rw)
        (funext fun u => by
          by_cases hm : mk u
          · rw [if_pos hm, if_pos hm, h u, expandRow_congr h mf]
          · rw [if_neg hm, if_neg hm])

theorem buildF_congr {r₁ r₂ : List (Nat × List Nat)} {mk : Nat → Bool}
    (h : ∀ k, alGet r₁ k = alGet r₂ k) (mf : Nat) :
    ∀ (f p : Nat), buildF r₁ mk mf f p = buildF r₂ mk mf f p
  | 0, _ => rfl
  | f + 1, p => by
      unfold buildF
      rw [h p, expandRow_congr h mf]
      exact List.map_congr_left fun c _ =>
        congrArg (Tree.node c) (buildF_congr h mf f c)

/-- `alGet` into the merged rows is branch-order-independent. -/
theorem outRows_alGet_comm {L A B : St} (mok : ModelOK L A B) (k : Nat) :
    alGet (outRows L A B) k = alGet (outRows L B A) k := by
  have hM :
      (skelOf L A B).rows.map (fun kv =>
        (kv.1,
          rowAssemble
            (branchCmds L A (skelOf L A B) (markerp L A B) ++
              branchCmds L B (skelOf L A B) (markerp L A B))
            kv.1 kv.2)) =
      (skelOf L A B).rows.map (fun kv =>
        (kv.1,
          rowAssemble
            (branchCmds L B (skelOf L A B) (markerp L A B) ++
              branchCmds L A (skelOf L A B) (markerp L A B))
            kv.1 kv.2)) :=
    List.map_congr_left fun kv _ => by rw [rowAssemble_comm mok]
  have hdisj : ∀ j, alHas (bbrows L A) j = true →
      alHas (bbrows L B) j = true → False := by
    intro j hA hB
    obtain ⟨hAr, hAl⟩ := alHas_bbrows_key hA
    obtain ⟨hBr, hBl⟩ := alHas_bbrows_key hB
    exact hAl (mok.common j hAr hBr)
  simp only [outRows]
  rw [skelOf_comm L B A, markerp_comm L B A, ← hM,
    List.append_assoc, List.append_assoc]
  exact alGet_swap_disjoint hdisj k

/-- **Lemma M1 (symmetry), state equality.** `sibling-linked-proof.md` §4
[sketch → proved]. Requires `ModelOK`: within-branch run determinism uses
WF A / WF B, cross-branch head distinctness uses the pattern-8 exclusion. -/
theorem merge_comm {L A B : St} (mok : ModelOK L A B) :
    merge L A B = merge L B A := by
  simp only [merge]
  rw [markerp_comm L B A,
    show (read L).length + (read B).length + (read A).length + 1 =
        (read L).length + (read A).length + (read B).length + 1 by omega]
  exact buildF_congr (outRows_alGet_comm mok) _ _ 0

/-! ## §5 Lemma M0 — well-formedness and the survivor set

Proved here: the *content* analysis — everything any merged row (and hence
the output read) contains is (i) a skeleton entry (an L-id in the working
set `W`), (ii) a run element (a branch id outside L), or (iii) a wholesale
`bbrows` element (an id in some born node's branch row); consequently the
output mints no ids (`merge_reads_bound`), uses `0` for no node
(`zero_not_mem_merge`), and — under the branch-structure hypothesis
`LRowsOK` — stays inside `W` (`merge_mem_wp`). Owed (documented `sorry`s):
the placed-exactly-once/reachability halves — output `Nodup`
(`merge_read_nodup`) and the exact survivor-set identity (`merge_ids`). -/

/-- Branch-structure hypothesis: in branch `X`, an L-node only ever sits in
the root row or in an L-node's row — never under a branch-born parent. This
holds on genuine branches evolved from `L` (inserts never reparent an
existing node; `delete d` reparents `d`'s children onto `d`'s *own* parent,
so an L-node's parent chain stays inside L ∪ {⌂}), but it is **not** a
consequence of `ModelOK`'s membership constraints alone — an adversarial
`A` with an L-node filed under a born node breaks both the survivor-set
identity and output Nodup (the node would be placed by the skeleton *and*
travel wholesale with the born row). Phase 2b should discharge it from
branch reachability. -/
def LRowsOK (L X : St) : Prop :=
  ∀ w q, w ∈ read L → w ∈ row X q → q = 0 ∨ q ∈ read L

/-- Unpack an `alGet` hit into the underlying alist entry. -/
theorem alGet_mem_of_mem {al : List (Nat × List Nat)} {k c : Nat}
    (h : c ∈ alGet al k) : ∃ kv, kv ∈ al ∧ kv.1 = k ∧ c ∈ kv.2 := by
  unfold alGet at h
  cases hf : al.find? (fun kv => kv.1 == k) with
  | none => rw [hf] at h; simp at h
  | some kv =>
      rw [hf] at h
      exact ⟨kv, List.mem_of_find?_eq_some hf,
        by simpa using List.find?_some hf, h⟩

/-- `bbrows` entries are precisely born nodes paired with their branch row. -/
theorem bbrows_mem {L X : St} {kv : Nat × List Nat}
    (hkv : kv ∈ bbrows L X) : ∃ q, q ∈ bornIds L X ∧ kv = (q, row X q) := by
  unfold bbrows at hkv
  rw [List.mem_filterMap] at hkv
  obtain ⟨q, hq, he⟩ := hkv
  by_cases hr : (row X q).isEmpty
  · rw [if_pos hr] at he
    cases he
  · rw [if_neg hr] at he
    cases he
    exact ⟨q, hq, rfl⟩

/-- Elements of an assembled row are skeleton entries or run elements. -/
theorem rowAssemble_content {cmds : List Cmd} {p : Nat} {skelRow : List Nat}
    {c : Nat} (h : c ∈ rowAssemble cmds p skelRow) :
    c ∈ skelRow ∨
      (∃ r k, r ∈ slotRuns cmds p k ∧ c ∈ r) ∨
      (∃ r, r ∈ endRuns cmds p ∧ c ∈ r) := by
  unfold rowAssemble at h
  rcases List.mem_append.mp h with h | h
  · rw [List.mem_flatMap] at h
    obtain ⟨k, -, h⟩ := h
    rcases List.mem_append.mp h with h | h
    · rw [List.mem_flatten] at h
      obtain ⟨r, hr, hc⟩ := h
      unfold sortRunsDesc at hr
      rw [List.mem_mergeSort] at hr
      exact Or.inr (Or.inl ⟨r, k, hr, hc⟩)
    · exact Or.inl (List.drop_subset _ _ (List.take_subset _ _ h))
  · rw [List.mem_flatten] at h
    obtain ⟨r, hr, hc⟩ := h
    unfold sortRunsDesc at hr
    rw [List.mem_mergeSort] at hr
    exact Or.inr (Or.inr ⟨r, hr, hc⟩)

/-- Skeleton rows carry only working-set L-ids. -/
theorem skelFold_content {P : Nat → Prop} (h : Nat → Nat) :
    ∀ (l : List Nat) (sk : Skel), (∀ u ∈ l, P u) →
      (∀ kv ∈ sk.rows, ∀ c ∈ kv.2, P c) →
      ∀ kv ∈ (l.foldl (fun sk u =>
          { rows := alEnsure (alApp sk.rows (h u) u) u
            rowof := sk.rowof ++ [(u, h u)] }) sk).rows,
        ∀ c ∈ kv.2, P c
  | [], _, _, hsk => hsk
  | u :: l, sk, hl, hsk => by
      refine skelFold_content h l _ (fun v hv => hl v (List.mem_cons_of_mem u hv)) ?_
      intro kv hkv c hc
      have hu : P u := hl u List.mem_cons_self
      have halApp : ∀ kv' ∈ alApp sk.rows (h u) u, ∀ d ∈ kv'.2, P d := by
        intro kv' hkv' d hd
        unfold alApp at hkv'
        by_cases hh : alHas sk.rows (h u)
        · rw [if_pos hh] at hkv'
          rw [List.mem_map] at hkv'
          obtain ⟨kv'', hkv'', rfl⟩ := hkv'
          by_cases hj : (kv''.1 == h u) = true
          · rw [if_pos hj] at hd
            rcases List.mem_append.mp hd with hd | hd
            · exact hsk kv'' hkv'' d hd
            · rcases List.mem_singleton.mp hd with rfl
              exact hu
          · rw [if_neg hj] at hd
            exact hsk kv'' hkv'' d hd
        · rw [if_neg hh] at hkv'
          rcases List.mem_append.mp hkv' with hkv' | hkv'
          · exact hsk kv' hkv' d hd
          · rcases List.mem_singleton.mp hkv' with rfl
            rcases List.mem_singleton.mp hd with rfl
            exact hu
      have hkv' : kv ∈ alEnsure (alApp sk.rows (h u) u) u := hkv
      unfold alEnsure at hkv'
      by_cases he : alHas (alApp sk.rows (h u) u) u
      · rw [if_pos he] at hkv'
        exact halApp kv hkv' c hc
      · rw [if_neg he] at hkv'
        rcases List.mem_append.mp hkv' with hkv' | hkv'
        · exact halApp kv hkv' c hc
        · rcases List.mem_singleton.mp hkv' with rfl
          simp at hc

theorem skelOf_rows_content {L A B : St} :
    ∀ kv ∈ (skelOf L A B).rows, ∀ c ∈ kv.2,
      c ∈ read L ∧ wp L A B c = true := by
  simp only [skelOf]
  refine skelFold_content (fun u => wpar L (wp L A B) u) _ _ ?_ ?_
  · intro u hu
    rw [List.mem_filter] at hu
    exact ⟨hu.1, hu.2⟩
  · intro kv hkv c hc
    rcases List.mem_singleton.mp hkv with rfl
    simp at hc

/-- Case analysis for a merged-row element: skeleton entry, run element, or
wholesale `bbrows` element. -/
theorem outRows_cases {L A B : St} {k c : Nat}
    (h : c ∈ alGet (outRows L A B) k) :
    (c ∈ read L ∧ wp L A B c = true) ∨
      ((c ∈ read A ∨ c ∈ read B) ∧ contains L c = false) ∨
      (∃ q, q ∈ bornIds L A ∧ c ∈ row A q) ∨
      (∃ q, q ∈ bornIds L B ∧ c ∈ row B q) := by
  obtain ⟨kv, hkv, -, hc⟩ := alGet_mem_of_mem h
  simp only [outRows] at hkv
  rcases List.mem_append.mp hkv with hkv | hkv
  · rcases List.mem_append.mp hkv with hkv | hkv
    · -- a skeleton-assembled row
      rw [List.mem_map] at hkv
      obtain ⟨kv', hkv', rfl⟩ := hkv
      rcases rowAssemble_content hc with hsk | ⟨r, k', hr, hcr⟩ | ⟨r, hr, hcr⟩
      · exact Or.inl (skelOf_rows_content kv' hkv' c hsk)
      · rw [slotRuns_append] at hr
        rcases List.mem_append.mp hr with hr | hr
        · exact Or.inr (Or.inl ⟨Or.inl ((slotRuns_run hr).mem_read hcr),
            (slotRuns_run hr).mem_notL hcr⟩)
        · exact Or.inr (Or.inl ⟨Or.inr ((slotRuns_run hr).mem_read hcr),
            (slotRuns_run hr).mem_notL hcr⟩)
      · rw [endRuns_append] at hr
        rcases List.mem_append.mp hr with hr | hr
        · exact Or.inr (Or.inl ⟨Or.inl ((endRuns_run hr).mem_read hcr),
            (endRuns_run hr).mem_notL hcr⟩)
        · exact Or.inr (Or.inl ⟨Or.inr ((endRuns_run hr).mem_read hcr),
            (endRuns_run hr).mem_notL hcr⟩)
    · obtain ⟨q, hq, rfl⟩ := bbrows_mem hkv
      exact Or.inr (Or.inr (Or.inl ⟨q, hq, hc⟩))
  · obtain ⟨q, hq, rfl⟩ := bbrows_mem hkv
    exact Or.inr (Or.inr (Or.inr ⟨q, hq, hc⟩))

/-- Reads of the rebuilt forest, unfolded one level. -/
theorem readF_map_node (g : Nat → List Tree) :
    ∀ l : List Nat,
      readF (l.map (fun c => Tree.node c (g c))) =
        l.flatMap (fun c => c :: readF (g c))
  | [] => by simp [readF]
  | c :: l => by simp [readF, readT, readF_map_node g l]

/-- Content closure through the marker splice. -/
theorem expandRow_content {rows : List (Nat × List Nat)} {mk : Nat → Bool}
    {P : Nat → Prop} (hrows : ∀ k c, c ∈ alGet rows k → P c) :
    ∀ (mf : Nat) (r : List Nat), (∀ c ∈ r, P c) →
      ∀ c ∈ expandRow rows mk mf r, P c
  | 0, _, hr => hr
  | mf + 1, r, hr => by
      intro c hc
      unfold expandRow at hc
      rw [List.mem_flatMap] at hc
      obtain ⟨u, hu, hc⟩ := hc
      by_cases hm : mk u
      · rw [if_pos hm] at hc
        exact expandRow_content hrows mf (alGet rows u)
          (fun d hd => hrows u d hd) c hc
      · rw [if_neg hm] at hc
        rcases List.mem_singleton.mp hc with rfl
        exact hr _ hu

/-- Content closure through the rebuild: whatever holds of every merged-row
element holds of every id the output displays. -/
theorem buildF_reads_content {rows : List (Nat × List Nat)}
    {mk : Nat → Bool} {P : Nat → Prop}
    (hrows : ∀ k c, c ∈ alGet rows k → P c) (mf : Nat) :
    ∀ (f p u : Nat), u ∈ readF (buildF rows mk mf f p) → P u
  | 0, p, u => by
      intro h
      simp [buildF, readF] at h
  | f + 1, p, u => by
      intro h
      unfold buildF at h
      rw [readF_map_node, List.mem_flatMap] at h
      obtain ⟨c, hc, h⟩ := h
      have hPc : P c :=
        expandRow_content hrows mf _ (fun d hd => hrows p d hd) c hc
      rcases List.mem_cons.mp h with rfl | h
      · exact hPc
      · exact buildF_reads_content hrows mf f c u h

/-- The merge mints no ids: every displayed id comes from an input. -/
theorem merge_reads_bound {L A B : St} {u : Nat}
    (h : u ∈ read (merge L A B)) : u ∈ read L ∨ u ∈ read A ∨ u ∈ read B := by
  simp only [merge, read] at h
  refine buildF_reads_content
    (P := fun c => c ∈ read L ∨ c ∈ read A ∨ c ∈ read B) ?_ _ _ _ u h
  intro k c hc
  rcases outRows_cases hc with ⟨hL, -⟩ | ⟨hAB, -⟩ | ⟨q, -, hr⟩ | ⟨q, -, hr⟩
  · exact Or.inl hL
  · exact Or.inr hAB
  · exact Or.inr (Or.inl (mem_row_read hr))
  · exact Or.inr (Or.inr (mem_row_read hr))

/-- The nonzero half of M0: the output never uses the root id `0`. -/
theorem zero_not_mem_merge {L A B : St} (mok : ModelOK L A B) :
    0 ∉ read (merge L A B) := by
  intro h
  rcases merge_reads_bound h with h | h | h
  · exact mok.wfL.2 h
  · exact mok.wfA.2 h
  · exact mok.wfB.2 h

/-- The proved approximation to `merge_ids`'s ⊆ direction: under `LRowsOK`,
every output id is in the working set `W = liveM ∪ markers`. What separates
this from the full ⊆ direction is fuel adequacy of the marker splice (with
the fuel `merge` supplies, `expandRow` eliminates every marker, so `W` can
be sharpened to `liveM`). -/
theorem merge_mem_wp {L A B : St} (mok : ModelOK L A B)
    (hA : LRowsOK L A) (hB : LRowsOK L B) {u : Nat}
    (h : u ∈ read (merge L A B)) : wp L A B u = true := by
  simp only [merge, read] at h
  refine buildF_reads_content (P := fun c => wp L A B c = true) ?_ _ _ _ u h
  intro k c hc
  rcases outRows_cases hc with ⟨-, hw⟩ | ⟨hAB, hnL⟩ | ⟨q, hq, hr⟩ | ⟨q, hq, hr⟩
  · exact hw
  · rcases hAB with hm | hm
    · simp [wp, liveMp, contains_iff.mpr hm, hnL]
    · simp [wp, liveMp, contains_iff.mpr hm, hnL]
  · -- inside a born A-row: LRowsOK bars L-ids, so this is a born id too
    rw [bornIds, List.mem_filter] at hq
    have hq0 : q ≠ 0 := fun h0 => mok.wfA.2 (h0 ▸ hq.1)
    have hqL : q ∉ read L := by
      have := hq.2
      simp only [Bool.not_eq_true'] at this
      exact contains_eq_false.mp this
    have hcL : contains L c = false := by
      rw [contains_eq_false]
      intro hcl
      rcases hA c q hcl hr with h0 | hL
      · exact hq0 h0
      · exact hqL hL
    have hcA : contains A c = true := contains_iff.mpr (mem_row_read hr)
    simp [wp, liveMp, hcA, hcL]
  · rw [bornIds, List.mem_filter] at hq
    have hq0 : q ≠ 0 := fun h0 => mok.wfB.2 (h0 ▸ hq.1)
    have hqL : q ∉ read L := by
      have := hq.2
      simp only [Bool.not_eq_true'] at this
      exact contains_eq_false.mp this
    have hcL : contains L c = false := by
      rw [contains_eq_false]
      intro hcl
      rcases hB c q hcl hr with h0 | hL
      · exact hq0 h0
      · exact hqL hL
    have hcB : contains B c = true := contains_iff.mpr (mem_row_read hr)
    simp [wp, liveMp, hcB, hcL]

/-! The survivor-set identity (`merge_ids`) and the `Nodup` half of M0
(`merge_read_nodup`, `merge_WF`) live in `Shesha_M0.lean`, on top of the
parent-chain layer (`Shesha_Forest.lean`) and the skeleton
characterization (`Shesha_Skel.lean`). -/

/-! ## §6 Lemma M2 — L-extension (`merge_extends_L`)

Proved here, kernel-clean: the *filter transport* (`precedes` is preserved
by filtering, both ways) and the *run transparency* half of M2
(`rowAssemble_filter_L`: runs insert only non-L ids between skeleton
entries, so filtering an assembled row to L-ids returns exactly its skeleton
row — the marker splice at assembly IS the delete splice, cf.
`delete_preserves_survivor_order`). Owed (documented `sorry`):
`merge_L_filter`, the skeleton/DFS order identity. `merge_extends_L` is
derived from it by the proved transport. -/

/-- `u` appears strictly before `v` in `l` (as the two-element sublist
`[u, v] <+ l`). On duplicate-free lists — all WF reads — this is exactly
the display order of the pair. -/
def precedes (l : List Nat) (u v : Nat) : Prop := [u, v] <+ l

/-- Filtering preserves `precedes` in both directions for elements the
filter keeps. -/
theorem precedes_filter_iff {P : Nat → Bool} {l : List Nat} {u v : Nat}
    (hu : P u = true) (hv : P v = true) :
    precedes (l.filter P) u v ↔ precedes l u v := by
  constructor
  · intro h
    exact h.trans List.filter_sublist
  · intro h
    have hf := h.filter P
    rwa [show [u, v].filter P = [u, v] by simp [hu, hv]] at hf

/-- Filtering commutes with `flatMap` (pointwise). -/
theorem filter_flatMap (P : Nat → Bool) (f : Nat → List Nat) :
    ∀ l : List Nat,
      (l.flatMap f).filter P = l.flatMap (fun k => (f k).filter P)
  | [] => rfl
  | k :: l => by simp [List.filter_append, filter_flatMap P f l]

/-- The gap/element decomposition `rowAssemble` uses reassembles the row. -/
theorem flatMap_take_drop :
    ∀ l : List Nat,
      (List.range (l.length + 1)).flatMap (fun k => (l.drop k).take 1) = l
  | [] => rfl
  | a :: l => by
      rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
        List.flatMap_map]
      simp only [List.drop_zero, List.take_succ_cons, List.take_zero,
        Nat.succ_eq_add_one, List.drop_succ_cons]
      rw [flatMap_take_drop l]
      rfl

/-- **Run transparency** (the `rowAssemble` half of M2): runs insert only
non-L ids, so an assembled row filtered to L-members is exactly its
skeleton row. -/
theorem rowAssemble_filter_L {L A B : St} {sk : Skel} {mk : Nat → Bool}
    {p : Nat} {skelRow : List Nat}
    (hrow : ∀ c ∈ skelRow, contains L c = true) :
    (rowAssemble (branchCmds L A sk mk ++ branchCmds L B sk mk) p
        skelRow).filter (fun w => contains L w) = skelRow := by
  have hruns_nil : ∀ rs : List (List Nat),
      (∀ r ∈ rs, IsRunOf L A r ∨ IsRunOf L B r) →
      rs.flatten.filter (fun w => contains L w) = [] := by
    intro rs hrs
    rw [List.filter_eq_nil_iff]
    intro a ha
    rw [List.mem_flatten] at ha
    obtain ⟨r, hr, ha⟩ := ha
    rcases hrs r hr with h | h
    · simp [h.mem_notL ha]
    · simp [h.mem_notL ha]
  have hend : ((sortRunsDesc (endRuns
      (branchCmds L A sk mk ++ branchCmds L B sk mk) p)).flatten).filter
        (fun w => contains L w) = [] := by
    apply hruns_nil
    intro r hr
    unfold sortRunsDesc at hr
    rw [List.mem_mergeSort, endRuns_append] at hr
    rcases List.mem_append.mp hr with h | h
    · exact Or.inl (endRuns_run h)
    · exact Or.inr (endRuns_run h)
  have hslot : ∀ k : Nat, ((sortRunsDesc (slotRuns
      (branchCmds L A sk mk ++ branchCmds L B sk mk) p k)).flatten).filter
        (fun w => contains L w) = [] := by
    intro k
    apply hruns_nil
    intro r hr
    unfold sortRunsDesc at hr
    rw [List.mem_mergeSort, slotRuns_append] at hr
    rcases List.mem_append.mp hr with h | h
    · exact Or.inl (slotRuns_run h)
    · exact Or.inr (slotRuns_run h)
  have hstep :
      (fun k => (((sortRunsDesc (slotRuns
          (branchCmds L A sk mk ++ branchCmds L B sk mk) p k)).flatten ++
        (skelRow.drop k).take 1).filter (fun w => contains L w))) =
      (fun k => (skelRow.drop k).take 1) := by
    funext k
    rw [List.filter_append, hslot k, List.nil_append]
    exact List.filter_eq_self.mpr fun a ha =>
      hrow a (List.drop_subset _ _ (List.take_subset _ _ ha))
  unfold rowAssemble
  rw [List.filter_append, hend, List.append_nil]
  rw [filter_flatMap, hstep]
  exact flatMap_take_drop skelRow

/-! The M2 core identity (`merge_L_filter`) and Lemma M2
(`merge_extends_L`) are discharged in `Shesha_M2.lean`, on top of the
subtree/`wpar` bridge and the collapse alignment. -/

end Shesha

section AxiomAudit
/-! Axiom audit. Everything in this file is kernel-clean: `propext,
Classical.choice, Quot.sound` at most. No `native_decide` anywhere. -/
#print axioms Shesha.merge_comm
#print axioms Shesha.merge_reads_bound
#print axioms Shesha.zero_not_mem_merge
#print axioms Shesha.merge_mem_wp
#print axioms Shesha.rowAssemble_filter_L
#print axioms Shesha.IsRunOf.head_det
#print axioms Shesha.precedes_filter_iff
end AxiomAudit
