import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Sig

/-! # Shesha — event-level facts feeding the join hook

The bridge between the framework hypotheses of `shesha_join_at_eff`
(honesty, `loOn`-respect, effectiveness, closure) and the datatype-level
effective-fold theory (`Shesha_EffFold.lean`):

* §1 `loOn` at `rc = Either` is exactly `vis`-restricted-to-non-commuting;
  positional (`Before`) reformulations of `respects`/`EffFrom`.
* §2 causal pasts are **finite and enumerable** (Lamport timestamps:
  `causal_mono` bounds a past by its event's time, `timestamps_distinct`
  injects it into `Fin t`) — so `GenHonest` is never vacuous.
* §3 the honesty exclusions: no id-0 inserts, every delete's target was
  visibly inserted, no delete of an insert's anchor `vis`-before it.
* §4 the non-commutation certificates (`¬ commutes`) for the three
  touching shapes: insert/delete of the same id, same-anchor inserts,
  anchor insert vs child insert. -/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-! ## §1 `loOn` at `rc = Either`; positional machinery -/

/-- With `rc := Either`, a `loOn`-edge is a visible non-commuting pair. -/
theorem loOn_shesha_iff {C : Sal.Emulation.Configuration SheshaD.toCRDTSig}
    {ev : Set (Op SAppOp)} {a b : Op SAppOp} :
    loOn C ev a b ↔ (C.vis a b ∧ ¬ SheshaD.toCRDTSig.commutes a b) := by
  constructor
  · rintro (h | ⟨-, -, hrc, -⟩)
    · exact h
    · exact RcRes.noConfusion hrc
  · exact Or.inl

/-- `a` occurs strictly before `b` in `l`. -/
def Before {α : Type} (l : List α) (a b : α) : Prop :=
  ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ b ∈ l₂

theorem before_cons {α : Type} {l : List α} {a b e : α}
    (h : Before l a b) : Before (e :: l) a b := by
  obtain ⟨l₁, l₂, hl, hb⟩ := h
  exact ⟨e :: l₁, l₂, by rw [hl]; rfl, hb⟩

theorem before_head {α : Type} {l : List α} {a b : α} (h : b ∈ l) :
    Before (a :: l) a b := ⟨[], l, rfl, h⟩

/-- Two distinct members of a list are positionally ordered one way or
the other. -/
theorem before_trichotomy {α : Type} :
    ∀ {l : List α} {a b : α}, a ∈ l → b ∈ l → a ≠ b →
      Before l a b ∨ Before l b a
  | e :: l, a, b, ha, hb, hne => by
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd rfl hne
        · exact Or.inl (before_head hb')
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact Or.inr (before_head ha')
        · rcases before_trichotomy ha' hb' hne with h | h
          · exact Or.inl (before_cons h)
          · exact Or.inr (before_cons h)

/-- `Pairwise R` gives `R` on every positionally ordered pair. -/
theorem pairwise_before {α : Type} {R : α → α → Prop} {l : List α}
    (hp : l.Pairwise R) {a b : α} (h : Before l a b) : R a b := by
  obtain ⟨l₁, l₂, hl, hb⟩ := h
  subst hl
  induction l₁ with
  | nil => exact (List.pairwise_cons.mp hp).1 b hb
  | cons e l₁ ih => exact ih (List.pairwise_cons.mp hp).2

/-- Converse: `R` on every positionally ordered pair gives `Pairwise R`. -/
theorem pairwise_of_before {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, (∀ a b, Before l a b → R a b) → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | e :: l, h => by
      refine List.pairwise_cons.mpr ⟨fun b hb => h e b (before_head hb), ?_⟩
      exact pairwise_of_before (fun a b hab => h a b (before_cons hab))

/-- A `loOn`-respecting enumeration never inverts a `loOn` edge:
if `a` is before `b`, there is no edge `b → a`. -/
theorem respects_before {C : Sal.Emulation.Configuration SheshaD.toCRDTSig}
    {ev : Set (Op SAppOp)} {ρ : List (Op SAppOp)} {a b : Op SAppOp}
    (hr : respects ρ (loOn C ev)) (h : Before ρ a b) : ¬ loOn C ev b a :=
  pairwise_before hr h

/-- Effectiveness at a position: the step at any split point is
effective at the fold of its prefix. -/
theorem effFrom_at :
    ∀ {ρ l₁ l₂ : List (Op SAppOp)} {e : Op SAppOp} {s : Shesha.St},
      EffFrom s ρ → ρ = l₁ ++ e :: l₂ →
      effStep (applySeq SheshaD.toCRDTSig s l₁) e := by
  intro ρ l₁
  induction l₁ generalizing ρ with
  | nil =>
      rintro l₂ e s hEff rfl
      exact hEff.1
  | cons o l₁ ih =>
      rintro l₂ e s hEff rfl
      exact ih (ρ := l₁ ++ e :: l₂) hEff.2 rfl

/-- Effectiveness restricted to a prefix. -/
theorem effFrom_prefix :
    ∀ {l₁ l₂ : List (Op SAppOp)} {s : Shesha.St},
      EffFrom s (l₁ ++ l₂) → EffFrom s l₁ := by
  intro l₁
  induction l₁ with
  | nil => exact fun _ => trivial
  | cons o l₁ ih =>
      intro l₂ s hEff
      exact ⟨hEff.1, ih hEff.2⟩

/-! ## §2 causal pasts are enumerable

Lamport timestamps make every causal past finite: `causal_mono` bounds
the predecessors' times by the event's own, and `timestamps_distinct`
makes time injective — the past injects into `Fin t`. So `GenHonest` is
never vacuous, and the honesty exclusions of §3 always fire. -/

open Classical in
/-- Enumerate, by timestamp, the events of `P` with time below `n`. -/
noncomputable def pickList (P : Op SAppOp → Prop) : Nat → List (Op SAppOp)
  | 0 => []
  | n + 1 =>
      pickList P n ++
        (if h : ∃ e, P e ∧ e.1 = n then [Classical.choose h] else [])

theorem pickList_mem {P : Op SAppOp → Prop} :
    ∀ {n : Nat} {x : Op SAppOp}, x ∈ pickList P n → P x ∧ x.1 < n
  | n + 1, x, hx => by
      rw [pickList, List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨hP, hlt⟩ := pickList_mem hx
        exact ⟨hP, Nat.lt_succ_of_lt hlt⟩
      · by_cases h : ∃ e, P e ∧ e.1 = n
        · rw [dif_pos h, List.mem_singleton] at hx
          obtain ⟨hP, ht⟩ := Classical.choose_spec h
          refine ⟨hx ▸ hP, ?_⟩
          rw [hx, ht]
          exact Nat.lt_succ_self n
        · rw [dif_neg h] at hx
          exact absurd hx List.not_mem_nil

theorem pickList_complete {P : Op SAppOp → Prop}
    (huniq : ∀ x y, P x → P y → x.1 = y.1 → x = y) :
    ∀ {n : Nat} {x : Op SAppOp}, P x → x.1 < n → x ∈ pickList P n
  | n + 1, x, hP, hlt => by
      rw [pickList, List.mem_append]
      by_cases he : x.1 = n
      · have hex : ∃ e, P e ∧ e.1 = n := ⟨x, hP, he⟩
        refine Or.inr ?_
        rw [dif_pos hex, List.mem_singleton]
        obtain ⟨hP', ht'⟩ := Classical.choose_spec hex
        exact huniq x _ hP hP' (he.trans ht'.symm)
      · exact Or.inl (pickList_complete huniq hP
          (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) he))

theorem pickList_nodup {P : Op SAppOp → Prop} :
    ∀ n : Nat, (pickList P n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [pickList]
      by_cases h : ∃ e, P e ∧ e.1 = n
      · rw [dif_pos h, List.nodup_append]
        refine ⟨pickList_nodup n, List.nodup_singleton _, ?_⟩
        intro x hx y hy heq
        rw [List.mem_singleton] at hy
        obtain ⟨-, hlt⟩ := pickList_mem hx
        obtain ⟨-, ht⟩ := Classical.choose_spec h
        rw [heq, hy, ht] at hlt
        exact Nat.lt_irrefl n hlt
      · rw [dif_neg h, List.append_nil]
        exact pickList_nodup n

/-- Any time-bounded, time-injective event predicate is enumerable. -/
theorem sep_enumerable {P : Op SAppOp → Prop} {n : Nat}
    (hbound : ∀ x, P x → x.1 < n)
    (huniq : ∀ x y, P x → P y → x.1 = y.1 → x = y) :
    ∃ π : List (Op SAppOp), π.Nodup ∧ ∀ x, x ∈ π ↔ P x :=
  ⟨pickList P n, pickList_nodup n, fun x =>
    ⟨fun h => (pickList_mem h).1,
     fun h => pickList_complete huniq h (hbound x h)⟩⟩

/-- **Causal pasts are enumerable** — `GenHonest` always bites. -/
theorem past_enumerable (C : Configuration SheshaD) (e : Op SAppOp) :
    ∃ π : List (Op SAppOp), listPermOf π {e' ∈ C.events | C.vis e' e} := by
  obtain ⟨π, hnd, hmem⟩ := sep_enumerable
    (P := fun e' => e' ∈ C.events ∧ C.vis e' e) (n := e.1)
    (fun x hx => C.causal_mono hx.2)
    (fun x y hx hy heq =>
      (Configuration.core C).ts_unique hx.1 hy.1 heq)
  exact ⟨π, hnd, hmem⟩

/-- A causal past enumerated with a prescribed last element. -/
theorem past_enumerable_last (C : Configuration SheshaD)
    {e d : Op SAppOp} (hd : d ∈ C.events) (hvd : C.vis d e) :
    ∃ π : List (Op SAppOp),
      listPermOf (π ++ [d]) {e' ∈ C.events | C.vis e' e} := by
  obtain ⟨π, hnd, hmem⟩ := sep_enumerable
    (P := fun e' => (e' ∈ C.events ∧ C.vis e' e) ∧ e' ≠ d) (n := e.1)
    (fun x hx => C.causal_mono hx.1.2)
    (fun x y hx hy heq =>
      (Configuration.core C).ts_unique hx.1.1 hy.1.1 heq)
  refine ⟨π, ?_, fun a => ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnd, List.nodup_singleton _, ?_⟩
    intro x hx y hy
    rw [List.mem_singleton] at hy
    rw [hy]
    exact ((hmem x).mp hx).2
  · rw [List.mem_append, List.mem_singleton]
    constructor
    · rintro (ha | rfl)
      · exact ((hmem a).mp ha).1
      · exact ⟨hd, hvd⟩
    · intro ha
      by_cases had : a = d
      · exact Or.inr had
      · exact Or.inl ((hmem a).mpr ⟨ha, had⟩)

/-! ## §3 the honesty exclusions -/

theorem opInsIds_map_toSOp :
    ∀ {ρ : List (Op SAppOp)} {u : Nat},
      u ∈ Shesha.opInsIds (ρ.map toSOp) →
      ∃ r a, (u, r, SAppOp.insA a) ∈ ρ
  | e :: ρ, u, h => by
      rcases e with ⟨t, r', op⟩
      cases op with
      | insA a =>
          rw [List.map_cons,
            show toSOp (t, r', SAppOp.insA a) = .ins t a from rfl,
            Shesha.opInsIds] at h
          rcases List.mem_cons.mp h with rfl | h'
          · exact ⟨r', a, List.mem_cons_self ..⟩
          · obtain ⟨r'', a'', hm⟩ := opInsIds_map_toSOp h'
            exact ⟨r'', a'', List.mem_cons_of_mem _ hm⟩
      | delA d =>
          rw [List.map_cons,
            show toSOp (t, r', SAppOp.delA d) = .del d from rfl,
            Shesha.opInsIds] at h
          obtain ⟨r'', a'', hm⟩ := opInsIds_map_toSOp h
          exact ⟨r'', a'', List.mem_cons_of_mem _ hm⟩

/-- A live id of a fold was inserted by some event of the enumeration. -/
theorem read_fold_ins {ρ : List (Op SAppOp)} {u : Nat}
    (h : u ∈ Shesha.read (applySeq SheshaD.toCRDTSig SheshaD.init ρ)) :
    ∃ r a, (u, r, SAppOp.insA a) ∈ ρ := by
  rw [applySeq_toSOp] at h
  rcases Shesha.mem_read_steps _ _ h with h' | h'
  · exact absurd h' List.not_mem_nil
  · exact opInsIds_map_toSOp h'

variable {C : Configuration SheshaD}

/-- No honest insert has id `0`. -/
theorem honest_ins_nonzero (hH : SheshaHonest C)
    {t : Timestamp} {r : Replica} {a : Nat}
    (he : (t, r, SAppOp.insA a) ∈ C.events) : t ≠ 0 := by
  obtain ⟨π, hπ⟩ := past_enumerable C (t, r, SAppOp.insA a)
  exact (hH _ he π hπ).2.1

/-- No honest insert is its own anchor. -/
theorem honest_ins_ne_anchor (hH : SheshaHonest C)
    {t : Timestamp} {r : Replica} {a : Nat}
    (he : (t, r, SAppOp.insA a) ∈ C.events) : t ≠ a := by
  obtain ⟨π, hπ⟩ := past_enumerable C (t, r, SAppOp.insA a)
  obtain ⟨hfresh, hnz, hanch⟩ := hH _ he π hπ
  intro hta
  rcases hanch with h0 | hmem
  · exact hnz (hta.trans h0)
  · exact hfresh (hta ▸ hmem)

/-- An honest delete's target was **visibly** inserted (the unique insert
of that id sits in the delete's causal past). -/
theorem honest_del_sees_ins (hH : SheshaHonest C)
    {t : Timestamp} {r : Replica} {d : Nat}
    (he : (t, r, SAppOp.delA d) ∈ C.events) :
    ∃ r' a', (d, r', SAppOp.insA a') ∈ C.events ∧
      C.vis (d, r', SAppOp.insA a') (t, r, SAppOp.delA d) := by
  obtain ⟨π, hπ⟩ := past_enumerable C (t, r, SAppOp.delA d)
  have hg : d ∈ Shesha.read (applySeq SheshaD.toCRDTSig SheshaD.init π) :=
    hH _ he π hπ
  obtain ⟨r', a', hm⟩ := read_fold_ins hg
  have hp := (hπ.2 _).mp hm
  exact ⟨r', a', hp.1, hp.2⟩

/-- No honest delete targets `0`. -/
theorem honest_del_nonzero (hH : SheshaHonest C)
    {t : Timestamp} {r : Replica} {d : Nat}
    (he : (t, r, SAppOp.delA d) ∈ C.events) : d ≠ 0 := by
  obtain ⟨r', a', hins, -⟩ := honest_del_sees_ins hH he
  exact honest_ins_nonzero hH hins

/-- **P1 exclusion, positive form**: an id's (unique) insert is
`vis`-before any delete of it. -/
theorem honest_ins_vis_del (hH : SheshaHonest C)
    {x : Nat} {ri : Replica} {ai : Nat} {td : Timestamp} {rd : Replica}
    (hi : (x, ri, SAppOp.insA ai) ∈ C.events)
    (hd : (td, rd, SAppOp.delA x) ∈ C.events) :
    C.vis (x, ri, SAppOp.insA ai) (td, rd, SAppOp.delA x) := by
  obtain ⟨r', a', hins, hvis⟩ := honest_del_sees_ins hH hd
  have heq : ((x, r', SAppOp.insA a') : Op SAppOp)
      = (x, ri, SAppOp.insA ai) :=
    (Configuration.core C).ts_unique hins hi rfl
  exact heq ▸ hvis

/-- An honest insert's (nonroot) anchor was visibly inserted. -/
theorem honest_anchor_sees_ins (hH : SheshaHonest C)
    {x : Nat} {r : Replica} {a : Nat} (ha0 : a ≠ 0)
    (hi : (x, r, SAppOp.insA a) ∈ C.events) :
    ∃ r' a', (a, r', SAppOp.insA a') ∈ C.events ∧
      C.vis (a, r', SAppOp.insA a') (x, r, SAppOp.insA a) := by
  obtain ⟨π, hπ⟩ := past_enumerable C (x, r, SAppOp.insA a)
  rcases (hH _ hi π hπ).2.2 with h0 | hmem
  · exact absurd h0 ha0
  · obtain ⟨r', a', hm⟩ := read_fold_ins hmem
    have hp := (hπ.2 _).mp hm
    exact ⟨r', a', hp.1, hp.2⟩

/-- **P2 exclusion**: no delete of an insert's own anchor is `vis`-before
that insert (the anchor would be dead at the issuer's causal past). -/
theorem honest_no_del_anchor_vis_ins (hH : SheshaHonest C)
    {x : Nat} {r : Replica} {a : Nat} {td : Timestamp} {rd : Replica}
    (ha0 : a ≠ 0)
    (hd : (td, rd, SAppOp.delA a) ∈ C.events)
    (hv : C.vis (td, rd, SAppOp.delA a) (x, r, SAppOp.insA a)) : False := by
  have hi : (x, r, SAppOp.insA a) ∈ C.events := C.vis_tgt hv
  obtain ⟨π, hπ⟩ := past_enumerable_last C hd hv
  rcases (hH _ hi _ hπ).2.2 with h0 | hmem
  · exact ha0 h0
  · rw [applySeq_append_single,
      show SheshaD.toCRDTSig.update
          (applySeq SheshaD.toCRDTSig SheshaD.init π) (td, rd, SAppOp.delA a)
        = Shesha.delete (applySeq SheshaD.toCRDTSig SheshaD.init π) a
        from rfl,
      Shesha.read_delete, Shesha.seqDel, List.mem_filter] at hmem
    exact absurd rfl (of_decide_eq_true hmem.2)

/-! ## §4 non-commutation certificates -/

theorem sUpdate_ins (s : Shesha.St) (t : Timestamp) (r : Replica) (a : Nat) :
    SheshaD.toCRDTSig.update s (t, r, SAppOp.insA a) = Shesha.insert s t a :=
  rfl

theorem sUpdate_del (s : Shesha.St) (t : Timestamp) (r : Replica) (d : Nat) :
    SheshaD.toCRDTSig.update s (t, r, SAppOp.delA d) = Shesha.delete s d :=
  rfl

/-- **G1**: an id's insert and its delete do not commute. -/
theorem ncomm_ins_del_self {x : Nat} {ri rd : Replica} {ai : Nat}
    {td : Timestamp} (hxa : x ≠ ai) :
    ¬ SheshaD.toCRDTSig.commutes
        (x, ri, SAppOp.insA ai) (td, rd, SAppOp.delA x) := by
  intro hc
  have hax : ai ≠ x := fun h' => hxa h'.symm
  by_cases ha0 : ai = 0
  · subst ha0
    have h := hc ([] : Shesha.St)
    rw [sUpdate_ins, sUpdate_del, sUpdate_del, sUpdate_ins] at h
    simp [Shesha.insert, Shesha.delete, Shesha.delF, Shesha.delT,
      Shesha.insF] at h
  · have h := hc ([Shesha.Tree.node ai []] : Shesha.St)
    rw [sUpdate_ins, sUpdate_del, sUpdate_del, sUpdate_ins] at h
    simp [Shesha.insert, Shesha.delete, ha0, Shesha.insF, Shesha.insT,
      Shesha.delF, Shesha.delT, hax] at h
    injection h with h1 h2
    injection h1 with h3 h4
    cases h4

/-- **G2**: same-anchor inserts do not commute. -/
theorem ncomm_ins_ins_same_anchor {x y p : Nat} {rx ry : Replica}
    (hxy : x ≠ y) (hxp : x ≠ p) (hyp : y ≠ p) :
    ¬ SheshaD.toCRDTSig.commutes
        (x, rx, SAppOp.insA p) (y, ry, SAppOp.insA p) := by
  intro hc
  by_cases hp0 : p = 0
  · subst hp0
    have h := hc ([] : Shesha.St)
    rw [sUpdate_ins, sUpdate_ins, sUpdate_ins, sUpdate_ins] at h
    simp [Shesha.insert] at h
    injection h with h1 h2
    injection h1 with h3 h4
    exact hxy h3.symm
  · have h := hc ([Shesha.Tree.node p []] : Shesha.St)
    rw [sUpdate_ins, sUpdate_ins, sUpdate_ins, sUpdate_ins] at h
    simp [Shesha.insert, hp0, Shesha.insF, Shesha.insT, hxp, hyp] at h
    injection h with h1 h2
    injection h1 with h3 h4
    injection h4 with h5 h6
    injection h5 with h7 h8
    exact hxy h7.symm

/-- **G3**: an anchor's insert and a child insert at that anchor do not
commute. -/
theorem ncomm_ins_anchor_child {p : Nat} {r' ri : Replica} {a' x : Nat}
    (hp0 : p ≠ 0) (hpa : p ≠ a') :
    ¬ SheshaD.toCRDTSig.commutes
        (p, r', SAppOp.insA a') (x, ri, SAppOp.insA p) := by
  intro hc
  by_cases ha0 : a' = 0
  · subst ha0
    have h := hc ([] : Shesha.St)
    rw [sUpdate_ins, sUpdate_ins, sUpdate_ins, sUpdate_ins] at h
    simp [Shesha.insert, hp0, Shesha.insF, Shesha.insT] at h
    injection h with h1 h2
    injection h1 with h3 h4
    cases h4
  · have hap : a' ≠ p := fun h' => hpa h'.symm
    have h := hc ([Shesha.Tree.node a' []] : Shesha.St)
    rw [sUpdate_ins, sUpdate_ins, sUpdate_ins, sUpdate_ins] at h
    simp [Shesha.insert, hp0, ha0, Shesha.insF, Shesha.insT, hap] at h
    injection h with h1 h2
    injection h1 with h3 h4
    injection h4 with h5 h6
    injection h5 with h7 h8
    cases h8

end Sal.ConditionedMRDTs
