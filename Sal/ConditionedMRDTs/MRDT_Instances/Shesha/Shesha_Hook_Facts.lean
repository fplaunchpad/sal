import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Sig

/-! # Shesha — event-level facts feeding the join hook

The bridge between the framework hypotheses of the join hook
(`shesha_join_at_effC`)
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

/-! ## §5 the witness normal form — positional and transport helpers -/

theorem before_split_prefix {γ : Type} :
    ∀ {ρ α β : List γ} {a b : γ}, ρ.Nodup → Before ρ a b →
      ρ = α ++ b :: β → a ∈ α := by
  intro ρ α
  induction α generalizing ρ with
  | nil =>
      rintro β a b hnd hab rfl
      obtain ⟨l₁, l₂, hl, hb⟩ := hab
      rw [List.nil_append] at hl hnd
      cases l₁ with
      | nil =>
          rw [List.nil_append] at hl
          injection hl with h1 h2
          refine absurd ?_ (List.nodup_cons.mp hnd).1
          rw [h2]
          exact hb
      | cons c l₁' =>
          rw [List.cons_append] at hl
          injection hl with h1 h2
          refine absurd ?_ (List.nodup_cons.mp hnd).1
          rw [h2]
          exact List.mem_append_right _ (List.mem_cons_of_mem _ hb)
  | cons e α' ih =>
      rintro β a b hnd hab rfl
      obtain ⟨l₁, l₂, hl, hb⟩ := hab
      rw [List.cons_append] at hl hnd
      cases l₁ with
      | nil =>
          rw [List.nil_append] at hl
          injection hl with h1 h2
          rw [← h1]
          exact List.mem_cons_self ..
      | cons c l₁' =>
          rw [List.cons_append] at hl
          injection hl with h1 h2
          exact List.mem_cons_of_mem _
            (ih (List.nodup_cons.mp hnd).2 ⟨l₁', l₂, h2, hb⟩ rfl)

theorem before_asymm {γ : Type} {ρ : List γ} {a b : γ}
    (hnd : ρ.Nodup) (h1 : Before ρ a b) (h2 : Before ρ b a) : False := by
  obtain ⟨l₁, l₂, hl, hb⟩ := h1
  have hbl₁ : b ∈ l₁ := before_split_prefix hnd h2 hl
  subst hl
  rw [List.nodup_append] at hnd
  exact hnd.2.2 b hbl₁ b (List.mem_cons_of_mem _ hb) rfl

theorem sublist2_nodup_ne {x y : Nat} {l : List Nat}
    (h : List.Sublist [x, y] l) (hnd : l.Nodup) : x ≠ y := by
  rintro rfl
  have hnd2 := List.Sublist.nodup h hnd
  exact (List.nodup_cons.mp hnd2).1 (List.mem_singleton.mpr rfl)

theorem mem_opInsIds_of_mem :
    ∀ {ρ : List (Op SAppOp)} {u : Nat} {r : Replica} {a : Nat},
      (u, r, SAppOp.insA a) ∈ ρ → u ∈ Shesha.opInsIds (ρ.map toSOp)
  | e :: ρ, u, r, a, hm => by
      rw [List.map_cons]
      rcases List.mem_cons.mp hm with he | hm'
      · rw [← he,
          show toSOp (u, r, SAppOp.insA a) = Shesha.Op.ins u a from rfl,
          Shesha.opInsIds]
        exact List.mem_cons_self ..
      · rcases e with ⟨t', r', op⟩
        cases op with
        | insA a' =>
            rw [show toSOp (t', r', SAppOp.insA a') = Shesha.Op.ins t' a'
                from rfl, Shesha.opInsIds]
            exact List.mem_cons_of_mem _ (mem_opInsIds_of_mem hm')
        | delA d =>
            rw [show toSOp (t', r', SAppOp.delA d) = Shesha.Op.del d
                from rfl, Shesha.opInsIds]
            exact mem_opInsIds_of_mem hm'

theorem mem_opDelIds_of_mem :
    ∀ {ρ : List (Op SAppOp)} {t : Timestamp} {r : Replica} {d : Nat},
      (t, r, SAppOp.delA d) ∈ ρ → d ∈ Shesha.opDelIds (ρ.map toSOp)
  | e :: ρ, t, r, d, hm => by
      rw [List.map_cons]
      rcases List.mem_cons.mp hm with he | hm'
      · rw [← he,
          show toSOp (t, r, SAppOp.delA d) = Shesha.Op.del d from rfl,
          Shesha.opDelIds]
        exact List.mem_cons_self ..
      · rcases e with ⟨t', r', op⟩
        cases op with
        | insA a' =>
            rw [show toSOp (t', r', SAppOp.insA a') = Shesha.Op.ins t' a'
                from rfl, Shesha.opDelIds]
            exact mem_opDelIds_of_mem hm'
        | delA d' =>
            rw [show toSOp (t', r', SAppOp.delA d') = Shesha.Op.del d'
                from rfl, Shesha.opDelIds]
            exact List.mem_cons_of_mem _ (mem_opDelIds_of_mem hm')

theorem opDelIds_map_toSOp :
    ∀ {ρ : List (Op SAppOp)} {d : Nat},
      d ∈ Shesha.opDelIds (ρ.map toSOp) →
      ∃ t r, (t, r, SAppOp.delA d) ∈ ρ
  | e :: ρ, d, h => by
      rcases e with ⟨t', r', op⟩
      cases op with
      | insA a' =>
          rw [List.map_cons,
            show toSOp (t', r', SAppOp.insA a') = Shesha.Op.ins t' a'
              from rfl, Shesha.opDelIds] at h
          obtain ⟨t, r, hm⟩ := opDelIds_map_toSOp h
          exact ⟨t, r, List.mem_cons_of_mem _ hm⟩
      | delA d' =>
          rw [List.map_cons,
            show toSOp (t', r', SAppOp.delA d') = Shesha.Op.del d'
              from rfl, Shesha.opDelIds] at h
          rcases List.mem_cons.mp h with rfl | h'
          · exact ⟨t', r', List.mem_cons_self ..⟩
          · obtain ⟨t, r, hm⟩ := opDelIds_map_toSOp h'
            exact ⟨t, r, List.mem_cons_of_mem _ hm⟩

theorem mem_anchIds_of_mem :
    ∀ {ρ : List (Op SAppOp)} {x : Nat} {r : Replica} {p : Nat},
      (x, r, SAppOp.insA p) ∈ ρ → x ∈ Shesha.anchIds (ρ.map toSOp) p
  | e :: ρ, x, r, p, hm => by
      rw [List.map_cons]
      rcases List.mem_cons.mp hm with he | hm'
      · rw [← he,
          show toSOp (x, r, SAppOp.insA p) = Shesha.Op.ins x p from rfl,
          Shesha.anchIds, if_pos rfl]
        exact List.mem_cons_self ..
      · rcases e with ⟨t', r', op⟩
        cases op with
        | insA a' =>
            rw [show toSOp (t', r', SAppOp.insA a') = Shesha.Op.ins t' a'
                from rfl, Shesha.anchIds]
            by_cases hap : a' = p
            · rw [if_pos hap]
              exact List.mem_cons_of_mem _ (mem_anchIds_of_mem hm')
            · rw [if_neg hap]
              exact mem_anchIds_of_mem hm'
        | delA d' =>
            rw [show toSOp (t', r', SAppOp.delA d') = Shesha.Op.del d'
                from rfl, Shesha.anchIds]
            exact mem_anchIds_of_mem hm'

theorem anchIds_map_toSOp :
    ∀ {ρ : List (Op SAppOp)} {x p : Nat},
      x ∈ Shesha.anchIds (ρ.map toSOp) p →
      ∃ r, (x, r, SAppOp.insA p) ∈ ρ
  | e :: ρ, x, p, h => by
      rcases e with ⟨t', r', op⟩
      cases op with
      | insA a' =>
          rw [List.map_cons,
            show toSOp (t', r', SAppOp.insA a') = Shesha.Op.ins t' a'
              from rfl, Shesha.anchIds] at h
          by_cases hap : a' = p
          · rw [if_pos hap] at h
            rcases List.mem_cons.mp h with rfl | h'
            · exact ⟨r', hap ▸ List.mem_cons_self ..⟩
            · obtain ⟨r, hm⟩ := anchIds_map_toSOp h'
              exact ⟨r, List.mem_cons_of_mem _ hm⟩
          · rw [if_neg hap] at h
            obtain ⟨r, hm⟩ := anchIds_map_toSOp h
            exact ⟨r, List.mem_cons_of_mem _ hm⟩
      | delA d' =>
          rw [List.map_cons,
            show toSOp (t', r', SAppOp.delA d') = Shesha.Op.del d'
              from rfl, Shesha.anchIds] at h
          obtain ⟨r, hm⟩ := anchIds_map_toSOp h
          exact ⟨r, List.mem_cons_of_mem _ hm⟩

/-- Two `p`-anchored ids in `anchIds` order come from positionally
ordered insert events. -/
theorem anchIds_sublist2_before :
    ∀ {ρ : List (Op SAppOp)} {p u v : Nat},
      List.Sublist [u, v] (Shesha.anchIds (ρ.map toSOp) p) →
      ∃ ru rv, Before ρ (u, ru, SAppOp.insA p) (v, rv, SAppOp.insA p)
  | [], p, u, v, h => by
      rw [List.map_nil, Shesha.anchIds] at h
      exact absurd (List.sublist_nil.mp h) (by intro hc; cases hc)
  | e :: ρ, p, u, v, h => by
      rcases e with ⟨t', r', op⟩
      cases op with
      | insA a' =>
          rw [List.map_cons,
            show toSOp (t', r', SAppOp.insA a') = Shesha.Op.ins t' a'
              from rfl, Shesha.anchIds] at h
          by_cases hap : a' = p
          · rw [if_pos hap] at h
            subst hap
            cases h with
            | cons _ h' =>
                obtain ⟨ru, rv, hb⟩ := anchIds_sublist2_before h'
                exact ⟨ru, rv, before_cons hb⟩
            | cons₂ _ h' =>
                have hv : v ∈ Shesha.anchIds (ρ.map toSOp) a' :=
                  (List.singleton_sublist.mp h')
                obtain ⟨rv, hm⟩ := anchIds_map_toSOp hv
                exact ⟨r', rv, before_head hm⟩
          · rw [if_neg hap] at h
            obtain ⟨ru, rv, hb⟩ := anchIds_sublist2_before h
            exact ⟨ru, rv, before_cons hb⟩
      | delA d' =>
          rw [List.map_cons,
            show toSOp (t', r', SAppOp.delA d') = Shesha.Op.del d'
              from rfl, Shesha.anchIds] at h
          obtain ⟨ru, rv, hb⟩ := anchIds_sublist2_before h
          exact ⟨ru, rv, before_cons hb⟩

theorem before_mem_left {γ : Type} {l : List γ} {a b : γ}
    (h : Before l a b) : a ∈ l := by
  obtain ⟨l₁, l₂, hl, -⟩ := h
  rw [hl]
  exact List.mem_append_right _ (List.mem_cons_self ..)

theorem before_mem_right {γ : Type} {l : List γ} {a b : γ}
    (h : Before l a b) : b ∈ l := by
  obtain ⟨l₁, l₂, hl, hb⟩ := h
  rw [hl]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ hb)

/-! ## §5b every ordered delete–insert pair of a witness is clean -/

section WitnessNF

variable {C : Configuration SheshaD}
variable {ev : Set (Op SAppOp)} {ρ : List (Op SAppOp)}

/-- **(†)**: in an honest, `loOn`-respecting, effective witness, a delete
positioned before an insert touches neither its id nor its anchor — the
hypothesis under which deletes postpone (`steps_postpone_deletes`). -/
theorem witness_delBeforeOK
    (hH : SheshaHonest C)
    (hirr : ∀ a : Op SAppOp, ¬ C.vis a a)
    (hsub : ∀ a ∈ ev, a ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev → a ∈ ev)
    (hperm : listPermOf ρ ev)
    (hresp : respects ρ (loOn (Configuration.core C) ev))
    (hW : SheshaEff ρ) :
    (ρ.map toSOp).Pairwise Shesha.DelBeforeOK := by
  rw [List.pairwise_map]
  refine pairwise_of_before (fun a b hab => ?_)
  have hmem : ∀ x, x ∈ ρ → x ∈ C.events := fun x hx =>
    hsub x ((hperm.2 x).mp hx)
  have haev : a ∈ C.events := hmem a (before_mem_left hab)
  have hbev : b ∈ C.events := hmem b (before_mem_right hab)
  rcases a with ⟨ta, ra, opa⟩
  rcases b with ⟨tb, rb, opb⟩
  cases opa with
  | insA _ => cases opb <;> trivial
  | delA d =>
    cases opb with
    | delA _ => trivial
    | insA p =>
      show d ≠ tb ∧ d ≠ p
      constructor
      · rintro rfl
        have hvis : C.vis (d, rb, SAppOp.insA p) (ta, ra, SAppOp.delA d) :=
          honest_ins_vis_del hH hbev haev
        have hnc := ncomm_ins_del_self (ri := rb) (rd := ra) (td := ta)
          (honest_ins_ne_anchor hH hbev)
        exact respects_before hresp hab (loOn_shesha_iff.mpr ⟨hvis, hnc⟩)
      · rintro rfl
        -- the delete targets the insert's anchor `p = d`
        have hp0 : d ≠ 0 := honest_del_nonzero hH haev
        obtain ⟨r', a', hpev, hpvis⟩ :=
          honest_anchor_sees_ins hH hp0 hbev
        have hpa : d ≠ a' := honest_ins_ne_anchor hH hpev
        set ep : Op SAppOp := (d, r', SAppOp.insA a') with hep
        have hnc_pb : ¬ SheshaD.toCRDTSig.commutes ep (tb, rb, SAppOp.insA d) :=
          ncomm_ins_anchor_child hp0 hpa
        have hepev : ep ∈ ev :=
          hclosed ep _ hpvis hnc_pb
            ((hperm.2 _).mp (before_mem_right hab))
        have hepρ : ep ∈ ρ := (hperm.2 ep).mpr hepev
        have hbρ : (tb, rb, SAppOp.insA d) ∈ ρ := before_mem_right hab
        have haρ : (ta, ra, SAppOp.delA d) ∈ ρ := before_mem_left hab
        -- ep is before b
        have hepb : Before ρ ep (tb, rb, SAppOp.insA d) := by
          rcases before_trichotomy hepρ hbρ (fun he => by
            rw [hep] at he
            exact hirr _ (he ▸ hpvis)) with h | h
          · exact h
          · exact absurd (loOn_shesha_iff.mpr ⟨hpvis, hnc_pb⟩)
              (respects_before hresp h)
        -- ep is before a
        have hvis_pa : C.vis ep (ta, ra, SAppOp.delA d) :=
          honest_ins_vis_del hH hpev haev
        have hnc_pa : ¬ SheshaD.toCRDTSig.commutes ep (ta, ra, SAppOp.delA d) :=
          ncomm_ins_del_self hpa
        have hepa : Before ρ ep (ta, ra, SAppOp.delA d) := by
          rcases before_trichotomy hepρ haρ (fun he => by
            rw [hep] at he
            exact SAppOp.noConfusion
              (congrArg (fun o : Op SAppOp => o.2.2) he)) with h | h
          · exact h
          · exact absurd (loOn_shesha_iff.mpr ⟨hvis_pa, hnc_pa⟩)
              (respects_before hresp h)
        -- split ρ at b; the prefix contains ep … a with no later ins-d
        obtain ⟨αb, βb, hbsplit⟩ := List.append_of_mem hbρ
        have haαb : (ta, ra, SAppOp.delA d) ∈ αb :=
          before_split_prefix hperm.1 hab hbsplit
        have hepαb : ep ∈ αb :=
          before_split_prefix hperm.1 hepb hbsplit
        have heff := effFrom_at hW hbsplit
        have hpread : d ∈ Shesha.read
            (applySeq SheshaD.toCRDTSig SheshaD.init αb) := by
          rcases (heff : d = 0 ∨ _) with h0 | h
          · exact absurd h0 hp0
          · exact h
        -- split the prefix at the delete
        obtain ⟨γ, δ, hasplit⟩ := List.append_of_mem haαb
        have hepδ : ep ∉ δ := by
          intro hin
          refine before_asymm hperm.1 hepa ⟨γ, δ ++ (tb, rb, SAppOp.insA d) :: βb, ?_, ?_⟩
          · rw [hbsplit, hasplit, List.append_assoc, List.cons_append]
          · exact List.mem_append_left _ hin
        have hnoins : d ∉ Shesha.opInsIds (δ.map toSOp) := by
          intro hin
          obtain ⟨r'', a'', hm⟩ := opInsIds_map_toSOp hin
          have hmρ : (d, r'', SAppOp.insA a'') ∈ ρ := by
            rw [hbsplit, hasplit, List.append_assoc, List.cons_append]
            exact List.mem_append_right _ (List.mem_cons_of_mem _
              (List.mem_append_left _ hm))
          have : ((d, r'', SAppOp.insA a'') : Op SAppOp) = ep :=
            (Configuration.core C).ts_unique (hmem _ hmρ) hpev rfl
          exact hepδ (this ▸ hm)
        -- compute: d is dead at the end of the prefix
        rw [applySeq_toSOp, hasplit, List.map_append, Shesha.steps_append,
          List.map_cons,
          show Shesha.steps (Shesha.steps SheshaD.init (γ.map toSOp))
              (toSOp (ta, ra, SAppOp.delA d) :: δ.map toSOp)
            = Shesha.steps (Shesha.delete
                (Shesha.steps SheshaD.init (γ.map toSOp)) d)
                (δ.map toSOp) from rfl] at hpread
        refine Shesha.not_mem_read_steps ?_ hnoins hpread
        rw [Shesha.read_delete, Shesha.seqDel]
        intro hc
        exact absurd rfl (of_decide_eq_true (List.mem_filter.mp hc).2)

/-! ## §5c the insert phase of a witness is effective and fresh -/

/-- Along a witness's insert phase, every insert is fresh (unique ids),
nonzero (honesty), and lands at a live-or-root anchor (effectiveness,
transferred through delete postponement). Stated for every prefix split,
recursively. -/
theorem witness_effFresh_go
    (hH : SheshaHonest C)
    (hsub : ∀ a ∈ ev, a ∈ C.events)
    (hperm : listPermOf ρ ev)
    (hW : SheshaEff ρ)
    (hDB : (ρ.map toSOp).Pairwise Shesha.DelBeforeOK) :
    ∀ (ρ' α : List (Op SAppOp)), ρ = α ++ ρ' →
      Shesha.EffFreshFrom
        (Shesha.steps SheshaD.init (Shesha.insPart (α.map toSOp)))
        (Shesha.insPart (ρ'.map toSOp))
  | [], _, _ => trivial
  | ⟨t, r, op⟩ :: ρ'', α, hsplit => by
      have hmem : ∀ x, x ∈ ρ → x ∈ C.events := fun x hx =>
        hsub x ((hperm.2 x).mp hx)
      have heρ : (⟨t, r, op⟩ : Op SAppOp) ∈ ρ := by
        rw [hsplit]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      have hsplit' : ρ = (α ++ [⟨t, r, op⟩]) ++ ρ'' := by
        rw [hsplit, List.append_assoc, List.singleton_append]
      have ih := witness_effFresh_go hH hsub hperm hW hDB ρ''
        (α ++ [⟨t, r, op⟩]) hsplit'
      cases op with
      | delA d =>
          rw [List.map_cons,
            show toSOp (t, r, SAppOp.delA d) = Shesha.Op.del d from rfl,
            Shesha.insPart]
          rw [List.map_append, Shesha.insPart_append,
            show (List.map toSOp [(⟨t, r, SAppOp.delA d⟩ : Op SAppOp)])
              = [Shesha.Op.del d] from rfl,
            show Shesha.insPart [Shesha.Op.del d] = [] from rfl,
            List.append_nil] at ih
          exact ih
      | insA p =>
          rw [List.map_cons,
            show toSOp (t, r, SAppOp.insA p) = Shesha.Op.ins t p from rfl,
            Shesha.insPart]
          rw [List.map_append, Shesha.insPart_append,
            show (List.map toSOp [(⟨t, r, SAppOp.insA p⟩ : Op SAppOp)])
              = [Shesha.Op.ins t p] from rfl,
            show Shesha.insPart [Shesha.Op.ins t p]
              = [Shesha.Op.ins t p] from rfl,
            Shesha.steps_append,
            show Shesha.steps
                (Shesha.steps SheshaD.init (Shesha.insPart (α.map toSOp)))
                [Shesha.Op.ins t p]
              = Shesha.insert
                  (Shesha.steps SheshaD.init (Shesha.insPart (α.map toSOp)))
                  t p from rfl] at ih
          refine ⟨?_, ?_, ?_, ih⟩
          · -- freshness: t was not inserted in the prefix
            intro hc
            rcases Shesha.mem_read_steps _ _ hc with h' | h'
            · exact absurd h' List.not_mem_nil
            · rw [Shesha.opInsIds_insPart] at h'
              obtain ⟨r'', a'', hm⟩ := opInsIds_map_toSOp h'
              have hmρ : (t, r'', SAppOp.insA a'') ∈ ρ := by
                rw [hsplit]
                exact List.mem_append_left _ hm
              have heq : ((t, r'', SAppOp.insA a'') : Op SAppOp)
                  = (t, r, SAppOp.insA p) :=
                (Configuration.core C).ts_unique (hmem _ hmρ) (hmem _ heρ) rfl
              have hnd := hperm.1
              rw [hsplit, List.nodup_append] at hnd
              exact hnd.2.2 _ (heq ▸ hm) _ (List.mem_cons_self ..) rfl
          · exact honest_ins_nonzero hH (hmem _ heρ)
          · -- the anchor is live-or-root, through delete postponement
            rcases (effFrom_at hW hsplit : p = 0 ∨ _) with h0 | hlive
            · exact Or.inl h0
            · refine Or.inr ?_
              rw [applySeq_toSOp,
                Shesha.steps_normal_form (α.map toSOp) ([] : Shesha.St)
                  (List.Pairwise.sublist
                    (List.Sublist.map toSOp
                      (hsplit ▸ List.sublist_append_left α _)) hDB),
                Shesha.read_dropF, List.mem_filter] at hlive
              exact hlive.1

end WitnessNF

/-! ## §5d the witness normal form -/

/-- Some insert event of id `x` anchored at `p` lies in `ev`. -/
def InsIn (ev : Set (Op SAppOp)) (x p : Nat) : Prop :=
  ∃ r, (x, r, SAppOp.insA p) ∈ ev

/-- Some delete event targeting `u` lies in `ev`. -/
def DelIn (ev : Set (Op SAppOp)) (u : Nat) : Prop :=
  ∃ t r, (t, r, SAppOp.delA u) ∈ ev

open Classical in
/-- **The witness normal form**: the fold of any honest, `loOn`-respecting,
effective enumeration of `ev` is the delete-collapse (`dropF`) of the
**anchored forest** of `ev`'s inserts — a WF forest whose rows are exactly
the same-anchor inserts, ordered against visibility (newer left). Every
slot of the join hook is analysed through this. -/
theorem witness_nf {C : Configuration SheshaD}
    {ev : Set (Op SAppOp)} {ρ : List (Op SAppOp)}
    (hH : SheshaHonest C)
    (hirr : ∀ a : Op SAppOp, ¬ C.vis a a)
    (hsub : ∀ a ∈ ev, a ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev → a ∈ ev)
    (hperm : listPermOf ρ ev)
    (hresp : respects ρ (loOn (Configuration.core C) ev))
    (hW : SheshaEff ρ) :
    ∃ T : Shesha.St,
      Shesha.WF T
      ∧ (∀ u, u ∈ Shesha.read T ↔ ∃ p, InsIn ev u p)
      ∧ (∀ p x, x ∈ Shesha.row T p ↔ InsIn ev x p)
      ∧ (∀ p x y rx ry, (x, rx, SAppOp.insA p) ∈ ev →
          (y, ry, SAppOp.insA p) ∈ ev →
          Shesha.precedes (Shesha.row T p) x y →
          ¬ C.vis (x, rx, SAppOp.insA p) (y, ry, SAppOp.insA p))
      ∧ applySeq SheshaD.toCRDTSig SheshaD.init ρ
          = Shesha.dropF (fun u => decide (DelIn ev u)) T
      ∧ (∀ p, Shesha.row T p
          = (Shesha.anchIds (ρ.map toSOp) p).reverse) := by
  have hDB := witness_delBeforeOK hH hirr hsub hclosed hperm hresp hW
  have hEF : Shesha.EffFreshFrom ([] : Shesha.St)
      (Shesha.insPart (ρ.map toSOp)) :=
    witness_effFresh_go hH hsub hperm hW hDB ρ [] rfl
  have hwf0 : Shesha.WF ([] : Shesha.St) := ⟨List.nodup_nil, List.not_mem_nil⟩
  have hAI := Shesha.allIns_insPart (ρ.map toSOp)
  set T := Shesha.steps ([] : Shesha.St) (Shesha.insPart (ρ.map toSOp))
    with hT
  have hWFT : Shesha.WF T := Shesha.wf_steps_ins _ _ hwf0 hAI hEF
  have hrow0 : ∀ p, Shesha.row ([] : Shesha.St) p = [] := by
    intro p
    rw [Shesha.row]
    by_cases hp : p = 0
    · rw [if_pos hp]
      rfl
    · rw [if_neg hp]
      rfl
  have hrowT : ∀ p, Shesha.row T p
      = (Shesha.anchIds (ρ.map toSOp) p).reverse := by
    intro p
    rw [hT, Shesha.row_steps_ins _ _ hwf0 hAI hEF p, hrow0,
      List.append_nil, Shesha.anchIds_insPart]
  have hmemev : ∀ x, x ∈ ρ ↔ x ∈ ev := hperm.2
  refine ⟨T, hWFT, ?_, ?_, ?_, ?_, hrowT⟩
  · -- live set = inserted ids
    intro u
    rw [hT]
    constructor
    · intro h
      rcases Shesha.mem_read_steps _ _ h with h' | h'
      · exact absurd h' List.not_mem_nil
      · rw [Shesha.opInsIds_insPart] at h'
        obtain ⟨r, a, hm⟩ := opInsIds_map_toSOp h'
        exact ⟨a, r, (hmemev _).mp hm⟩
    · rintro ⟨p, r, hm⟩
      exact (Shesha.read_steps_ins _ _ hAI hEF u).mpr
        (Or.inr (by
          rw [Shesha.opInsIds_insPart]
          exact mem_opInsIds_of_mem ((hmemev _).mpr hm)))
  · -- rows = same-anchor inserts
    intro p x
    rw [hrowT, List.mem_reverse]
    constructor
    · intro h
      obtain ⟨r, hm⟩ := anchIds_map_toSOp h
      exact ⟨r, (hmemev _).mp hm⟩
    · rintro ⟨r, hm⟩
      exact mem_anchIds_of_mem ((hmemev _).mpr hm)
  · -- row order: newer (vis-later) strictly left
    intro p x y rx ry hxev hyev hprec
    rw [hrowT] at hprec
    have hyx : List.Sublist [y, x] (Shesha.anchIds (ρ.map toSOp) p) := by
      have h2 := List.Sublist.reverse hprec
      rw [List.reverse_reverse] at h2
      exact h2
    have hnd : (Shesha.anchIds (ρ.map toSOp) p).Nodup := by
      have := Shesha.row_nodup hWFT p
      rw [hrowT] at this
      exact (List.nodup_reverse).mp this
    have hxy : x ≠ y := (sublist2_nodup_ne hyx hnd).symm
    obtain ⟨ry', rx', hbefore⟩ := anchIds_sublist2_before hyx
    have hyρ : (y, ry', SAppOp.insA p) ∈ ρ := before_mem_left hbefore
    have hxρ : (x, rx', SAppOp.insA p) ∈ ρ := before_mem_right hbefore
    have hxeq : ((x, rx', SAppOp.insA p) : Op SAppOp)
        = (x, rx, SAppOp.insA p) :=
      (Configuration.core C).ts_unique
        (hsub _ ((hmemev _).mp hxρ)) (hsub _ hxev) rfl
    have hyeq : ((y, ry', SAppOp.insA p) : Op SAppOp)
        = (y, ry, SAppOp.insA p) :=
      (Configuration.core C).ts_unique
        (hsub _ ((hmemev _).mp hyρ)) (hsub _ hyev) rfl
    intro hv
    refine respects_before hresp hbefore ?_
    rw [hxeq, hyeq]
    exact loOn_shesha_iff.mpr ⟨hv,
      ncomm_ins_ins_same_anchor hxy
        (honest_ins_ne_anchor hH (hsub _ hxev))
        (honest_ins_ne_anchor hH (hsub _ hyev))⟩
  · -- the fold is the delete-collapse of the anchored forest
    rw [applySeq_toSOp,
      Shesha.steps_normal_form (ρ.map toSOp) SheshaD.init hDB]
    refine Shesha.dropF_congr (fun u => ?_) _
    by_cases hd : DelIn ev u
    · rw [decide_eq_true hd]
      obtain ⟨t, r, hm⟩ := hd
      exact List.contains_iff_mem.mpr
        (mem_opDelIds_of_mem ((hmemev _).mpr hm))
    · rw [decide_eq_false hd]
      rcases hc : (Shesha.opDelIds (ρ.map toSOp)).contains u with _ | _
      · rfl
      · obtain ⟨t, r, hm⟩ :=
          opDelIds_map_toSOp (List.contains_iff_mem.mp hc)
        exact absurd ⟨t, r, (hmemev _).mp hm⟩ hd

end Sal.ConditionedMRDTs
