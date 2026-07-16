import Mathlib.Data.List.Basic
import Sal.Interfaces.Map_Extended
import Sal.MRDTs.RGA_Embed.Embed_Code

/-!
# The embedded-chain RGA (`embed-code`) — MRDT kernel

Design and pen-and-paper proofs: `whiteboard/embed-code-design.pdf`;
Python-validated artifact: `whiteboard/litmus/embed_tree.py` (battery clean
except one-sided L19; DAG PBT 120/120 and 300/300; lockstep read-equal with
the published tombstoned RGA 120/120).

This is the **absolute-coordinate model**: the state stores each live id's
full coordinate — the concatenation of prefix-free codewords along its birth
chain — as an immutable value. Compare `Sal/MRDTs/RGA_Rehoming/RGA_Tombstone_Free_MRDT.lean`
(the proved flat RGA), whose state stores mutable anchors and whose proofs
need resolve/rehome/climb algebra. Here:

* `Del` carries **no path** and rehomes **nothing** — deletion is domain
  removal, because coordinates are absolute (the isometric fold of the
  design's parent-relative runtime is the identity on absolutes).
* `merge` never climbs: survivorship is the OR-set formula and values are
  immutable, so the value function just reads any input that has the id.
* `Ins` carries the anchor's coordinate as a **prefix `π` — for the proof,
  and the proof alone** (design doc §3): `do_` computes the newcomer's
  coordinate from `π` and the two timestamps, never reading the state, which
  makes every operation pair commute **to states equal under `eq`,
  unconditionally enough that `rc = Either` discharges without path algebra**.
  On honest states `π` is exactly the anchor's stored coordinate
  (`accurate`), and `ins_prefix_ghost` proves the runtime that reads the
  state instead executes the same transition — the `ins_path_free` analogue,
  direction flipped.

The read side (display = chain-lex; L1 delete-order as a SPOT theorem;
non-interleaving; RGA† read-equivalence) is the next layer — see `PLAN.md`.
-/

namespace Sal.EmbedRGA

/-- A coordinate: the birth chain, arithmetized as a bit string. -/
abbrev coord := List Bool

/-- State: `id ↦ (element, absolute coordinate)`. Live nodes only; values are
immutable once written (coordinates are birth constants — design doc Thm 2). -/
abbrev concrete_st (α : Type := ℕ) := map ℕ (α × coord)

variable {α : Type} [DecidableEq α]

@[simp] def el (s : concrete_st α) (t : ℕ) : α := (sel s t).1
@[simp] def pos (s : concrete_st α) (t : ℕ) : coord := (sel s t).2

@[simp] def init_st (α : Type := ℕ) [Inhabited α] : concrete_st α :=
  const_on empty (default, [])

/-- Operations.
* `Ins e π a`: insert element `e` after anchor `a`, carrying `a`'s coordinate
  `π` (the proof-only prefix; `[]` for the root).
* `Del x`: delete `x`. No path — nothing is rehomed. -/
inductive app_op_t (α : Type := ℕ) : Type where
  | Ins : α → coord → ℕ → app_op_t α
  | Del : ℕ → app_op_t α
  deriving DecidableEq

/-- `(timestamp, replica-id, op)`. -/
abbrev op_t (α : Type := ℕ) := ℕ × ℕ × app_op_t α

@[simp] def distinct_ops (op1 op2 : op_t α) := Prod.fst op1 != Prod.fst op2
@[simp] def get_rid (o : op_t α) := match o with | (_, (rid, _)) => rid

/-- The mint: the newcomer's coordinate is its anchor's coordinate extended by
the codeword of the timestamp delta. State-independent by construction. -/
@[simp] def mint (Γ : OrderedPrefixCode) (π : coord) (t a : ℕ) : coord :=
  π ++ Γ.enc (t - a)

/-- Effect. `Ins` writes a record whose value is computed from the op alone;
`Del` removes the id. Neither reads any other record. -/
@[simp] def do_ (Γ : OrderedPrefixCode) (s : concrete_st α) (o : op_t α) :
    concrete_st α :=
  match o with
  | (t, _, .Ins e π a) => upd s t (e, mint Γ π t a)
  | (_, _, .Del x)     => del s x

/-- Conflict-resolution table: `Either` everywhere (design doc §3 — any
oriented ins/del entry awakens the machine-refuted `cond_comm_base`). -/
inductive rc_res : Type where
  | Fst_then_snd : rc_res
  | Snd_then_fst : rc_res
  | Either       : rc_res
  deriving DecidableEq

@[simp] def rc (_o1 _o2 : op_t α) : rc_res := rc_res.Either

@[simp] def eq (a b : concrete_st α) : Prop :=
  ∀ k, (contains a k = contains b k) ∧ (contains a k → sel a k = sel b k)

omit [DecidableEq α] in
theorem eq_symm (a b : concrete_st α) : eq a b → eq b a := by
  intro h k
  obtain ⟨hc, hs⟩ := h k
  exact ⟨hc.symm, fun hk => (hs (hc ▸ hk)).symm⟩

/-- Three-way merge: OR-set survival on identities; the value function reads
any input holding the id (values are immutable, so the priority order is
immaterial on coherent inputs — `merge_comm`). No climb: coordinates are
absolute. -/
@[simp] def merge (l a b : concrete_st α) : concrete_st α :=
  let dl := domain l
  let da := domain a
  let db := domain b
  let I : set ℕ := union (intersection (intersection dl da) db)
                         (union (difference da dl) (difference db dl))
  map.mk (fun t =>
    if contains l t then sel l t else if contains a t then sel a t else sel b t) I

/-! ## Honesty predicates (mirroring the proved flat RGA's shape) -/

/-- The op's claims are true in `s`: an `Ins`'s prefix is its anchor's stored
coordinate (or the anchor is the root and the prefix empty), and the delta is
positive (causality — the anchor was seen before the insert); a `Del`'s
target is live. -/
@[simp] def accurate (o : op_t α) (s : concrete_st α) : Prop :=
  match o with
  | (t, _, .Ins _ π a) =>
      a < t ∧ ((a = 0 ∧ π = []) ∨ (contains s a = true ∧ π = pos s a))
  | (_, _, .Del x)     => contains s x = true

/-- An `Ins` uses a fresh, nonzero timestamp; `Del` creates nothing. -/
@[simp] def fresh_ts (o : op_t α) (s : concrete_st α) : Prop :=
  match o with
  | (t, _, .Ins _ _ _) => t ≠ 0 ∧ contains s t = false
  | (_, _, .Del _)     => True

/-! ## The ghost lemma: the prefix is for the proof alone

A runtime whose anchors are live (every honest generation site) may read the
anchor's coordinate from the state and drop `π` from the wire: on accurate
ops the two transition functions are literally the same. -/

/-- The state-reading insert — what an implementation actually executes. -/
@[simp] def do_run (Γ : OrderedPrefixCode) (s : concrete_st α) (o : op_t α) :
    concrete_st α :=
  match o with
  | (t, _, .Ins e _ a) =>
      upd s t (e, mint Γ (if a = 0 then [] else pos s a) t a)
  | (_, _, .Del x)     => del s x

omit [DecidableEq α] in
theorem ins_prefix_ghost (Γ : OrderedPrefixCode) (s : concrete_st α)
    (o : op_t α) (h0 : contains s 0 = false) (hacc : accurate o s) :
    do_ Γ s o = do_run Γ s o := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Del x => rfl
  | Ins e π a =>
      simp only [accurate] at hacc
      obtain ⟨-, h⟩ := hacc
      rcases h with ⟨ha, hπ⟩ | ⟨ha, hπ⟩
      · simp [do_, do_run, ha, hπ]
      · have ha0 : a ≠ 0 := by
          intro hz
          rw [hz] at ha
          rw [ha] at h0
          exact Bool.noConfusion h0
        simp [do_, do_run, hπ, ha0]

/-! ## Commutation kernel

Every pair commutes. `Ins` values are state-independent, so the proofs are
pure map/set algebra — no resolve, no rehome, no path induction. The only
hypothesis with content: a `Del`'s live target is never a fresh `Ins`'s
timestamp (`accurate` + `fresh_ts`), which rules out the ins-then-delete-it
shape that is causally impossible. -/

omit [DecidableEq α] in
theorem insins_comm (Γ : OrderedPrefixCode) (s : concrete_st α)
    (t1 r1 : ℕ) (e1 : α) (π1 : coord) (a1 : ℕ)
    (t2 r2 : ℕ) (e2 : α) (π2 : coord) (a2 : ℕ)
    (hdist : t1 ≠ t2) :
    eq (do_ Γ (do_ Γ s (t1, r1, .Ins e1 π1 a1)) (t2, r2, .Ins e2 π2 a2))
       (do_ Γ (do_ Γ s (t2, r2, .Ins e2 π2 a2)) (t1, r1, .Ins e1 π1 a1)) := by
  intro k
  constructor
  · simp only [do_, upd, contains, mem]
    grind
  · intro _
    simp only [do_, upd, sel]
    grind

omit [DecidableEq α] in
theorem insdel_comm (Γ : OrderedPrefixCode) (s : concrete_st α)
    (t1 r1 : ℕ) (e1 : α) (π1 : coord) (a1 : ℕ)
    (t2 r2 x2 : ℕ)
    (hne : t1 ≠ x2) :
    eq (do_ Γ (do_ Γ s (t1, r1, .Ins e1 π1 a1)) (t2, r2, .Del x2))
       (do_ Γ (do_ Γ s (t2, r2, .Del x2)) (t1, r1, .Ins e1 π1 a1)) := by
  intro k
  constructor
  · simp only [do_, upd, del, contains, domain, mem]
    grind
  · intro _
    simp only [do_, upd, del, sel]

omit [DecidableEq α] in
theorem deldel_comm (Γ : OrderedPrefixCode) (s : concrete_st α)
    (t1 r1 x1 t2 r2 x2 : ℕ) :
    eq (do_ Γ (do_ Γ s (t1, r1, .Del x1)) (t2, r2, .Del x2))
       (do_ Γ (do_ Γ s (t2, r2, .Del x2)) (t1, r1, .Del x1)) := by
  intro k
  constructor
  · simp only [do_, del, contains, domain, mem]
    grind
  · intro _
    simp only [do_, del, sel]

/-- Reachability-conditioned commutation, the flat RGA's shape: `0` is never a
stored key, both ops' claims are true, both timestamps fresh. -/
@[simp] def commutes_with' (Γ : OrderedPrefixCode) (o1 o2 : op_t α) : Prop :=
  ∀ s, contains s 0 = false → accurate o1 s → accurate o2 s →
       fresh_ts o1 s → fresh_ts o2 s →
       eq (do_ Γ (do_ Γ s o1) o2) (do_ Γ (do_ Γ s o2) o1)

omit [DecidableEq α] in
/-- `rc = Either` is honest: every distinct pair commutes on honest states. -/
theorem rc_non_comm' (Γ : OrderedPrefixCode) (o1 o2 : op_t α) :
    (distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2)
    → (rc o1 o2 = rc_res.Either ↔ commutes_with' Γ o1 o2) := by
  rintro ⟨hdist, _hrid⟩
  refine ⟨fun _ => ?_, fun _ => rfl⟩
  intro s _h0 ha1 ha2 hf1 hf2
  simp only [distinct_ops, bne_iff_ne, ne_eq] at hdist
  obtain ⟨t1, r1, op1⟩ := o1
  obtain ⟨t2, r2, op2⟩ := o2
  cases op1 with
  | Ins e1 π1 a1 =>
    cases op2 with
    | Ins e2 π2 a2 => exact insins_comm Γ s t1 r1 e1 π1 a1 t2 r2 e2 π2 a2 hdist
    | Del x2 =>
        -- t1 fresh (∉ s), x2 live (∈ s) ⟹ t1 ≠ x2
        have hne : t1 ≠ x2 := by
          intro hxy
          simp only [fresh_ts] at hf1
          simp only [accurate] at ha2
          rw [hxy] at hf1
          rw [ha2] at hf1
          exact Bool.noConfusion hf1.2
        exact insdel_comm Γ s t1 r1 e1 π1 a1 t2 r2 x2 hne
  | Del x1 =>
    cases op2 with
    | Ins e2 π2 a2 =>
        have hne : t2 ≠ x1 := by
          intro hxy
          simp only [fresh_ts] at hf2
          simp only [accurate] at ha1
          rw [hxy] at hf2
          rw [ha1] at hf2
          exact Bool.noConfusion hf2.2
        exact eq_symm _ _ (insdel_comm Γ s t2 r2 e2 π2 a2 t1 r1 x1 hne)
    | Del x2 => exact deldel_comm Γ s t1 r1 x1 t2 r2 x2

/-! ## Merge algebra -/

/-- Two states agree on every id they share — the immutability invariant on
reachable configurations (coordinates are birth constants). -/
@[simp] def coherent2 (a b : concrete_st α) : Prop :=
  ∀ t, contains a t → contains b t → sel a t = sel b t

omit [DecidableEq α] in
theorem merge_idem (s : concrete_st α) : eq (merge s s s) s := by
  intro k
  constructor
  · simp only [merge, contains, domain, mem]
    grind
  · intro hk
    simp only [merge, contains, domain, mem] at hk ⊢
    simp only [sel]
    grind

/-- The value an op writes — a function of the op alone (never the state).
`Del` writes nothing. -/
@[simp] def opVal (Γ : OrderedPrefixCode) (o : op_t α) : Option (ℕ × (α × coord)) :=
  match o with
  | (t, _, .Ins e π a) => some (t, (e, mint Γ π t a))
  | (_, _, .Del _)     => none

/-- `o` is coherent with a bystander state `s'`: if `s'` already holds the id
`o` writes, it holds the same value — true in any execution, since a shared id
means `s'` applied the same `Ins` (ids are unique), whose value is a function
of the op. -/
@[simp] def opCoherent (Γ : OrderedPrefixCode) (o : op_t α) (s' : concrete_st α) : Prop :=
  match opVal Γ o with
  | some (t, v) => contains s' t → sel s' t = v
  | none        => True

omit [DecidableEq α] in
/-- Applying an op preserves coherence with any bystander it is coherent with:
the immutability invariant is closed under `do_`. -/
theorem do_coherent (Γ : OrderedPrefixCode) (s s' : concrete_st α) (o : op_t α)
    (hco : coherent2 s s') (hop : opCoherent Γ o s') :
    coherent2 (do_ Γ s o) s' := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Del x =>
      intro k hk hk'
      refine hco k ?_ hk'
      simp only [do_, del, contains, domain, mem] at hk ⊢
      grind
  | Ins e π a =>
      intro k hk hk'
      simp only [opCoherent, opVal] at hop
      by_cases hkt : k = t
      · subst hkt
        simp only [do_, upd, sel]
        simp only [contains] at hk'
        rw [(hop hk').symm]
        simp
      · simp only [do_, upd, sel, contains, mem] at hk ⊢
        rw [if_neg hkt]
        refine hco k ?_ hk'
        simp only [contains]
        grind

omit [DecidableEq α] in
/-- Merging preserves coherence with any bystander coherent with all three
inputs: merge values are read from the inputs, never invented. -/
theorem merge_coherent (l a b s' : concrete_st α)
    (hl : coherent2 l s') (ha : coherent2 a s') (hb : coherent2 b s') :
    coherent2 (merge l a b) s' := by
  intro k hk hk'
  simp only [merge, contains, domain, mem] at hk
  simp only [merge, sel]
  by_cases hkl : contains l k
  · rw [if_pos hkl]; exact hl k hkl hk'
  · rw [if_neg hkl]
    by_cases hka : contains a k
    · rw [if_pos hka]; exact ha k hka hk'
    · rw [if_neg hka]
      refine hb k ?_ hk'
      simp only [contains] at hkl hka ⊢
      grind

omit [DecidableEq α] in
/-- Branch symmetry, on coherent inputs. -/
theorem merge_comm (l a b : concrete_st α)
    (hab : coherent2 a b) :
    eq (merge l a b) (merge l b a) := by
  intro k
  constructor
  · simp only [merge, contains, domain, mem]
    grind
  · intro hk
    simp only [merge, contains, domain, mem] at hk
    simp only [merge, sel]
    have := hab k
    simp only [contains, sel] at this
    grind

end Sal.EmbedRGA
