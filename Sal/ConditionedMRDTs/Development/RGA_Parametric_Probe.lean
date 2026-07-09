import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide

import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal

open Classical

/-!
# PROBE: is the tombstone-free RGA payload-parametric?

This file transcribes the CORE datatype + convergence spine of
`Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean` with the element
type generalized from `ℕ` to an arbitrary `α`.  The state becomes
`concrete_st α := map ℕ (α × ℕ)` (`id ↦ (element, anchor)`); ids and anchors
stay `ℕ`.

The proofs below are COPIED VERBATIM from the concrete file (only element-type
annotations changed).  If they go through, the element is opaque and the RGA is
payload-parametric.  The only typeclasses used:

* `[DecidableEq α]` — for `deriving DecidableEq` on `app_op_t α`.
* `[Inhabited α]`   — ONLY to construct `init_st` (a dead default: the element
  at the empty domain is never read).  Everything else is `DecidableEq`-only.

The concrete file's `#eval`/`native_decide` demo theorems (`trio_converges`,
`prefix_converges`, …) are DELETED here: they are ℕ-pinned illustrations, not
part of the convergence proof, and `native_decide` cannot run at an opaque `α`.
-/

section
variable {α : Type} [DecidableEq α]

/-- State generalized: `id ↦ (element : α, immediate-anchor : ℕ)`. -/
abbrev concrete_st (α : Type) := map ℕ (α × ℕ)

@[simp] def el (s : concrete_st α) (t : ℕ) : α := (sel s t).1
@[simp] def anc (s : concrete_st α) (t : ℕ) : ℕ := (sel s t).2

@[simp] def init_st [Inhabited α] : concrete_st α := const_on empty (default, 0)

@[simp] def resolve (s : concrete_st α) : List ℕ → ℕ
  | []        => 0
  | c :: rest => if contains s c then c else resolve s rest

end

/-- Operations. `Ins` now carries an `α` element. `deriving DecidableEq`
generates `[DecidableEq α] → DecidableEq (app_op_t α)`. -/
inductive app_op_t (α : Type) : Type where
| Ins : α → List ℕ → ℕ → app_op_t α      -- element, prefix, anchor
| Del : List ℕ → ℕ → app_op_t α          -- prefix, target
deriving DecidableEq

abbrev op_t (α : Type) := ℕ × ℕ × app_op_t α

section
variable {α : Type} [DecidableEq α]

@[simp] def distinct_ops (op1 op2 : op_t α) := Prod.fst op1 != Prod.fst op2
@[simp] def get_rid (o : op_t α) := match o with | (_, (rid, _)) => rid

@[simp] def opLeaf : app_op_t α → ℕ | .Ins _ _ a => a | .Del _ x => x
@[simp] def opPath : app_op_t α → List ℕ | .Ins _ p _ => p | .Del p _ => p

@[simp] def do_ (s : concrete_st α) (o : op_t α) : concrete_st α :=
  match o with
  | (t, _, .Ins e pre a) => upd s t (e, resolve s (a :: pre))
  | (_, _, .Del pre x)   =>
      let tgt := resolve s pre
      del (iter_upd (fun _ ea => if ea.2 = x then (ea.1, tgt) else ea) s) x

def climb_aux (ancL : ℕ → ℕ) (I : set ℕ) : ℕ → ℕ → ℕ
  | 0,        x => x
  | (fuel+1), x => if x = 0 || I x then x else climb_aux ancL I fuel (ancL x)

@[simp] def climb (ancL : ℕ → ℕ) (I : set ℕ) (x : ℕ) : ℕ := climb_aux ancL I x x

@[simp] def merge (l a b : concrete_st α) : concrete_st α :=
  let dl := domain l
  let da := domain a
  let db := domain b
  let I : set ℕ := union (intersection (intersection dl da) db)
                         (union (difference da dl) (difference db dl))
  let ancL : ℕ → ℕ := fun y => anc l y
  let elf : ℕ → α := fun t =>
    if contains l t then el l t else if contains a t then el a t else el b t
  let betaf : ℕ → ℕ := fun t =>
    if contains l t then anc l t else if contains a t then anc a t else anc b t
  map.mk (fun t => (elf t, climb ancL I (betaf t))) I

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either
deriving DecidableEq

@[simp] def rc (_o1 _o2 : op_t α) : rc_res := rc_res.Either

@[simp] def eq (a b : concrete_st α) : Prop :=
  ∀ k, (contains a k = contains b k) ∧ (contains a k → sel a k = sel b k)

/-! ## Verification -/

set_option maxHeartbeats 1000000

theorem cond_comm_base (s : concrete_st α) (o1 o2 o3 : op_t α) :
    (distinct_ops o1 o2 ∧ distinct_ops o2 o3 ∧ distinct_ops o1 o3
      ∧ rc o1 o2 = rc_res.Fst_then_snd ∧ ¬(rc o2 o3 = rc_res.Either))
    → eq (do_ (do_ (do_ s o1) o2) o3) (do_ (do_ (do_ s o2) o1) o3) := by
  intro h; simp [rc] at h

theorem no_rc_chain (o1 o2 o3 : op_t α) :
    (distinct_ops o1 o2 ∧ distinct_ops o2 o3)
    → ¬(rc o1 o2 = rc_res.Fst_then_snd ∧ rc o2 o3 = rc_res.Fst_then_snd) := by
  intro _; simp [rc]

theorem ins_path_free (s : concrete_st α) (t r : ℕ) (e : α) (a : ℕ) (pre : List ℕ)
    (h : contains s a = true) :
    do_ s (t, r, .Ins e pre a) = upd s t (e, a) := by
  have hr : resolve s (a :: pre) = a := by simp only [resolve, h, if_true]
  simp only [do_, hr]

theorem climb_fixpoint (ancL : ℕ → ℕ) (I : set ℕ) (x : ℕ)
    (h : x = 0 ∨ I x = true) : climb ancL I x = x := by
  unfold climb
  cases x with
  | zero => rfl
  | succ n =>
    unfold climb_aux
    have : I (n + 1) = true := by rcases h with h | h <;> simp_all
    simp [this]

@[simp] def wf (s : concrete_st α) : Prop :=
  ∀ t, contains s t → (anc s t = 0 ∨ contains s (anc s t))

theorem merge_idem (s : concrete_st α) (hwf : wf s) : eq (merge s s s) s := by
  intro k
  constructor
  · simp only [merge, contains, domain, mem]
    grind
  · intro hk
    have hcontain : contains s k = true := by
      simpa [merge, contains, domain, mem] using hk
    have hres : anc s k = 0 ∨ contains s (anc s k) = true := hwf k hcontain
    simp only [merge, sel, el, anc, contains, domain, mem] at hcontain ⊢
    simp only [hcontain, if_true]
    rw [climb_fixpoint (fun y => (s.mappings y).2)
          (union (intersection (intersection s.domain s.domain) s.domain)
                 (union (difference s.domain s.domain) (difference s.domain s.domain)))
          ((s.mappings k).2)
          (by
            rcases hres with h | h
            · left; simpa [anc, sel] using h
            · right
              simp only [union, intersection, difference, contains, mem, anc, sel] at h ⊢
              grind)]

/-! ## Reachability predicates -/

@[simp] def IsAncPath (s : concrete_st α) : ℕ → List ℕ → Prop
  | leaf, []      => anc s leaf = 0
  | leaf, p :: ps => anc s leaf = p ∧ contains s p = true ∧ IsAncPath s p ps

@[simp] def accurate (o : op_t α) (s : concrete_st α) : Prop :=
  (opLeaf o.2.2 = 0 ∧ opPath o.2.2 = []) ∨
  (contains s (opLeaf o.2.2) = true ∧ IsAncPath s (opLeaf o.2.2) (opPath o.2.2))

@[simp] def fresh_ts (o : op_t α) (s : concrete_st α) : Prop :=
  match o with
  | (t, _, .Ins _ _ _) => t ≠ 0 ∧ contains s t = false
  | (_, _, .Del _ _)   => True

@[simp] def commutes_with' (o1 o2 : op_t α) : Prop :=
  ∀ s, contains s 0 = false → accurate o1 s → accurate o2 s →
       fresh_ts o1 s → fresh_ts o2 s →
       eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

/-! ## Group A: resolve algebra -/

theorem resolve_dom_eq (s1 s2 : concrete_st α) :
    ∀ cands : List ℕ, (∀ c ∈ cands, contains s1 c = contains s2 c) →
      resolve s1 cands = resolve s2 cands := by
  intro cands
  induction cands with
  | nil => intro _; rfl
  | cons c rest ih =>
    intro h
    have hc : contains s1 c = contains s2 c := h c (by simp)
    have hrest : ∀ x ∈ rest, contains s1 x = contains s2 x :=
      fun x hx => h x (by simp [hx])
    simp only [resolve, hc]
    cases hcc : contains s2 c with
    | true  => simp
    | false => simp; exact ih hrest

theorem resolve_upd_notMem (s : concrete_st α) (t : ℕ) (v : α × ℕ)
    (cands : List ℕ) (ht : t ∉ cands) :
    resolve (upd s t v) cands = resolve s cands := by
  apply resolve_dom_eq
  intro c hc
  have : c ≠ t := fun e => ht (e ▸ hc)
  simp [contains, upd, mem, union, _root_.singleton]
  grind

theorem upd_comm (s : concrete_st α) (t1 t2 : ℕ) (v w : α × ℕ) (h : t1 ≠ t2) :
    upd (upd s t1 v) t2 w = upd (upd s t2 w) t1 v := by
  apply (map_lemma_equal_elim _ _).mp
  constructor
  · funext x; by_cases e1 : x = t1 <;> by_cases e2 : x = t2 <;> simp_all [upd]
  · intro x; simp only [upd, union, _root_.singleton]; grind

/-! ## Group B: eq plumbing -/

theorem eq_symm (a b : concrete_st α) : eq a b → eq b a := by
  intro h k
  obtain ⟨hc, hs⟩ := h k
  refine ⟨hc.symm, ?_⟩
  intro hb; exact (hs (hc ▸ hb)).symm

/-! ## resolve / IsAncPath facts -/

theorem resolve_cons_eq (s' : concrete_st α) (a : ℕ) (p : List ℕ)
    (h : (a = 0 ∧ p = [] ∧ contains s' 0 = false) ∨ contains s' a = true) :
    resolve s' (a :: p) = a := by
  rcases h with ⟨ha, hp, h0⟩ | hc
  · subst ha; subst hp; simp only [resolve]; split <;> rfl
  · simp only [resolve]; rw [if_pos hc]

theorem resolve_dead_head (s' : concrete_st α) (a : ℕ) (p : List ℕ)
    (h : contains s' a = false) : resolve s' (a :: p) = resolve s' p := by
  simp only [resolve]; rw [if_neg (by rw [h]; simp)]

theorem resolve_live_head (s' : concrete_st α) (a : ℕ) (p : List ℕ)
    (h : contains s' a = true) : resolve s' (a :: p) = a := by
  simp only [resolve]; rw [if_pos h]

theorem isAncPath_resolve (s : concrete_st α) :
    ∀ (y : ℕ) (p : List ℕ), IsAncPath s y p → resolve s p = anc s y := by
  intro y p
  cases p with
  | nil => intro h; simp only [IsAncPath] at h; simp only [resolve]; exact h.symm
  | cons c cs =>
    intro h
    simp only [IsAncPath] at h
    obtain ⟨h1, h2, _⟩ := h
    rw [show anc s y = c from h1]
    simp only [resolve]
    rw [if_pos h2]

theorem isAncPath_self (s : concrete_st α) :
    ∀ (p : List ℕ) (y : ℕ), IsAncPath s y p → anc s y = y → y = 0 := by
  intro p
  induction p with
  | nil => intro y h he; simp only [IsAncPath] at h; rw [he] at h; exact h
  | cons c cs ih =>
    intro y h he
    simp only [IsAncPath] at h
    obtain ⟨h1, _, h3⟩ := h
    have : c = y := by rw [← h1]; exact he
    subst this
    exact ih c h3 he

theorem isAncPath_mem (s : concrete_st α) :
    ∀ (y : ℕ) (p : List ℕ), IsAncPath s y p → ∀ c ∈ p, contains s c = true := by
  intro y p
  induction p generalizing y with
  | nil => intro _ c hc; simp at hc
  | cons d ds ih =>
    intro h c hc
    simp only [IsAncPath] at h
    obtain ⟨_, h2, h3⟩ := h
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact h2
    · exact ih d h3 c hc'

theorem contains_ne_zero (s : concrete_st α) (k : ℕ) (h0 : contains s 0 = false)
    (h : contains s k = true) : k ≠ 0 := by
  intro e; rw [e, h0] at h; exact absurd h (by simp)

/-! ## Del state algebra -/

theorem contains_doDel (s : concrete_st α) (t r x : ℕ) (pre : List ℕ) (k : ℕ) :
    contains (do_ s (t, r, .Del pre x)) k = (contains s k && k != x) := by
  simp only [do_, del, iter_upd, contains, domain, remove, mem]
  grind

theorem sel_doDel (s : concrete_st α) (t r x : ℕ) (pre : List ℕ) (k : ℕ) :
    sel (do_ s (t, r, .Del pre x)) k
      = (if anc s k = x then (el s k, resolve s pre) else sel s k) := by
  simp only [do_, del, iter_upd, sel, el, anc]

theorem del_path_free (s : concrete_st α) (t r x : ℕ) (pre : List ℕ)
    (h : IsAncPath s x pre) :
    do_ s (t, r, .Del pre x)
      = del (iter_upd (fun _ ea => if ea.2 = x then (ea.1, anc s x) else ea) s) x := by
  have hr : resolve s pre = anc s x := isAncPath_resolve s x pre h
  simp only [do_, hr]

def doDelPF (s : concrete_st α) (x : ℕ) : concrete_st α :=
  del (iter_upd (fun _ ea => if ea.2 = x then (ea.1, anc s x) else ea) s) x

theorem del_prefix_dispensable (s : concrete_st α) (t r x : ℕ) (pre : List ℕ)
    (h : IsAncPath s x pre) :
    do_ s (t, r, .Del pre x) = doDelPF s x := by
  unfold doDelPF; exact del_path_free s t r x pre h

/-! ## Case lemmas -/

theorem insins_comm (s : concrete_st α) (t1 r1 : ℕ) (e1 : α) (a1 t2 r2 : ℕ) (e2 : α) (a2 : ℕ) (p1 p2 : List ℕ)
    (hdist : t1 ≠ t2) (h0 : contains s 0 = false)
    (ha1 : accurate (t1, r1, .Ins e1 p1 a1) s) (ha2 : accurate (t2, r2, .Ins e2 p2 a2) s)
    (hf1 : fresh_ts (t1, r1, .Ins e1 p1 a1) s) (hf2 : fresh_ts (t2, r2, .Ins e2 p2 a2) s) :
    eq (do_ (do_ s (t1, r1, .Ins e1 p1 a1)) (t2, r2, .Ins e2 p2 a2))
       (do_ (do_ s (t2, r2, .Ins e2 p2 a2)) (t1, r1, .Ins e1 p1 a1)) := by
  simp only [fresh_ts] at hf1 hf2
  obtain ⟨ht1, _⟩ := hf1
  obtain ⟨ht2, _⟩ := hf2
  simp only [accurate, opLeaf, opPath] at ha1 ha2
  have r1eq : resolve s (a1 :: p1) = a1 := by
    apply resolve_cons_eq
    rcases ha1 with ⟨h, hp⟩ | h
    · exact Or.inl ⟨h, hp, h0⟩
    · exact Or.inr h.1
  have r2eq : resolve s (a2 :: p2) = a2 := by
    apply resolve_cons_eq
    rcases ha2 with ⟨h, hp⟩ | h
    · exact Or.inl ⟨h, hp, h0⟩
    · exact Or.inr h.1
  simp only [do_]
  rw [r1eq, r2eq]
  have hc0_1 : contains (upd s t1 (e1, a1)) 0 = false := by
    simp only [contains, upd, mem, union, _root_.singleton]
    have : (0 = t1) = False := by simp [Ne.symm ht1]
    grind
  have hc0_2 : contains (upd s t2 (e2, a2)) 0 = false := by
    simp only [contains, upd, mem, union, _root_.singleton]
    have : (0 = t2) = False := by simp [Ne.symm ht2]
    grind
  have r2eq' : resolve (upd s t1 (e1, a1)) (a2 :: p2) = a2 := by
    apply resolve_cons_eq
    rcases ha2 with ⟨h,hp⟩|h
    · exact Or.inl ⟨h, hp, hc0_1⟩
    · refine Or.inr ?_
      simp only [contains, upd, mem, union, _root_.singleton]
      have := h.1; simp only [contains, mem] at this; grind
  have r1eq' : resolve (upd s t2 (e2, a2)) (a1 :: p1) = a1 := by
    apply resolve_cons_eq
    rcases ha1 with ⟨h,hp⟩|h
    · exact Or.inl ⟨h, hp, hc0_2⟩
    · refine Or.inr ?_
      simp only [contains, upd, mem, union, _root_.singleton]
      have := h.1; simp only [contains, mem] at this; grind
  rw [r2eq', r1eq']
  rw [upd_comm s t1 t2 (e1, a1) (e2, a2) hdist]
  intro k; exact ⟨rfl, fun _ => rfl⟩

theorem insdel_comm (s : concrete_st α) (t1 r1 : ℕ) (e1 : α) (a1 : ℕ) (p1 : List ℕ)
    (t2 r2 : ℕ) (p2 : List ℕ) (x2 : ℕ)
    (hdist : t1 ≠ t2) (h0 : contains s 0 = false)
    (ha1 : accurate (t1, r1, .Ins e1 p1 a1) s) (ha2 : accurate (t2, r2, .Del p2 x2) s)
    (hf1 : fresh_ts (t1, r1, .Ins e1 p1 a1) s) (hf2 : fresh_ts (t2, r2, .Del p2 x2) s) :
    eq (do_ (do_ s (t1, r1, .Ins e1 p1 a1)) (t2, r2, .Del p2 x2))
       (do_ (do_ s (t2, r2, .Del p2 x2)) (t1, r1, .Ins e1 p1 a1)) := by
  simp only [fresh_ts] at hf1
  obtain ⟨ht1_0, ht1_dom⟩ := hf1
  simp only [accurate, opLeaf, opPath] at ha1 ha2
  have rIns : resolve s (a1 :: p1) = a1 := by
    apply resolve_cons_eq
    rcases ha1 with ⟨h, hp⟩ | h
    · exact Or.inl ⟨h, hp, h0⟩
    · exact Or.inr h.1
  have ht1p2 : t1 ∉ p2 := by
    intro hmem
    have hc : contains s t1 = true := by
      rcases ha2 with ⟨_, hp⟩ | h
      · rw [hp] at hmem; simp at hmem
      · exact isAncPath_mem s x2 p2 h.2 t1 hmem
    rw [ht1_dom] at hc; exact absurd hc (by simp)
  have ht1x2 : t1 ≠ x2 := by
    rcases ha2 with ⟨hx, _⟩ | h
    · rw [hx]; exact ht1_0
    · intro e; rw [e, h.1] at ht1_dom; exact absurd ht1_dom (by simp)
  have hInsL : do_ s (t1, r1, .Ins e1 p1 a1) = upd s t1 (e1, a1) := by
    simp only [do_]; rw [rIns]
  rw [hInsL]
  set US : concrete_st α := upd s t1 (e1, a1) with hUS
  set DS : concrete_st α := do_ s (t2, r2, .Del p2 x2) with hDS
  have anchorR : resolve DS (a1 :: p1) = (if a1 = x2 then resolve s p2 else a1) := by
    by_cases hax : a1 = x2
    · subst hax
      simp only
      have hcDSa : contains DS a1 = false := by
        rw [hDS, contains_doDel]; simp
      rw [resolve_dead_head DS a1 p1 hcDSa]
      rcases ha1 with ⟨ha10, hp1⟩ | h1
      · subst ha10; subst hp1
        rcases ha2 with ⟨_, hp2⟩ | h2
        · rw [hp2]; rfl
        · exact absurd h2.1 (by rw [h0]; simp)
      · have hx2live : contains s a1 = true := h1.1
        have hx2ne : a1 ≠ 0 := contains_ne_zero s a1 h0 hx2live
        have hR2 : resolve s p2 = anc s a1 := by
          rcases ha2 with ⟨hx20, _⟩ | h2
          · exact absurd hx20 hx2ne
          · exact isAncPath_resolve s a1 p2 h2.2
        rw [hR2]
        cases p1 with
        | nil =>
          have : anc s a1 = 0 := by simpa [IsAncPath] using h1.2
          rw [this]; rfl
        | cons c cs =>
          obtain ⟨hc1, hc2, _⟩ := h1.2
          have hcne : c ≠ a1 := by
            intro e
            have : anc s a1 = a1 := by rw [hc1, e]
            exact hx2ne (isAncPath_self s (c :: cs) a1 h1.2 this)
          have hcDSc : contains DS c = true := by
            rw [hDS, contains_doDel, hc2]; simp [hcne]
          rw [resolve_live_head DS c cs hcDSc]
          exact hc1.symm
    · simp only [if_neg hax]
      apply resolve_cons_eq
      rcases ha1 with ⟨ha10, hp1⟩ | h1
      · refine Or.inl ⟨ha10, hp1, ?_⟩
        rw [hDS, contains_doDel, h0]; simp
      · refine Or.inr ?_
        rw [hDS, contains_doDel, h1.1]; simp [hax]
  have rUSp2 : resolve US p2 = resolve s p2 := by
    rw [hUS]; exact resolve_upd_notMem s t1 (e1, a1) p2 ht1p2
  show eq (do_ US (t2, r2, .Del p2 x2))
          (upd DS t1 (e1, resolve DS (a1 :: p1)))
  rw [anchorR]
  intro k
  refine ⟨?_, ?_⟩
  · rw [contains_doDel US t2 r2 x2 p2 k,
        lemma_InDomUpd1 DS t1 k (e1, (if a1 = x2 then resolve s p2 else a1)),
        hDS, contains_doDel s t2 r2 x2 p2 k, hUS, lemma_InDomUpd1]
    by_cases hk : k = t1
    · subst hk; simpa using ht1x2
    · have htk : ¬ (t1 = k) := fun e => hk e.symm
      simp [htk]
  · intro _
    rw [sel_doDel US t2 r2 x2 p2 k, rUSp2]
    by_cases hk : k = t1
    · subst hk
      have e1us : sel US k = (e1, a1) := by rw [hUS]; simp
      simp only [anc, el, e1us]
      rw [lemma_SelUpd1]
      by_cases hax : a1 = x2 <;> simp [hax]
    · have eus : sel US k = sel s k := by
        rw [hUS]; simp only [sel, upd]; rw [if_neg hk]
      simp only [anc, el, eus]
      rw [lemma_SelUpd2 DS k t1 (e1, (if a1 = x2 then resolve s p2 else a1))
            (by simp only [bne_iff_ne, ne_eq]; exact fun e => hk e.symm),
          hDS, sel_doDel s t2 r2 x2 p2 k]
      simp only [anc, el]

/-! ## Del/Del helper lemmas -/

theorem isancpath_resolve_self_filter (s : concrete_st α) :
    ∀ leaf p, IsAncPath s leaf p →
      resolve s (p.filter (fun c => c != leaf)) = anc s leaf := by
  intro leaf p
  induction p generalizing leaf with
  | nil => intro h; exact h.symm
  | cons c ps ih =>
    intro h
    simp only [IsAncPath] at h
    obtain ⟨hac, hcc, hrest⟩ := h
    rw [List.filter_cons]
    by_cases hcl : c = leaf
    · subst hcl
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      exact ih c hrest
    · have hb : (c != leaf) = true := by simp [hcl]
      simp only [hb, if_true, resolve, hcc, if_true]
      exact hac.symm

theorem resolve_doDel (s : concrete_st α) (t r x : ℕ) (pre cands : List ℕ) :
    resolve (do_ s (t, r, .Del pre x)) cands
      = resolve s (cands.filter (fun c => c != x)) := by
  induction cands with
  | nil => rfl
  | cons c rest ih =>
    rw [List.filter_cons]
    by_cases hcx : c = x
    · subst hcx
      have hd : contains (do_ s (t, r, .Del pre c)) c = false := by
        rw [contains_doDel]; simp
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      simp only [resolve, hd, if_false, Bool.false_eq_true]
      exact ih
    · have hb : (c != x) = true := by simp [hcx]
      have hcc : contains (do_ s (t, r, .Del pre x)) c = contains s c := by
        rw [contains_doDel, hb]; simp
      simp only [hb, if_true, resolve, hcc]
      cases hh : contains s c with
      | true => simp
      | false => simp; exact ih

theorem IsAncPath_unique (s : concrete_st α) (h0 : contains s 0 = false) :
    ∀ (leaf : ℕ) (p q : List ℕ), IsAncPath s leaf p → IsAncPath s leaf q → p = q := by
  intro leaf p
  induction p generalizing leaf with
  | nil =>
    intro q hp hq
    cases q with
    | nil => rfl
    | cons b bs =>
      simp only [IsAncPath] at hp hq
      obtain ⟨hb, hcb, _⟩ := hq
      rw [hp] at hb; rw [← hb] at hcb; rw [h0] at hcb; exact Bool.noConfusion hcb
  | cons a as ih =>
    intro q hp hq
    cases q with
    | nil =>
      simp only [IsAncPath] at hp hq
      obtain ⟨ha, hca, _⟩ := hp
      rw [hq] at ha; rw [← ha] at hca; rw [h0] at hca; exact Bool.noConfusion hca
    | cons b bs =>
      simp only [IsAncPath] at hp hq
      obtain ⟨ha, _, hpas⟩ := hp
      obtain ⟨hb, _, hqbs⟩ := hq
      have hab : a = b := by rw [← ha, ← hb]
      subst hab
      have hasbs : as = bs := ih a bs hpas hqbs
      rw [hasbs]

theorem resolve_filter_ne (s : concrete_st α) (y : ℕ) :
    ∀ p, resolve s p ≠ y → resolve s (p.filter (fun c => c != y)) = resolve s p := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons c rest ih =>
    intro hne
    rw [List.filter_cons]
    cases hcon : contains s c with
    | true =>
      rw [resolve_live_head s c rest hcon] at hne ⊢
      have hcy : (c != y) = true := by simp [hne]
      rw [if_pos hcy]
      exact resolve_live_head s c _ hcon
    | false =>
      rw [resolve_dead_head s c rest hcon] at hne ⊢
      by_cases hcy : c = y
      · rw [if_neg (by simp [hcy])]; exact ih hne
      · rw [if_pos (by simp [hcy] : (c != y) = true), resolve_dead_head s c _ hcon]
        exact ih hne

theorem el_doDel (s : concrete_st α) (t r x : ℕ) (pre : List ℕ) (k : ℕ) :
    el (do_ s (t, r, .Del pre x)) k = el s k := by
  show (sel (do_ s (t, r, .Del pre x)) k).1 = el s k
  rw [sel_doDel s t r x pre k]
  by_cases h : anc s k = x
  · rw [if_pos h]
  · rw [if_neg h]; rfl

theorem anc_doDel (s : concrete_st α) (t r x : ℕ) (pre : List ℕ) (k : ℕ) :
    anc (do_ s (t, r, .Del pre x)) k = if anc s k = x then resolve s pre else anc s k := by
  show (sel (do_ s (t, r, .Del pre x)) k).2 = if anc s k = x then resolve s pre else anc s k
  rw [sel_doDel s t r x pre k]
  by_cases h : anc s k = x
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]; rfl

theorem collapse (s : concrete_st α) (h0 : contains s 0 = false) (a b : ℕ) (pa pb : List ℕ)
    (hpa : (a = 0 ∧ pa = []) ∨ (contains s a = true ∧ IsAncPath s a pa))
    (hpb : (b = 0 ∧ pb = []) ∨ (contains s b = true ∧ IsAncPath s b pb))
    (hab : a ≠ b) (hres : resolve s pa = b) :
    resolve s (pb.filter (fun c => c != a)) = resolve s (pa.filter (fun c => c != b)) := by
  rcases hpa with ⟨ha0, hpanil⟩ | ⟨halive, hapath⟩
  · subst hpanil
    have hb0 : b = 0 := by simpa [resolve] using hres.symm
    rcases hpb with ⟨_, hpbnil⟩ | ⟨hblive, _⟩
    · subst hpbnil; rfl
    · rw [hb0, h0] at hblive; exact Bool.noConfusion hblive
  · have hanca : anc s a = b := by rw [← isAncPath_resolve s a pa hapath]; exact hres
    rcases hpb with ⟨hb0, hpbnil⟩ | ⟨hblive, hbpath⟩
    · subst hpbnil
      have hpanil : pa = [] := by
        cases pa with
        | nil => rfl
        | cons c cs =>
          simp only [IsAncPath] at hapath
          obtain ⟨hc1, hc2, _⟩ := hapath
          rw [hanca, hb0] at hc1
          rw [← hc1, h0] at hc2; exact Bool.noConfusion hc2
      subst hpanil; rfl
    · have hbne0 : b ≠ 0 := contains_ne_zero s b h0 hblive
      have hpaeq : pa = b :: pb := by
        cases pa with
        | nil =>
          simp only [IsAncPath] at hapath
          rw [hanca] at hapath; exact absurd hapath hbne0
        | cons c cs =>
          simp only [IsAncPath] at hapath
          obtain ⟨hc1, _, hcs⟩ := hapath
          have hcb : c = b := by rw [← hc1]; exact hanca
          subst hcb
          have : cs = pb := IsAncPath_unique s h0 c cs pb hcs hbpath
          rw [this]
      have hancb_ne : anc s b ≠ a := by
        intro hba
        have hane0 : a ≠ 0 := contains_ne_zero s a h0 halive
        have hpbeq : pb = a :: pa := by
          cases pb with
          | nil =>
            simp only [IsAncPath] at hbpath
            rw [hba] at hbpath; exact absurd hbpath hane0
          | cons d ds =>
            simp only [IsAncPath] at hbpath
            obtain ⟨hd1, _, hds⟩ := hbpath
            have hda : d = a := by rw [← hd1]; exact hba
            subst hda
            have : ds = pa := IsAncPath_unique s h0 d ds pa hds hapath
            rw [this]
        rw [hpbeq] at hpaeq
        have hlen := congrArg List.length hpaeq
        simp only [List.length_cons] at hlen; omega
      have hRHS : resolve s (pa.filter (fun c => c != b)) = anc s b := by
        rw [hpaeq, List.filter_cons]
        simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
        exact isancpath_resolve_self_filter s b pb hbpath
      have hLHS : resolve s (pb.filter (fun c => c != a)) = anc s b := by
        have hrne : resolve s pb ≠ a := by
          rw [isAncPath_resolve s b pb hbpath]; exact hancb_ne
        rw [resolve_filter_ne s a pb hrne, isAncPath_resolve s b pb hbpath]
      rw [hLHS, hRHS]

theorem deldel_comm (s : concrete_st α) (t1 r1 : ℕ) (p1 : List ℕ) (x1 : ℕ)
    (t2 r2 : ℕ) (p2 : List ℕ) (x2 : ℕ) (h0 : contains s 0 = false)
    (ha1 : accurate (t1, r1, .Del p1 x1) s) (ha2 : accurate (t2, r2, .Del p2 x2) s) :
    eq (do_ (do_ s (t1, r1, .Del p1 x1)) (t2, r2, .Del p2 x2))
       (do_ (do_ s (t2, r2, .Del p2 x2)) (t1, r1, .Del p1 x1)) := by
  simp only [accurate, opLeaf, opPath] at ha1 ha2
  intro k
  refine ⟨?_, ?_⟩
  · simp only [contains_doDel]
    rw [Bool.and_right_comm]
  · intro _
    have hel : el (do_ (do_ s (t1, r1, .Del p1 x1)) (t2, r2, .Del p2 x2)) k
             = el (do_ (do_ s (t2, r2, .Del p2 x2)) (t1, r1, .Del p1 x1)) k := by
      simp only [el_doDel]
    have han : anc (do_ (do_ s (t1, r1, .Del p1 x1)) (t2, r2, .Del p2 x2)) k
             = anc (do_ (do_ s (t2, r2, .Del p2 x2)) (t1, r1, .Del p1 x1)) k := by
      simp only [anc_doDel, resolve_doDel]
      by_cases h1 : anc s k = x1
      · by_cases h2 : anc s k = x2
        · have hx12 : x1 = x2 := h1.symm.trans h2
          subst hx12
          simp only [if_pos h1]
          rcases ha1 with ⟨hx10, hp1nil⟩ | ⟨h1live, h1path⟩
          · subst hp1nil; subst hx10
            rcases ha2 with ⟨_, hp2nil⟩ | ⟨h2live, _⟩
            · subst hp2nil; simp [resolve]
            · rw [h0] at h2live; exact Bool.noConfusion h2live
          · have hx1ne0 : x1 ≠ 0 := contains_ne_zero s x1 h0 h1live
            rcases ha2 with ⟨hx20, _⟩ | ⟨_, h2path⟩
            · exact absurd hx20 hx1ne0
            · have hp12 : p1 = p2 := IsAncPath_unique s h0 x1 p1 p2 h1path h2path
              subst hp12
              have hres1 : resolve s p1 = anc s x1 := isAncPath_resolve s x1 p1 h1path
              have hne : resolve s p1 ≠ x1 := by
                rw [hres1]; intro he; exact hx1ne0 (isAncPath_self s p1 x1 h1path he)
              simp only [if_neg hne]
        · have hx12 : x1 ≠ x2 := fun e => h2 (h1.trans e)
          simp only [if_pos h1, if_neg h2]
          by_cases hA : resolve s p1 = x2
          · rw [if_pos hA]
            exact collapse s h0 x1 x2 p1 p2 ha1 ha2 hx12 hA
          · rw [if_neg hA]
            exact (resolve_filter_ne s x2 p1 hA).symm
      · by_cases h2 : anc s k = x2
        · have hx21 : x2 ≠ x1 := fun e => h1 (h2.trans e)
          simp only [if_neg h1, if_pos h2]
          by_cases hB : resolve s p2 = x1
          · rw [if_pos hB]
            exact (collapse s h0 x2 x1 p2 p1 ha2 ha1 hx21 hB).symm
          · rw [if_neg hB]
            exact resolve_filter_ne s x1 p2 hB
        · simp only [if_neg h1, if_neg h2]
    exact Prod.ext_iff.mpr ⟨hel, han⟩

/-! ## Main theorem -/

theorem rc_non_comm' (o1 o2 : op_t α) :
    (distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2)
    → (rc o1 o2 = rc_res.Either ↔ commutes_with' o1 o2) := by
  rintro ⟨hdist, _hrid⟩
  refine ⟨fun _ => ?_, fun _ => rfl⟩
  intro s h0 ha1 ha2 hf1 hf2
  simp only [distinct_ops, bne_iff_ne, ne_eq] at hdist
  obtain ⟨t1, r1, op1⟩ := o1
  obtain ⟨t2, r2, op2⟩ := o2
  cases op1 with
  | Ins e1 p1 a1 =>
    cases op2 with
    | Ins e2 p2 a2 => exact insins_comm s t1 r1 e1 a1 t2 r2 e2 a2 p1 p2 hdist h0 ha1 ha2 hf1 hf2
    | Del p2 x2    => exact insdel_comm s t1 r1 e1 a1 p1 t2 r2 p2 x2 hdist h0 ha1 ha2 hf1 hf2
  | Del p1 x1 =>
    cases op2 with
    | Ins e2 p2 a2 =>
        exact eq_symm _ _ (insdel_comm s t2 r2 e2 a2 p2 t1 r1 p1 x1
          (Ne.symm hdist) h0 ha2 ha1 hf2 hf1)
    | Del p2 x2    => exact deldel_comm s t1 r1 p1 x1 t2 r2 p2 x2 h0 ha1 ha2

end

#print axioms rc_non_comm'
#print axioms merge_idem
#print axioms deldel_comm
