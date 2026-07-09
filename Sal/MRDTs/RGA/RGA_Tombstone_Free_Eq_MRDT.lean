import Sal.MRDTs.RGA.RGA_Tombstone_Free_MRDT

/-!
# The eq-variant tombstone-free RGA: a normalizing implementation

The tombstone-free RGA converges only up to its observational equivalence `eq`
(equal domains, equal payloads **on** the domain), because the `map`
representation carries *ghost payloads at deleted keys*: `del` shrinks the
domain but keeps the mapping, `iter_upd` rewrites mappings at every key
(ghosts included), and `merge` manufactures payloads outside its survivor set.
Different replay orders leave different ghosts — this is the entire content of
the `≈` in `rga_ra_linearizable3_eq`
(the conditioned RGA capstone in `Sal/ConditionedMRDTs/MRDT_Instances/RGA/`).

This file shows the `≈` is **purely representational** by exhibiting the
normalizing variant: `doN`/`mergeN` behave identically on live data
(`doN_eq_do`, `mergeN_eq_merge` — pointwise `eq` at every input state) but pin
every out-of-domain payload to the default `(0, 0)` (`Norm`, an invariant of
the variant: `norm_init`/`norm_doN`/`norm_mergeN`). On normalized states the
observational equivalence **is** structural equality (`eq_iff_eq_of_norm`),
and the variant's update folds are the normal forms of the original's
(`foldN_eq_fold`). Consequently, for the variant, the RA-linearizability
witness of the capstone theorem holds with `=` in place of `≈` between
normalized states: the quotient in the conditioned metatheory prices exactly
the representation junk a normalizing implementation never creates.
-/

set_option maxHeartbeats 1000000

/-! ## §1  The normal form and the normalizing operations -/

/-- **Normal form**: out-of-domain payloads are the default. -/
def Norm (s : concrete_st) : Prop :=
  ∀ k, contains s k = false → sel s k = (0, 0)

/-- Normalizing delete: shrink the domain AND reset the payload. -/
def delN (s : concrete_st) (x : ℕ) : concrete_st :=
  map.mk (fun k => if k = x then (0, 0) else s.mappings k)
    (remove (domain s) x)

/-- Domain-restricted rewrite: `iter_upd`, but ghosts are left alone. -/
def iter_updD (f : ℕ → (ℕ × ℕ) → (ℕ × ℕ)) (s : concrete_st) : concrete_st :=
  map.mk (fun k => if mem k s.domain then f k (s.mappings k) else s.mappings k)
    s.domain

/-- The normalizing `do`: `Ins` as before (it writes only the key it adds to
the domain); `Del` rehomes on-domain only and resets the deleted key. -/
def doN (s : concrete_st) (o : op_t) : concrete_st :=
  match o with
  | (t, _, .Ins e pre a) => upd s t (e, resolve s (a :: pre))
  | (_, _, .Del pre x)   =>
      let tgt := resolve s pre
      delN (iter_updD (fun _ ea => if ea.2 = x then (ea.1, tgt) else ea) s) x

/-- The survivor set of the merge. -/
def mergeNI (l a b : concrete_st) : set ℕ :=
  union (intersection (intersection (domain l) (domain a)) (domain b))
        (union (difference (domain a) (domain l))
               (difference (domain b) (domain l)))

def mergeNElf (l a b : concrete_st) (t : ℕ) : ℕ :=
  if contains l t then el l t else if contains a t then el a t else el b t

def mergeNBeta (l a b : concrete_st) (t : ℕ) : ℕ :=
  if contains l t then anc l t else if contains a t then anc a t else anc b t

/-- The normalizing merge: identical on the survivor set, default outside. -/
def mergeN (l a b : concrete_st) : concrete_st :=
  map.mk (fun t => if mem t (mergeNI l a b) then
      (mergeNElf l a b t,
        climb (fun y => anc l y) (mergeNI l a b) (mergeNBeta l a b t))
    else (0, 0)) (mergeNI l a b)

theorem mergeN_mappings (l a b : concrete_st) (k : ℕ) :
    (mergeN l a b).mappings k
      = if mem k (mergeNI l a b) then
          (mergeNElf l a b k,
            climb (fun y => anc l y) (mergeNI l a b) (mergeNBeta l a b k))
        else (0, 0) := rfl

/-! ## §2  `Norm` is an invariant of the variant -/

theorem norm_init : Norm init_st := fun _ _ => rfl

theorem norm_doN {s : concrete_st} (hs : Norm s) (o : op_t) :
    Norm (doN s o) := by
  rcases o with ⟨t, r, op⟩
  cases op with
  | Ins e pre a =>
    intro k hk
    have hk' : (s.domain k || decide (k = t)) = false := hk
    have hks : s.domain k = false := by
      cases h : s.domain k
      · rfl
      · rw [h] at hk'; exact Bool.noConfusion hk'
    have hkt : k ≠ t := by
      intro h
      rw [h] at hk'
      simp at hk'
    show (if k = t then _ else s.mappings k) = (0, 0)
    rw [if_neg hkt]
    exact hs k hks
  | Del pre x =>
    intro k hk
    have hk' : (s.domain k && !(x == k)) = false := hk
    show (if k = x then ((0, 0) : ℕ × ℕ)
        else if mem k s.domain then _ else s.mappings k) = (0, 0)
    by_cases hkx : k = x
    · rw [if_pos hkx]
    · rw [if_neg hkx]
      have hks : s.domain k = false := by
        cases h : s.domain k
        · rfl
        · exfalso
          rw [h] at hk'
          have : (x == k) = true := by
            cases hxk : x == k
            · rw [hxk] at hk'; exact Bool.noConfusion hk'
            · rfl
          exact hkx (beq_iff_eq.mp this).symm
      show (if mem k s.domain then _ else s.mappings k) = (0, 0)
      rw [show mem k s.domain = false from hks, if_neg (by simp)]
      exact hs k hks

theorem norm_mergeN (l a b : concrete_st) : Norm (mergeN l a b) := by
  intro k hk
  have hk' : mem k (mergeNI l a b) = false := hk
  show (mergeN l a b).mappings k = (0, 0)
  rw [mergeN_mappings, hk']
  simp

/-! ## §3  On normal forms, observational equivalence IS equality -/

theorem eq_iff_eq_of_norm {a b : concrete_st} (ha : Norm a) (hb : Norm b) :
    eq a b ↔ a = b := by
  constructor
  · intro h
    have hdom : a.domain = b.domain := by
      funext k
      exact (h k).1
    have hmap : a.mappings = b.mappings := by
      funext k
      cases hc : contains a k
      · have hcb : contains b k = false := by rw [← (h k).1]; exact hc
        have h1 := ha k hc
        have h2 := hb k hcb
        show a.mappings k = b.mappings k
        have h1' : a.mappings k = (0, 0) := h1
        have h2' : b.mappings k = (0, 0) := h2
        rw [h1', h2']
      · have := (h k).2 hc
        exact this
    cases a with
    | mk am ad =>
      cases b with
      | mk bm bd =>
        have h1 : am = bm := hmap
        have h2 : ad = bd := hdom
        rw [h1, h2]
  · intro h
    subst h
    exact fun k => ⟨rfl, fun _ => rfl⟩

/-! ## §4  The variant agrees with the original on live data -/

theorem doN_eq_do (s : concrete_st) (o : op_t) : eq (doN s o) (do_ s o) := by
  rcases o with ⟨t, r, op⟩
  cases op with
  | Ins e pre a => exact fun k => ⟨rfl, fun _ => rfl⟩
  | Del pre x =>
    intro k
    constructor
    · rfl
    · intro hk
      have hk' : (s.domain k && !(x == k)) = true := hk
      have hks : s.domain k = true := (Bool.and_eq_true_iff.mp hk').1
      have hkx : k ≠ x := by
        intro h
        have := (Bool.and_eq_true_iff.mp hk').2
        rw [h] at this
        simp at this
      show (if k = x then _
          else if mem k s.domain then _ else s.mappings k) = _
      rw [if_neg hkx, show mem k s.domain = true from hks,
        if_pos (by simp)]
      rfl

theorem mergeN_eq_merge (l a b : concrete_st) :
    eq (mergeN l a b) (merge l a b) := by
  intro k
  constructor
  · rfl
  · intro hk
    have hk' : mem k (mergeNI l a b) = true := hk
    show (mergeN l a b).mappings k = _
    rw [mergeN_mappings, hk']
    simp only [if_pos]
    rfl

/-! ## §5  Congruence of the original `do_` under `eq`, and the fold bridge -/

theorem resolve_eq_congr {s s' : concrete_st} (h : eq s s') :
    ∀ L : List ℕ, resolve s L = resolve s' L := by
  intro L
  induction L with
  | nil => rfl
  | cons c rest ih =>
    show (if contains s c then c else resolve s rest)
        = (if contains s' c then c else resolve s' rest)
    rw [(h c).1, ih]

theorem do_eq_congr {s s' : concrete_st} (h : eq s s') (o : op_t) :
    eq (do_ s o) (do_ s' o) := by
  rcases o with ⟨t, r, op⟩
  cases op with
  | Ins e pre a =>
    intro k
    constructor
    · show (s.domain k || decide (k = t)) = (s'.domain k || decide (k = t))
      rw [show s.domain k = s'.domain k from (h k).1]
    · intro hk
      show (if k = t then _ else s.mappings k)
          = (if k = t then _ else s'.mappings k)
      by_cases hkt : k = t
      · rw [if_pos hkt, if_pos hkt, resolve_eq_congr h]
      · rw [if_neg hkt, if_neg hkt]
        have hk' : (s.domain k || decide (k = t)) = true := hk
        have hks : s.domain k = true := by
          rcases Bool.or_eq_true_iff.mp hk' with h' | h'
          · exact h'
          · exact absurd (of_decide_eq_true h') hkt
        exact (h k).2 hks
  | Del pre x =>
    intro k
    constructor
    · show (s.domain k && !(x == k)) = (s'.domain k && !(x == k))
      rw [show s.domain k = s'.domain k from (h k).1]
    · intro hk
      have hk' : (s.domain k && !(x == k)) = true := hk
      have hks : s.domain k = true := (Bool.and_eq_true_iff.mp hk').1
      show (if (s.mappings k).2 = x
            then ((s.mappings k).1, resolve s pre) else s.mappings k)
          = (if (s'.mappings k).2 = x
            then ((s'.mappings k).1, resolve s' pre) else s'.mappings k)
      have hsel : s.mappings k = s'.mappings k := (h k).2 hks
      rw [hsel, resolve_eq_congr h]

private theorem eq_refl' (s : concrete_st) : eq s s :=
  fun _ => ⟨rfl, fun _ => rfl⟩

private theorem eq_trans' {a b c : concrete_st} (h1 : eq a b) (h2 : eq b c) :
    eq a c := by
  intro k
  refine ⟨(h1 k).1.trans (h2 k).1, fun hk => ?_⟩
  refine ((h1 k).2 hk).trans ((h2 k).2 ?_)
  rw [← (h1 k).1]
  exact hk

/-- **The fold bridge**: the variant's update folds are (the normal forms of)
the original's. -/
theorem foldN_eq_fold : ∀ (ρ : List op_t) (s s' : concrete_st), eq s s' →
    eq (List.foldl doN s ρ) (List.foldl do_ s' ρ) := by
  intro ρ
  induction ρ with
  | nil => intro s s' h; exact h
  | cons o ρ ih =>
    intro s s' h
    exact ih (doN s o) (do_ s' o)
      (eq_trans' (doN_eq_do s o) (do_eq_congr h o))

/-- The variant's from-`init` fold is the normal form of the original's. -/
theorem foldN_norm_form (ρ : List op_t) :
    Norm (List.foldl doN init_st ρ)
      ∧ eq (List.foldl doN init_st ρ) (List.foldl do_ init_st ρ) := by
  constructor
  · have hgen : ∀ (π : List op_t) (s : concrete_st), Norm s →
        Norm (List.foldl doN s π) := by
      intro π
      induction π with
      | nil => exact fun _ h => h
      | cons o π ih => exact fun s h => ih (doN s o) (norm_doN h o)
    exact hgen ρ init_st norm_init
  · exact foldN_eq_fold ρ init_st init_st (eq_refl' init_st)

/-! ## Axiom audit -/

#print axioms norm_doN
#print axioms norm_mergeN
#print axioms eq_iff_eq_of_norm
#print axioms doN_eq_do
#print axioms mergeN_eq_merge
#print axioms foldN_norm_form
