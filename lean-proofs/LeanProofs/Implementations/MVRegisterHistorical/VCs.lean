import LeanProofs1.Implementations.MVRegisterHistorical.Definition
import LeanProofs1.Metatheory.Adequacy

/-!
# The grow-only multi-value register: `Laws(D_type)` and VC1 to VC5

Both stores are grow-only and `do` only sets bits, so every pair of events
commutes and `rc` is empty. `Laws(D_type)` is then immediate.

The merge is the three-way shape rather than a plain union, so VC3, VC4 and
VC5 need one fact about canonical states: a bit is set exactly when some
event of the set sets it, and therefore a smaller event set gives a smaller
state. On arguments ordered that way the three-way merge **is** the union,
and the conditions become identities among disjunctions.
-/

namespace LeanProofs1.Implementations.MVRegisterHistorical

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

theorem do_eq (s : St) (e : D.Event) : D.do_ s e = step s e := rfl
theorem merge_eq (l a b : D.Sigma) : D.merge l a b = mergeState l a b := rfl
theorem sigma0_eq : D.sigma0 = ((fun _ => false), (fun _ => false)) := rfl

/-! ## Every pair of events commutes -/

theorem all_commute (e₁ e₂ : D.Event) : D.Commutes e₁ e₂ := by
  intro s
  simp only [do_eq, step]
  refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
    simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

/-! ## `Laws(D_type)` -/

theorem no_rc_edge (e₁ e₂ : D.Event) : ¬ D.EventRcBefore e₁ e₂ := by
  simp [Impl.EventRcBefore, Impl.RcBefore, D, rcOf]

theorem no_rc_chain (o₁ o₂ o₃ : type.OType) :
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃) := by
  rintro ⟨h, -⟩
  simp [Impl.RcBefore, D, rcOf] at h

theorem rc_non_comm (e₁ e₂ : D.Event)
    (_ht : D.time e₁ ≠ D.time e₂) (_hr : D.rep e₁ ≠ D.rep e₂) :
    ((¬ D.Commutes e₁ e₂ ∧ e₁.op ≠ e₂.op) ↔
      D.EventRcBefore e₁ e₂ ∨ D.EventRcBefore e₂ e₁) := by
  constructor
  · exact fun h => absurd (all_commute e₁ e₂) h.1
  · rintro (h | h) <;> exact absurd h (no_rc_edge _ _)

theorem rc_non_comm_uniform : UniformRcNonComm D := by
  intro e₁ e₂
  constructor
  · exact fun h => absurd (all_commute e₁ e₂) h
  · rintro (h | h) <;> exact absurd h (no_rc_edge _ _)

theorem cond_comm (sigma : D.Sigma) (e e' e'' : D.Event) (pi : List D.Event)
    (_ht : D.time e ≠ D.time e') (_hr : D.rep e ≠ D.rep e')
    (hrc : D.EventRcBefore e e') (_hnc : ¬ D.Commutes e' e'') :
    D.do_ (D.applyList (D.do_ (D.do_ sigma e') e) pi) e''
      = D.do_ (D.applyList (D.do_ (D.do_ sigma e) e') pi) e'' :=
  absurd hrc (no_rc_edge e e')

theorem laws : Laws D := ⟨rc_non_comm, no_rc_chain, cond_comm⟩

/-! ## What a replay leaves in each store -/

theorem fst_applyList : ∀ (s : D.Sigma) (pi : List D.Event) (p : Nat × Nat),
    (D.applyList s pi).1 p = true
      ↔ s.1 p = true ∨ ∃ e ∈ pi, p = (newId e.op, writeValue e.op)
  | s, [], p => by simp [Impl.applyList]
  | s, e :: rest, p => by
      show (D.applyList (D.do_ s e) rest).1 p = true ↔ _
      rw [fst_applyList (D.do_ s e) rest p]
      simp only [do_eq, step, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨f, hf, hp⟩)
        · exact Or.inl h
        · exact Or.inr ⟨e, Or.inl rfl, h⟩
        · exact Or.inr ⟨f, Or.inr hf, hp⟩
      · rintro (h | ⟨f, hf | hf, hp⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (hf ▸ hp))
        · exact Or.inr ⟨f, hf, hp⟩

theorem snd_applyList : ∀ (s : D.Sigma) (pi : List D.Event) (n : Nat),
    (D.applyList s pi).2 n = true
      ↔ s.2 n = true ∨ ∃ e ∈ pi, n ∈ overwrites e.op
  | s, [], n => by simp [Impl.applyList]
  | s, e :: rest, n => by
      show (D.applyList (D.do_ s e) rest).2 n = true ↔ _
      rw [snd_applyList (D.do_ s e) rest n]
      simp only [do_eq, step, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨f, hf, hn⟩)
        · exact Or.inl h
        · exact Or.inr ⟨e, Or.inl rfl, h⟩
        · exact Or.inr ⟨f, Or.inr hf, hn⟩
      · rintro (h | ⟨f, hf | hf, hn⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (hf ▸ hn))
        · exact Or.inr ⟨f, hf, hn⟩

/-- **A canonical state is the union of its events' contributions.** -/
theorem canonical_fst {C : Ctx D} {E : Set D.Event} {s : D.Sigma}
    (hs : IsCanOn D C E s) (p : Nat × Nat) :
    s.1 p = true ↔ ∃ e ∈ E, p = (newId e.op, writeValue e.op) := by
  obtain ⟨pi, hpi, -, hf⟩ := id hs
  rw [show s = D.applyList D.sigma0 pi from hf.symm, fst_applyList]
  simp only [sigma0_eq]
  constructor
  · rintro (h | ⟨e, he, hp⟩)
    · exact absurd h (by simp)
    · exact ⟨e, (hpi.2 e).mp he, hp⟩
  · rintro ⟨e, he, hp⟩
    exact Or.inr ⟨e, (hpi.2 e).mpr he, hp⟩

theorem canonical_snd {C : Ctx D} {E : Set D.Event} {s : D.Sigma}
    (hs : IsCanOn D C E s) (n : Nat) :
    s.2 n = true ↔ ∃ e ∈ E, n ∈ overwrites e.op := by
  obtain ⟨pi, hpi, -, hf⟩ := id hs
  rw [show s = D.applyList D.sigma0 pi from hf.symm, snd_applyList]
  simp only [sigma0_eq]
  constructor
  · rintro (h | ⟨e, he, hn⟩)
    · exact absurd h (by simp)
    · exact ⟨e, (hpi.2 e).mp he, hn⟩
  · rintro ⟨e, he, hn⟩
    exact Or.inr ⟨e, (hpi.2 e).mpr he, hn⟩

/-- **A smaller event set gives a smaller state.** -/
theorem canonical_mono {C : Ctx D} {E F : Set D.Event} {s t : D.Sigma}
    (hs : IsCanOn D C E s) (ht : IsCanOn D C F t) (hEF : E ⊆ F) :
    (∀ p, s.1 p = true → t.1 p = true) ∧ (∀ n, s.2 n = true → t.2 n = true) := by
  refine ⟨fun p hp => ?_, fun n hn => ?_⟩
  · obtain ⟨e, he, hq⟩ := (canonical_fst hs p).mp hp
    exact (canonical_fst ht p).mpr ⟨e, hEF he, hq⟩
  · obtain ⟨e, he, hq⟩ := (canonical_snd hs n).mp hn
    exact (canonical_snd ht n).mpr ⟨e, hEF he, hq⟩

/-! ## The three-way merge is a union on ordered arguments -/

/-- One state is below another, componentwise. -/
def Le (a b : D.Sigma) : Prop :=
  (∀ p, a.1 p = true → b.1 p = true) ∧ (∀ n, a.2 n = true → b.2 n = true)

/-- The componentwise union. -/
def union (a b : D.Sigma) : D.Sigma :=
  ((fun p => a.1 p || b.1 p), (fun n => a.2 n || b.2 n))

theorem le_refl (a : D.Sigma) : Le a a := ⟨fun _ h => h, fun _ h => h⟩

theorem le_step (s : D.Sigma) (e : D.Event) : Le s (D.do_ s e) :=
  ⟨fun p h => by simp [do_eq, step, h], fun n h => by simp [do_eq, step, h]⟩

theorem le_union_left (a b : D.Sigma) : Le a (union a b) :=
  ⟨fun p h => by simp [union, h], fun n h => by simp [union, h]⟩

theorem le_trans {a b c : D.Sigma} (hab : Le a b) (hbc : Le b c) : Le a c :=
  ⟨fun p h => hbc.1 p (hab.1 p h), fun n h => hbc.2 n (hab.2 n h)⟩

/-- When the base is below both branches, the three-way shape is the
union. -/
theorem merge_eq_union {l a b : D.Sigma} (hla : Le l a) (hlb : Le l b) :
    D.merge l a b = union a b := by
  simp only [merge_eq, mergeState, union]
  refine Prod.ext (funext fun p => ?_) (funext fun n => ?_)
  · cases hl : l.1 p
    · simp [hl]
    · simp [hl, hla.1 p hl, hlb.1 p hl]
  · cases hl : l.2 n
    · simp [hl]
    · simp [hl, hla.2 n hl, hlb.2 n hl]

theorem union_comm (a b : D.Sigma) : union a b = union b a := by
  refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
    simp [union, Bool.or_comm]

theorem union_assoc (a b c : D.Sigma) : union (union a b) c = union a (union b c) := by
  refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
    simp [union, Bool.or_assoc]

/-! ## VC1 to VC5 -/

theorem vc1_merge_comm (l a b : D.Sigma) : D.merge l a b = D.merge l b a := by
  simp only [merge_eq, mergeState]
  refine Prod.ext (funext fun p => ?_) (funext fun n => ?_)
  · dsimp only
    cases l.1 p <;> cases a.1 p <;> cases b.1 p <;> rfl
  · dsimp only
    cases l.2 n <;> cases a.2 n <;> cases b.2 n <;> rfl

theorem vc2_merge_init :
    ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
      SupportedOn D C E → IsCanOn D C E s → D.merge D.sigma0 D.sigma0 s = s := by
  intro _ _ s _ _
  simp only [merge_eq, mergeState, sigma0_eq]
  refine Prod.ext (funext fun p => ?_) (funext fun n => ?_)
  · simp
  · simp

/-- Canonical monotonicity, as a `Le`. -/
theorem le_of_subset {C : Ctx D} {E F : Set D.Event} {s t : D.Sigma}
    (hs : IsCanOn D C E s) (ht : IsCanOn D C F t) (hEF : E ⊆ F) : Le s t :=
  canonical_mono hs ht hEF

theorem vc3_local_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (l m x y : D.Sigma) (e : D.Event),
      VisStrict D C →
      SupportedOn D C E₁ → SupportedOn D C E₂ →
      WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
      e ∈ E₁ → e ∉ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
      IsCanOn D C (E₁ ∩ E₂) l →
      IsCanOn D C (downset C e \ {e}) m →
      IsCanOn D C (E₁ \ {e}) x →
      IsCanOn D C E₂ y →
      D.merge l (D.merge m x (D.do_ m e)) y
        = D.merge m (D.merge l x y) (D.do_ m e) := by
  intro C E₁ E₂ l m x y e hvs _ _ hcl₁ _ he₁ he₂ _ hl hm hx hy
  have hmx : Le m x := le_of_subset hm hx (fun a ha =>
    ⟨downset_subset hcl₁ he₁ ha.1, ha.2⟩)
  have hlx : Le l x := le_of_subset hl hx (fun a ha =>
    ⟨ha.1, fun hae => he₂ (hae ▸ ha.2)⟩)
  have hly : Le l y := le_of_subset hl hy (fun a ha => ha.2)
  rw [merge_eq_union hmx (le_step m e),
    merge_eq_union hlx hly,
    merge_eq_union (le_trans hlx (le_union_left x (D.do_ m e))) hly,
    merge_eq_union (le_trans hmx (le_union_left x y)) (le_step m e),
    union_assoc, union_assoc]
  rw [union_comm (D.do_ m e) y]

/-! ## VC4 and VC5

Because every pair of events commutes, `lo^C_E` orders nothing, so the
downset of an event is the event itself and the base of CAUSAL-DELTA is
`sigma0`. That is also what makes VC5's base `sigma0`. -/

theorem le_sigma0 (a : D.Sigma) : Le D.sigma0 a := by
  refine ⟨fun p h => ?_, fun n h => ?_⟩ <;> rw [sigma0_eq] at h <;> exact absurd h (by simp)

theorem downset_eq (C : Ctx D) (e : D.Event) :
    downset C e \ {e} = (∅ : Set D.Event) := by
  ext x
  simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro (hx | hx)
  · exact fun hne => hne hx
  · intro _
    exfalso
    cases hx with
    | single h' => exact h'.2 (all_commute _ _)
    | tail _ h' => exact h'.2 (all_commute _ _)

theorem union_step_sigma0 (A : D.Sigma) (e : D.Event) :
    union A (D.do_ D.sigma0 e) = D.do_ A e := by
  refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
    simp [union, do_eq, step, sigma0_eq]

theorem vc4_causal_delta :
    ∀ (C : Ctx D) (U : Set D.Event) (A B : D.Sigma) (e : D.Event),
      VisStrict D C →
      SupportedOn D C U → WeaklyClosed D C U →
      e ∈ U → MaximalOn D C U e →
      IsCanOn D C (U \ {e}) A →
      IsCanOn D C (downset C e \ {e}) B →
      D.merge B A (D.do_ B e) = D.do_ A e := by
  letI : EventOrder D.toMRDTSig.toUpdateSig := Interface.rcOrder D
  intro C U A B e _ _ _ _ _ _ hB
  have hBinit : B = D.sigma0 := isCanonicalState_empty (downset_eq C e) hB
  subst hBinit
  show D.merge D.sigma0 A (D.do_ D.sigma0 e) = D.do_ A e
  rw [merge_eq_union (le_sigma0 A) (le_sigma0 _), union_step_sigma0]

theorem union_le_union {a b : D.Sigma} (h : Le a b) (c : D.Sigma) :
    Le (union a c) (union b c) := by
  refine ⟨fun p hp => ?_, fun n hn => ?_⟩
  · simp only [union, Bool.or_eq_true] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl (h.1 p hp)
    · exact Or.inr hp
  · simp only [union, Bool.or_eq_true] at hn ⊢
    rcases hn with hn | hn
    · exact Or.inl (h.2 n hn)
    · exact Or.inr hn

theorem union_pair (a b c : D.Sigma) :
    union (union a c) (union b c) = union (union a b) c := by
  refine Prod.ext (funext fun p => ?_) (funext fun n => ?_) <;>
    simp [union, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

theorem vc5_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (x₀ x₁ x₂ m : D.Sigma) (e : D.Event),
      VisStrict D C →
      SupportedOn D C E₁ → SupportedOn D C E₂ →
      WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
      e ∈ E₁ → e ∈ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
      IsCanOn D C ((E₁ ∩ E₂) \ {e}) x₀ →
      IsCanOn D C (downset C e \ {e}) m →
      IsCanOn D C (E₁ \ {e}) x₁ →
      IsCanOn D C (E₂ \ {e}) x₂ →
      D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
          (D.merge m x₂ (D.do_ m e))
        = D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e) := by
  intro C E₁ E₂ x₀ x₁ x₂ m e _ _ _ _ _ _ _ _ hx₀ hm hx₁ hx₂
  letI : EventOrder D.toMRDTSig.toUpdateSig := Interface.rcOrder D
  have hminit : m = D.sigma0 := isCanonicalState_empty (downset_eq C e) hm
  subst hminit
  have h₀₁ : Le x₀ x₁ := le_of_subset hx₀ hx₁ (fun a ha => ⟨ha.1.1, ha.2⟩)
  have h₀₂ : Le x₀ x₂ := le_of_subset hx₀ hx₂ (fun a ha => ⟨ha.1.2, ha.2⟩)
  rw [merge_eq_union (le_sigma0 x₀) (le_sigma0 _),
    merge_eq_union (le_sigma0 x₁) (le_sigma0 _),
    merge_eq_union (le_sigma0 x₂) (le_sigma0 _),
    merge_eq_union h₀₁ h₀₂,
    merge_eq_union (le_sigma0 _) (le_sigma0 _),
    merge_eq_union (union_le_union h₀₁ (D.do_ D.sigma0 e))
      (union_le_union h₀₂ (D.do_ D.sigma0 e))]
  exact union_pair x₁ x₂ (D.do_ D.sigma0 e)

theorem joinLaws : CanonicalJoinLawsOn D (fun _ => True) where
  vc1_merge_comm := vc1_merge_comm
  vc2_merge_init := fun C E s _ => vc2_merge_init C E s
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ =>
    vc3_local_redistribute C E₁ E₂ l m x y e
  vc4_causal_delta := fun C U A B e _ => vc4_causal_delta C U A B e
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ =>
    vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e

theorem obligations : Obligations D :=
  Obligations.ofCommuting laws all_commute joinLaws

/-! ## Clause 2: the compact fold agrees with the grow-only query

The specification drops superseded entries; the implementation marks them.
The two agree because, in a legal history, a write only ever names
identities allocated **before** it, and never its own. So "removed by a
later write" and "named by any write at all" are the same condition. -/

/-- A list where no write names its own identity, and no write names an
identity allocated after it. Both follow from honest issuance. -/
def Sane (pi : List D.Event) : Prop :=
  (∀ e ∈ pi, newId e.op ∉ overwrites e.op)
    ∧ ∀ pre f post, pi = pre ++ f :: post →
        ∀ e ∈ post, newId e.op ∉ overwrites f.op

theorem Sane.tail {e : D.Event} {rest : List D.Event} (h : Sane (e :: rest)) :
    Sane rest :=
  ⟨fun f hf => h.1 f (by simp [hf]),
   fun pre f post hsplit g hg => h.2 (e :: pre) f post (by rw [hsplit]; rfl) g hg⟩

theorem Sane.head_not_later {e : D.Event} {rest : List D.Event}
    (h : Sane (e :: rest)) {f : D.Event} (hf : f ∈ rest) :
    newId f.op ∉ overwrites e.op :=
  h.2 [] e rest rfl f hf

/-- **The compact fold.** An entry survives exactly when some write made it
and no write of the list names it. -/
theorem fold_live : ∀ (pi : List D.Event) (S : SpecState) (p : Nat × Nat),
    Sane pi →
    (p ∈ (pi.foldl (fun s e => sstep s e.op) S).1
      ↔ ((p ∈ S.1 ∨ ∃ e ∈ pi, (newId e.op, writeValue e.op) = p)
          ∧ ∀ f ∈ pi, p.1 ∉ overwrites f.op))
  | [], S, p, _ => by simp
  | e :: rest, S, p, hs => by
      show p ∈ ((rest.foldl (fun s f => sstep s f.op) (sstep S e.op)).1) ↔ _
      rw [fold_live rest (sstep S e.op) p hs.tail]
      have hmem : p ∈ (sstep S e.op).1 ↔
          (newId e.op, writeValue e.op) = p ∨ (p ∈ S.1 ∧ p.1 ∉ overwrites e.op) := by
        simp only [sstep, Finset.mem_insert, Finset.mem_filter]
        constructor
        · rintro (h | h)
          · exact Or.inl h.symm
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h.symm
          · exact Or.inr h
      rw [hmem]
      constructor
      · rintro ⟨(hhead | ⟨hpS, hpe⟩) | ⟨f, hf, hfp⟩, hnone⟩
        · refine ⟨Or.inr ⟨e, by simp, hhead⟩, fun f hf => ?_⟩
          rcases List.mem_cons.mp hf with rfl | hf
          · rw [← hhead]; exact hs.1 f (by simp)
          · exact hnone f hf
        · exact ⟨Or.inl hpS, fun f hf => by
            rcases List.mem_cons.mp hf with rfl | hf
            · exact hpe
            · exact hnone f hf⟩
        · refine ⟨Or.inr ⟨f, by simp [hf], hfp⟩, fun g hg => ?_⟩
          rcases List.mem_cons.mp hg with rfl | hg
          · rw [← hfp]; exact hs.head_not_later hf
          · exact hnone g hg
      · rintro ⟨hp, hnone⟩
        refine ⟨?_, fun f hf => hnone f (by simp [hf])⟩
        rcases hp with hpS | ⟨f, hf, hfp⟩
        · exact Or.inl (Or.inr ⟨hpS, hnone e (by simp)⟩)
        · rcases List.mem_cons.mp hf with rfl | hf
          · exact Or.inl (Or.inl hfp)
          · exact Or.inr ⟨f, hf, hfp⟩

/-! ## Honest issuance makes a causal replay sane -/

variable {C : Configuration D.toMRDTSig}

theorem time_ne {K : Ctx D} {a b : D.Event} (ha : a ∈ K.events) (hb : b ∈ K.events)
    (hne : a ≠ b) : a.time ≠ b.time := by
  obtain ⟨p, t, hL, ht⟩ := ha
  obtain ⟨p', t', hL', ht'⟩ := hb
  exact K.timestamps_distinct hL ht hL' ht' hne

/-- From `MintHonest`: the identity is the timestamp, it is not named by the
write itself, and every named identity was written by an observed event. -/
theorem issued (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {e : D.Event} (he : e ∈ C.events) :
    newId e.op = e.time ∧ newId e.op ∉ overwrites e.op
      ∧ ∀ n ∈ overwrites e.op, ∃ f, C.vis f e ∧ f ∈ C.events ∧ newId f.op = n := by
  obtain ⟨pi, hpi, -, hg⟩ := hmint e he
  rw [show issuance.CanIssue e (applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init pi)
        = issuance.CanIssue e (D.applyList D.sigma0 pi) from rfl] at hg
  obtain ⟨hid, hfresh, hborn⟩ := hg
  refine ⟨hid, fun hself => hfresh (hborn _ hself), fun n hn => ?_⟩
  obtain ⟨v, hv⟩ := hborn n hn
  obtain ⟨f, hf, hfp⟩ := (fst_applyList D.sigma0 pi (n, v)).mp hv |>.resolve_left
    (by rw [sigma0_eq]; simp)
  have hmem := (hpi.2 f).mp hf
  exact ⟨f, hmem.2, hmem.1, (congrArg Prod.fst hfp).symm⟩

/-- A `vis`-respecting replay of honest events is sane. -/
theorem sane_of_respects (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {pi : List D.Event} (hsub : ∀ a ∈ pi, a ∈ C.events)
    (hr : respects pi C.vis) : Sane pi := by
  refine ⟨fun e he => (issued hmint (hsub e he)).2.1, ?_⟩
  intro pre f post hsplit e he hname
  obtain ⟨g, hvis, hgC, hgn⟩ := (issued hmint (hsub f (by rw [hsplit]; simp))).2.2
    _ hname
  have hge : g = e := by
    by_contra hne
    refine time_ne (K := C.replayContext)
      (by rw [Configuration.replayContext_events]; exact hgC)
      (by rw [Configuration.replayContext_events]
          exact hsub e (by rw [hsplit]; simp [he])) hne ?_
    rw [← (issued hmint hgC).1, ← (issued hmint (hsub e
      (by rw [hsplit]; simp [he]))).1, hgn]
  subst hge
  have hrp : respects (pre ++ f :: post) C.vis := by rw [← hsplit]; exact hr
  exact (List.pairwise_cons.mp (List.pairwise_append.mp hrp).2.1).1 g he hvis

/-! ## The query agrees -/

theorem readValues_eq {K : Ctx D} {E : Set D.Event} {s : D.Sigma}
    (hs : IsCanOn D K E s) :
    readValues s
      = {v | ∃ i, (∃ e ∈ E, (newId e.op, writeValue e.op) = (i, v))
          ∧ ∀ f ∈ E, i ∉ overwrites f.op} := by
  ext v
  simp only [readValues, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hb, hg⟩
    refine ⟨i, ?_, fun f hf hn => ?_⟩
    · obtain ⟨e, he, hp⟩ := (canonical_fst hs (i, v)).mp hb
      exact ⟨e, he, hp.symm⟩
    · exact absurd ((canonical_snd hs i).mpr ⟨f, hf, hn⟩) (by rw [hg]; simp)
  · rintro ⟨i, ⟨e, he, hp⟩, hg⟩
    refine ⟨i, (canonical_fst hs (i, v)).mpr ⟨e, he, hp.symm⟩, ?_⟩
    cases hgi : s.2 i
    · rfl
    · obtain ⟨f, hf, hn⟩ := (canonical_snd hs i).mp hgi
      exact absurd hn (hg f hf)

/-! ## The sequential premise

Clause 1 accepts any enumeration, since `lo^C_E` has no edges. The one that
explains the query is the replay in **timestamp order**. A configuration's
`causal_mono` says visibility increases the timestamp, so that order is
causal, and a write then names only identities already allocated, which is
exactly what the specification's legality asks.
-/

/-- Order events by timestamp. -/
def byTime (a b : D.Event) : Bool := decide (a.time ≤ b.time)

/-- The explaining replay. -/
def arrange (pi : List D.Event) : List D.Event := pi.mergeSort byTime

theorem arrange_perm (pi : List D.Event) : (arrange pi).Perm pi :=
  List.mergeSort_perm _ _

theorem arrange_sorted (pi : List D.Event) :
    (arrange pi).Pairwise (fun a b => a.time ≤ b.time) := by
  have := List.pairwise_mergeSort (le := byTime)
    (by intro a b c hab hbc
        simp only [byTime, decide_eq_true_eq] at hab hbc ⊢
        exact Nat.le_trans hab hbc)
    (by intro a b
        simp only [byTime, Bool.or_eq_true, decide_eq_true_eq]
        exact Nat.le_total _ _) pi
  exact this.imp (by intro a b h; simpa only [byTime, decide_eq_true_eq] using h)

/-- The identities allocated by a replay. -/
theorem fold_born : ∀ (l : List D.Event) (S : SpecState),
    (l.foldl (fun s e => sstep s e.op) S).2
      = S.2 ∪ (l.map (fun e => newId e.op)).toFinset
  | [], S => by simp
  | e :: l, S => by
      show (l.foldl (fun s f => sstep s f.op) (sstep S e.op)).2 = _
      rw [fold_born l (sstep S e.op)]
      simp only [sstep, List.map_cons, List.toFinset_cons]
      ext n
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset]
      tauto

/-- **The machine accepts a timestamp-ordered honest replay.** Freshness
comes from distinct timestamps; the named identities are already allocated
because visibility increases the timestamp, so their writes sit in the
prefix. -/
theorem runs_updates (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {E : Set D.Event} (hsub : ∀ e ∈ E, e ∈ C.events)
    (hclosed : ∀ a b, C.replayContext.vis a b → b ∈ E → a ∈ E) :
    ∀ (pre l : List D.Event) (S : SpecState),
      (pre ++ l).Nodup → (∀ a, a ∈ pre ++ l ↔ a ∈ E) →
      (pre ++ l).Pairwise (fun a b => a.time ≤ b.time) →
      S.2 = (pre.map (fun e => newId e.op)).toFinset →
      Runs specMachine.transition S
        (DeterministicSpec.updateLabels (l.map Op.op))
        ((l.map Op.op).foldl sstep S)
  | _, [], S, _, _, _, _ => Runs.nil _
  | pre, e :: l, S, hnd, hall, hsort, hS => by
      have heE : e ∈ E := (hall e).mp (by simp)
      obtain ⟨hid, -, hborn⟩ := issued hmint (hsub e heE)
      have hev : ∀ a ∈ pre ++ e :: l, a ∈ C.replayContext.events := by
        intro a ha
        rw [Configuration.replayContext_events]
        exact hsub a ((hall a).mp ha)
      have hndA : (pre ++ e :: l).Nodup := hnd
      have hfresh : newId e.op ∉ S.2 := by
        rw [hS]
        simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]
        intro f hf hfn
        have hfpre : f ∈ pre ++ e :: l := List.mem_append.mpr (Or.inl hf)
        have hne : f ≠ e := by
          intro hfe
          rw [List.nodup_append] at hndA
          exact hndA.2.2 f hf e (by simp) hfe
        have hfE : f ∈ E := (hall f).mp hfpre
        have hfid := (issued hmint (hsub f hfE)).1
        refine time_ne (hev f hfpre) (hev e (by simp)) hne ?_
        show f.time = e.time
        rw [← hfid, ← hid]
        exact hfn
      have hnamed : ∀ n ∈ overwrites e.op, n ∈ S.2 := by
        intro n hn
        obtain ⟨g, hvis, -, hgn⟩ := hborn n hn
        have hgE : g ∈ E := hclosed g e hvis heE
        have hglt : g.time < e.time := C.causal_mono hvis
        have hgmem : g ∈ pre ++ e :: l := (hall g).mpr hgE
        have hgpre : g ∈ pre := by
          rcases List.mem_append.mp hgmem with hg | hg
          · exact hg
          · rcases List.mem_cons.mp hg with hge | hg
            · exact absurd (hge ▸ hglt) (lt_irrefl _)
            · have hle := (List.pairwise_cons.mp
                (List.pairwise_append.mp hsort).2.1).1 g hg
              exact absurd hglt (Nat.not_lt.mpr hle)
        rw [hS]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨g, hgpre, hgn⟩)
      exact Runs.cons (l := .update e.op) ⟨hfresh, hnamed, rfl⟩
        (runs_updates hmint hsub hclosed (pre ++ [e]) l (sstep S e.op)
          (by simpa using hnd) (by intro a; simpa using hall a)
          (by simpa using hsort)
          (by simp [sstep, hS]))

/-! ## Assembling clause 2 -/

/-- The grow-only query, read off the replay. -/
theorem readValues_list (pi : List D.Event) :
    readValues (D.applyList D.sigma0 pi)
      = {v | ∃ i, (∃ e ∈ pi, (newId e.op, writeValue e.op) = (i, v))
          ∧ ∀ f ∈ pi, i ∉ overwrites f.op} := by
  ext v
  simp only [readValues, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hb, hg⟩
    refine ⟨i, ?_, fun f hf hn => ?_⟩
    · obtain ⟨e, he, hp⟩ := (fst_applyList D.sigma0 pi (i, v)).mp hb |>.resolve_left
        (by rw [sigma0_eq]; simp)
      exact ⟨e, he, hp.symm⟩
    · have := (snd_applyList D.sigma0 pi i).mpr (Or.inr ⟨f, hf, hn⟩)
      rw [hg] at this
      exact absurd this (by simp)
  · rintro ⟨i, ⟨e, he, hp⟩, hg⟩
    refine ⟨i, (fst_applyList D.sigma0 pi (i, v)).mpr (Or.inr ⟨e, he, hp.symm⟩), ?_⟩
    cases hgi : (D.applyList D.sigma0 pi).2 i
    · rfl
    · obtain ⟨f, hf, hn⟩ := (snd_applyList D.sigma0 pi i).mp hgi |>.resolve_left
        (by rw [sigma0_eq]; simp)
      exact absurd hn (hg f hf)

/-- A timestamp-ordered honest replay is sane. -/
theorem sane_arrange (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {E : Set D.Event} (hsub : ∀ e ∈ E, e ∈ C.events)
    {pi : List D.Event} (hall : ∀ a, a ∈ pi ↔ a ∈ E)
    (hsort : pi.Pairwise (fun a b => a.time ≤ b.time)) : Sane pi := by
  refine ⟨fun e he => (issued hmint (hsub e ((hall e).mp he))).2.1, ?_⟩
  intro pre f post hsplit e he hname
  have hfpi : f ∈ pi := by rw [hsplit]; simp
  have hepi : e ∈ pi := by rw [hsplit]; simp [he]
  obtain ⟨g, hvis, hgC, hgn⟩ :=
    (issued hmint (hsub f ((hall f).mp hfpi))).2.2 _ hname
  have hge : g = e := by
    by_contra hne
    refine time_ne (K := C.replayContext)
      (by rw [Configuration.replayContext_events]; exact hgC)
      (by rw [Configuration.replayContext_events]; exact hsub e ((hall e).mp hepi))
      hne ?_
    rw [← (issued hmint hgC).1,
      ← (issued hmint (hsub e ((hall e).mp hepi))).1, hgn]
  subst hge
  have hlt : g.time < f.time := C.causal_mono hvis
  have hle : f.time ≤ g.time := by
    rw [hsplit] at hsort
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hsort).2.1).1 g he
  exact absurd hlt (Nat.not_lt.mpr hle)

/-- **The sequential premise, execution-scoped.** -/
theorem historySound : Soundness.HistorySound D historySpec issuance := by
  rintro C hmint E hsub hclosed ⟨pi, hpi⟩ q
  have hperm := arrange_perm pi
  have hnd : (arrange pi).Nodup := hperm.nodup_iff.mpr hpi.1
  have hall : ∀ a, a ∈ arrange pi ↔ a ∈ E := fun a =>
    (hperm.mem_iff).trans (hpi.2 a)
  have hsort := arrange_sorted pi
  have hsane : Sane (arrange pi) := sane_arrange hmint hsub hall hsort
  refine ⟨arrange pi, ⟨hnd, hall⟩, ?_, ?_⟩
  · exact hnd.imp (fun {_ _} _ =>
      Soundness.paperOrder_false rc_non_comm_uniform all_commute _ _ _ _)
  · have hlabels : projectedUpdates (D := D.toMRDTSig) (arrange pi)
        = DeterministicSpec.updateLabels ((arrange pi).map Op.op) := by
      simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
        Function.comp]
    rw [hlabels]
    refine ⟨_, Runs.append
      (m := ((arrange pi).map Op.op).foldl sstep ((∅ : Finset (Nat × Nat)), ∅))
      (runs_updates hmint hsub hclosed [] (arrange pi) _
        (by simpa using hnd) (by intro a; simpa using hall a)
        (by simpa using hsort) rfl)
      (Runs.cons (l := SeqLabel.query q _) ⟨rfl, ?_⟩ (Runs.nil _))⟩
    show D.query (applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init (arrange pi)) q
      = {v | ∃ u, (u, v) ∈ (((arrange pi).map Op.op).foldl sstep
          ((∅ : Finset (Nat × Nat)), ∅)).1}
    rw [show applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init (arrange pi)
          = D.applyList D.sigma0 (arrange pi) from rfl]
    show readValues (D.applyList D.sigma0 (arrange pi)) = _
    rw [readValues_list]
    ext v
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hmk, hg⟩
      refine ⟨i, ?_⟩
      rw [show ((arrange pi).map Op.op).foldl sstep ((∅ : Finset (Nat × Nat)), ∅)
            = (arrange pi).foldl (fun s e => sstep s e.op) (∅, ∅) from by
          simp [List.foldl_map]]
      exact (fold_live (arrange pi) (∅, ∅) (i, v) hsane).mpr
        ⟨Or.inr (by obtain ⟨e, he, hp⟩ := hmk; exact ⟨e, he, hp⟩), hg⟩
    · rintro ⟨i, hmem⟩
      rw [show ((arrange pi).map Op.op).foldl sstep ((∅ : Finset (Nat × Nat)), ∅)
            = (arrange pi).foldl (fun s e => sstep s e.op) (∅, ∅) from by
          simp [List.foldl_map]] at hmem
      obtain ⟨hor, hg⟩ := (fold_live (arrange pi) (∅, ∅) (i, v) hsane).mp hmem
      exact ⟨i, hor.resolve_left (by simp), hg⟩

end LeanProofs1.Implementations.MVRegisterHistorical
