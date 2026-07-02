import Sal.MRDTs.Metatheory.Adequacy

/-!
# THE DISCHARGED MRDTs — all instance proofs in one file

Every RDT taken end-to-end through the metatheory, with its full discharge:

| MRDT | end-to-end theorem | route |
|---|---|---|
| G-Set (LCA-blind) | `gset_ra_linearizable3_cd` | unconditional delta |
| Counter (`a+b−l`) | `counter_ra_linearizable3_cd` | unconditional delta |
| **OR-Set** (production mirror) | `ORSet_ra_linearizable3` | feasible delta + CD |
| **OR-Set-efficient** (production mirror) | `ORSetE_ra_linearizable3` | feasible delta + CD |
| **Enable-wins flag** (production mirror) | `EWFlag_ra_linearizable3` | direct full-closure join |

The three production mirrors are faithful to `Sal/MRDTs/{OR_Set,
OR_Set_Efficient, Enable_Wins_Flag}` (deviations documented at the mirror
definitions: `decide`-normalization, kept Boolean association,
`mysel`-semantics for the Enable-wins map). σ-characterizations: an OR-Set
tag is live iff added with no vis-later same-element `Rem` (the LCA is the
tombstone); ORSetE adds the same-replica eviction killer (closed by
same-replica totality); Enable-wins counts per-key Enables and reads flag
liveness through the counter comparison (certified exactly where the
known-broken global-counter sibling fails — see the `fa ∧ ¬fb` corner of
`EWFlag_joinLemma3F`). The commuting class is covered generically by
`cdVC3_of_all_comm` in `Adequacy.lean`.
-/

namespace Sal.Metatheory

open Sal.Emulation
open Classical

/-! ## G-Set -/

/-- Every pair of G-Set events commutes (insert-insert). -/
theorem GSet_all_comm : ∀ a b : Op GSetCond.AppOp,
    GSetCond.toCRDTSig.commutes a b :=
  fun a b s => (Set.insert_comm a.2.2 b.2.2 s).symm

/-- G-Set's `rc` is constantly `Either`. -/
theorem GSet_rc_either : ∀ o₁ o₂ : Op GSetCond.AppOp,
    GSetCond.toCRDTSig.rc o₁ o₂ = RcRes.Either :=
  fun _ _ => rfl

/-- The update-layer bundle for G-Set: `rc = Either` kills every rc premise. -/
theorem GSet_updateVCs : UpdateVCs GSetCond.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (GSet_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [GSet_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [GSet_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [GSet_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

/-- G-Set `update`, unfolded to `Set Nat` (where the instances live). -/
theorem GSet_update_eq (s : Set Nat) (e : Op GSetCond.AppOp) :
    GSetCond.update s e = insert e.2.2 s := rfl

/-- G-Set `mergeL`, unfolded to `Set Nat`. -/
theorem GSet_mergeL_eq (l a b : Set Nat) :
    GSetCond.mergeL l a b = a ∪ b := rfl

/-- The ternary core bundle for G-Set (`mergeL _ a b = a ∪ b`, LCA-blind). -/
theorem GSet_coreVCs3 : CoreVCs3 GSetCond := by
  refine ⟨GSet_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    exact Set.union_comm a b
  · intro s
    exact Set.empty_union s
  · intro l a b e
    simp only [GSet_update_eq, GSet_mergeL_eq]
    apply Set.ext
    intro x
    simp only [Set.mem_union, Set.mem_insert_iff]
    tauto
  · intro a e π₀ π₂ _ _
    simp only [GSet_update_eq, GSet_mergeL_eq]
    exact Set.insert_union

/-! ## Counter -/

/-- The counter MRDT: `mergeL l a b = a + b - l`. The LCA argument prevents
double-counting — the mathematically canonical example of an MRDT whose merge
*needs* the LCA. Its binary slice `merge a b = mergeL 0 a b = a + b` is the
paper's CRDT collapse — and it is exactly this slice that breaks `lem_0op`. -/
def Counter : ConditionedMRDTSig where
  State := Int
  dec_state := inferInstance
  init := 0
  AppOp := Unit
  dec_op := inferInstance
  Query := Unit
  Value := Int
  update := fun s _ => s + 1
  merge := fun a b => a + b
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => a + b - l
  merge_init_slice := fun a b => by show a + b - 0 = a + b; omega
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem Counter_update_eq (s : Int) (e : Op Counter.AppOp) :
    Counter.update s e = s + 1 := rfl

theorem Counter_merge_eq (a b : Int) :
    Counter.toCRDTSig.merge a b = a + b := rfl

theorem Counter_mergeL_eq (l a b : Int) :
    Counter.mergeL l a b = a + b - l := rfl

theorem Counter_init_eq : Counter.init = (0 : Int) := rfl

/-- Every pair of counter events commutes. -/
theorem Counter_all_comm : ∀ a b : Op Counter.AppOp,
    Counter.toCRDTSig.commutes a b :=
  fun _ _ _ => rfl

theorem Counter_rc_either : ∀ o₁ o₂ : Op Counter.AppOp,
    Counter.toCRDTSig.rc o₁ o₂ = RcRes.Either :=
  fun _ _ => rfl

theorem Counter_updateVCs : UpdateVCs Counter.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (Counter_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [Counter_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [Counter_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [Counter_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

/-- The ternary core bundle for the counter — note `lem_0op3` holds exactly
because the LCA argument absorbs the double count:
`(a+1) + (b+1) - (l+1) = (a + b - l) + 1`. -/
theorem Counter_coreVCs3 : CoreVCs3 Counter := by
  refine ⟨Counter_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    simp only [Counter_mergeL_eq]
    have go : ∀ l' a' b' : Int, a' + b' - l' = b' + a' - l' := by omega
    exact go l a b
  · intro s
    simp only [Counter_mergeL_eq, Counter_init_eq]
    have go : ∀ s' : Int, (0 : Int) + s' - 0 = s' := by omega
    exact go s
  · intro l a b e
    simp only [Counter_update_eq, Counter_mergeL_eq]
    have go : ∀ l' a' b' : Int,
        a' + 1 + (b' + 1) - (l' + 1) = a' + b' - l' + 1 := by omega
    exact go l a b
  · intro a e π₀ π₂ _ _
    simp only [Counter_update_eq, Counter_mergeL_eq]
    have go : ∀ x y z : Int, y + 1 + z - x = y + z - x + 1 := by omega
    exact go _ _ _

/-- The Counter satisfies the delta contract — the **group instance**
(`mergeL l a b = a + (b − l)`; deltas are translation-invariant). Note it
satisfies neither `merge_idem` nor any lattice law: the binary CD route is
closed to it, the ternary one is not. -/
theorem Counter_deltaVCs3 : DeltaVCs3 Counter := by
  constructor
  · intro m x₀ x₁ x₂ c
    simp only [Counter_mergeL_eq]
    have go : ∀ m' x₀' x₁' x₂' c' : Int,
        x₁' + c' - m' + (x₂' + c' - m') - (x₀' + c' - m')
          = x₁' + x₂' - x₀' + c' - m' := by omega
    exact go m x₀ x₁ x₂ c
  · intro l m x c y
    simp only [Counter_mergeL_eq]
    have go : ∀ l' m' x' c' y' : Int,
        x' + c' - m' + y' - l' = x' + y' - l' + c' - m' := by omega
    exact go l m x c y

/-- G-Set satisfies the delta contract — the **lattice instance** (LCA-blind
`mergeL` over an ACI join; the laws collapse to ACI consequences). -/
theorem GSet_deltaVCs3 : DeltaVCs3 GSetCond := by
  constructor
  · intro m x₀ x₁ x₂ c
    simp only [GSet_mergeL_eq]
    apply Set.ext
    intro y
    simp only [Set.mem_union]
    tauto
  · intro l m x c y
    simp only [GSet_mergeL_eq]
    apply Set.ext
    intro z
    simp only [Set.mem_union]
    tauto

/-- The ternary Join Lemma for the Counter, via the CD route. -/
theorem Counter_joinLemma3_cd : JoinLemma3 Counter :=
  join_lemma3_of_cd Counter_coreVCs3 Counter_deltaVCs3
    (cdVC3_of_all_comm Counter_coreVCs3 Counter_all_comm)

/-- The ternary Join Lemma for G-Set, via the CD route. -/
theorem GSet_joinLemma3_cd : JoinLemma3 GSetCond :=
  join_lemma3_of_cd GSet_coreVCs3 GSet_deltaVCs3
    (cdVC3_of_all_comm GSet_coreVCs3 GSet_all_comm)

open LabeledTS in
/-- End-to-end RA-linearizability for the Counter via the delta/CD route. -/
theorem counter_ra_linearizable3_cd
    (C : Configuration Counter)
    (hReach : (labeledTS3 Counter).ReachableFrom
      (initConfig Counter trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_join Counter_joinLemma3_cd C hReach

open LabeledTS in
/-- End-to-end RA-linearizability for G-Set via the delta/CD route. -/
theorem gset_ra_linearizable3_cd
    (C : Configuration GSetCond)
    (hReach : (labeledTS3 GSetCond).ReachableFrom
      (initConfig GSetCond trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_join GSet_joinLemma3_cd C hReach


/-! ## §1. The OR-Set mirror -/

/-- OR-Set ops (production `app_op_t`). -/
inductive ORSetOp : Type where
  | add : ℕ → ORSetOp
  | rem : ℕ → ORSetOp
deriving DecidableEq

/-- Production `do_`: `Add e` at ts stakes the tag `(ts, e)`; `Rem e` filters
every tag of `e`. -/
def orUpdate (s : (ℕ × ℕ) → Bool) (o : Op ORSetOp) : (ℕ × ℕ) → Bool :=
  match o.2.2 with
  | .add e => fun t => s t || decide (t = (o.1, e))
  | .rem e => fun t => s t && !(decide (t.2 = e))

/-- Production three-way merge: `(l ∩ a ∩ b) ∪ (a ∖ l) ∪ (b ∖ l)` — the
T8.6 shape, on tagged elements. -/
def orMergeL (l a b : (ℕ × ℕ) → Bool) : (ℕ × ℕ) → Bool :=
  fun t => (l t && (a t && b t)) || ((a t && !(l t)) || (b t && !(l t)))

/-- Production `rc`: Add-vs-Rem on the same element is ordered rem-first
(add-wins); all other pairs `Either`. -/
def orRc (o₁ o₂ : Op ORSetOp) : RcRes :=
  match o₁.2.2, o₂.2.2 with
  | .add e₁, .rem e₂ => if e₁ = e₂ then RcRes.Snd_then_fst else RcRes.Either
  | .rem e₁, .add e₂ => if e₁ = e₂ then RcRes.Fst_then_snd else RcRes.Either
  | _, _ => RcRes.Either

/-- The OR-Set MRDT (mirror of `Sal/MRDTs/OR_Set/OR_Set_MRDT.lean`). -/
noncomputable def ORSet : ConditionedMRDTSig where
  State := (ℕ × ℕ) → Bool
  dec_state := fun _ _ => Classical.propDecidable _
  init := fun _ => false
  AppOp := ORSetOp
  dec_op := inferInstance
  Query := Unit
  Value := (ℕ × ℕ) → Bool
  update := orUpdate
  merge := fun a b => orMergeL (fun _ => false) a b
  query := fun s _ => s
  rc := orRc
  mergeL := orMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem ORSet_update_eq (s : ORSet.State) (o : Op ORSet.AppOp) :
    ORSet.update s o = orUpdate s o := rfl

theorem ORSet_mergeL_eq (l a b : ORSet.State) :
    ORSet.mergeL l a b = orMergeL l a b := rfl

theorem ORSet_init_eq : ORSet.init = fun _ => false := rfl

/-! ## §2. The OR-Set-efficient mirror -/

/-- Production `do_`: `Add e` at (ts, rid) first filters the prior
`(rid, _, e)` tag, then stakes `(rid, ts, e)`; `Rem e` filters the element. -/
def orEUpdate (s : (ℕ × ℕ × ℕ) → Bool) (o : Op ORSetOp) :
    (ℕ × ℕ × ℕ) → Bool :=
  match o.2.2 with
  | .add e => fun t =>
      (s t && !(decide (o.2.1 = t.1 ∧ e = t.2.2)))
        || decide (t = (o.2.1, o.1, e))
  | .rem e => fun t => s t && !(decide (e = t.2.2))

/-- Same three-way merge formula over `(rid, ts, elem)` triples. -/
def orEMergeL (l a b : (ℕ × ℕ × ℕ) → Bool) : (ℕ × ℕ × ℕ) → Bool :=
  fun t => (l t && (a t && b t)) || ((a t && !(l t)) || (b t && !(l t)))

/-- The OR-Set-efficient MRDT (mirror of
`Sal/MRDTs/OR_Set_Efficient/OR_Set_Efficient_MRDT.lean`). -/
noncomputable def ORSetE : ConditionedMRDTSig where
  State := (ℕ × ℕ × ℕ) → Bool
  dec_state := fun _ _ => Classical.propDecidable _
  init := fun _ => false
  AppOp := ORSetOp
  dec_op := inferInstance
  Query := Unit
  Value := (ℕ × ℕ × ℕ) → Bool
  update := orEUpdate
  merge := fun a b => orEMergeL (fun _ => false) a b
  query := fun s _ => s
  rc := orRc
  mergeL := orEMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem ORSetE_update_eq (s : ORSetE.State) (o : Op ORSetE.AppOp) :
    ORSetE.update s o = orEUpdate s o := rfl

theorem ORSetE_mergeL_eq (l a b : ORSetE.State) :
    ORSetE.mergeL l a b = orEMergeL l a b := rfl

/-! ## §3. The Enable-wins flag mirror -/

/-- Enable-wins ops (production `app_op_t`). -/
inductive EWOp : Type where
  | enable
  | disable
deriving DecidableEq

/-- Production `merge_cf`: counter `a + b − l` (ℕ-truncated, as in
production), flag by the four-case enable-wins rule. -/
def ewMergeCF (l a b : ℕ × Bool) : ℕ × Bool :=
  (a.1 + b.1 - l.1,
    if a.2 && b.2 then true
    else if !a.2 && !b.2 then false
    else if a.2 then decide (a.1 > l.1)
    else decide (b.1 > l.1))

/-- Production `do_` through `mysel`: `Enable` bumps this replica's counter
and sets its flag; `Disable` clears every replica's flag. -/
def ewUpdate (s : ℕ → ℕ × Bool) (o : Op EWOp) : ℕ → ℕ × Bool :=
  match o.2.2 with
  | .enable => fun k => if k = o.2.1 then ((s o.2.1).1 + 1, true) else s k
  | .disable => fun k => ((s k).1, false)

/-- The Enable-wins flag MRDT (mirror of
`Sal/MRDTs/Enable_Wins_Flag/Enable_Wins_Flag_MRDT.lean`, `mysel`-semantics —
see the file header for the domain-tracking deviation). -/
noncomputable def EWFlag : ConditionedMRDTSig where
  State := ℕ → ℕ × Bool
  dec_state := fun _ _ => Classical.propDecidable _
  init := fun _ => (0, false)
  AppOp := EWOp
  dec_op := inferInstance
  Query := Unit
  Value := ℕ → ℕ × Bool
  update := ewUpdate
  merge := fun a b => fun k => ewMergeCF ((0 : ℕ), false) (a k) (b k)
  query := fun s _ => s
  rc := fun o₁ o₂ =>
    match o₁.2.2, o₂.2.2 with
    | .enable, .disable => RcRes.Snd_then_fst
    | .disable, .enable => RcRes.Fst_then_snd
    | _, _ => RcRes.Either
  mergeL := fun l a b => fun k => ewMergeCF (l k) (a k) (b k)
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem EWFlag_update_eq (s : EWFlag.State) (o : Op EWFlag.AppOp) :
    EWFlag.update s o = ewUpdate s o := rfl

theorem EWFlag_mergeL_eq (l a b : EWFlag.State) :
    EWFlag.mergeL l a b = fun k => ewMergeCF (l k) (a k) (b k) := rfl

theorem EWFlag_init_eq : EWFlag.init = fun _ => ((0 : ℕ), false) := rfl

/-! ## §6. The slim core's merge law holds unconditionally for all three -/

/-- OR-Set `mergeL` is commutative in its branch arguments. -/
theorem ORSet_mergeL_comm (l a b : ORSet.State) :
    ORSet.mergeL l a b = ORSet.mergeL l b a := by
  funext t
  show orMergeL l a b t = orMergeL l b a t
  unfold orMergeL
  cases l t <;> cases a t <;> cases b t <;> rfl

/-- OR-Set-efficient `mergeL` is commutative in its branch arguments. -/
theorem ORSetE_mergeL_comm (l a b : ORSetE.State) :
    ORSetE.mergeL l a b = ORSetE.mergeL l b a := by
  funext t
  show orEMergeL l a b t = orEMergeL l b a t
  unfold orEMergeL
  cases l t <;> cases a t <;> cases b t <;> rfl

/-- Enable-wins `mergeL` is commutative in its branch arguments. -/
theorem EWFlag_mergeL_comm (l a b : EWFlag.State) :
    EWFlag.mergeL l a b = EWFlag.mergeL l b a := by
  funext k
  show ewMergeCF (l k) (a k) (b k) = ewMergeCF (l k) (b k) (a k)
  unfold ewMergeCF
  cases h_a : (a k).2 <;> cases h_b : (b k).2 <;>
    simp [h_a, h_b] <;> omega

/-! ## The OR-Set discharge -/

/-! ## §1. Pointwise infrastructure -/

/-- Updates are pointwise: agreement at a point is transported. -/
theorem orUpdate_pointwise (a b : ORSet.State) (o : Op ORSet.AppOp)
    (p : ℕ × ℕ) (h : a p = b p) :
    ORSet.update a o p = ORSet.update b o p := by
  rcases o with ⟨ts, rid, op⟩
  cases op with
  | add e =>
    show (a p || decide (p = (ts, e))) = (b p || decide (p = (ts, e)))
    rw [h]
  | rem e =>
    show (a p && !(decide (p.2 = e))) = (b p && !(decide (p.2 = e)))
    rw [h]

/-- Folds transport pointwise agreement (off any fixed point, in particular). -/
theorem orsApplySeq_agree {a b : ORSet.State}
    (π : List (Op ORSet.AppOp)) (p : ℕ × ℕ) (h : a p = b p) :
    applySeq ORSet.toCRDTSig a π p = applySeq ORSet.toCRDTSig b π p := by
  induction π generalizing a b with
  | nil => exact h
  | cons o π ih => exact ih (orUpdate_pointwise a b o p h)

/-! ## §2. Commutation classification -/

theorem ORSet_commutes_symm {o₁ o₂ : Op ORSet.AppOp}
    (h : ORSet.toCRDTSig.commutes o₁ o₂) :
    ORSet.toCRDTSig.commutes o₂ o₁ :=
  fun s => (h s).symm

theorem ORSet_comm_add_add (ts₁ r₁ x₁ ts₂ r₂ x₂ : ℕ) :
    ORSet.toCRDTSig.commutes (ts₁, r₁, ORSetOp.add x₁)
      (ts₂, r₂, ORSetOp.add x₂) := by
  intro s
  funext p
  show ((s p || decide (p = (ts₁, x₁))) || decide (p = (ts₂, x₂)))
     = ((s p || decide (p = (ts₂, x₂))) || decide (p = (ts₁, x₁)))
  cases hs : s p <;> cases h1 : decide (p = (ts₁, x₁)) <;>
    cases h2 : decide (p = (ts₂, x₂)) <;> rfl

theorem ORSet_comm_rem_rem (ts₁ r₁ x₁ ts₂ r₂ x₂ : ℕ) :
    ORSet.toCRDTSig.commutes (ts₁, r₁, ORSetOp.rem x₁)
      (ts₂, r₂, ORSetOp.rem x₂) := by
  intro s
  funext p
  show ((s p && !(decide (p.2 = x₁))) && !(decide (p.2 = x₂)))
     = ((s p && !(decide (p.2 = x₂))) && !(decide (p.2 = x₁)))
  cases hs : s p <;> cases h1 : decide (p.2 = x₁) <;>
    cases h2 : decide (p.2 = x₂) <;> rfl

theorem ORSet_comm_add_rem_ne (ts₁ r₁ x ts₂ r₂ y : ℕ) (hxy : x ≠ y) :
    ORSet.toCRDTSig.commutes (ts₁, r₁, ORSetOp.add x)
      (ts₂, r₂, ORSetOp.rem y) := by
  intro s
  funext p
  show ((s p || decide (p = (ts₁, x))) && !(decide (p.2 = y)))
     = ((s p && !(decide (p.2 = y))) || decide (p = (ts₁, x)))
  by_cases hp : p = (ts₁, x)
  · subst hp
    have hy : decide (((ts₁, x) : ℕ × ℕ).2 = y) = false :=
      decide_eq_false hxy
    rw [hy, decide_eq_true (show ((ts₁, x) : ℕ × ℕ) = (ts₁, x) from rfl)]
    cases s (ts₁, x) <;> rfl
  · rw [decide_eq_false hp]
    cases hs : s p <;> cases hd : decide (p.2 = y) <;> rfl

theorem ORSet_ncomm_add_rem (ts₁ r₁ ts₂ r₂ x : ℕ) :
    ¬ ORSet.toCRDTSig.commutes (ts₁, r₁, ORSetOp.add x)
      (ts₂, r₂, ORSetOp.rem x) := by
  intro h
  have h0 := congrFun (h ORSet.init) (ts₁, x)
  have h0' : ((false || decide (((ts₁, x) : ℕ × ℕ) = (ts₁, x)))
      && !(decide (((ts₁, x) : ℕ × ℕ).2 = x)))
      = ((false && !(decide (((ts₁, x) : ℕ × ℕ).2 = x)))
      || decide (((ts₁, x) : ℕ × ℕ) = (ts₁, x))) := h0
  simp at h0'

/-- The classification: an `Add x` fails to commute only with `Rem x`. -/
theorem ORSet_ncomm_add_dest {ts r x : ℕ} {o : Op ORSet.AppOp}
    (h : ¬ ORSet.toCRDTSig.commutes (ts, r, ORSetOp.add x) o) :
    o.2.2 = ORSetOp.rem x := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add y => exact absurd (ORSet_comm_add_add ts r x ts' r' y) h
  | rem y =>
    by_cases hxy : x = y
    · subst hxy; rfl
    · exact absurd (ORSet_comm_add_rem_ne ts r x ts' r' y hxy) h

/-- The classification: a `Rem x` fails to commute only with `Add x`. -/
theorem ORSet_ncomm_rem_dest {ts r x : ℕ} {o : Op ORSet.AppOp}
    (h : ¬ ORSet.toCRDTSig.commutes (ts, r, ORSetOp.rem x) o) :
    o.2.2 = ORSetOp.add x := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add y =>
    by_cases hxy : y = x
    · subst hxy; rfl
    · exact absurd
        (ORSet_commutes_symm (ORSet_comm_add_rem_ne ts' r' y ts r x hxy)) h
  | rem y => exact absurd (ORSet_comm_rem_rem ts r x ts' r' y) h

/-! ## §3. The update layer of `CoreVCs3CD` -/

theorem ORSet_no_rc_chain :
    ∀ o₁ o₂ o₃ : Op ORSet.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (ORSet.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         ORSet.toCRDTSig.rc o₂ o₃ = RcRes.Fst_then_snd) := by
  rintro ⟨ts₁, r₁, op₁⟩ ⟨ts₂, r₂, op₂⟩ ⟨ts₃, r₃, op₃⟩ _ _ ⟨h1, h2⟩
  cases op₂ with
  | add x₂ =>
    cases op₃ with
    | add x₃ => exact RcRes.noConfusion (show RcRes.Either = _ from h2)
    | rem x₃ =>
      have h2' : (if x₂ = x₃ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := h2
      by_cases hx : x₂ = x₃
      · rw [if_pos hx] at h2'; exact RcRes.noConfusion h2'
      · rw [if_neg hx] at h2'; exact RcRes.noConfusion h2'
  | rem x₂ =>
    cases op₁ with
    | add x₁ =>
      have h1' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := h1
      by_cases hx : x₁ = x₂
      · rw [if_pos hx] at h1'; exact RcRes.noConfusion h1'
      · rw [if_neg hx] at h1'; exact RcRes.noConfusion h1'
    | rem x₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h1)

theorem ORSet_rc_non_comm_directional :
    ∀ o₁ o₂ : Op ORSet.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (¬ ORSet.toCRDTSig.commutes o₁ o₂ ↔
       (ORSet.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∨
        ORSet.toCRDTSig.rc o₂ o₁ = RcRes.Fst_then_snd)) := by
  intro o₁ o₂ _ _
  constructor
  · intro hnc
    rcases o₁ with ⟨ts₁, r₁, op₁⟩
    cases op₁ with
    | add x =>
      have h2 := ORSet_ncomm_add_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = ORSetOp.rem x := h2
      subst h2'
      right
      show (if x = x then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd
      rw [if_pos rfl]
    | rem x =>
      have h2 := ORSet_ncomm_rem_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = ORSetOp.add x := h2
      subst h2'
      left
      show (if x = x then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd
      rw [if_pos rfl]
  · rintro (h | h)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₁ with
      | add x₁ =>
        exfalso
        cases op₂ with
        | add x₂ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rem x₂ =>
          have h' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₁ = x₂
          · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
          · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
      | rem x₁ =>
        cases op₂ with
        | add x₂ =>
          have h' : (if x₁ = x₂ then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₁ = x₂
          · subst hx
            intro hc
            exact ORSet_ncomm_add_rem ts₂ r₂ ts₁ r₁ x₁
              (ORSet_commutes_symm hc)
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | rem x₂ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₂ with
      | add x₂ =>
        exfalso
        cases op₁ with
        | add x₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rem x₁ =>
          have h' : (if x₂ = x₁ then RcRes.Snd_then_fst else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₂ = x₁
          · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
          · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
      | rem x₂ =>
        cases op₁ with
        | add x₁ =>
          have h' : (if x₂ = x₁ then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₂ = x₁
          · subst hx
            exact ORSet_ncomm_add_rem ts₁ r₁ ts₂ r₂ x₂
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | rem x₁ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)

/-- `cond_comm_lift`: the `Rem x`/`Add x` swap perturbs the state by at most
the fresh tag; the perturbation is pointwise-invisible off that tag, and the
final non-commuting `e''` (= `Rem x`) erases it. -/
theorem ORSet_cond_comm_lift :
    ∀ (s : ORSet.State) (e e' e'' : Op ORSet.AppOp)
      (π : List (Op ORSet.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      ORSet.toCRDTSig.rc e e' = RcRes.Fst_then_snd →
      ¬ ORSet.toCRDTSig.commutes e' e'' →
      ORSet.update (applySeq ORSet.toCRDTSig
          (ORSet.update (ORSet.update s e') e) π) e''
        = ORSet.update (applySeq ORSet.toCRDTSig
            (ORSet.update (ORSet.update s e) e') π) e'' := by
  intro s e e' e'' π _ _ _ hrc hnc
  rcases e with ⟨ts₁, r₁, op₁⟩
  rcases e' with ⟨ts₂, r₂, op₂⟩
  -- rc = Fst forces (rem x, add x)
  cases op₁ with
  | add x₁ =>
    exfalso
    cases op₂ with
    | add x₂ => exact RcRes.noConfusion (show RcRes.Either = _ from hrc)
    | rem x₂ =>
      have h' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := hrc
      by_cases hx : x₁ = x₂
      · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
      · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
  | rem x₁ =>
    cases op₂ with
    | rem x₂ =>
      exact absurd (show RcRes.Either = _ from hrc)
        (fun hh => RcRes.noConfusion hh)
    | add x₂ =>
      have h' : (if x₁ = x₂ then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd := hrc
      by_cases hx : x₁ = x₂
      swap
      · rw [if_neg hx] at h'; exact absurd h' (fun hh => RcRes.noConfusion hh)
      · subst hx
        -- e'' = rem x₁
        have hdest := ORSet_ncomm_add_dest hnc
        rcases e'' with ⟨ts₃, r₃, op₃⟩
        have hdest' : op₃ = ORSetOp.rem x₁ := hdest
        subst hdest'
        funext q
        show (applySeq ORSet.toCRDTSig
            (ORSet.update (ORSet.update s (ts₂, r₂, ORSetOp.add x₁))
              (ts₁, r₁, ORSetOp.rem x₁)) π q && !(decide (q.2 = x₁)))
          = (applySeq ORSet.toCRDTSig
              (ORSet.update (ORSet.update s (ts₁, r₁, ORSetOp.rem x₁))
                (ts₂, r₂, ORSetOp.add x₁)) π q && !(decide (q.2 = x₁)))
        by_cases hq2 : q.2 = x₁
        · rw [decide_eq_true hq2]
          simp
        · have hq : q ≠ (ts₂, x₁) := by
            intro h
            exact hq2 (by rw [h])
          have hagree :
              (ORSet.update (ORSet.update s (ts₂, r₂, ORSetOp.add x₁))
                (ts₁, r₁, ORSetOp.rem x₁)) q
              = (ORSet.update (ORSet.update s (ts₁, r₁, ORSetOp.rem x₁))
                  (ts₂, r₂, ORSetOp.add x₁)) q := by
            show ((s q || decide (q = (ts₂, x₁))) && !(decide (q.2 = x₁)))
              = ((s q && !(decide (q.2 = x₁))) || decide (q = (ts₂, x₁)))
            rw [decide_eq_false hq, decide_eq_false hq2]
            cases s q <;> rfl
          rw [orsApplySeq_agree π q hagree]

/-! ## §4. Fold facts -/

/-- **Bound**: a live tag has an adding event in the list. -/
theorem ORSet_fold_bound {ρ : List (Op ORSet.AppOp)} {p : ℕ × ℕ}
    (h : applySeq ORSet.toCRDTSig ORSet.init ρ p = true) :
    ∃ o ∈ ρ, o.2.2 = ORSetOp.add p.2 ∧ o.1 = p.1 := by
  induction ρ using List.reverseRecOn with
  | nil => exact absurd (show (false : Bool) = true from h) Bool.noConfusion
  | append_singleton ρ o ih =>
    rw [applySeq_append_single] at h
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | add e =>
      have h' : (applySeq ORSet.toCRDTSig ORSet.init ρ p
          || decide (p = (ts, e))) = true := h
      cases hfa : applySeq ORSet.toCRDTSig ORSet.init ρ p with
      | true =>
        obtain ⟨o', ho', h1, h2⟩ := ih hfa
        exact ⟨o', List.mem_append_left _ ho', h1, h2⟩
      | false =>
        rw [hfa] at h'
        have hd : decide (p = (ts, e)) = true := by simpa using h'
        have hp' : p = (ts, e) := of_decide_eq_true hd
        refine ⟨(ts, rid, ORSetOp.add e),
          List.mem_append_right _ List.mem_cons_self, ?_, ?_⟩
        · show ORSetOp.add e = ORSetOp.add p.2
          rw [hp']
        · show ts = p.1
          rw [hp']
    | rem e =>
      have h' : (applySeq ORSet.toCRDTSig ORSet.init ρ p
          && !(decide (p.2 = e))) = true := h
      have h'' : applySeq ORSet.toCRDTSig ORSet.init ρ p = true :=
        (Bool.and_eq_true_iff.mp h').1
      obtain ⟨o', ho', h1, h2⟩ := ih h''
      exact ⟨o', List.mem_append_left _ ho', h1, h2⟩

/-- A dead tag stays dead if no event re-adds it. -/
theorem ORSet_fold_stays_false {p : ℕ × ℕ} :
    ∀ (β : List (Op ORSet.AppOp)) (s : ORSet.State),
      s p = false →
      (∀ o ∈ β, ¬(o.2.2 = ORSetOp.add p.2 ∧ o.1 = p.1)) →
      applySeq ORSet.toCRDTSig s β p = false := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : ORSet.update s o p = false := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add e =>
        show (s p || decide (p = (ts, e))) = false
        rw [hs]
        cases hd : decide (p = (ts, e)) with
        | false => rfl
        | true =>
          exfalso
          have hp' : p = (ts, e) := of_decide_eq_true hd
          exact hβ _ List.mem_cons_self
            ⟨show ORSetOp.add e = ORSetOp.add p.2 by rw [hp'],
             show ts = p.1 by rw [hp']⟩
      | rem e =>
        show (s p && !(decide (p.2 = e))) = false
        rw [hs]
        rfl
    exact ih (ORSet.update s o) hupd
      (fun o' ho' => hβ o' (List.mem_cons_of_mem _ ho'))

/-- A live tag stays live if no same-element rem follows. -/
theorem ORSet_fold_stays_true {p : ℕ × ℕ} :
    ∀ (β : List (Op ORSet.AppOp)) (s : ORSet.State),
      s p = true →
      (∀ o ∈ β, o.2.2 ≠ ORSetOp.rem p.2) →
      applySeq ORSet.toCRDTSig s β p = true := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : ORSet.update s o p = true := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add e =>
        show (s p || decide (p = (ts, e))) = true
        rw [hs]
        rfl
      | rem e =>
        show (s p && !(decide (p.2 = e))) = true
        rw [hs]
        have hne : p.2 ≠ e := by
          intro h
          exact hβ _ List.mem_cons_self (by rw [h])
        rw [decide_eq_false hne]
        rfl
    exact ih (ORSet.update s o) hupd
      (fun o' ho' => hβ o' (List.mem_cons_of_mem _ ho'))

/-! ## §5. The canonical-state σ-facts -/

/-- Live tags come from adds of the set. -/
theorem ORSet_canonical_bound
    {C : Sal.Emulation.Configuration ORSet.toCRDTSig}
    {F : Set (Op ORSet.AppOp)} {s : ORSet.State} {p : ℕ × ℕ}
    (hs : IsCanonicalState C F s) (hp : s p = true) :
    ∃ o ∈ F, o.2.2 = ORSetOp.add p.2 ∧ o.1 = p.1 := by
  obtain ⟨ρ, hperm, -, hfold⟩ := hs
  rw [← hfold] at hp
  obtain ⟨o, ho, h1, h2⟩ := ORSet_fold_bound hp
  exact ⟨o, (hperm.2 o).mp ho, h1, h2⟩

/-- **Kill**: a live tag admits no same-element rem vis-after its add. -/
theorem ORSet_live_no_later_rem
    {C : Sal.Emulation.Configuration ORSet.toCRDTSig}
    {F : Set (Op ORSet.AppOp)} {s : ORSet.State} {p : ℕ × ℕ}
    (h_in : ∀ o ∈ F, o ∈ C.events)
    (hs : IsCanonicalState C F s)
    (hp : s p = true)
    {tsa rda tsr rdr : ℕ}
    (haF : (tsa, rda, ORSetOp.add p.2) ∈ F) (haTs : tsa = p.1)
    (hrF : (tsr, rdr, ORSetOp.rem p.2) ∈ F)
    (hvis : C.vis (tsa, rda, ORSetOp.add p.2) (tsr, rdr, ORSetOp.rem p.2)) :
    False := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold] at hp
  have hne_ar : (tsa, rda, ORSetOp.add p.2) ≠ (tsr, rdr, ORSetOp.rem p.2) := by
    intro h
    have := congrArg (fun o : Op ORSet.AppOp => o.2.2) h
    exact ORSetOp.noConfusion this
  have hnc : ¬ ORSet.toCRDTSig.commutes (tsa, rda, ORSetOp.add p.2)
      (tsr, rdr, ORSetOp.rem p.2) :=
    ORSet_ncomm_add_rem tsa rda tsr rdr p.2
  have hedge : loOn C F (tsa, rda, ORSetOp.add p.2)
      (tsr, rdr, ORSetOp.rem p.2) := Or.inl ⟨hvis, hnc⟩
  have hrρ : (tsr, rdr, ORSetOp.rem p.2) ∈ ρ := (hperm.2 _).mpr hrF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem hrρ
  subst hsplit
  have haρ : (tsa, rda, ORSetOp.add p.2)
      ∈ α ++ (tsr, rdr, ORSetOp.rem p.2) :: β := (hperm.2 _).mpr haF
  have hmid := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  have haα : (tsa, rda, ORSetOp.add p.2) ∈ α := by
    rcases List.mem_append.mp haρ with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h hne_ar
      · exact absurd hedge (hmid.1 _ h)
  have hstep : applySeq ORSet.toCRDTSig ORSet.init
      (α ++ (tsr, rdr, ORSetOp.rem p.2) :: β)
      = applySeq ORSet.toCRDTSig
          (ORSet.update (applySeq ORSet.toCRDTSig ORSet.init α)
            (tsr, rdr, ORSetOp.rem p.2)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep] at hp
  have hkill : ORSet.update (applySeq ORSet.toCRDTSig ORSet.init α)
      (tsr, rdr, ORSetOp.rem p.2) p = false := by
    show (applySeq ORSet.toCRDTSig ORSet.init α p
        && !(decide (p.2 = p.2))) = false
    rw [decide_eq_true rfl]
    cases applySeq ORSet.toCRDTSig ORSet.init α p <;> rfl
  have hnoadd : ∀ o ∈ β, ¬(o.2.2 = ORSetOp.add p.2 ∧ o.1 = p.1) := by
    rintro o ho ⟨hoT, hoTs⟩
    have hoρ : o ∈ α ++ (tsr, rdr, ORSetOp.rem p.2) :: β :=
      List.mem_append_right _ (List.mem_cons_of_mem _ ho)
    have hoF : o ∈ F := (hperm.2 o).mp hoρ
    have hoa : o = (tsa, rda, ORSetOp.add p.2) := by
      by_contra hne
      exact distinctOps_of_events (h_in o hoF)
        (h_in _ haF) hne (hoTs.trans haTs.symm)
    rw [hoa] at ho
    have hnd := hperm.1
    rw [List.nodup_append] at hnd
    exact hnd.2.2 _ haα _ (List.mem_cons_of_mem _ ho) rfl
  rw [ORSet_fold_stays_false β _ hkill hnoadd] at hp
  exact Bool.noConfusion hp

/-- **Live**: an add with no same-element rem vis-after it yields a live
tag. -/
theorem ORSet_no_later_kill_live
    {C : Sal.Emulation.Configuration ORSet.toCRDTSig}
    {F : Set (Op ORSet.AppOp)} {s : ORSet.State} {p : ℕ × ℕ}
    (h_in : ∀ o ∈ F, o ∈ C.events)
    (hs : IsCanonicalState C F s)
    {rda : ℕ}
    (haF : (p.1, rda, ORSetOp.add p.2) ∈ F)
    (hno : ∀ r ∈ F, (r : Op ORSet.AppOp).2.2 = ORSetOp.rem p.2 →
      ¬ C.vis (p.1, rda, ORSetOp.add p.2) r) :
    s p = true := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold]
  have haρ : (p.1, rda, ORSetOp.add p.2) ∈ ρ := (hperm.2 _).mpr haF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem haρ
  subst hsplit
  have hcons := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  -- no same-element rem in β
  have hnorem : ∀ o ∈ β, (o : Op ORSet.AppOp).2.2 ≠ ORSetOp.rem p.2 := by
    intro o ho hoT
    have hoF : o ∈ F := (hperm.2 o).mp
      (List.mem_append_right _ (List.mem_cons_of_mem _ ho))
    have hnovis : ¬ C.vis (p.1, rda, ORSetOp.add p.2) o := hno o hoF hoT
    rcases o with ⟨tso, rdo, opo⟩
    have hoT' : opo = ORSetOp.rem p.2 := hoT
    subst hoT'
    have hnc_oa : ¬ ORSet.toCRDTSig.commutes (tso, rdo, ORSetOp.rem p.2)
        (p.1, rda, ORSetOp.add p.2) :=
      fun h => ORSet_ncomm_add_rem p.1 rda tso rdo p.2
        (ORSet_commutes_symm h)
    have hedge : loOn C F (tso, rdo, ORSetOp.rem p.2)
        (p.1, rda, ORSetOp.add p.2) := by
      by_cases hvo : C.vis (tso, rdo, ORSetOp.rem p.2)
          (p.1, rda, ORSetOp.add p.2)
      · exact Or.inl ⟨hvo, hnc_oa⟩
      · refine Or.inr ⟨hvo, hnovis, ?_, ?_⟩
        · show (if p.2 = p.2 then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
          rw [if_pos rfl]
        · rintro ⟨e₃, he₃F, hve₃, hnce₃⟩
          have h₃T := ORSet_ncomm_add_dest hnce₃
          exact hno e₃ he₃F h₃T hve₃
    exact hcons.1 _ ho hedge
  have hstep : applySeq ORSet.toCRDTSig ORSet.init
      (α ++ (p.1, rda, ORSetOp.add p.2) :: β)
      = applySeq ORSet.toCRDTSig
          (ORSet.update (applySeq ORSet.toCRDTSig ORSet.init α)
            (p.1, rda, ORSetOp.add p.2)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep]
  refine ORSet_fold_stays_true β _ ?_ hnorem
  show (applySeq ORSet.toCRDTSig ORSet.init α p
      || decide (p = (p.1, p.2))) = true
  have : decide (p = (p.1, p.2)) = true := decide_eq_true (by
    exact Prod.ext rfl rfl)
  rw [this]
  cases applySeq ORSet.toCRDTSig ORSet.init α p <;> rfl

/-! ## §6. The maximal-Rem trichotomy and `CDVC3` -/

/-- For a maximal `Rem x`, every live `x`-tag of `σ(U∖e)` is live in the
punctured downset. -/
theorem ORSet_rem_max_trichotomy
    {C : Sal.Emulation.Configuration ORSet.toCRDTSig}
    {U : Set (Op ORSet.AppOp)} {A B : ORSet.State}
    {ts rid x : ℕ}
    (h_in : ∀ o ∈ U, o ∈ C.events)
    (h_cl : ∀ a b, C.vis a b → ¬ ORSet.toCRDTSig.commutes a b →
      b ∈ U → a ∈ U)
    (h_e : (ts, rid, ORSetOp.rem x) ∈ U)
    (h_max : ∀ y ∈ U, y ≠ (ts, rid, ORSetOp.rem x) →
      ¬ loOn C U (ts, rid, ORSetOp.rem x) y)
    (hA : IsCanonicalState C (U \ {(ts, rid, ORSetOp.rem x)}) A)
    (hB : IsCanonicalState C
      (downset C (ts, rid, ORSetOp.rem x) \ {(ts, rid, ORSetOp.rem x)}) B)
    {p : ℕ × ℕ} (hpx : p.2 = x) (hpA : A p = true) :
    B p = true := by
  have h_inA : ∀ o ∈ U \ {(ts, rid, ORSetOp.rem x)}, o ∈ C.events :=
    fun o ho => h_in o ho.1
  have h_dsub : downset C (ts, rid, ORSetOp.rem x) ⊆ U :=
    downset_subset h_cl h_e
  have h_inB : ∀ o ∈ downset C (ts, rid, ORSetOp.rem x)
      \ {(ts, rid, ORSetOp.rem x)}, o ∈ C.events :=
    fun o ho => h_in o (h_dsub ho.1)
  -- the (unique) add of the live tag
  obtain ⟨a, haU', haT, haTs⟩ := ORSet_canonical_bound hA hpA
  rcases a with ⟨tsa, rda, opa⟩
  have haT' : opa = ORSetOp.add p.2 := haT
  subst haT'
  have haTs' : tsa = p.1 := haTs
  subst haTs'
  have hane : ((p.1, rda, ORSetOp.add p.2) : Op ORSet.AppOp)
      ≠ (ts, rid, ORSetOp.rem x) := haU'.2
  have hnc_ae : ¬ ORSet.toCRDTSig.commutes (p.1, rda, ORSetOp.add p.2)
      (ts, rid, ORSetOp.rem x) := by
    rw [← hpx]
    exact ORSet_ncomm_add_rem p.1 rda ts rid p.2
  by_cases hva : C.vis (p.1, rda, ORSetOp.add p.2) (ts, rid, ORSetOp.rem x)
  · -- vis-before: the add is in the punctured downset and live there
    have haD : (p.1, rda, ORSetOp.add p.2)
        ∈ downset C (ts, rid, ORSetOp.rem x) \ {(ts, rid, ORSetOp.rem x)} :=
      ⟨Or.inr (Relation.TransGen.single ⟨hva, hnc_ae⟩), hane⟩
    refine ORSet_no_later_kill_live h_inB hB haD ?_
    intro r hrD hrT hvar
    have hrU' : r ∈ U \ {(ts, rid, ORSetOp.rem x)} :=
      ⟨h_dsub hrD.1, hrD.2⟩
    rcases r with ⟨tsr, rdr, opr⟩
    have hrT' : opr = ORSetOp.rem p.2 := hrT
    subst hrT'
    exact ORSet_live_no_later_rem h_inA hA hpA haU' rfl hrU' hvar
  · by_cases hvea : C.vis (ts, rid, ORSetOp.rem x) (p.1, rda, ORSetOp.add p.2)
    · -- vis-after the maximal rem: a vis-edge out of e — contradiction
      exfalso
      have hnc_ea : ¬ ORSet.toCRDTSig.commutes (ts, rid, ORSetOp.rem x)
          (p.1, rda, ORSetOp.add p.2) :=
        fun h => hnc_ae (ORSet_commutes_symm h)
      exact h_max _ haU'.1 hane (Or.inl ⟨hvea, hnc_ea⟩)
    · -- concurrent: the rc-edge is unabsorbed — contradiction
      exfalso
      refine h_max _ haU'.1 hane (Or.inr ⟨hvea, hva, ?_, ?_⟩)
      · show (if x = p.2 then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
        rw [hpx, if_pos rfl]
      · rintro ⟨e₃, he₃U, hve₃, hnce₃⟩
        have h₃T := ORSet_ncomm_add_dest hnce₃
        have h₃ne : e₃ ≠ (ts, rid, ORSetOp.rem x) := by
          intro h
          rw [h] at hve₃
          exact hva hve₃
        rcases e₃ with ⟨ts₃, rd₃, op₃⟩
        have h₃T' : op₃ = ORSetOp.rem p.2 := h₃T
        subst h₃T'
        exact ORSet_live_no_later_rem h_inA hA hpA haU' rfl
          ⟨he₃U, h₃ne⟩ hve₃

/-- **`CDVC3` for the OR-Set.** `Add`-maximal: pure set algebra plus tag
freshness. `Rem`-maximal: the trichotomy. -/
theorem ORSet_cdVC3 : CDVC3 ORSet := by
  intro C U A B e h_tr h_ir h_in h_cl h_e h_max hA hB
  rcases e with ⟨ts, rid, op⟩
  cases op with
  | add x =>
    have hBt : B (ts, x) = false := by
      cases hBt : B (ts, x) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨o, hoB, hoT, hoTs⟩ := ORSet_canonical_bound hB hBt
        have hoU : o ∈ U := downset_subset h_cl h_e hoB.1
        exact distinctOps_of_events (h_in o hoU) (h_in _ h_e) hoB.2 hoTs
    funext p
    show ((B p && (A p && ORSet.update B (ts, rid, ORSetOp.add x) p))
        || ((A p && !(B p))
        || (ORSet.update B (ts, rid, ORSetOp.add x) p && !(B p))))
      = (A p || decide (p = (ts, x)))
    show ((B p && (A p && (B p || decide (p = (ts, x)))))
        || ((A p && !(B p))
        || ((B p || decide (p = (ts, x))) && !(B p))))
      = (A p || decide (p = (ts, x)))
    by_cases hp : p = (ts, x)
    · subst hp
      rw [hBt, decide_eq_true rfl]
      cases A (ts, x) <;> rfl
    · rw [decide_eq_false hp]
      cases B p <;> cases A p <;> rfl
  | rem x =>
    have himp : ∀ q : ℕ × ℕ, q.2 = x → A q = true → B q = true :=
      fun q hqx hqA =>
        ORSet_rem_max_trichotomy h_in h_cl h_e h_max hA hB hqx hqA
    funext p
    show ((B p && (A p && ORSet.update B (ts, rid, ORSetOp.rem x) p))
        || ((A p && !(B p))
        || (ORSet.update B (ts, rid, ORSetOp.rem x) p && !(B p))))
      = (A p && !(decide (p.2 = x)))
    show ((B p && (A p && (B p && !(decide (p.2 = x)))))
        || ((A p && !(B p))
        || ((B p && !(decide (p.2 = x))) && !(B p))))
      = (A p && !(decide (p.2 = x)))
    by_cases hx : p.2 = x
    · rw [decide_eq_true hx]
      cases hBp : B p with
      | true => cases A p <;> rfl
      | false =>
        cases hAp : A p with
        | false => rfl
        | true => exact Bool.noConfusion (hBp.symm.trans (himp p hx hAp))
    · rw [decide_eq_false hx]
      cases B p <;> cases A p <;> rfl

/-! ## §7. The feasible delta laws -/

/-- The redistribution law is a Boolean tautology for the OR-Set merge —
**unconditional**, all five states arbitrary. -/
theorem orMergeL_redistribute (B t₀ t₁ t₂ u : ORSet.State) :
    orMergeL (orMergeL B t₀ u) (orMergeL B t₁ u) (orMergeL B t₂ u)
      = orMergeL B (orMergeL t₀ t₁ t₂) u := by
  funext p
  show ((orMergeL B t₀ u p && (orMergeL B t₁ u p && orMergeL B t₂ u p))
      || ((orMergeL B t₁ u p && !(orMergeL B t₀ u p))
      || (orMergeL B t₂ u p && !(orMergeL B t₀ u p))))
    = ((B p && (orMergeL t₀ t₁ t₂ p && u p))
      || ((orMergeL t₀ t₁ t₂ p && !(B p)) || (u p && !(B p))))
  show ((((B p && (t₀ p && u p)) || ((t₀ p && !(B p)) || (u p && !(B p))))
      && (((B p && (t₁ p && u p)) || ((t₁ p && !(B p)) || (u p && !(B p))))
      && ((B p && (t₂ p && u p)) || ((t₂ p && !(B p)) || (u p && !(B p))))))
      || ((((B p && (t₁ p && u p)) || ((t₁ p && !(B p)) || (u p && !(B p))))
      && !(((B p && (t₀ p && u p)) || ((t₀ p && !(B p)) || (u p && !(B p))))))
      || (((B p && (t₂ p && u p)) || ((t₂ p && !(B p)) || (u p && !(B p))))
      && !(((B p && (t₀ p && u p)) || ((t₀ p && !(B p)) || (u p && !(B p))))))))
    = ((B p && (((t₀ p && (t₁ p && t₂ p)) || ((t₁ p && !(t₀ p))
      || (t₂ p && !(t₀ p)))) && u p))
      || ((((t₀ p && (t₁ p && t₂ p)) || ((t₁ p && !(t₀ p))
      || (t₂ p && !(t₀ p)))) && !(B p)) || (u p && !(B p))))
  cases B p <;> cases t₀ p <;> cases t₁ p <;> cases t₂ p <;>
    cases u p <;> rfl

/-- **The feasible delta contract for the OR-Set.** -/
theorem ORSet_feasibleDeltaVCs3 : FeasibleDeltaVCs3 ORSet := by
  refine ⟨?_, ?_, ?_⟩
  · -- feasible_init (holds unconditionally for the OR-Set)
    intro C ev s _ _
    funext p
    show ((false && (false && s p)) || ((false && !false)
        || (s p && !false))) = s p
    cases s p <;> rfl
  · -- feasible_local_redistribute
    intro C ev₁ ev₂ s₀ B t₁ s₂ e _ _ h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂
      h_max hc₀ hB ht₁ hc₂
    rcases e with ⟨ts, rid, op⟩
    cases op with
    | add x =>
      -- tag freshness against B and s₀
      have hBt : B (ts, x) = false := by
        cases hBt : B (ts, x) with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨o, hoB, hoT, hoTs⟩ := ORSet_canonical_bound hB hBt
          have hoU : o ∈ ev₁ := downset_subset h_cl₁ he₁ hoB.1
          exact distinctOps_of_events (h_in₁ o hoU) (h_in₁ _ he₁)
            hoB.2 hoTs
      have hs₀t : s₀ (ts, x) = false := by
        cases hs₀t : s₀ (ts, x) with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨o, ho₀, hoT, hoTs⟩ := ORSet_canonical_bound hc₀ hs₀t
          have hone : o ≠ (ts, rid, ORSetOp.add x) := by
            intro h
            rw [h] at ho₀
            exact he₂ ho₀.2
          exact distinctOps_of_events (h_in₁ o ho₀.1) (h_in₁ _ he₁)
            hone hoTs
      funext p
      show ((s₀ p && ((orMergeL B t₁ (ORSet.update B (ts, rid, ORSetOp.add x)) p) && s₂ p))
          || (((orMergeL B t₁ (ORSet.update B (ts, rid, ORSetOp.add x)) p) && !(s₀ p))
          || (s₂ p && !(s₀ p))))
        = ((B p && ((orMergeL s₀ t₁ s₂ p) && ORSet.update B (ts, rid, ORSetOp.add x) p))
          || (((orMergeL s₀ t₁ s₂ p) && !(B p))
          || (ORSet.update B (ts, rid, ORSetOp.add x) p && !(B p))))
      show ((s₀ p && (((B p && (t₁ p && (B p || decide (p = (ts, x)))))
          || ((t₁ p && !(B p)) || ((B p || decide (p = (ts, x))) && !(B p)))) && s₂ p))
          || ((((B p && (t₁ p && (B p || decide (p = (ts, x)))))
          || ((t₁ p && !(B p)) || ((B p || decide (p = (ts, x))) && !(B p)))) && !(s₀ p))
          || (s₂ p && !(s₀ p))))
        = ((B p && (((s₀ p && (t₁ p && s₂ p)) || ((t₁ p && !(s₀ p))
          || (s₂ p && !(s₀ p)))) && (B p || decide (p = (ts, x)))))
          || ((((s₀ p && (t₁ p && s₂ p)) || ((t₁ p && !(s₀ p))
          || (s₂ p && !(s₀ p)))) && !(B p))
          || ((B p || decide (p = (ts, x))) && !(B p))))
      by_cases hp : p = (ts, x)
      · subst hp
        rw [hBt, hs₀t, decide_eq_true rfl]
        cases t₁ (ts, x) <;> cases s₂ (ts, x) <;> rfl
      · rw [decide_eq_false hp]
        cases s₀ p <;> cases B p <;> cases t₁ p <;> cases s₂ p <;> rfl
    | rem x =>
      -- the X2 exclusion via the σ-facts
      have himp : ∀ q : ℕ × ℕ, q.2 = x → B q = true → s₂ q = true →
          s₀ q = true := by
        intro q hqx hqB hqs₂
        obtain ⟨a', ha'B, ha'T, ha'Ts⟩ := ORSet_canonical_bound hB hqB
        obtain ⟨a'', ha''₂, ha''T, ha''Ts⟩ := ORSet_canonical_bound hc₂ hqs₂
        have ha'U : a' ∈ ev₁ := downset_subset h_cl₁ he₁ ha'B.1
        have heq : a'' = a' := by
          by_contra hne
          exact distinctOps_of_events (h_in₂ a'' ha''₂) (h_in₁ a' ha'U)
            hne (ha''Ts.trans ha'Ts.symm)
        rcases a' with ⟨tsa, rda, opa⟩
        have ha'T' : opa = ORSetOp.add q.2 := ha'T
        subst ha'T'
        have ha'Ts' : tsa = q.1 := ha'Ts
        subst ha'Ts'
        have ha₀ : ((q.1, rda, ORSetOp.add q.2) : Op ORSet.AppOp)
            ∈ ev₁ ∩ ev₂ := ⟨ha'U, heq ▸ ha''₂⟩
        refine ORSet_no_later_kill_live (fun o ho => h_in₁ o ho.1)
          hc₀ ha₀ ?_
        intro r hr₀ hrT hvar
        rcases r with ⟨tsr, rdr, opr⟩
        have hrT' : opr = ORSetOp.rem q.2 := hrT
        subst hrT'
        exact ORSet_live_no_later_rem h_in₂ hc₂ hqs₂
          (heq ▸ ha''₂) rfl hr₀.2 hvar
      funext p
      show ((s₀ p && ((orMergeL B t₁ (ORSet.update B (ts, rid, ORSetOp.rem x)) p) && s₂ p))
          || (((orMergeL B t₁ (ORSet.update B (ts, rid, ORSetOp.rem x)) p) && !(s₀ p))
          || (s₂ p && !(s₀ p))))
        = ((B p && ((orMergeL s₀ t₁ s₂ p) && ORSet.update B (ts, rid, ORSetOp.rem x) p))
          || (((orMergeL s₀ t₁ s₂ p) && !(B p))
          || (ORSet.update B (ts, rid, ORSetOp.rem x) p && !(B p))))
      show ((s₀ p && (((B p && (t₁ p && (B p && !(decide (p.2 = x)))))
          || ((t₁ p && !(B p)) || ((B p && !(decide (p.2 = x))) && !(B p)))) && s₂ p))
          || ((((B p && (t₁ p && (B p && !(decide (p.2 = x)))))
          || ((t₁ p && !(B p)) || ((B p && !(decide (p.2 = x))) && !(B p)))) && !(s₀ p))
          || (s₂ p && !(s₀ p))))
        = ((B p && (((s₀ p && (t₁ p && s₂ p)) || ((t₁ p && !(s₀ p))
          || (s₂ p && !(s₀ p)))) && (B p && !(decide (p.2 = x)))))
          || ((((s₀ p && (t₁ p && s₂ p)) || ((t₁ p && !(s₀ p))
          || (s₂ p && !(s₀ p)))) && !(B p))
          || ((B p && !(decide (p.2 = x))) && !(B p))))
      by_cases hx : p.2 = x
      · rw [decide_eq_true hx]
        cases hBp : B p with
        | false =>
          cases s₀ p <;> cases t₁ p <;> cases s₂ p <;> rfl
        | true =>
          cases hs₀p : s₀ p with
          | true => cases t₁ p <;> cases s₂ p <;> rfl
          | false =>
            cases hs₂p : s₂ p with
            | false => cases t₁ p <;> rfl
            | true =>
              exact Bool.noConfusion
                (hs₀p.symm.trans (himp p hx hBp hs₂p))
      · rw [decide_eq_false hx]
        cases s₀ p <;> cases B p <;> cases t₁ p <;> cases s₂ p <;> rfl
  · -- feasible_redistribute: the unconditional tautology
    intro C ev₁ ev₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _
    exact orMergeL_redistribute B t₀ t₁ t₂ (ORSet.update B e)

/-! ## §8. The bundles and the end-to-end theorem -/

theorem ORSet_updateVCs : UpdateVCs ORSet.toCRDTSig :=
  ⟨ORSet_rc_non_comm_directional, ORSet_no_rc_chain, ORSet_cond_comm_lift⟩

theorem ORSet_coreVCs3CD : CoreVCs3CD ORSet :=
  ⟨ORSet_updateVCs, ORSet_mergeL_comm⟩

/-- The ternary Join Lemma for the production OR-Set. -/
theorem ORSet_joinLemma3 : JoinLemma3 ORSet :=
  join_lemma3_of_cd_feasible ORSet_coreVCs3CD ORSet_feasibleDeltaVCs3
    ORSet_cdVC3

open LabeledTS in
/-- **End-to-end RA-linearizability for the production OR-Set** — the first
LCA-sensitive, non-commuting real MRDT through the metatheory. -/
theorem ORSet_ra_linearizable3
    (C : Configuration ORSet)
    (hReach : (labeledTS3 ORSet).ReachableFrom
      (initConfig ORSet trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_join ORSet_joinLemma3 C hReach

/-! ## The OR-Set-efficient discharge -/

/-- Same-replica, same-element `Add`s with distinct timestamps do not commute
in the OR-Set-efficient: the later add evicts the earlier tag. -/
theorem ORSetE_ncomm_add_add_same (ts₁ ts₂ r x : ℕ) (hts : ts₁ ≠ ts₂) :
    ¬ ORSetE.toCRDTSig.commutes (ts₁, r, ORSetOp.add x)
      (ts₂, r, ORSetOp.add x) := by
  intro hc
  have h0 := congrFun (hc (fun _ => false)) (r, ts₁, x)
  simp [ORSetE_update_eq, orEUpdate] at h0
  exact absurd h0 hts

/-! ## §1. Pointwise infrastructure -/

theorem orEUpdate_pointwise (a b : ORSetE.State) (o : Op ORSetE.AppOp)
    (q : ℕ × ℕ × ℕ) (h : a q = b q) :
    ORSetE.update a o q = ORSetE.update b o q := by
  rcases o with ⟨ts, rid, op⟩
  cases op with
  | add e =>
    show ((a q && !(decide (rid = q.1 ∧ e = q.2.2)))
        || decide (q = (rid, ts, e)))
      = ((b q && !(decide (rid = q.1 ∧ e = q.2.2)))
        || decide (q = (rid, ts, e)))
    rw [h]
  | rem e =>
    show (a q && !(decide (e = q.2.2))) = (b q && !(decide (e = q.2.2)))
    rw [h]

theorem orEApplySeq_agree {a b : ORSetE.State}
    (π : List (Op ORSetE.AppOp)) (q : ℕ × ℕ × ℕ) (h : a q = b q) :
    applySeq ORSetE.toCRDTSig a π q = applySeq ORSetE.toCRDTSig b π q := by
  induction π generalizing a b with
  | nil => exact h
  | cons o π ih => exact ih (orEUpdate_pointwise a b o q h)

/-! ## §2. Commutation classification -/

theorem ORSetE_commutes_symm {o₁ o₂ : Op ORSetE.AppOp}
    (h : ORSetE.toCRDTSig.commutes o₁ o₂) :
    ORSetE.toCRDTSig.commutes o₂ o₁ :=
  fun s => (h s).symm

theorem ORSetE_comm_add_add (ts₁ r₁ x₁ ts₂ r₂ x₂ : ℕ)
    (hne : ¬(r₁ = r₂ ∧ x₁ = x₂)) :
    ORSetE.toCRDTSig.commutes (ts₁, r₁, ORSetOp.add x₁)
      (ts₂, r₂, ORSetOp.add x₂) := by
  intro s
  funext t
  show ((((s t && !(decide (r₁ = t.1 ∧ x₁ = t.2.2)))
      || decide (t = (r₁, ts₁, x₁))) && !(decide (r₂ = t.1 ∧ x₂ = t.2.2)))
      || decide (t = (r₂, ts₂, x₂)))
    = ((((s t && !(decide (r₂ = t.1 ∧ x₂ = t.2.2)))
      || decide (t = (r₂, ts₂, x₂))) && !(decide (r₁ = t.1 ∧ x₁ = t.2.2)))
      || decide (t = (r₁, ts₁, x₁)))
  by_cases h₁ : t = (r₁, ts₁, x₁)
  · subst h₁
    have hf₂ : ¬(r₂ = r₁ ∧ x₂ = x₁) := fun ⟨hr, hx⟩ => hne ⟨hr.symm, hx.symm⟩
    have hne₂ : ((r₁, ts₁, x₁) : ℕ × ℕ × ℕ) ≠ (r₂, ts₂, x₂) := by
      intro h
      exact hne ⟨congrArg Prod.fst h, congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) h⟩
    rw [decide_eq_true
        (show ((r₁, ts₁, x₁) : ℕ × ℕ × ℕ) = (r₁, ts₁, x₁) from rfl),
      decide_eq_false hne₂, decide_eq_false hf₂]
    cases s (r₁, ts₁, x₁) <;>
      cases hf1 : decide (r₁ = r₁ ∧ x₁ = x₁) <;> rfl
  · by_cases h₂ : t = (r₂, ts₂, x₂)
    · subst h₂
      have hf₁ : ¬(r₁ = r₂ ∧ x₁ = x₂) := hne
      rw [decide_eq_true
          (show ((r₂, ts₂, x₂) : ℕ × ℕ × ℕ) = (r₂, ts₂, x₂) from rfl),
        decide_eq_false h₁, decide_eq_false hf₁]
      cases s (r₂, ts₂, x₂) <;>
        cases hf2 : decide (r₂ = r₂ ∧ x₂ = x₂) <;> rfl
    · rw [decide_eq_false h₁, decide_eq_false h₂]
      cases s t <;> cases hf1 : decide (r₁ = t.1 ∧ x₁ = t.2.2) <;>
        cases hf2 : decide (r₂ = t.1 ∧ x₂ = t.2.2) <;> rfl

theorem ORSetE_comm_add_rem_ne (ts₁ r₁ x ts₂ r₂ y : ℕ) (hxy : x ≠ y) :
    ORSetE.toCRDTSig.commutes (ts₁, r₁, ORSetOp.add x)
      (ts₂, r₂, ORSetOp.rem y) := by
  intro s
  funext t
  show (((s t && !(decide (r₁ = t.1 ∧ x = t.2.2)))
      || decide (t = (r₁, ts₁, x))) && !(decide (y = t.2.2)))
    = (((s t && !(decide (y = t.2.2))) && !(decide (r₁ = t.1 ∧ x = t.2.2)))
      || decide (t = (r₁, ts₁, x)))
  by_cases h₁ : t = (r₁, ts₁, x)
  · subst h₁
    have hy : ¬(y = ((r₁, ts₁, x) : ℕ × ℕ × ℕ).2.2) := fun h => hxy h.symm
    rw [decide_eq_true
        (show ((r₁, ts₁, x) : ℕ × ℕ × ℕ) = (r₁, ts₁, x) from rfl),
      decide_eq_false hy]
    cases s (r₁, ts₁, x) <;>
      cases hf : decide (r₁ = r₁ ∧ x = x) <;> rfl
  · rw [decide_eq_false h₁]
    cases s t <;> cases hg : decide (y = t.2.2) <;>
      cases hf : decide (r₁ = t.1 ∧ x = t.2.2) <;> rfl

theorem ORSetE_comm_rem_rem (ts₁ r₁ x₁ ts₂ r₂ x₂ : ℕ) :
    ORSetE.toCRDTSig.commutes (ts₁, r₁, ORSetOp.rem x₁)
      (ts₂, r₂, ORSetOp.rem x₂) := by
  intro s
  funext t
  show ((s t && !(decide (x₁ = t.2.2))) && !(decide (x₂ = t.2.2)))
    = ((s t && !(decide (x₂ = t.2.2))) && !(decide (x₁ = t.2.2)))
  cases s t <;> cases h1 : decide (x₁ = t.2.2) <;>
    cases h2 : decide (x₂ = t.2.2) <;> rfl

theorem ORSetE_ncomm_add_rem (ts₁ r₁ ts₂ r₂ x : ℕ) :
    ¬ ORSetE.toCRDTSig.commutes (ts₁, r₁, ORSetOp.add x)
      (ts₂, r₂, ORSetOp.rem x) := by
  intro h
  have h0 := congrFun (h (fun _ => false)) (r₁, ts₁, x)
  simp [ORSetE_update_eq, orEUpdate] at h0

/-- Classification: an `Add x @ rid` fails to commute only with a `Rem x` or
a same-replica `Add x` — exactly the killers of its tag. -/
theorem ORSetE_ncomm_add_dest {ts r x : ℕ} {o : Op ORSetE.AppOp}
    (h : ¬ ORSetE.toCRDTSig.commutes (ts, r, ORSetOp.add x) o) :
    o.2.2 = ORSetOp.rem x ∨ (o.2.2 = ORSetOp.add x ∧ o.2.1 = r) := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add y =>
    by_cases hry : r = r' ∧ x = y
    · right
      exact ⟨show ORSetOp.add y = ORSetOp.add x by rw [hry.2],
        show r' = r by rw [hry.1]⟩
    · exact absurd (ORSetE_comm_add_add ts r x ts' r' y hry) h
  | rem y =>
    by_cases hxy : x = y
    · left
      show ORSetOp.rem y = ORSetOp.rem x
      rw [hxy]
    · exact absurd (ORSetE_comm_add_rem_ne ts r x ts' r' y hxy) h

theorem ORSetE_ncomm_rem_dest {ts r x : ℕ} {o : Op ORSetE.AppOp}
    (h : ¬ ORSetE.toCRDTSig.commutes (ts, r, ORSetOp.rem x) o) :
    o.2.2 = ORSetOp.add x := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add y =>
    by_cases hxy : y = x
    · subst hxy; rfl
    · exact absurd
        (ORSetE_commutes_symm (ORSetE_comm_add_rem_ne ts' r' y ts r x hxy)) h
  | rem y => exact absurd (ORSetE_comm_rem_rem ts r x ts' r' y) h

/-! ## §3. The update layer (guarded) -/

theorem ORSetE_no_rc_chain :
    ∀ o₁ o₂ o₃ : Op ORSetE.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (ORSetE.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         ORSetE.toCRDTSig.rc o₂ o₃ = RcRes.Fst_then_snd) := by
  rintro ⟨ts₁, r₁, op₁⟩ ⟨ts₂, r₂, op₂⟩ ⟨ts₃, r₃, op₃⟩ _ _ ⟨h1, h2⟩
  cases op₂ with
  | add x₂ =>
    cases op₃ with
    | add x₃ => exact RcRes.noConfusion (show RcRes.Either = _ from h2)
    | rem x₃ =>
      have h2' : (if x₂ = x₃ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := h2
      by_cases hx : x₂ = x₃
      · rw [if_pos hx] at h2'; exact RcRes.noConfusion h2'
      · rw [if_neg hx] at h2'; exact RcRes.noConfusion h2'
  | rem x₂ =>
    cases op₁ with
    | add x₁ =>
      have h1' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := h1
      by_cases hx : x₁ = x₂
      · rw [if_pos hx] at h1'; exact RcRes.noConfusion h1'
      · rw [if_neg hx] at h1'; exact RcRes.noConfusion h1'
    | rem x₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h1)

theorem ORSetE_rc_non_comm_directional :
    ∀ o₁ o₂ : Op ORSetE.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (¬ ORSetE.toCRDTSig.commutes o₁ o₂ ↔
       (ORSetE.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∨
        ORSetE.toCRDTSig.rc o₂ o₁ = RcRes.Fst_then_snd)) := by
  intro o₁ o₂ _ hrep
  constructor
  · intro hnc
    rcases o₁ with ⟨ts₁, r₁, op₁⟩
    cases op₁ with
    | add x =>
      rcases ORSetE_ncomm_add_dest hnc with h2 | ⟨h2, h2r⟩
      · rcases o₂ with ⟨ts₂, r₂, op₂⟩
        have h2' : op₂ = ORSetOp.rem x := h2
        subst h2'
        right
        show (if x = x then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
        rw [if_pos rfl]
      · exact absurd h2r.symm hrep
    | rem x =>
      have h2 := ORSetE_ncomm_rem_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = ORSetOp.add x := h2
      subst h2'
      left
      show (if x = x then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd
      rw [if_pos rfl]
  · rintro (h | h)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₁ with
      | add x₁ =>
        exfalso
        cases op₂ with
        | add x₂ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rem x₂ =>
          have h' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₁ = x₂
          · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
          · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
      | rem x₁ =>
        cases op₂ with
        | add x₂ =>
          have h' : (if x₁ = x₂ then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₁ = x₂
          · subst hx
            intro hc
            exact ORSetE_ncomm_add_rem ts₂ r₂ ts₁ r₁ x₁
              (ORSetE_commutes_symm hc)
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | rem x₂ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₂ with
      | add x₂ =>
        exfalso
        cases op₁ with
        | add x₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rem x₁ =>
          have h' : (if x₂ = x₁ then RcRes.Snd_then_fst else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₂ = x₁
          · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
          · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
      | rem x₂ =>
        cases op₁ with
        | add x₁ =>
          have h' : (if x₂ = x₁ then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₂ = x₁
          · subst hx
            exact ORSetE_ncomm_add_rem ts₁ r₁ ts₂ r₂ x₂
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | rem x₁ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)

/-- `cond_comm_lift`: the swap perturbs at most the fresh tag; a final `Rem x`
kills it, a final same-replica `Add x` evicts it (its own tag having a
distinct timestamp by `distinctOps`). -/
theorem ORSetE_cond_comm_lift :
    ∀ (s : ORSetE.State) (e e' e'' : Op ORSetE.AppOp)
      (π : List (Op ORSetE.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      ORSetE.toCRDTSig.rc e e' = RcRes.Fst_then_snd →
      ¬ ORSetE.toCRDTSig.commutes e' e'' →
      ORSetE.update (applySeq ORSetE.toCRDTSig
          (ORSetE.update (ORSetE.update s e') e) π) e''
        = ORSetE.update (applySeq ORSetE.toCRDTSig
            (ORSetE.update (ORSetE.update s e) e') π) e'' := by
  intro s e e' e'' π _ _ hd₃ hrc hnc
  rcases e with ⟨ts₁, r₁, op₁⟩
  rcases e' with ⟨ts₂, r₂, op₂⟩
  cases op₁ with
  | add x₁ =>
    exfalso
    cases op₂ with
    | add x₂ => exact RcRes.noConfusion (show RcRes.Either = _ from hrc)
    | rem x₂ =>
      have h' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := hrc
      by_cases hx : x₁ = x₂
      · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
      · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
  | rem x₁ =>
    cases op₂ with
    | rem x₂ =>
      exact absurd (show RcRes.Either = _ from hrc)
        (fun hh => RcRes.noConfusion hh)
    | add x₂ =>
      have h' : (if x₁ = x₂ then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd := hrc
      by_cases hx : x₁ = x₂
      swap
      · rw [if_neg hx] at h'
        exact absurd h' (fun hh => RcRes.noConfusion hh)
      · subst hx
        have hagree : ∀ q : ℕ × ℕ × ℕ, q ≠ (r₂, ts₂, x₁) →
            (ORSetE.update (ORSetE.update s (ts₂, r₂, ORSetOp.add x₁))
              (ts₁, r₁, ORSetOp.rem x₁)) q
            = (ORSetE.update (ORSetE.update s (ts₁, r₁, ORSetOp.rem x₁))
                (ts₂, r₂, ORSetOp.add x₁)) q := by
          intro q hq
          show (((s q && !(decide (r₂ = q.1 ∧ x₁ = q.2.2)))
              || decide (q = (r₂, ts₂, x₁))) && !(decide (x₁ = q.2.2)))
            = (((s q && !(decide (x₁ = q.2.2)))
              && !(decide (r₂ = q.1 ∧ x₁ = q.2.2)))
              || decide (q = (r₂, ts₂, x₁)))
          rw [decide_eq_false hq]
          cases s q <;> cases hf : decide (r₂ = q.1 ∧ x₁ = q.2.2) <;>
            cases hg : decide (x₁ = q.2.2) <;> rfl
        rcases ORSetE_ncomm_add_dest hnc with h3 | ⟨h3, h3r⟩
        · -- final op is Rem x₁
          rcases e'' with ⟨ts₃, r₃, op₃⟩
          have h3' : op₃ = ORSetOp.rem x₁ := h3
          subst h3'
          funext q
          show (applySeq ORSetE.toCRDTSig
              (ORSetE.update (ORSetE.update s (ts₂, r₂, ORSetOp.add x₁))
                (ts₁, r₁, ORSetOp.rem x₁)) π q && !(decide (x₁ = q.2.2)))
            = (applySeq ORSetE.toCRDTSig
                (ORSetE.update (ORSetE.update s (ts₁, r₁, ORSetOp.rem x₁))
                  (ts₂, r₂, ORSetOp.add x₁)) π q && !(decide (x₁ = q.2.2)))
          by_cases hq2 : x₁ = q.2.2
          · rw [decide_eq_true hq2]
            simp
          · have hq : q ≠ (r₂, ts₂, x₁) := by
              intro h
              exact hq2 (by rw [h])
            rw [orEApplySeq_agree π q (hagree q hq)]
        · -- final op is the evicting same-replica Add x₁
          rcases e'' with ⟨ts₃, r₃, op₃⟩
          have h3' : op₃ = ORSetOp.add x₁ := h3
          subst h3'
          have h3r' : r₂ = r₃ := (show r₃ = r₂ from h3r).symm
          subst h3r'
          have hts : ts₂ ≠ ts₃ := hd₃
          funext q
          show ((applySeq ORSetE.toCRDTSig
              (ORSetE.update (ORSetE.update s (ts₂, r₂, ORSetOp.add x₁))
                (ts₁, r₁, ORSetOp.rem x₁)) π q
              && !(decide (r₂ = q.1 ∧ x₁ = q.2.2)))
              || decide (q = (r₂, ts₃, x₁)))
            = ((applySeq ORSetE.toCRDTSig
                (ORSetE.update (ORSetE.update s (ts₁, r₁, ORSetOp.rem x₁))
                  (ts₂, r₂, ORSetOp.add x₁)) π q
                && !(decide (r₂ = q.1 ∧ x₁ = q.2.2)))
                || decide (q = (r₂, ts₃, x₁)))
          by_cases hq : q = (r₂, ts₂, x₁)
          · subst hq
            rw [decide_eq_true
                (show (r₂ = ((r₂, ts₂, x₁) : ℕ × ℕ × ℕ).1
                  ∧ x₁ = ((r₂, ts₂, x₁) : ℕ × ℕ × ℕ).2.2) from ⟨rfl, rfl⟩)]
            simp
          · rw [orEApplySeq_agree π q (hagree q hq)]

/-! ## §4. The two-killer fold facts -/

/-- The killers of tag `q = (rid, ts, x)`: a `Rem x`, or an `Add x` at the
same replica (eviction). Note this is exactly `ORSetE_ncomm_add_dest`'s
conclusion for `q`'s adder. -/
def orEKills (q : ℕ × ℕ × ℕ) (o : Op ORSetE.AppOp) : Prop :=
  o.2.2 = ORSetOp.rem q.2.2 ∨ (o.2.2 = ORSetOp.add q.2.2 ∧ o.2.1 = q.1)

/-- A live tag has *its* adding event (tag-determined) in the list. -/
theorem ORSetE_fold_bound {ρ : List (Op ORSetE.AppOp)} {q : ℕ × ℕ × ℕ}
    (h : applySeq ORSetE.toCRDTSig ORSetE.init ρ q = true) :
    (q.2.1, q.1, ORSetOp.add q.2.2) ∈ ρ := by
  induction ρ using List.reverseRecOn with
  | nil => exact absurd (show (false : Bool) = true from h) Bool.noConfusion
  | append_singleton ρ o ih =>
    rw [applySeq_append_single] at h
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | add e =>
      have h' : ((applySeq ORSetE.toCRDTSig ORSetE.init ρ q
          && !(decide (rid = q.1 ∧ e = q.2.2)))
          || decide (q = (rid, ts, e))) = true := h
      cases hd : decide (q = (rid, ts, e)) with
      | true =>
        have hq : q = (rid, ts, e) := of_decide_eq_true hd
        refine List.mem_append_right _ ?_
        have hqe : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
            = (ts, rid, ORSetOp.add e) := by
          rw [hq]
        rw [hqe]
        exact List.mem_cons_self
      | false =>
        rw [hd] at h'
        have h'' : applySeq ORSetE.toCRDTSig ORSetE.init ρ q = true := by
          rcases Bool.or_eq_true_iff.mp h' with h1 | h1
          · exact (Bool.and_eq_true_iff.mp h1).1
          · exact absurd h1 Bool.noConfusion
        exact List.mem_append_left _ (ih h'')
    | rem e =>
      have h' : (applySeq ORSetE.toCRDTSig ORSetE.init ρ q
          && !(decide (e = q.2.2))) = true := h
      exact List.mem_append_left _ (ih (Bool.and_eq_true_iff.mp h').1)

/-- A dead tag stays dead if its (unique, tag-determined) adder is absent. -/
theorem ORSetE_fold_stays_false {q : ℕ × ℕ × ℕ} :
    ∀ (β : List (Op ORSetE.AppOp)) (s : ORSetE.State),
      s q = false →
      ((q.2.1, q.1, ORSetOp.add q.2.2) ∉ β) →
      applySeq ORSetE.toCRDTSig s β q = false := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : ORSetE.update s o q = false := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add e =>
        show ((s q && !(decide (rid = q.1 ∧ e = q.2.2)))
            || decide (q = (rid, ts, e))) = false
        rw [hs]
        cases hd : decide (q = (rid, ts, e)) with
        | false => rfl
        | true =>
          exfalso
          have hq : q = (rid, ts, e) := of_decide_eq_true hd
          refine hβ ?_
          have hqe : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
              = (ts, rid, ORSetOp.add e) := by
            rw [hq]
          rw [hqe]
          exact List.mem_cons_self
      | rem e =>
        show (s q && !(decide (e = q.2.2))) = false
        rw [hs]
        rfl
    exact ih (ORSetE.update s o) hupd
      (fun hmem => hβ (List.mem_cons_of_mem _ hmem))

/-- A live tag stays live if no killer follows. -/
theorem ORSetE_fold_stays_true {q : ℕ × ℕ × ℕ} :
    ∀ (β : List (Op ORSetE.AppOp)) (s : ORSetE.State),
      s q = true →
      (∀ o ∈ β, ¬ orEKills q o) →
      applySeq ORSetE.toCRDTSig s β q = true := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : ORSetE.update s o q = true := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add e =>
        show ((s q && !(decide (rid = q.1 ∧ e = q.2.2)))
            || decide (q = (rid, ts, e))) = true
        rw [hs]
        have hf : ¬(rid = q.1 ∧ e = q.2.2) := by
          rintro ⟨hr, he⟩
          exact hβ _ List.mem_cons_self
            (Or.inr ⟨show ORSetOp.add e = ORSetOp.add q.2.2 by rw [he], hr⟩)
        rw [decide_eq_false hf]
        rfl
      | rem e =>
        show (s q && !(decide (e = q.2.2))) = true
        rw [hs]
        have hne : ¬(e = q.2.2) := by
          intro h
          exact hβ _ List.mem_cons_self
            (Or.inl (show ORSetOp.rem e = ORSetOp.rem q.2.2 by rw [h]))
        rw [decide_eq_false hne]
        rfl
    exact ih (ORSetE.update s o) hupd
      (fun o' ho' => hβ o' (List.mem_cons_of_mem _ ho'))

/-! ## §5. The canonical-state σ-facts -/

theorem ORSetE_canonical_bound
    {C : Sal.Emulation.Configuration ORSetE.toCRDTSig}
    {F : Set (Op ORSetE.AppOp)} {s : ORSetE.State} {q : ℕ × ℕ × ℕ}
    (hs : IsCanonicalState C F s) (hq : s q = true) :
    (q.2.1, q.1, ORSetOp.add q.2.2) ∈ F := by
  obtain ⟨ρ, hperm, -, hfold⟩ := hs
  rw [← hfold] at hq
  exact (hperm.2 _).mp (ORSetE_fold_bound hq)

/-- **Kill**: a live tag admits no killer vis-after its add. -/
theorem ORSetE_live_no_later_kill
    {C : Sal.Emulation.Configuration ORSetE.toCRDTSig}
    {F : Set (Op ORSetE.AppOp)} {s : ORSetE.State} {q : ℕ × ℕ × ℕ}
    (hs : IsCanonicalState C F s)
    (hq : s q = true)
    {k : Op ORSetE.AppOp}
    (hkF : k ∈ F) (hkill : orEKills q k)
    (hkne : k ≠ (q.2.1, q.1, ORSetOp.add q.2.2))
    (hvis : C.vis (q.2.1, q.1, ORSetOp.add q.2.2) k) : False := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold] at hq
  have hnc : ¬ ORSetE.toCRDTSig.commutes
      (q.2.1, q.1, ORSetOp.add q.2.2) k := by
    rcases hkill with hk | ⟨hk, hkr⟩
    · rcases k with ⟨tsk, rk, opk⟩
      have hk' : opk = ORSetOp.rem q.2.2 := hk
      subst hk'
      exact ORSetE_ncomm_add_rem q.2.1 q.1 tsk rk q.2.2
    · rcases k with ⟨tsk, rk, opk⟩
      have hk' : opk = ORSetOp.add q.2.2 := hk
      subst hk'
      have hkr' : rk = q.1 := hkr
      subst hkr'
      have hts : q.2.1 ≠ tsk := fun h => hkne (by rw [h])
      exact ORSetE_ncomm_add_add_same q.2.1 tsk q.1 q.2.2 hts
  have hedge : loOn C F (q.2.1, q.1, ORSetOp.add q.2.2) k :=
    Or.inl ⟨hvis, hnc⟩
  have hkρ : k ∈ ρ := (hperm.2 k).mpr hkF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem hkρ
  subst hsplit
  have haρ : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
      ∈ α ++ k :: β := (hperm.2 _).mpr (by
        have : applySeq ORSetE.toCRDTSig ORSetE.init (α ++ k :: β) q
            = true := hq
        exact (hperm.2 _).mp (ORSetE_fold_bound this))
  have hmid := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  have haα : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp) ∈ α := by
    rcases List.mem_append.mp haρ with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h.symm hkne
      · exact absurd hedge (hmid.1 _ h)
  have hstep : applySeq ORSetE.toCRDTSig ORSetE.init (α ++ k :: β)
      = applySeq ORSetE.toCRDTSig
          (ORSetE.update (applySeq ORSetE.toCRDTSig ORSetE.init α) k) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep] at hq
  have hkillq : ORSetE.update (applySeq ORSetE.toCRDTSig ORSetE.init α) k q
      = false := by
    rcases hkill with hk | ⟨hk, hkr⟩
    · rcases k with ⟨tsk, rk, opk⟩
      have hk' : opk = ORSetOp.rem q.2.2 := hk
      subst hk'
      show (applySeq ORSetE.toCRDTSig ORSetE.init α q
          && !(decide (q.2.2 = q.2.2))) = false
      rw [decide_eq_true rfl]
      cases applySeq ORSetE.toCRDTSig ORSetE.init α q <;> rfl
    · rcases k with ⟨tsk, rk, opk⟩
      have hk' : opk = ORSetOp.add q.2.2 := hk
      subst hk'
      have hkr' : rk = q.1 := hkr
      subst hkr'
      have hts : q.2.1 ≠ tsk := fun h => hkne (by rw [h])
      show ((applySeq ORSetE.toCRDTSig ORSetE.init α q
          && !(decide (q.1 = q.1 ∧ q.2.2 = q.2.2)))
          || decide (q = (q.1, tsk, q.2.2))) = false
      have hqt : q ≠ (q.1, tsk, q.2.2) := by
        intro h
        exact hts (congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) h)
      rw [decide_eq_true (show (q.1 = q.1 ∧ q.2.2 = q.2.2) from ⟨rfl, rfl⟩),
        decide_eq_false hqt]
      cases applySeq ORSetE.toCRDTSig ORSetE.init α q <;> rfl
  have hnoadd : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp) ∉ β := by
    intro ho
    have hnd := hperm.1
    rw [List.nodup_append] at hnd
    exact hnd.2.2 _ haα _ (List.mem_cons_of_mem _ ho) rfl
  rw [ORSetE_fold_stays_false β _ hkillq hnoadd] at hq
  exact Bool.noConfusion hq

/-- **Live**: an add with no killer vis-after it yields a live tag; the
concurrent eviction case is impossible by same-replica totality. -/
theorem ORSetE_no_later_kill_live
    {C : Sal.Emulation.Configuration ORSetE.toCRDTSig}
    {F : Set (Op ORSetE.AppOp)} {s : ORSetE.State} {q : ℕ × ℕ × ℕ}
    (h_in : ∀ o ∈ F, o ∈ C.events)
    (hs : IsCanonicalState C F s)
    (haF : (q.2.1, q.1, ORSetOp.add q.2.2) ∈ F)
    (hno : ∀ k ∈ F, orEKills q k →
      ¬ C.vis (q.2.1, q.1, ORSetOp.add q.2.2) k) :
    s q = true := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold]
  have haρ : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp) ∈ ρ :=
    (hperm.2 _).mpr haF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem haρ
  subst hsplit
  have hcons := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  have hnokill : ∀ o ∈ β, ¬ orEKills q o := by
    intro k hk hkill
    have hkF : k ∈ F := (hperm.2 k).mp
      (List.mem_append_right _ (List.mem_cons_of_mem _ hk))
    have hkne : k ≠ (q.2.1, q.1, ORSetOp.add q.2.2) := by
      intro h
      have hnd := hperm.1
      rw [List.nodup_append, List.nodup_cons] at hnd
      exact hnd.2.1.1 (h ▸ hk)
    have hnovis : ¬ C.vis (q.2.1, q.1, ORSetOp.add q.2.2) k :=
      hno k hkF hkill
    -- the killer does not commute with the add
    have hnc_ak : ¬ ORSetE.toCRDTSig.commutes
        (q.2.1, q.1, ORSetOp.add q.2.2) k := by
      rcases hkill with hk' | ⟨hk', hkr⟩
      · rcases k with ⟨tsk, rk, opk⟩
        have h' : opk = ORSetOp.rem q.2.2 := hk'
        subst h'
        exact ORSetE_ncomm_add_rem q.2.1 q.1 tsk rk q.2.2
      · rcases k with ⟨tsk, rk, opk⟩
        have h' : opk = ORSetOp.add q.2.2 := hk'
        subst h'
        have hkr' : rk = q.1 := hkr
        subst hkr'
        have hts : q.2.1 ≠ tsk := fun h => hkne (by rw [h])
        exact ORSetE_ncomm_add_add_same q.2.1 tsk q.1 q.2.2 hts
    by_cases hvk : C.vis k (q.2.1, q.1, ORSetOp.add q.2.2)
    · exact absurd (Or.inl ⟨hvk, fun hc => hnc_ak (ORSetE_commutes_symm hc)⟩)
        (hcons.1 _ hk)
    · rcases hkill with hk' | ⟨hk', hkr⟩
      · -- concurrent rem-killer: the rc-edge is unabsorbed
        rcases k with ⟨tsk, rk, opk⟩
        have h' : opk = ORSetOp.rem q.2.2 := hk'
        subst h'
        refine absurd (Or.inr ⟨hvk, hnovis, ?_, ?_⟩) (hcons.1 _ hk)
        · show (if q.2.2 = q.2.2 then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd
          rw [if_pos rfl]
        · rintro ⟨e₃, he₃F, hve₃, hnce₃⟩
          exact hno e₃ he₃F (ORSetE_ncomm_add_dest hnce₃) hve₃
      · -- concurrent same-replica eviction: impossible by totality
        rcases k with ⟨tsk, rk, opk⟩
        have h' : opk = ORSetOp.add q.2.2 := hk'
        subst h'
        have hkr' : rk = q.1 := hkr
        subst hkr'
        obtain ⟨rK, sK, hLK, hsK⟩ := h_in _ hkF
        obtain ⟨rA, sA, hLA, hsA⟩ := h_in _ haF
        rcases C.vis_total_same_replica hLK hsK hLA hsA hkne rfl
          with hv | hv
        · exact hvk hv
        · exact hnovis hv
  have hstep : applySeq ORSetE.toCRDTSig ORSetE.init
      (α ++ ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp) :: β)
      = applySeq ORSetE.toCRDTSig
          (ORSetE.update (applySeq ORSetE.toCRDTSig ORSetE.init α)
            (q.2.1, q.1, ORSetOp.add q.2.2)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep]
  refine ORSetE_fold_stays_true β _ ?_ hnokill
  show ((applySeq ORSetE.toCRDTSig ORSetE.init α q
      && !(decide (q.1 = q.1 ∧ q.2.2 = q.2.2)))
      || decide (q = (q.1, q.2.1, q.2.2))) = true
  rw [decide_eq_true
      (show q = (q.1, q.2.1, q.2.2) from Prod.ext rfl (Prod.ext rfl rfl))]
  simp

/-! ## §6. The maximal-event trichotomies and `CDVC3` -/

/-- Maximal `Rem`: every live tag of the element in `σ(U∖e)` is live in the
punctured downset. -/
theorem ORSetE_rem_max_trichotomy
    {C : Sal.Emulation.Configuration ORSetE.toCRDTSig}
    {U : Set (Op ORSetE.AppOp)} {A B : ORSetE.State}
    {ts rid : ℕ} {q : ℕ × ℕ × ℕ}
    (h_ir : ∀ a : Op ORSetE.AppOp, ¬ C.vis a a)
    (h_in : ∀ o ∈ U, o ∈ C.events)
    (h_cl : ∀ a b, C.vis a b → ¬ ORSetE.toCRDTSig.commutes a b →
      b ∈ U → a ∈ U)
    (h_e : (ts, rid, ORSetOp.rem q.2.2) ∈ U)
    (h_max : ∀ y ∈ U, y ≠ (ts, rid, ORSetOp.rem q.2.2) →
      ¬ loOn C U (ts, rid, ORSetOp.rem q.2.2) y)
    (hA : IsCanonicalState C (U \ {(ts, rid, ORSetOp.rem q.2.2)}) A)
    (hB : IsCanonicalState C
      (downset C (ts, rid, ORSetOp.rem q.2.2)
        \ {(ts, rid, ORSetOp.rem q.2.2)}) B)
    (hqA : A q = true) : B q = true := by
  have h_dsub : downset C (ts, rid, ORSetOp.rem q.2.2) ⊆ U :=
    downset_subset h_cl h_e
  have haU' := ORSetE_canonical_bound hA hqA
  have hane : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
      ≠ (ts, rid, ORSetOp.rem q.2.2) := by
    intro h
    exact ORSetOp.noConfusion (congrArg (fun z : Op ORSetE.AppOp => z.2.2) h)
  have hnc_ae : ¬ ORSetE.toCRDTSig.commutes (q.2.1, q.1, ORSetOp.add q.2.2)
      (ts, rid, ORSetOp.rem q.2.2) :=
    ORSetE_ncomm_add_rem q.2.1 q.1 ts rid q.2.2
  by_cases hva : C.vis (q.2.1, q.1, ORSetOp.add q.2.2)
      (ts, rid, ORSetOp.rem q.2.2)
  · have haD : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
        ∈ downset C (ts, rid, ORSetOp.rem q.2.2)
          \ {(ts, rid, ORSetOp.rem q.2.2)} :=
      ⟨Or.inr (Relation.TransGen.single ⟨hva, hnc_ae⟩), hane⟩
    refine ORSetE_no_later_kill_live
      (fun o ho => h_in o (h_dsub ho.1)) hB haD ?_
    intro k hkD hkill hvak
    by_cases hka : k = (q.2.1, q.1, ORSetOp.add q.2.2)
    · rw [hka] at hvak
      exact h_ir _ hvak
    · exact ORSetE_live_no_later_kill hA hqA
        ⟨h_dsub hkD.1, hkD.2⟩ hkill hka hvak
  · by_cases hvea : C.vis (ts, rid, ORSetOp.rem q.2.2)
        (q.2.1, q.1, ORSetOp.add q.2.2)
    · exact absurd
        (Or.inl ⟨hvea, fun hc => hnc_ae (ORSetE_commutes_symm hc)⟩)
        (h_max _ haU'.1 hane)
    · exfalso
      refine h_max _ haU'.1 hane
        (Or.inr ⟨hvea, hva, ?_, ?_⟩)
      · show (if q.2.2 = q.2.2 then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
        rw [if_pos rfl]
      · rintro ⟨e₃, he₃U, hve₃, hnce₃⟩
        by_cases he₃a : e₃ = (q.2.1, q.1, ORSetOp.add q.2.2)
        · rw [he₃a] at hve₃
          exact h_ir _ hve₃
        · have he₃ne : e₃ ≠ (ts, rid, ORSetOp.rem q.2.2) := by
            intro h
            rw [h] at hve₃
            exact hva hve₃
          exact ORSetE_live_no_later_kill hA hqA ⟨he₃U, he₃ne⟩
            (ORSetE_ncomm_add_dest hnce₃) he₃a hve₃

/-- Maximal `Add` at replica `q.1`: every live evicted-family tag of `σ(U∖e)`
is live in the punctured downset — by same-replica totality. -/
theorem ORSetE_add_max_trichotomy
    {C : Sal.Emulation.Configuration ORSetE.toCRDTSig}
    {U : Set (Op ORSetE.AppOp)} {A B : ORSetE.State}
    {ts : ℕ} {q : ℕ × ℕ × ℕ}
    (h_ir : ∀ a : Op ORSetE.AppOp, ¬ C.vis a a)
    (h_in : ∀ o ∈ U, o ∈ C.events)
    (h_cl : ∀ a b, C.vis a b → ¬ ORSetE.toCRDTSig.commutes a b →
      b ∈ U → a ∈ U)
    (h_e : (ts, q.1, ORSetOp.add q.2.2) ∈ U)
    (h_max : ∀ y ∈ U, y ≠ (ts, q.1, ORSetOp.add q.2.2) →
      ¬ loOn C U (ts, q.1, ORSetOp.add q.2.2) y)
    (hA : IsCanonicalState C (U \ {(ts, q.1, ORSetOp.add q.2.2)}) A)
    (hB : IsCanonicalState C
      (downset C (ts, q.1, ORSetOp.add q.2.2)
        \ {(ts, q.1, ORSetOp.add q.2.2)}) B)
    (hqts : q.2.1 ≠ ts)
    (hqA : A q = true) : B q = true := by
  have h_dsub : downset C (ts, q.1, ORSetOp.add q.2.2) ⊆ U :=
    downset_subset h_cl h_e
  have haU' := ORSetE_canonical_bound hA hqA
  have hane : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
      ≠ (ts, q.1, ORSetOp.add q.2.2) := by
    intro h
    exact hqts (congrArg (fun z : Op ORSetE.AppOp => z.1) h)
  have hnc_ae : ¬ ORSetE.toCRDTSig.commutes (q.2.1, q.1, ORSetOp.add q.2.2)
      (ts, q.1, ORSetOp.add q.2.2) :=
    ORSetE_ncomm_add_add_same q.2.1 ts q.1 q.2.2 hqts
  -- same replica: vis-comparable
  obtain ⟨rA, sA, hLA, hsA⟩ := h_in _ haU'.1
  obtain ⟨rE, sE, hLE, hsE⟩ := h_in _ h_e
  rcases C.vis_total_same_replica hLA hsA hLE hsE hane rfl with hva | hvea
  · have haD : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
        ∈ downset C (ts, q.1, ORSetOp.add q.2.2)
          \ {(ts, q.1, ORSetOp.add q.2.2)} :=
      ⟨Or.inr (Relation.TransGen.single ⟨hva, hnc_ae⟩), hane⟩
    refine ORSetE_no_later_kill_live
      (fun o ho => h_in o (h_dsub ho.1)) hB haD ?_
    intro k hkD hkill hvak
    by_cases hka : k = (q.2.1, q.1, ORSetOp.add q.2.2)
    · rw [hka] at hvak
      exact h_ir _ hvak
    · exact ORSetE_live_no_later_kill hA hqA
        ⟨h_dsub hkD.1, hkD.2⟩ hkill hka hvak
  · exact absurd
      (Or.inl ⟨hvea, fun hc => hnc_ae (ORSetE_commutes_symm hc)⟩)
      (h_max _ haU'.1 hane)

/-- **`CDVC3` for the OR-Set-efficient.** -/
theorem ORSetE_cdVC3 : CDVC3 ORSetE := by
  intro C U A B e h_tr h_ir h_in h_cl h_e h_max hA hB
  rcases e with ⟨ts, rid, op⟩
  cases op with
  | add x =>
    funext q
    show ((B q && (A q && ORSetE.update B (ts, rid, ORSetOp.add x) q))
        || ((A q && !(B q))
        || (ORSetE.update B (ts, rid, ORSetOp.add x) q && !(B q))))
      = ((A q && !(decide (rid = q.1 ∧ x = q.2.2)))
        || decide (q = (rid, ts, x)))
    show ((B q && (A q && ((B q && !(decide (rid = q.1 ∧ x = q.2.2)))
        || decide (q = (rid, ts, x)))))
        || ((A q && !(B q))
        || (((B q && !(decide (rid = q.1 ∧ x = q.2.2)))
        || decide (q = (rid, ts, x))) && !(B q))))
      = ((A q && !(decide (rid = q.1 ∧ x = q.2.2)))
        || decide (q = (rid, ts, x)))
    by_cases hq : q = (rid, ts, x)
    · subst hq
      have hBt : B (rid, ts, x) = false := by
        cases hBt : B (rid, ts, x) with
        | false => rfl
        | true =>
          have hmem := ORSetE_canonical_bound hB hBt
          exact absurd rfl hmem.2
      rw [hBt, decide_eq_true
        (show ((rid, ts, x) : ℕ × ℕ × ℕ) = (rid, ts, x) from rfl)]
      cases A (rid, ts, x) <;>
        cases hf : decide (rid = ((rid, ts, x) : ℕ × ℕ × ℕ).1
          ∧ x = ((rid, ts, x) : ℕ × ℕ × ℕ).2.2) <;> rfl
    · by_cases hev : rid = q.1 ∧ x = q.2.2
      · have hqts : q.2.1 ≠ ts := by
          intro h
          exact hq (Prod.ext hev.1.symm (Prod.ext h hev.2.symm))
        rw [hev.1, hev.2] at h_e h_max hA hB
        have himp := ORSetE_add_max_trichotomy h_ir h_in h_cl h_e h_max
          hA hB hqts
        rw [decide_eq_true hev, decide_eq_false hq]
        cases hBq : B q with
        | true => cases A q <;> rfl
        | false =>
          cases hAq : A q with
          | false => rfl
          | true => exact Bool.noConfusion (hBq.symm.trans (himp hAq))
      · rw [decide_eq_false hev, decide_eq_false hq]
        cases B q <;> cases A q <;> rfl
  | rem x =>
    funext q
    show ((B q && (A q && ORSetE.update B (ts, rid, ORSetOp.rem x) q))
        || ((A q && !(B q))
        || (ORSetE.update B (ts, rid, ORSetOp.rem x) q && !(B q))))
      = (A q && !(decide (x = q.2.2)))
    show ((B q && (A q && (B q && !(decide (x = q.2.2)))))
        || ((A q && !(B q))
        || ((B q && !(decide (x = q.2.2))) && !(B q))))
      = (A q && !(decide (x = q.2.2)))
    by_cases hx : x = q.2.2
    · rw [hx] at h_e h_max hA hB
      have himp := ORSetE_rem_max_trichotomy h_ir h_in h_cl h_e h_max hA hB
      rw [decide_eq_true hx]
      cases hBq : B q with
      | true => cases A q <;> rfl
      | false =>
        cases hAq : A q with
        | false => rfl
        | true => exact Bool.noConfusion (hBq.symm.trans (himp hAq))
    · rw [decide_eq_false hx]
      cases B q <;> cases A q <;> rfl

/-! ## §7. The feasible delta laws -/

/-- The redistribution law is a Boolean tautology for the ORSetE merge. -/
theorem orEMergeL_redistribute (B t₀ t₁ t₂ u : ORSetE.State) :
    orEMergeL (orEMergeL B t₀ u) (orEMergeL B t₁ u) (orEMergeL B t₂ u)
      = orEMergeL B (orEMergeL t₀ t₁ t₂) u := by
  funext q
  show ((orEMergeL B t₀ u q && (orEMergeL B t₁ u q && orEMergeL B t₂ u q))
      || ((orEMergeL B t₁ u q && !(orEMergeL B t₀ u q))
      || (orEMergeL B t₂ u q && !(orEMergeL B t₀ u q))))
    = ((B q && (orEMergeL t₀ t₁ t₂ q && u q))
      || ((orEMergeL t₀ t₁ t₂ q && !(B q)) || (u q && !(B q))))
  show ((((B q && (t₀ q && u q)) || ((t₀ q && !(B q)) || (u q && !(B q))))
      && (((B q && (t₁ q && u q)) || ((t₁ q && !(B q)) || (u q && !(B q))))
      && ((B q && (t₂ q && u q)) || ((t₂ q && !(B q)) || (u q && !(B q))))))
      || ((((B q && (t₁ q && u q)) || ((t₁ q && !(B q)) || (u q && !(B q))))
      && !(((B q && (t₀ q && u q)) || ((t₀ q && !(B q)) || (u q && !(B q))))))
      || (((B q && (t₂ q && u q)) || ((t₂ q && !(B q)) || (u q && !(B q))))
      && !(((B q && (t₀ q && u q))
      || ((t₀ q && !(B q)) || (u q && !(B q))))))))
    = ((B q && (((t₀ q && (t₁ q && t₂ q)) || ((t₁ q && !(t₀ q))
      || (t₂ q && !(t₀ q)))) && u q))
      || ((((t₀ q && (t₁ q && t₂ q)) || ((t₁ q && !(t₀ q))
      || (t₂ q && !(t₀ q)))) && !(B q)) || (u q && !(B q))))
  cases B q <;> cases t₀ q <;> cases t₁ q <;> cases t₂ q <;>
    cases u q <;> rfl

/-- **The feasible delta contract for the OR-Set-efficient.** -/
theorem ORSetE_feasibleDeltaVCs3 : FeasibleDeltaVCs3 ORSetE := by
  refine ⟨?_, ?_, ?_⟩
  · -- feasible_init (unconditional for ORSetE)
    intro C ev s _ _
    funext q
    show ((false && (false && s q)) || ((false && !false)
        || (s q && !false))) = s q
    cases s q <;> rfl
  · -- feasible_local_redistribute
    intro C ev₁ ev₂ s₀ B t₁ s₂ e h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂
      h_max hc₀ hB ht₁ hc₂
    -- the e-agnostic exclusion: a tag live in the punctured downset and in
    -- ev₂ but dead in ev₁ ∩ ev₂ is impossible
    have himp2 : ∀ q : ℕ × ℕ × ℕ, B q = true → s₂ q = true →
        s₀ q = true := by
      intro q hqB hqs₂
      have haB := ORSetE_canonical_bound hB hqB
      have ha₂ := ORSetE_canonical_bound hc₂ hqs₂
      have ha₁ : ((q.2.1, q.1, ORSetOp.add q.2.2) : Op ORSetE.AppOp)
          ∈ ev₁ := downset_subset h_cl₁ he₁ haB.1
      refine ORSetE_no_later_kill_live (fun o ho => h_in₁ o ho.1)
        hc₀ ⟨ha₁, ha₂⟩ ?_
      intro k hk₀ hkill hvak
      by_cases hka : k = (q.2.1, q.1, ORSetOp.add q.2.2)
      · rw [hka] at hvak
        exact h_ir _ hvak
      · exact ORSetE_live_no_later_kill hc₂ hqs₂ hk₀.2 hkill hka hvak
    rcases e with ⟨ts, rid, op⟩
    cases op with
    | add x =>
      have hBt : B (rid, ts, x) = false := by
        cases hBt : B (rid, ts, x) with
        | false => rfl
        | true =>
          have hmem := ORSetE_canonical_bound hB hBt
          exact absurd rfl hmem.2
      have hs₀t : s₀ (rid, ts, x) = false := by
        cases h : s₀ (rid, ts, x) with
        | false => rfl
        | true =>
          have hmem := ORSetE_canonical_bound hc₀ h
          exact absurd hmem.2 he₂
      funext q
      show ((s₀ q && ((orEMergeL B t₁
          (ORSetE.update B (ts, rid, ORSetOp.add x)) q) && s₂ q))
          || (((orEMergeL B t₁
          (ORSetE.update B (ts, rid, ORSetOp.add x)) q) && !(s₀ q))
          || (s₂ q && !(s₀ q))))
        = ((B q && ((orEMergeL s₀ t₁ s₂ q)
          && ORSetE.update B (ts, rid, ORSetOp.add x) q))
          || (((orEMergeL s₀ t₁ s₂ q) && !(B q))
          || (ORSetE.update B (ts, rid, ORSetOp.add x) q && !(B q))))
      show ((s₀ q && (((B q && (t₁ q && ((B q
          && !(decide (rid = q.1 ∧ x = q.2.2)))
          || decide (q = (rid, ts, x)))))
          || ((t₁ q && !(B q)) || (((B q
          && !(decide (rid = q.1 ∧ x = q.2.2)))
          || decide (q = (rid, ts, x))) && !(B q)))) && s₂ q))
          || ((((B q && (t₁ q && ((B q
          && !(decide (rid = q.1 ∧ x = q.2.2)))
          || decide (q = (rid, ts, x)))))
          || ((t₁ q && !(B q)) || (((B q
          && !(decide (rid = q.1 ∧ x = q.2.2)))
          || decide (q = (rid, ts, x))) && !(B q)))) && !(s₀ q))
          || (s₂ q && !(s₀ q))))
        = ((B q && (((s₀ q && (t₁ q && s₂ q)) || ((t₁ q && !(s₀ q))
          || (s₂ q && !(s₀ q)))) && ((B q
          && !(decide (rid = q.1 ∧ x = q.2.2)))
          || decide (q = (rid, ts, x)))))
          || ((((s₀ q && (t₁ q && s₂ q)) || ((t₁ q && !(s₀ q))
          || (s₂ q && !(s₀ q)))) && !(B q))
          || (((B q && !(decide (rid = q.1 ∧ x = q.2.2)))
          || decide (q = (rid, ts, x))) && !(B q))))
      by_cases hq : q = (rid, ts, x)
      · subst hq
        rw [hBt, hs₀t, decide_eq_true
          (show ((rid, ts, x) : ℕ × ℕ × ℕ) = (rid, ts, x) from rfl)]
        cases t₁ (rid, ts, x) <;> cases s₂ (rid, ts, x) <;>
          cases hf : decide (rid = ((rid, ts, x) : ℕ × ℕ × ℕ).1
            ∧ x = ((rid, ts, x) : ℕ × ℕ × ℕ).2.2) <;> rfl
      · by_cases hev : rid = q.1 ∧ x = q.2.2
        · rw [decide_eq_true hev, decide_eq_false hq]
          cases hBq : B q with
          | false => cases s₀ q <;> cases t₁ q <;> cases s₂ q <;> rfl
          | true =>
            cases hs₀q : s₀ q with
            | true => cases t₁ q <;> cases s₂ q <;> rfl
            | false =>
              cases hs₂q : s₂ q with
              | false => cases t₁ q <;> rfl
              | true =>
                exact Bool.noConfusion
                  (hs₀q.symm.trans (himp2 q hBq hs₂q))
        · rw [decide_eq_false hev, decide_eq_false hq]
          cases s₀ q <;> cases B q <;> cases t₁ q <;> cases s₂ q <;> rfl
    | rem x =>
      funext q
      show ((s₀ q && ((orEMergeL B t₁
          (ORSetE.update B (ts, rid, ORSetOp.rem x)) q) && s₂ q))
          || (((orEMergeL B t₁
          (ORSetE.update B (ts, rid, ORSetOp.rem x)) q) && !(s₀ q))
          || (s₂ q && !(s₀ q))))
        = ((B q && ((orEMergeL s₀ t₁ s₂ q)
          && ORSetE.update B (ts, rid, ORSetOp.rem x) q))
          || (((orEMergeL s₀ t₁ s₂ q) && !(B q))
          || (ORSetE.update B (ts, rid, ORSetOp.rem x) q && !(B q))))
      show ((s₀ q && (((B q && (t₁ q && (B q && !(decide (x = q.2.2)))))
          || ((t₁ q && !(B q)) || ((B q && !(decide (x = q.2.2)))
          && !(B q)))) && s₂ q))
          || ((((B q && (t₁ q && (B q && !(decide (x = q.2.2)))))
          || ((t₁ q && !(B q)) || ((B q && !(decide (x = q.2.2)))
          && !(B q)))) && !(s₀ q))
          || (s₂ q && !(s₀ q))))
        = ((B q && (((s₀ q && (t₁ q && s₂ q)) || ((t₁ q && !(s₀ q))
          || (s₂ q && !(s₀ q)))) && (B q && !(decide (x = q.2.2)))))
          || ((((s₀ q && (t₁ q && s₂ q)) || ((t₁ q && !(s₀ q))
          || (s₂ q && !(s₀ q)))) && !(B q))
          || ((B q && !(decide (x = q.2.2))) && !(B q))))
      by_cases hx : x = q.2.2
      · rw [decide_eq_true hx]
        cases hBq : B q with
        | false => cases s₀ q <;> cases t₁ q <;> cases s₂ q <;> rfl
        | true =>
          cases hs₀q : s₀ q with
          | true => cases t₁ q <;> cases s₂ q <;> rfl
          | false =>
            cases hs₂q : s₂ q with
            | false => cases t₁ q <;> rfl
            | true =>
              exact Bool.noConfusion
                (hs₀q.symm.trans (himp2 q hBq hs₂q))
      · rw [decide_eq_false hx]
        cases s₀ q <;> cases B q <;> cases t₁ q <;> cases s₂ q <;> rfl
  · -- feasible_redistribute: the unconditional tautology
    intro C ev₁ ev₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _
    exact orEMergeL_redistribute B t₀ t₁ t₂ (ORSetE.update B e)

/-! ## §8. The bundles and the end-to-end theorem -/

theorem ORSetE_updateVCs : UpdateVCs ORSetE.toCRDTSig :=
  ⟨ORSetE_rc_non_comm_directional, ORSetE_no_rc_chain,
   ORSetE_cond_comm_lift⟩

theorem ORSetE_coreVCs3CD : CoreVCs3CD ORSetE :=
  ⟨ORSetE_updateVCs, ORSetE_mergeL_comm⟩

/-- The ternary Join Lemma for the production OR-Set-efficient. -/
theorem ORSetE_joinLemma3 : JoinLemma3 ORSetE :=
  join_lemma3_of_cd_feasible ORSetE_coreVCs3CD ORSetE_feasibleDeltaVCs3
    ORSetE_cdVC3

open LabeledTS in
/-- **End-to-end RA-linearizability for the production OR-Set-efficient.** -/
theorem ORSetE_ra_linearizable3
    (C : Configuration ORSetE)
    (hReach : (labeledTS3 ORSetE).ReachableFrom
      (initConfig ORSetE trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_join ORSetE_joinLemma3 C hReach

/-! ## The Enable-wins flag discharge -/

/-! ## §1. Pointwise value lemmas -/

theorem ewUpdate_en (s : EWFlag.State) (ts r : ℕ) (k : ℕ) :
    EWFlag.update s (ts, r, EWOp.enable) k
      = if k = r then ((s r).1 + 1, true) else s k := rfl

theorem ewUpdate_dis (s : EWFlag.State) (ts r : ℕ) (k : ℕ) :
    EWFlag.update s (ts, r, EWOp.disable) k = ((s k).1, false) := rfl

/-! ## §2. Commutation classification and the update layer -/

theorem EWFlag_commutes_symm {o₁ o₂ : Op EWFlag.AppOp}
    (h : EWFlag.toCRDTSig.commutes o₁ o₂) :
    EWFlag.toCRDTSig.commutes o₂ o₁ :=
  fun s => (h s).symm

theorem EWFlag_comm_en_en (ts₁ r₁ ts₂ r₂ : ℕ) :
    EWFlag.toCRDTSig.commutes (ts₁, r₁, EWOp.enable)
      (ts₂, r₂, EWOp.enable) := by
  intro s
  funext k
  show EWFlag.update (EWFlag.update s (ts₁, r₁, EWOp.enable))
      (ts₂, r₂, EWOp.enable) k
    = EWFlag.update (EWFlag.update s (ts₂, r₂, EWOp.enable))
      (ts₁, r₁, EWOp.enable) k
  rw [ewUpdate_en, ewUpdate_en, ewUpdate_en, ewUpdate_en, ewUpdate_en,
    ewUpdate_en]
  by_cases h12 : r₁ = r₂
  · subst h12
    by_cases hk : k = r₁ <;> simp [hk]
  · by_cases hk2 : k = r₂
    · subst hk2
      rw [if_pos rfl, if_neg (fun h => h12 h.symm), if_pos rfl,
        if_neg (fun h => h12 h.symm)]
    · rw [if_neg hk2]
      by_cases hk1 : k = r₁
      · subst hk1
        rw [if_pos rfl, if_pos rfl, if_neg h12]
      · rw [if_neg hk1, if_neg hk1, if_neg hk2]

theorem EWFlag_comm_dis_dis (ts₁ r₁ ts₂ r₂ : ℕ) :
    EWFlag.toCRDTSig.commutes (ts₁, r₁, EWOp.disable)
      (ts₂, r₂, EWOp.disable) :=
  fun s => rfl

theorem EWFlag_ncomm_en_dis (ts₁ r₁ ts₂ r₂ : ℕ) :
    ¬ EWFlag.toCRDTSig.commutes (ts₁, r₁, EWOp.enable)
      (ts₂, r₂, EWOp.disable) := by
  intro h
  have h0 := congrFun (h EWFlag.init) r₁
  simp [EWFlag_update_eq, ewUpdate, EWFlag_init_eq] at h0

/-- An Enable fails to commute only with a Disable. -/
theorem EWFlag_ncomm_en_dest {ts r : ℕ} {o : Op EWFlag.AppOp}
    (h : ¬ EWFlag.toCRDTSig.commutes (ts, r, EWOp.enable) o) :
    o.2.2 = EWOp.disable := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | enable => exact absurd (EWFlag_comm_en_en ts r ts' r') h
  | disable => rfl

/-- A Disable fails to commute only with an Enable. -/
theorem EWFlag_ncomm_dis_dest {ts r : ℕ} {o : Op EWFlag.AppOp}
    (h : ¬ EWFlag.toCRDTSig.commutes (ts, r, EWOp.disable) o) :
    o.2.2 = EWOp.enable := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | enable => rfl
  | disable => exact absurd (EWFlag_comm_dis_dis ts r ts' r') h

theorem EWFlag_no_rc_chain :
    ∀ o₁ o₂ o₃ : Op EWFlag.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (EWFlag.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         EWFlag.toCRDTSig.rc o₂ o₃ = RcRes.Fst_then_snd) := by
  rintro ⟨ts₁, r₁, op₁⟩ ⟨ts₂, r₂, op₂⟩ ⟨ts₃, r₃, op₃⟩ _ _ ⟨h1, h2⟩
  cases op₂ with
  | enable =>
    cases op₃ with
    | enable => exact RcRes.noConfusion (show RcRes.Either = _ from h2)
    | disable =>
      exact RcRes.noConfusion (show RcRes.Snd_then_fst = _ from h2)
  | disable =>
    cases op₁ with
    | enable =>
      exact RcRes.noConfusion (show RcRes.Snd_then_fst = _ from h1)
    | disable => exact RcRes.noConfusion (show RcRes.Either = _ from h1)

/-- The guarded field. NOTE (T10.7): the `differentReplicas` guard is NOT
load-bearing for the Enable-wins flag — it has no `rc = Either`
non-commuting pairs (same-replica Enables commute; Enable/Disable is
rc-ordered at any replica pair). -/
theorem EWFlag_rc_non_comm_directional :
    ∀ o₁ o₂ : Op EWFlag.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (¬ EWFlag.toCRDTSig.commutes o₁ o₂ ↔
       (EWFlag.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∨
        EWFlag.toCRDTSig.rc o₂ o₁ = RcRes.Fst_then_snd)) := by
  intro o₁ o₂ _ _
  constructor
  · intro hnc
    rcases o₁ with ⟨ts₁, r₁, op₁⟩
    cases op₁ with
    | enable =>
      have h2 := EWFlag_ncomm_en_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = EWOp.disable := h2
      subst h2'
      right
      rfl
    | disable =>
      have h2 := EWFlag_ncomm_dis_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = EWOp.enable := h2
      subst h2'
      left
      rfl
  · rintro (h | h)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₁ with
      | enable =>
        exfalso
        cases op₂ with
        | enable => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | disable =>
          exact RcRes.noConfusion (show RcRes.Snd_then_fst = _ from h)
      | disable =>
        cases op₂ with
        | enable =>
          intro hc
          exact EWFlag_ncomm_en_dis ts₂ r₂ ts₁ r₁
            (EWFlag_commutes_symm hc)
        | disable =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₂ with
      | enable =>
        exfalso
        cases op₁ with
        | enable => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | disable =>
          exact RcRes.noConfusion (show RcRes.Snd_then_fst = _ from h)
      | disable =>
        cases op₁ with
        | enable => exact EWFlag_ncomm_en_dis ts₁ r₁ ts₂ r₂
        | disable =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)

/-- Agreement invariant for `cond_comm_lift`: equal counters everywhere,
equal values off the perturbed key. -/
private noncomputable def ewAgree (r : ℕ) (a b : EWFlag.State) : Prop :=
  (∀ k, (a k).1 = (b k).1) ∧ ∀ k, k ≠ r → a k = b k

private theorem ewAgree_update {r : ℕ} {a b : EWFlag.State}
    (h : ewAgree r a b) (o : Op EWFlag.AppOp) :
    ewAgree r (EWFlag.update a o) (EWFlag.update b o) := by
  rcases o with ⟨ts, r', op⟩
  cases op with
  | enable =>
    constructor
    · intro k
      rw [ewUpdate_en, ewUpdate_en]
      by_cases hk : k = r'
      · rw [if_pos hk, if_pos hk]
        simp [h.1 r']
      · rw [if_neg hk, if_neg hk]
        exact h.1 k
    · intro k hk
      rw [ewUpdate_en, ewUpdate_en]
      by_cases hkr : k = r'
      · rw [if_pos hkr, if_pos hkr, h.1 r']
      · rw [if_neg hkr, if_neg hkr]
        exact h.2 k hk
  | disable =>
    constructor
    · intro k
      rw [ewUpdate_dis, ewUpdate_dis]
      simp [h.1 k]
    · intro k hk
      rw [ewUpdate_dis, ewUpdate_dis, h.1 k]

private theorem ewAgree_fold {r : ℕ} {a b : EWFlag.State}
    (h : ewAgree r a b) (π : List (Op EWFlag.AppOp)) :
    ewAgree r (applySeq EWFlag.toCRDTSig a π)
      (applySeq EWFlag.toCRDTSig b π) := by
  induction π generalizing a b with
  | nil => exact h
  | cons o π ih => exact ih (ewAgree_update h o)

theorem EWFlag_cond_comm_lift :
    ∀ (s : EWFlag.State) (e e' e'' : Op EWFlag.AppOp)
      (π : List (Op EWFlag.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      EWFlag.toCRDTSig.rc e e' = RcRes.Fst_then_snd →
      ¬ EWFlag.toCRDTSig.commutes e' e'' →
      EWFlag.update (applySeq EWFlag.toCRDTSig
          (EWFlag.update (EWFlag.update s e') e) π) e''
        = EWFlag.update (applySeq EWFlag.toCRDTSig
            (EWFlag.update (EWFlag.update s e) e') π) e'' := by
  intro s e e' e'' π _ _ _ hrc hnc
  rcases e with ⟨ts₁, r₁, op₁⟩
  rcases e' with ⟨ts₂, r₂, op₂⟩
  cases op₁ with
  | enable =>
    exfalso
    cases op₂ with
    | enable => exact RcRes.noConfusion (show RcRes.Either = _ from hrc)
    | disable =>
      exact RcRes.noConfusion (show RcRes.Snd_then_fst = _ from hrc)
  | disable =>
    cases op₂ with
    | disable =>
      exact absurd (show RcRes.Either = _ from hrc)
        (fun hh => RcRes.noConfusion hh)
    | enable =>
      have hdest := EWFlag_ncomm_en_dest hnc
      rcases e'' with ⟨ts₃, r₃, op₃⟩
      have hdest' : op₃ = EWOp.disable := hdest
      subst hdest'
      -- prefixes agree on counters everywhere and off r₂ entirely
      have hpre : ewAgree r₂
          (EWFlag.update (EWFlag.update s (ts₂, r₂, EWOp.enable))
            (ts₁, r₁, EWOp.disable))
          (EWFlag.update (EWFlag.update s (ts₁, r₁, EWOp.disable))
            (ts₂, r₂, EWOp.enable)) := by
        constructor
        · intro k
          simp only [ewUpdate_dis, ewUpdate_en]
          by_cases hk : k = r₂ <;> simp [hk]
        · intro k hk
          simp only [ewUpdate_dis, ewUpdate_en]
          simp [hk]
      have hagree := ewAgree_fold hpre π
      funext k
      rw [ewUpdate_dis, ewUpdate_dis, hagree.1 k]

/-! ## §3. The counting layer -/

/-- Bool predicate: an Enable by replica `k`. -/
noncomputable def ewEnK (k : ℕ) (o : Op EWFlag.AppOp) : Bool :=
  decide (o.2.1 = k ∧ o.2.2 = EWOp.enable)

/-- The Enables-by-`k` of an event set. -/
def ewEnSet (k : ℕ) (F : Set (Op EWFlag.AppOp)) : Set (Op EWFlag.AppOp) :=
  {o | o ∈ F ∧ o.2.1 = k ∧ o.2.2 = EWOp.enable}

/-- The filtered enumeration enumerates the Enables-by-`k`. -/
theorem ew_filter_perm {ρ : List (Op EWFlag.AppOp)}
    {F : Set (Op EWFlag.AppOp)} (h : listPermOf ρ F) (k : ℕ) :
    listPermOf (ρ.filter (ewEnK k)) (ewEnSet k F) := by
  refine ⟨h.1.filter _, fun o => ?_⟩
  rw [List.mem_filter]
  constructor
  · rintro ⟨ho, hd⟩
    exact ⟨(h.2 o).mp ho, of_decide_eq_true hd⟩
  · rintro ⟨ho, hd⟩
    exact ⟨(h.2 o).mpr ho, decide_eq_true hd⟩

/-- Counts across nodup enumerations: same set, same count. -/
theorem ew_count_eq {l l' : List (Op EWFlag.AppOp)}
    {S : Set (Op EWFlag.AppOp)}
    (h : listPermOf l S) (h' : listPermOf l' S) : l.length = l'.length :=
  listPermOf_length_eq h h'

/-- Monotone counts along set inclusion. -/
theorem ew_count_le {l l' : List (Op EWFlag.AppOp)}
    {S S' : Set (Op EWFlag.AppOp)}
    (h : listPermOf l S) (h' : listPermOf l' S') (hsub : S ⊆ S') :
    l.length ≤ l'.length := by
  have hsp : List.Subperm l l' := by
    refine List.subperm_of_subset h.1 ?_
    intro a ha
    exact (h'.2 a).mpr (hsub ((h.2 a).mp ha))
  exact hsp.length_le

/-- Strict counts from a witness outside the smaller set. -/
theorem ew_count_lt {l l' : List (Op EWFlag.AppOp)}
    {S S' : Set (Op EWFlag.AppOp)} {x : Op EWFlag.AppOp}
    (h : listPermOf l S) (h' : listPermOf l' S') (hsub : S ⊆ S')
    (hx : x ∈ S') (hxn : x ∉ S) :
    l.length < l'.length := by
  have hnd : (x :: l).Nodup := by
    rw [List.nodup_cons]
    exact ⟨fun hmem => hxn ((h.2 x).mp hmem), h.1⟩
  have hsp : List.Subperm (x :: l) l' := by
    refine List.subperm_of_subset hnd ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact (h'.2 a).mpr hx
    · exact (h'.2 a).mpr (hsub ((h.2 a).mp ha'))
  have hle := hsp.length_le
  simp only [List.length_cons] at hle
  omega

/-- Length splits along any Bool predicate. -/
theorem ew_filter_split {α : Type} (l : List α) (q : α → Bool) :
    l.length = (l.filter q).length
      + (l.filter (fun a => !(q a))).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hq : q a <;>
      simp [List.filter_cons, hq, ih] <;> omega

/-- The fold's counter at `k` counts the Enables-by-`k`. -/
theorem ew_fold_cnt (ρ : List (Op EWFlag.AppOp)) (k : ℕ) :
    (applySeq EWFlag.toCRDTSig EWFlag.init ρ k).1
      = (ρ.filter (ewEnK k)).length := by
  induction ρ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ρ o ih =>
    rw [applySeq_append_single, List.filter_append, List.length_append]
    rcases o with ⟨ts, r, op⟩
    cases op with
    | enable =>
      rw [ewUpdate_en]
      by_cases hk : k = r
      · subst hk
        rw [if_pos rfl]
        have : ewEnK k (ts, k, EWOp.enable) = true :=
          decide_eq_true ⟨rfl, rfl⟩
        simp [List.filter_cons, this, ih]
      · rw [if_neg hk]
        have : ewEnK k (ts, r, EWOp.enable) = false :=
          decide_eq_false (fun ⟨hr, _⟩ => hk hr.symm)
        simp [List.filter_cons, this, ih]
    | disable =>
      rw [ewUpdate_dis]
      have : ewEnK k (ts, r, EWOp.disable) = false :=
        decide_eq_false (fun ⟨_, hop⟩ => EWOp.noConfusion hop)
      simp [List.filter_cons, this, ih]

/-! ## §4. The flag σ-facts -/

/-- List-level (K): a set flag has an Enable-by-`k` with no later Disable. -/
theorem ew_flag_split {ρ : List (Op EWFlag.AppOp)} {k : ℕ}
    (h : (applySeq EWFlag.toCRDTSig EWFlag.init ρ k).2 = true) :
    ∃ α w β, ρ = α ++ w :: β ∧ (w : Op EWFlag.AppOp).2.1 = k
      ∧ w.2.2 = EWOp.enable
      ∧ ∀ d ∈ β, (d : Op EWFlag.AppOp).2.2 ≠ EWOp.disable := by
  induction ρ using List.reverseRecOn with
  | nil => exact absurd (show (false : Bool) = true from h) Bool.noConfusion
  | append_singleton ρ o ih =>
    rw [applySeq_append_single] at h
    rcases o with ⟨ts, r, op⟩
    cases op with
    | enable =>
      rw [ewUpdate_en] at h
      by_cases hk : k = r
      · exact ⟨ρ, ((ts, r, EWOp.enable) : Op EWFlag.AppOp), [], rfl,
          hk.symm, rfl, fun d hd => absurd hd List.not_mem_nil⟩
      · rw [if_neg hk] at h
        obtain ⟨α, w, β, heq, hw1, hw2, hβ⟩ := ih h
        refine ⟨α, w, β ++ [((ts, r, EWOp.enable) : Op EWFlag.AppOp)],
          ?_, hw1, hw2, ?_⟩
        · rw [heq, List.append_assoc]
          rfl
        · intro d hd
          rcases List.mem_append.mp hd with hd | hd
          · exact hβ d hd
          · rw [List.mem_singleton] at hd
            subst hd
            exact fun hh => EWOp.noConfusion hh
    | disable =>
      rw [ewUpdate_dis] at h
      exact absurd h Bool.noConfusion

/-- The flag stays set if no Disable follows. -/
theorem ew_flag_stays {k : ℕ} :
    ∀ (β : List (Op EWFlag.AppOp)) (s : EWFlag.State),
      (s k).2 = true →
      (∀ d ∈ β, (d : Op EWFlag.AppOp).2.2 ≠ EWOp.disable) →
      (applySeq EWFlag.toCRDTSig s β k).2 = true := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : (EWFlag.update s o k).2 = true := by
      rcases o with ⟨ts, r, op⟩
      cases op with
      | enable =>
        rw [ewUpdate_en]
        by_cases hk : k = r
        · rw [if_pos hk]
        · rw [if_neg hk]
          exact hs
      | disable =>
        exact absurd rfl (hβ _ List.mem_cons_self)
    exact ih (EWFlag.update s o) hupd
      (fun d hd => hβ d (List.mem_cons_of_mem _ hd))

/-- **(K)**: a set flag at `k` yields an Enable-by-`k` in the set with no
Disable of the set vis-after it. -/
theorem ew_flag_witness
    {C : Sal.Emulation.Configuration EWFlag.toCRDTSig}
    {F : Set (Op EWFlag.AppOp)} {s : EWFlag.State} {k : ℕ}
    (hs : IsCanonicalState C F s) (hf : (s k).2 = true) :
    ∃ w ∈ F, (w : Op EWFlag.AppOp).2.1 = k ∧ w.2.2 = EWOp.enable ∧
      ∀ d ∈ F, (d : Op EWFlag.AppOp).2.2 = EWOp.disable → ¬ C.vis w d := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold] at hf
  obtain ⟨α, w, β, heq, hw1, hw2, hβ⟩ := ew_flag_split hf
  subst heq
  refine ⟨w, (hperm.2 w).mp (List.mem_append_right _ List.mem_cons_self),
    hw1, hw2, ?_⟩
  intro d hdF hdT hvis
  -- the edge w → d forces d after w; β has no disables; d ≠ w by shape
  have hnc : ¬ EWFlag.toCRDTSig.commutes w d := by
    rcases w with ⟨tsw, rw', opw⟩
    have hw2' : opw = EWOp.enable := hw2
    subst hw2'
    rcases d with ⟨tsd, rd, opd⟩
    have hdT' : opd = EWOp.disable := hdT
    subst hdT'
    exact EWFlag_ncomm_en_dis tsw rw' tsd rd
  have hedge : loOn C F w d := Or.inl ⟨hvis, hnc⟩
  have hdρ : d ∈ α ++ w :: β := (hperm.2 d).mpr hdF
  have hdw : d ≠ w := by
    intro h
    rw [h, hw2] at hdT
    exact EWOp.noConfusion hdT
  rcases List.mem_append.mp hdρ with hd | hd
  · -- d before w with a mandatory edge w → d: respects violation
    have hcross := (List.pairwise_append.mp hresp).2.2
    exact hcross d hd w List.mem_cons_self hedge
  · rcases List.mem_cons.mp hd with hd | hd
    · exact hdw hd
    · exact hβ d hd hdT

/-- **(L)**: an Enable-by-`k` with no Disable of the set vis-after it sets
the flag. -/
theorem ew_live_flag
    {C : Sal.Emulation.Configuration EWFlag.toCRDTSig}
    {F : Set (Op EWFlag.AppOp)} {s : EWFlag.State} {k tsw rw' : ℕ}
    (hs : IsCanonicalState C F s)
    (hwF : (tsw, rw', EWOp.enable) ∈ F) (hwk : rw' = k)
    (hno : ∀ d ∈ F, (d : Op EWFlag.AppOp).2.2 = EWOp.disable →
      ¬ C.vis (tsw, rw', EWOp.enable) d) :
    (s k).2 = true := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  rw [← hfold]
  have hwρ : ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp) ∈ ρ :=
    (hperm.2 _).mpr hwF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem hwρ
  subst hsplit
  have hcons := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  have hnodis : ∀ d ∈ β, (d : Op EWFlag.AppOp).2.2 ≠ EWOp.disable := by
    intro d hd hdT
    have hdF : d ∈ F := (hperm.2 d).mp
      (List.mem_append_right _ (List.mem_cons_of_mem _ hd))
    have hnovis := hno d hdF hdT
    rcases d with ⟨tsd, rd, opd⟩
    have hdT' : opd = EWOp.disable := hdT
    subst hdT'
    have hnc_dw : ¬ EWFlag.toCRDTSig.commutes (tsd, rd, EWOp.disable)
        (tsw, rw', EWOp.enable) :=
      fun h => EWFlag_ncomm_en_dis tsw rw' tsd rd
        (EWFlag_commutes_symm h)
    by_cases hvd : C.vis (tsd, rd, EWOp.disable) (tsw, rw', EWOp.enable)
    · exact hcons.1 _ hd (Or.inl ⟨hvd, hnc_dw⟩)
    · refine hcons.1 _ hd (Or.inr ⟨hvd, hnovis, rfl, ?_⟩)
      rintro ⟨e₃, he₃F, hve₃, hnce₃⟩
      exact hno e₃ he₃F (EWFlag_ncomm_en_dest hnce₃) hve₃
  have hstep : applySeq EWFlag.toCRDTSig EWFlag.init
      (α ++ ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp) :: β)
      = applySeq EWFlag.toCRDTSig
          (EWFlag.update (applySeq EWFlag.toCRDTSig EWFlag.init α)
            (tsw, rw', EWOp.enable)) β := by
    simp [applySeq, List.foldl_append]
  rw [hstep]
  refine ew_flag_stays β _ ?_ hnodis
  rw [ewUpdate_en, if_pos hwk.symm]

/-! ## §6. The direct join for the Enable-wins flag -/

/-- **The full-closure join lemma for the Enable-wins flag**, proved
directly per key: counters by inclusion–exclusion of enable-counts, flags by
the four-corner liveness analysis. The `fa ∧ ¬fb` corner is the
theorem-backed certification of the production `merge_flag` (see the file
header). -/
theorem EWFlag_joinLemma3F : JoinLemma3F EWFlag := by
  intro C F₁ F₂ l a b h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ hcl hca hcb
  classical
  have hU : UpdateVCs EWFlag.toCRDTSig :=
    ⟨EWFlag_rc_non_comm_directional, EWFlag_no_rc_chain,
     EWFlag_cond_comm_lift⟩
  have h_inU : ∀ o ∈ F₁ ∪ F₂, o ∈ C.events := by
    rintro o (h | h)
    · exact h_in₁ o h
    · exact h_in₂ o h
  obtain ⟨ρ₀, hp₀, -, hf₀⟩ := id hcl
  obtain ⟨ρ₁, hp₁, -, hf₁⟩ := id hca
  obtain ⟨ρ₂, hp₂, -, hf₂⟩ := id hcb
  have hpU := listPermOf_union (D := EWFlag.toCRDTSig) hp₁ hp₂
  obtain ⟨s, hcs⟩ : ∃ s, IsCanonicalState C (F₁ ∪ F₂) s :=
    isCanonicalState_exists_u hU h_tr h_ir hpU h_inU
  suffices hEq : EWFlag.mergeL l a b = s by
    rw [hEq]
    exact hcs
  obtain ⟨ρU, hpUU, -, hfU⟩ := id hcs
  -- pointwise values via the folds
  funext k
  -- counters
  have hcnt₀ : (l k).1 = (ρ₀.filter (ewEnK k)).length := by
    rw [← hf₀]; exact ew_fold_cnt ρ₀ k
  have hcnt₁ : (a k).1 = (ρ₁.filter (ewEnK k)).length := by
    rw [← hf₁]; exact ew_fold_cnt ρ₁ k
  have hcnt₂ : (b k).1 = (ρ₂.filter (ewEnK k)).length := by
    rw [← hf₂]; exact ew_fold_cnt ρ₂ k
  have hcntU : (s k).1 = (ρU.filter (ewEnK k)).length := by
    rw [← hfU]; exact ew_fold_cnt ρU k
  -- inclusion–exclusion of the enable counts
  have hpf₀ := ew_filter_perm hp₀ k
  have hpf₁ := ew_filter_perm hp₁ k
  have hpf₂ := ew_filter_perm hp₂ k
  have hpfU := ew_filter_perm hpUU k
  -- the explicit union enumeration splits the count
  have hIE : (ρU.filter (ewEnK k)).length + (ρ₀.filter (ewEnK k)).length
      = (ρ₁.filter (ewEnK k)).length + (ρ₂.filter (ewEnK k)).length := by
    -- X := enables of F₂ outside F₁, counted from ρ₂'s enumeration
    have hsplit := ew_filter_split (ρ₂.filter (ewEnK k))
      (fun o => decide (o ∈ F₁))
    -- the ∈F₁ part enumerates ewEnSet k (F₁ ∩ F₂)
    have hin_perm : listPermOf
        ((ρ₂.filter (ewEnK k)).filter (fun o => decide (o ∈ F₁)))
        (ewEnSet k (F₁ ∩ F₂)) := by
      refine ⟨hpf₂.1.filter _, fun o => ?_⟩
      rw [List.mem_filter]
      constructor
      · rintro ⟨ho, hd⟩
        have := (hpf₂.2 o).mp ho
        exact ⟨⟨of_decide_eq_true hd, this.1⟩, this.2⟩
      · rintro ⟨⟨ho₁, ho₂⟩, hok⟩
        exact ⟨(hpf₂.2 o).mpr ⟨ho₂, hok⟩, decide_eq_true ho₁⟩
    -- the ∉F₁ part enumerates ewEnSet k (F₂ \ F₁)
    have hout_perm : listPermOf
        ((ρ₂.filter (ewEnK k)).filter (fun o => !(decide (o ∈ F₁))))
        (ewEnSet k (F₂ \ F₁)) := by
      refine ⟨hpf₂.1.filter _, fun o => ?_⟩
      rw [List.mem_filter]
      constructor
      · rintro ⟨ho, hd⟩
        have hmem := (hpf₂.2 o).mp ho
        have hnot : o ∉ F₁ := by
          intro hin
          rw [decide_eq_true hin] at hd
          exact Bool.noConfusion hd
        exact ⟨⟨hmem.1, hnot⟩, hmem.2⟩
      · rintro ⟨⟨ho₂, hno₁⟩, hok⟩
        refine ⟨(hpf₂.2 o).mpr ⟨ho₂, hok⟩, ?_⟩
        rw [decide_eq_false hno₁]
        rfl
    -- the union enumeration's filter splits over ρ₁ and the fresh part
    have hUperm₂ : listPermOf
        ((ρ₂.filter (fun o => decide (o ∉ ρ₁))).filter (ewEnK k))
        (ewEnSet k (F₂ \ F₁)) := by
      refine ⟨(hp₂.1.filter _).filter _, fun o => ?_⟩
      rw [List.mem_filter, List.mem_filter]
      constructor
      · rintro ⟨⟨ho₂, hd₁⟩, hdk⟩
        have hno₁ : o ∉ F₁ := fun hin =>
          (of_decide_eq_true hd₁) ((hp₁.2 o).mpr hin)
        exact ⟨⟨(hp₂.2 o).mp ho₂, hno₁⟩, of_decide_eq_true hdk⟩
      · rintro ⟨⟨ho₂, hno₁⟩, hok⟩
        refine ⟨⟨(hp₂.2 o).mpr ho₂, ?_⟩, decide_eq_true hok⟩
        exact decide_eq_true (fun hmem => hno₁ ((hp₁.2 o).mp hmem))
    have hcU : (ρU.filter (ewEnK k)).length
        = ((ρ₁ ++ ρ₂.filter (fun o => decide (o ∉ ρ₁))).filter
            (ewEnK k)).length := by
      refine ew_count_eq hpfU (ew_filter_perm hpU k)
    rw [hcU, List.filter_append, List.length_append]
    have h1 : ((ρ₂.filter (fun o => decide (o ∉ ρ₁))).filter
        (ewEnK k)).length
        = ((ρ₂.filter (ewEnK k)).filter
            (fun o => !(decide (o ∈ F₁)))).length :=
      ew_count_eq hUperm₂ hout_perm
    have h2 : (ρ₀.filter (ewEnK k)).length
        = ((ρ₂.filter (ewEnK k)).filter
            (fun o => decide (o ∈ F₁))).length :=
      ew_count_eq hpf₀ hin_perm
    omega
  -- flags: (K)/(L) corner analysis
  -- the union-side liveness helper for a witness outside F₂
  have hliveU₁ : ∀ tsw rw', (tsw, rw', EWOp.enable) ∈ F₁ →
      ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp) ∉ F₂ →
      (∀ d ∈ F₁, (d : Op EWFlag.AppOp).2.2 = EWOp.disable →
        ¬ C.vis (tsw, rw', EWOp.enable) d) →
      ∀ d ∈ F₁ ∪ F₂, (d : Op EWFlag.AppOp).2.2 = EWOp.disable →
        ¬ C.vis (tsw, rw', EWOp.enable) d := by
    intro tsw rw' hw hnF₂ hlive d hd hdT hvis
    rcases hd with hd | hd
    · exact hlive d hd hdT hvis
    · exact hnF₂ (h_cl₂ _ d hvis hd)
  -- the flag equation
  have hflag : (EWFlag.mergeL l a b k).2 = (s k).2 := by
    show (ewMergeCF (l k) (a k) (b k)).2 = (s k).2
    show (if (a k).2 && (b k).2 then true
        else if !(a k).2 && !(b k).2 then false
        else if (a k).2 then decide ((a k).1 > (l k).1)
        else decide ((b k).1 > (l k).1)) = (s k).2
    cases hfa : (a k).2 with
    | true =>
      cases hfb : (b k).2 with
      | true =>
        -- both live: the vis-later witness is union-live
        obtain ⟨wa, hwaF, hwak, hwaE, hwaL⟩ := ew_flag_witness hca hfa
        obtain ⟨wb, hwbF, hwbk, hwbE, hwbL⟩ := ew_flag_witness hcb hfb
        rcases wa with ⟨tsa, ra, opa⟩
        have : opa = EWOp.enable := hwaE
        subst this
        rcases wb with ⟨tsb, rb, opb⟩
        have : opb = EWOp.enable := hwbE
        subst this
        have hsU : (s k).2 = true := by
          by_cases hab : ((tsa, ra, EWOp.enable) : Op EWFlag.AppOp)
              = (tsb, rb, EWOp.enable)
          · refine ew_live_flag hcs (Or.inl hwaF) hwak ?_
            intro d hd hdT hvis
            rcases hd with hd | hd
            · exact hwaL d hd hdT hvis
            · rw [hab] at hvis
              exact hwbL d hd hdT hvis
          · obtain ⟨r1', s1', hL1, hs1⟩ := h_in₁ _ hwaF
            obtain ⟨r2', s2', hL2, hs2⟩ := h_in₂ _ hwbF
            have hrep : ra = rb := hwak.trans hwbk.symm
            rcases C.vis_total_same_replica hL1 hs1 hL2 hs2 hab hrep
              with hv | hv
            · -- wa before wb: wb is union-live
              refine ew_live_flag hcs (Or.inr hwbF) hwbk ?_
              intro d hd hdT hvis
              rcases hd with hd | hd
              · exact hwaL d hd hdT (h_tr hv hvis)
              · exact hwbL d hd hdT hvis
            · -- wb before wa: wa is union-live
              refine ew_live_flag hcs (Or.inl hwaF) hwak ?_
              intro d hd hdT hvis
              rcases hd with hd | hd
              · exact hwaL d hd hdT hvis
              · exact hwbL d hd hdT (h_tr hv hvis)
        rw [hsU]
        rfl
      | false =>
        -- fa ∧ ¬fb: the flag equals the counter comparison N₁ > N₀
        have hiff : (s k).2 = true ↔ (a k).1 > (l k).1 := by
          constructor
          · intro hsU
            obtain ⟨w, hwF, hwk, hwE, hwL⟩ := ew_flag_witness hcs hsU
            rcases w with ⟨tsw, rw', opw⟩
            have : opw = EWOp.enable := hwE
            subst this
            -- w is not in F₂ (else live there, contradicting ¬fb)
            have hwn₂ : ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp)
                ∉ F₂ := by
              intro hw₂
              have : (b k).2 = true := by
                refine ew_live_flag hcb hw₂ hwk ?_
                intro d hd hdT hvis
                exact hwL d (Or.inr hd) hdT hvis
              rw [hfb] at this
              exact Bool.noConfusion this
            have hw₁ : ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp)
                ∈ F₁ := by
              rcases hwF with h | h
              · exact h
              · exact absurd h hwn₂
            -- strict count via the witness
            rw [hcnt₁, hcnt₀]
            exact ew_count_lt hpf₀ hpf₁
              (fun o ho => ⟨ho.1.1, ho.2⟩)
              ⟨hw₁, hwk, rfl⟩ (fun ho => hwn₂ ho.1.2)
          · intro hgt
            rw [hcnt₁, hcnt₀] at hgt
            -- a witness enable in F₁ outside F₀ exists
            have hwit : ∃ g ∈ ewEnSet k F₁, g ∉ ewEnSet k (F₁ ∩ F₂) := by
              by_contra hno
              push_neg at hno
              have := ew_count_le hpf₁ hpf₀ hno
              omega
            obtain ⟨g, hg₁, hg₀⟩ := hwit
            have hgn₂ : g ∉ F₂ := fun h =>
              hg₀ ⟨⟨hg₁.1, h⟩, hg₁.2⟩
            rcases g with ⟨tsg, rg, opg⟩
            have hgE : opg = EWOp.enable := hg₁.2.2
            subst hgE
            have hgk : rg = k := hg₁.2.1
            -- the live witness of a
            obtain ⟨wa, hwaF, hwak, hwaE, hwaL⟩ := ew_flag_witness hca hfa
            rcases wa with ⟨tsa, ra, opa⟩
            have : opa = EWOp.enable := hwaE
            subst this
            by_cases hwan₂ : ((tsa, ra, EWOp.enable) : Op EWFlag.AppOp)
                ∈ F₂
            · -- wa ∈ F₂: then g is after wa (full closure), and union-live
              have hgne : ((tsg, rg, EWOp.enable) : Op EWFlag.AppOp)
                  ≠ (tsa, ra, EWOp.enable) := by
                intro h
                rw [h] at hgn₂
                exact hgn₂ hwan₂
              obtain ⟨rg', sg', hLg, hsg⟩ := h_in₁ _ hg₁.1
              obtain ⟨ra', sa', hLa, hsa⟩ := h_in₁ _ hwaF
              have hrep : rg = ra := hgk.trans hwak.symm
              rcases C.vis_total_same_replica hLg hsg hLa hsa hgne hrep
                with hv | hv
              · -- vis g wa with wa ∈ F₂: full closure drags g into F₂ ✗
                exact absurd (h_cl₂ _ _ hv hwan₂) hgn₂
              · -- vis wa g: g is union-live
                refine ew_live_flag hcs (Or.inl hg₁.1) hgk ?_
                intro d hd hdT hvis
                rcases hd with hd | hd
                · exact hwaL d hd hdT (h_tr hv hvis)
                · exact hgn₂ (h_cl₂ _ d hvis hd)
            · -- wa ∉ F₂: wa itself is union-live
              refine ew_live_flag hcs (Or.inl hwaF) hwak
                (hliveU₁ tsa ra hwaF hwan₂ hwaL)
        by_cases hgt : (a k).1 > (l k).1
        · rw [decide_eq_true hgt, (hiff.mpr hgt)]
          rfl
        · have hsf : (s k).2 = false := by
            cases hsf : (s k).2 with
            | false => rfl
            | true => exact absurd (hiff.mp hsf) hgt
          rw [decide_eq_false hgt, hsf]
          rfl
    | false =>
      cases hfb : (b k).2 with
      | true =>
        -- ¬fa ∧ fb: mirror with N₂ > N₀
        have hiff : (s k).2 = true ↔ (b k).1 > (l k).1 := by
          constructor
          · intro hsU
            obtain ⟨w, hwF, hwk, hwE, hwL⟩ := ew_flag_witness hcs hsU
            rcases w with ⟨tsw, rw', opw⟩
            have : opw = EWOp.enable := hwE
            subst this
            have hwn₁ : ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp)
                ∉ F₁ := by
              intro hw₁
              have : (a k).2 = true := by
                refine ew_live_flag hca hw₁ hwk ?_
                intro d hd hdT hvis
                exact hwL d (Or.inl hd) hdT hvis
              rw [hfa] at this
              exact Bool.noConfusion this
            have hw₂ : ((tsw, rw', EWOp.enable) : Op EWFlag.AppOp)
                ∈ F₂ := by
              rcases hwF with h | h
              · exact absurd h hwn₁
              · exact h
            rw [hcnt₂, hcnt₀]
            exact ew_count_lt hpf₀ hpf₂
              (fun o ho => ⟨ho.1.2, ho.2⟩)
              ⟨hw₂, hwk, rfl⟩ (fun ho => hwn₁ ho.1.1)
          · intro hgt
            rw [hcnt₂, hcnt₀] at hgt
            have hwit : ∃ g ∈ ewEnSet k F₂, g ∉ ewEnSet k (F₁ ∩ F₂) := by
              by_contra hno
              push_neg at hno
              have := ew_count_le hpf₂ hpf₀ hno
              omega
            obtain ⟨g, hg₂, hg₀⟩ := hwit
            have hgn₁ : g ∉ F₁ := fun h =>
              hg₀ ⟨⟨h, hg₂.1⟩, hg₂.2⟩
            rcases g with ⟨tsg, rg, opg⟩
            have hgE : opg = EWOp.enable := hg₂.2.2
            subst hgE
            have hgk : rg = k := hg₂.2.1
            obtain ⟨wb, hwbF, hwbk, hwbE, hwbL⟩ := ew_flag_witness hcb hfb
            rcases wb with ⟨tsb, rb, opb⟩
            have : opb = EWOp.enable := hwbE
            subst this
            by_cases hwbn₁ : ((tsb, rb, EWOp.enable) : Op EWFlag.AppOp)
                ∈ F₁
            · have hgne : ((tsg, rg, EWOp.enable) : Op EWFlag.AppOp)
                  ≠ (tsb, rb, EWOp.enable) := by
                intro h
                rw [h] at hgn₁
                exact hgn₁ hwbn₁
              obtain ⟨rg', sg', hLg, hsg⟩ := h_in₂ _ hg₂.1
              obtain ⟨rb', sb', hLb, hsb⟩ := h_in₂ _ hwbF
              have hrep : rg = rb := hgk.trans hwbk.symm
              rcases C.vis_total_same_replica hLg hsg hLb hsb hgne hrep
                with hv | hv
              · exact absurd (h_cl₁ _ _ hv hwbn₁) hgn₁
              · refine ew_live_flag hcs (Or.inr hg₂.1) hgk ?_
                intro d hd hdT hvis
                rcases hd with hd | hd
                · exact hgn₁ (h_cl₁ _ d hvis hd)
                · exact hwbL d hd hdT (h_tr hv hvis)
            · refine ew_live_flag hcs (Or.inr hwbF) hwbk ?_
              intro d hd hdT hvis
              rcases hd with hd | hd
              · exact hwbn₁ (h_cl₁ _ d hvis hd)
              · exact hwbL d hd hdT hvis
        by_cases hgt : (b k).1 > (l k).1
        · rw [decide_eq_true hgt, (hiff.mpr hgt)]
          rfl
        · have hsf : (s k).2 = false := by
            cases hsf : (s k).2 with
            | false => rfl
            | true => exact absurd (hiff.mp hsf) hgt
          rw [decide_eq_false hgt, hsf]
          rfl
      | false =>
        -- neither side live: the union flag is unset
        have hsf : (s k).2 = false := by
          cases hsf : (s k).2 with
          | false => rfl
          | true =>
            exfalso
            obtain ⟨w, hwF, hwk, hwE, hwL⟩ := ew_flag_witness hcs hsf
            rcases w with ⟨tsw, rw', opw⟩
            have : opw = EWOp.enable := hwE
            subst this
            rcases hwF with hw | hw
            · have : (a k).2 = true := by
                refine ew_live_flag hca hw hwk ?_
                intro d hd hdT hvis
                exact hwL d (Or.inl hd) hdT hvis
              rw [hfa] at this
              exact Bool.noConfusion this
            · have : (b k).2 = true := by
                refine ew_live_flag hcb hw hwk ?_
                intro d hd hdT hvis
                exact hwL d (Or.inr hd) hdT hvis
              rw [hfb] at this
              exact Bool.noConfusion this
        rw [hsf]
        rfl
  -- assemble the pair
  show ewMergeCF (l k) (a k) (b k) = s k
  have hcnt : (ewMergeCF (l k) (a k) (b k)).1 = (s k).1 := by
    show (a k).1 + (b k).1 - (l k).1 = (s k).1
    rw [hcnt₁, hcnt₂, hcnt₀, hcntU]
    have hle := ew_count_le hpf₀ hpf₂
      (fun o ho => ⟨ho.1.2, ho.2⟩)
    omega
  exact Prod.ext hcnt hflag

/-! ## §7. End-to-end -/

open LabeledTS in
/-- **End-to-end RA-linearizability for the production Enable-wins flag.** -/
theorem EWFlag_ra_linearizable3
    (C : Configuration EWFlag)
    (hReach : (labeledTS3 EWFlag).ReachableFrom
      (initConfig EWFlag trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_joinF EWFlag_joinLemma3F C hReach

/-! # Phase 2: the production catalog sweep (T11)

Six further production MRDTs, all in the **commuting class**: `rc = Either`
everywhere and all update pairs commute. Four are LCA-inclusive grow-only
unions (`mergeL l a b = l ∪ a ∪ b`, componentwise) — Grow-Only Set, Grow-Only
Map, RGA (tombstone), Peritext — for which every merge law is a Boolean
tautology (the `bor_*` kernel below); two are the counter group form
(`mergeL l a b = a + b − l`) — Increment-Only Counter, PN-Counter. All six
land end-to-end via `ra_linearizable_of_core_delta_cd3` with
`cdVC3_of_all_comm`.

Faithfulness notes: `set α = α → Bool` mirrors as before; Grow-Only Map's
`map ℕ (set ℕ)` is mirrored uncurried as `(ℕ × ℕ) → Bool` (its
`mysel`-observable semantics); Peritext's `MarkOp`/`AnchorAttachment`
structures are flattened to tuples (componentwise identical fields). -/

/-! ## The Boolean kernel for LCA-inclusive unions -/

private theorem bor_rc (a b c : Bool) :
    ((a || b) || c) = ((a || c) || b) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem bor_comm (l a b : Bool) :
    (l || (a || b)) = (l || (b || a)) := by
  cases l <;> cases a <;> cases b <;> rfl

private theorem bor_init (s : Bool) : (false || (false || s)) = s := by
  cases s <;> rfl

private theorem bor_0op (l a b d : Bool) :
    ((l || d) || ((a || d) || (b || d))) = ((l || (a || b)) || d) := by
  cases l <;> cases a <;> cases b <;> cases d <;> rfl

private theorem bor_peel (f a g d : Bool) :
    (f || ((a || d) || g)) = ((f || (a || g)) || d) := by
  cases f <;> cases a <;> cases g <;> cases d <;> rfl

private theorem bor_redis (m x0 x1 x2 c : Bool) :
    ((m || (x0 || c)) || ((m || (x1 || c)) || (m || (x2 || c))))
      = (m || ((x0 || (x1 || x2)) || c)) := by
  cases m <;> cases x0 <;> cases x1 <;> cases x2 <;> cases c <;> rfl

private theorem bor_lredis (l m x c y : Bool) :
    (l || ((m || (x || c)) || y)) = (m || ((l || (x || y)) || c)) := by
  cases l <;> cases m <;> cases x <;> cases c <;> cases y <;> rfl

/-! ## Grow-Only Set (production mirror: `Sal/MRDTs/Grow_Only_Set`) -/

def goUpdate (s : ℕ → Bool) (o : Op ℕ) : ℕ → Bool :=
  fun x => s x || decide (x = o.2.2)

noncomputable def GOSet : ConditionedMRDTSig where
  State := ℕ → Bool
  dec_state := fun _ _ => Classical.propDecidable _
  init := fun _ => false
  AppOp := ℕ
  dec_op := inferInstance
  Query := Unit
  Value := ℕ → Bool
  update := goUpdate
  merge := fun a b => fun x => false || (a x || b x)
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => fun x => l x || (a x || b x)
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem GOSet_rc_either : ∀ o₁ o₂ : Op GOSet.AppOp,
    GOSet.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem GOSet_all_comm : ∀ a b : Op GOSet.AppOp,
    GOSet.toCRDTSig.commutes a b := by
  intro a b s
  funext x
  exact bor_rc (s x) (decide (x = a.2.2)) (decide (x = b.2.2))

theorem GOSet_updateVCs : UpdateVCs GOSet.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (GOSet_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [GOSet_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [GOSet_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [GOSet_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem GOSet_coreVCs3 : CoreVCs3 GOSet := by
  refine ⟨GOSet_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    funext x
    exact bor_comm (l x) (a x) (b x)
  · intro s
    funext x
    exact bor_init (s x)
  · intro l a b e
    funext x
    exact bor_0op (l x) (a x) (b x) (decide (x = e.2.2))
  · intro a e π₀ π₂ _ _
    funext x
    exact bor_peel (applySeq GOSet.toCRDTSig GOSet.init π₀ x) (a x)
      (applySeq GOSet.toCRDTSig GOSet.init π₂ x) (decide (x = e.2.2))

theorem GOSet_deltaVCs3 : DeltaVCs3 GOSet := by
  constructor
  · intro m x₀ x₁ x₂ c
    funext x
    exact bor_redis (m x) (x₀ x) (x₁ x) (x₂ x) (c x)
  · intro l m x c y
    funext p
    exact bor_lredis (l p) (m p) (x p) (c p) (y p)

open LabeledTS in
/-- End-to-end RA-linearizability for the production Grow-Only Set. -/
theorem goset_ra_linearizable3
    (C : Configuration GOSet)
    (hReach : (labeledTS3 GOSet).ReachableFrom
      (initConfig GOSet trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable_of_core_delta_cd3 GOSet_coreVCs3 GOSet_deltaVCs3
    (cdVC3_of_all_comm GOSet_coreVCs3 GOSet_all_comm) C hReach

/-! ## Grow-Only Map (production mirror: `Sal/MRDTs/Grow_Only_Map`;
uncurried `mysel`-view: `(key, value)`-membership) -/

def gomUpdate (s : ℕ × ℕ → Bool) (o : Op (ℕ × ℕ)) : ℕ × ℕ → Bool :=
  fun p => s p || decide (p = o.2.2)

noncomputable def GOMap : ConditionedMRDTSig where
  State := ℕ × ℕ → Bool
  dec_state := fun _ _ => Classical.propDecidable _
  init := fun _ => false
  AppOp := ℕ × ℕ
  dec_op := inferInstance
  Query := Unit
  Value := ℕ × ℕ → Bool
  update := gomUpdate
  merge := fun a b => fun p => false || (a p || b p)
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => fun p => l p || (a p || b p)
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem GOMap_rc_either : ∀ o₁ o₂ : Op GOMap.AppOp,
    GOMap.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem GOMap_all_comm : ∀ a b : Op GOMap.AppOp,
    GOMap.toCRDTSig.commutes a b := by
  intro a b s
  funext p
  exact bor_rc (s p) (decide (p = a.2.2)) (decide (p = b.2.2))

theorem GOMap_updateVCs : UpdateVCs GOMap.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (GOMap_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [GOMap_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [GOMap_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [GOMap_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem GOMap_coreVCs3 : CoreVCs3 GOMap := by
  refine ⟨GOMap_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    funext p
    exact bor_comm (l p) (a p) (b p)
  · intro s
    funext p
    exact bor_init (s p)
  · intro l a b e
    funext p
    exact bor_0op (l p) (a p) (b p) (decide (p = e.2.2))
  · intro a e π₀ π₂ _ _
    funext p
    exact bor_peel (applySeq GOMap.toCRDTSig GOMap.init π₀ p) (a p)
      (applySeq GOMap.toCRDTSig GOMap.init π₂ p) (decide (p = e.2.2))

theorem GOMap_deltaVCs3 : DeltaVCs3 GOMap := by
  constructor
  · intro m x₀ x₁ x₂ c
    funext p
    exact bor_redis (m p) (x₀ p) (x₁ p) (x₂ p) (c p)
  · intro l m x c y
    funext p
    exact bor_lredis (l p) (m p) (x p) (c p) (y p)

open LabeledTS in
/-- End-to-end RA-linearizability for the production Grow-Only Map. -/
theorem gomap_ra_linearizable3
    (C : Configuration GOMap)
    (hReach : (labeledTS3 GOMap).ReachableFrom
      (initConfig GOMap trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable_of_core_delta_cd3 GOMap_coreVCs3 GOMap_deltaVCs3
    (cdVC3_of_all_comm GOMap_coreVCs3 GOMap_all_comm) C hReach

/-! ## Increment-Only Counter (production mirror:
`Sal/MRDTs/Increment_Only_Counter`; the metatheory's `Counter` toy is this
RDT up to the singleton op type) -/

inductive IOCOp : Type where
  | incr
deriving DecidableEq

def IOC : ConditionedMRDTSig where
  State := Int
  dec_state := inferInstance
  init := 0
  AppOp := IOCOp
  dec_op := inferInstance
  Query := Unit
  Value := Int
  update := fun s _ => s + 1
  merge := fun a b => a + b - (0 : Int)
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => a + b - l
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem IOC_update_eq (s : Int) (e : Op IOC.AppOp) :
    IOC.update s e = s + 1 := rfl

theorem IOC_mergeL_eq (l a b : Int) : IOC.mergeL l a b = a + b - l := rfl

theorem IOC_init_eq : IOC.init = (0 : Int) := rfl

theorem IOC_rc_either : ∀ o₁ o₂ : Op IOC.AppOp,
    IOC.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem IOC_all_comm : ∀ a b : Op IOC.AppOp, IOC.toCRDTSig.commutes a b :=
  fun _ _ _ => rfl

theorem IOC_updateVCs : UpdateVCs IOC.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (IOC_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [IOC_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [IOC_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [IOC_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem IOC_coreVCs3 : CoreVCs3 IOC := by
  refine ⟨IOC_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    simp only [IOC_mergeL_eq]
    have go : ∀ l' a' b' : Int, a' + b' - l' = b' + a' - l' := by omega
    exact go l a b
  · intro s
    simp only [IOC_mergeL_eq, IOC_init_eq]
    have go : ∀ s' : Int, (0 : Int) + s' - 0 = s' := by omega
    exact go s
  · intro l a b e
    simp only [IOC_update_eq, IOC_mergeL_eq]
    have go : ∀ l' a' b' : Int,
        a' + 1 + (b' + 1) - (l' + 1) = a' + b' - l' + 1 := by omega
    exact go l a b
  · intro a e π₀ π₂ _ _
    simp only [IOC_update_eq, IOC_mergeL_eq]
    have go : ∀ x y z : Int, y + 1 + z - x = y + z - x + 1 := by omega
    exact go _ _ _

theorem IOC_deltaVCs3 : DeltaVCs3 IOC := by
  constructor
  · intro m x₀ x₁ x₂ c
    simp only [IOC_mergeL_eq]
    have go : ∀ m' x₀' x₁' x₂' c' : Int,
        x₁' + c' - m' + (x₂' + c' - m') - (x₀' + c' - m')
          = x₁' + x₂' - x₀' + c' - m' := by omega
    exact go m x₀ x₁ x₂ c
  · intro l m x c y
    simp only [IOC_mergeL_eq]
    have go : ∀ l' m' x' c' y' : Int,
        x' + c' - m' + y' - l' = x' + y' - l' + c' - m' := by omega
    exact go l m x c y

open LabeledTS in
/-- End-to-end RA-linearizability for the production Increment-Only
Counter. -/
theorem ioc_ra_linearizable3
    (C : Configuration IOC)
    (hReach : (labeledTS3 IOC).ReachableFrom
      (initConfig IOC trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable_of_core_delta_cd3 IOC_coreVCs3 IOC_deltaVCs3
    (cdVC3_of_all_comm IOC_coreVCs3 IOC_all_comm) C hReach

/-! ## PN-Counter (production mirror: `Sal/MRDTs/PN_Counter`) -/

inductive PNOp : Type where
  | inc
  | dec
deriving DecidableEq

def pnUpdate (s : Int) (o : Op PNOp) : Int :=
  match o.2.2 with
  | .inc => s + 1
  | .dec => s - 1

def PN : ConditionedMRDTSig where
  State := Int
  dec_state := inferInstance
  init := 0
  AppOp := PNOp
  dec_op := inferInstance
  Query := Unit
  Value := Int
  update := pnUpdate
  merge := fun a b => a + b - (0 : Int)
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => a + b - l
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem PN_update_inc (s : Int) (ts r : ℕ) :
    PN.update s (ts, r, PNOp.inc) = s + 1 := rfl

theorem PN_update_dec (s : Int) (ts r : ℕ) :
    PN.update s (ts, r, PNOp.dec) = s - 1 := rfl

theorem PN_mergeL_eq (l a b : Int) : PN.mergeL l a b = a + b - l := rfl

theorem PN_init_eq : PN.init = (0 : Int) := rfl

theorem PN_rc_either : ∀ o₁ o₂ : Op PN.AppOp,
    PN.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem PN_all_comm : ∀ a b : Op PN.AppOp, PN.toCRDTSig.commutes a b := by
  rintro ⟨tsa, ra, opa⟩ ⟨tsb, rb, opb⟩ s
  have go1 : ∀ x : Int, x + 1 - 1 = x - 1 + 1 := by omega
  have go2 : ∀ x : Int, x - 1 + 1 = x + 1 - 1 := by omega
  cases opa <;> cases opb
  · rfl
  · exact go1 s
  · exact go2 s
  · rfl

theorem PN_updateVCs : UpdateVCs PN.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (PN_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [PN_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [PN_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [PN_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem PN_coreVCs3 : CoreVCs3 PN := by
  refine ⟨PN_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    simp only [PN_mergeL_eq]
    have go : ∀ l' a' b' : Int, a' + b' - l' = b' + a' - l' := by omega
    exact go l a b
  · intro s
    simp only [PN_mergeL_eq, PN_init_eq]
    have go : ∀ s' : Int, (0 : Int) + s' - 0 = s' := by omega
    exact go s
  · rintro l a b ⟨ts, r, op⟩
    have goi : ∀ l' a' b' : Int,
        a' + 1 + (b' + 1) - (l' + 1) = a' + b' - l' + 1 := by omega
    have god : ∀ l' a' b' : Int,
        a' - 1 + (b' - 1) - (l' - 1) = a' + b' - l' - 1 := by omega
    cases op
    · exact goi l a b
    · exact god l a b
  · rintro a ⟨ts, r, op⟩ π₀ π₂ _ _
    have goi : ∀ x y z : Int, y + 1 + z - x = y + z - x + 1 := by omega
    have god : ∀ x y z : Int, y - 1 + z - x = y + z - x - 1 := by omega
    cases op
    · exact goi _ a _
    · exact god _ a _

theorem PN_deltaVCs3 : DeltaVCs3 PN := by
  constructor
  · intro m x₀ x₁ x₂ c
    simp only [PN_mergeL_eq]
    have go : ∀ m' x₀' x₁' x₂' c' : Int,
        x₁' + c' - m' + (x₂' + c' - m') - (x₀' + c' - m')
          = x₁' + x₂' - x₀' + c' - m' := by omega
    exact go m x₀ x₁ x₂ c
  · intro l m x c y
    simp only [PN_mergeL_eq]
    have go : ∀ l' m' x' c' y' : Int,
        x' + c' - m' + y' - l' = x' + y' - l' + c' - m' := by omega
    exact go l m x c y

open LabeledTS in
/-- End-to-end RA-linearizability for the production PN-Counter. -/
theorem pn_ra_linearizable3
    (C : Configuration PN)
    (hReach : (labeledTS3 PN).ReachableFrom
      (initConfig PN trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable_of_core_delta_cd3 PN_coreVCs3 PN_deltaVCs3
    (cdVC3_of_all_comm PN_coreVCs3 PN_all_comm) C hReach

/-! ## RGA, tombstone-based (production mirror: `Sal/MRDTs/RGA`) —
Tier-1 in disguise: both components grow-only, `rc = Either`, all pairs
commute, LCA-inclusive union merge. -/

inductive RGAOp : Type where
  | addAfter : ℕ → ℕ → RGAOp
  | remove : ℕ → RGAOp
deriving DecidableEq

def rgaUpdate (s : ((ℕ × ℕ × ℕ) → Bool) × (ℕ → Bool)) (o : Op RGAOp) :
    ((ℕ × ℕ × ℕ) → Bool) × (ℕ → Bool) :=
  match o.2.2 with
  | .addAfter af el => (fun p => s.1 p || decide (p = (o.1, af, el)), s.2)
  | .remove id => (s.1, fun x => s.2 x || decide (x = id))

noncomputable def RGAM : ConditionedMRDTSig where
  State := ((ℕ × ℕ × ℕ) → Bool) × (ℕ → Bool)
  dec_state := fun _ _ => Classical.propDecidable _
  init := (fun _ => false, fun _ => false)
  AppOp := RGAOp
  dec_op := inferInstance
  Query := Unit
  Value := ((ℕ × ℕ × ℕ) → Bool) × (ℕ → Bool)
  update := rgaUpdate
  merge := fun a b =>
    (fun p => false || (a.1 p || b.1 p), fun x => false || (a.2 x || b.2 x))
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b =>
    (fun p => l.1 p || (a.1 p || b.1 p), fun x => l.2 x || (a.2 x || b.2 x))
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem RGAM_rc_either : ∀ o₁ o₂ : Op RGAM.AppOp,
    RGAM.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem RGAM_all_comm : ∀ a b : Op RGAM.AppOp,
    RGAM.toCRDTSig.commutes a b := by
  rintro ⟨tsa, ra, opa⟩ ⟨tsb, rb, opb⟩ s
  cases opa <;> cases opb
  · exact Prod.ext (funext fun p => bor_rc (s.1 p) _ _) rfl
  · rfl
  · rfl
  · exact Prod.ext rfl (funext fun x => bor_rc (s.2 x) _ _)

theorem RGAM_updateVCs : UpdateVCs RGAM.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (RGAM_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [RGAM_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [RGAM_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [RGAM_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem RGAM_coreVCs3 : CoreVCs3 RGAM := by
  refine ⟨RGAM_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    exact Prod.ext (funext fun p => bor_comm (l.1 p) (a.1 p) (b.1 p))
      (funext fun x => bor_comm (l.2 x) (a.2 x) (b.2 x))
  · intro s
    exact Prod.ext (funext fun p => bor_init (s.1 p))
      (funext fun x => bor_init (s.2 x))
  · rintro l a b ⟨ts, r, op⟩
    cases op with
    | addAfter af el =>
      exact Prod.ext (funext fun p => bor_0op (l.1 p) (a.1 p) (b.1 p) _) rfl
    | remove id =>
      exact Prod.ext rfl (funext fun x => bor_0op (l.2 x) (a.2 x) (b.2 x) _)
  · rintro a ⟨ts, r, op⟩ π₀ π₂ _ _
    cases op with
    | addAfter af el =>
      exact Prod.ext (funext fun p =>
        bor_peel ((applySeq RGAM.toCRDTSig RGAM.init π₀).1 p) (a.1 p)
          ((applySeq RGAM.toCRDTSig RGAM.init π₂).1 p) _) rfl
    | remove id =>
      exact Prod.ext rfl (funext fun x =>
        bor_peel ((applySeq RGAM.toCRDTSig RGAM.init π₀).2 x) (a.2 x)
          ((applySeq RGAM.toCRDTSig RGAM.init π₂).2 x) _)

theorem RGAM_deltaVCs3 : DeltaVCs3 RGAM := by
  constructor
  · intro m x₀ x₁ x₂ c
    exact Prod.ext
      (funext fun p => bor_redis (m.1 p) (x₀.1 p) (x₁.1 p) (x₂.1 p) (c.1 p))
      (funext fun x => bor_redis (m.2 x) (x₀.2 x) (x₁.2 x) (x₂.2 x) (c.2 x))
  · intro l m x c y
    exact Prod.ext
      (funext fun p => bor_lredis (l.1 p) (m.1 p) (x.1 p) (c.1 p) (y.1 p))
      (funext fun q => bor_lredis (l.2 q) (m.2 q) (x.2 q) (c.2 q) (y.2 q))

open LabeledTS in
/-- End-to-end RA-linearizability for the production tombstone RGA. -/
theorem rga_ra_linearizable3
    (C : Configuration RGAM)
    (hReach : (labeledTS3 RGAM).ReachableFrom
      (initConfig RGAM trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable_of_core_delta_cd3 RGAM_coreVCs3 RGAM_deltaVCs3
    (cdVC3_of_all_comm RGAM_coreVCs3 RGAM_all_comm) C hReach

/-! ## Peritext (production mirror: `Sal/MRDTs/Peritext`) — three grow-only
components (chars, tombstones, anchor-attached marks; `RemoveMark` *adds* a
mark record with `isAdd = false`), `rc = Either`, all pairs commute. -/

/-- Flattened `MarkOp`: `(opId, startId, startSide, endId, endSide,
markType, isAdd)`. -/
abbrev PtMark : Type :=
  (ℕ × ℕ) × (ℕ × ℕ) × Bool × (ℕ × ℕ) × Bool × ℕ × Bool

/-- Flattened `AnchorAttachment`: `(endId, endSide, mark)`. -/
abbrev PtAnchor : Type := (ℕ × ℕ) × Bool × PtMark

/-- Flattened `CharRec`: `(opId, after, ch)`. -/
abbrev PtChar : Type := (ℕ × ℕ) × (ℕ × ℕ) × ℕ

inductive PtOp : Type where
  | insert : ℕ → ℕ × ℕ → PtOp
  | remove : ℕ × ℕ → PtOp
  | addMark : ℕ × ℕ → Bool → ℕ × ℕ → Bool → ℕ → PtOp
  | removeMark : ℕ × ℕ → Bool → ℕ × ℕ → Bool → ℕ → PtOp
deriving DecidableEq

abbrev PtState : Type :=
  (PtChar → Bool) × ((ℕ × ℕ) → Bool) × (PtAnchor → Bool)

noncomputable def ptUpdate (s : PtState) (o : Op PtOp) : PtState :=
  match o.2.2 with
  | .insert ch af =>
      (fun q => s.1 q || decide (q = ((o.1, o.2.1), af, ch)), s.2.1, s.2.2)
  | .remove t =>
      (s.1, fun q => s.2.1 q || decide (q = t), s.2.2)
  | .addMark sI sS eI eS mt =>
      (s.1, s.2.1, fun q =>
        s.2.2 q || decide (q = (eI, eS, ((o.1, o.2.1), sI, sS, eI, eS, mt,
          true))))
  | .removeMark sI sS eI eS mt =>
      (s.1, s.2.1, fun q =>
        s.2.2 q || decide (q = (eI, eS, ((o.1, o.2.1), sI, sS, eI, eS, mt,
          false))))

noncomputable def Peritext : ConditionedMRDTSig where
  State := PtState
  dec_state := fun _ _ => Classical.propDecidable _
  init := (fun _ => false, fun _ => false, fun _ => false)
  AppOp := PtOp
  dec_op := inferInstance
  Query := Unit
  Value := PtState
  update := ptUpdate
  merge := fun a b =>
    (fun q => false || (a.1 q || b.1 q),
     fun q => false || (a.2.1 q || b.2.1 q),
     fun q => false || (a.2.2 q || b.2.2 q))
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b =>
    (fun q => l.1 q || (a.1 q || b.1 q),
     fun q => l.2.1 q || (a.2.1 q || b.2.1 q),
     fun q => l.2.2 q || (a.2.2 q || b.2.2 q))
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem Peritext_rc_either : ∀ o₁ o₂ : Op Peritext.AppOp,
    Peritext.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem Peritext_all_comm : ∀ a b : Op Peritext.AppOp,
    Peritext.toCRDTSig.commutes a b := by
  rintro ⟨tsa, ra, opa⟩ ⟨tsb, rb, opb⟩ s
  cases opa <;> cases opb <;>
    first
      | rfl
      | exact Prod.ext (funext fun q => bor_rc (s.1 q) _ _) rfl
      | exact Prod.ext rfl (Prod.ext (funext fun q => bor_rc (s.2.1 q) _ _)
          rfl)
      | exact Prod.ext rfl (Prod.ext rfl
          (funext fun q => bor_rc (s.2.2 q) _ _))

theorem Peritext_updateVCs : UpdateVCs Peritext.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (Peritext_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [Peritext_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [Peritext_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [Peritext_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem Peritext_coreVCs3 : CoreVCs3 Peritext := by
  refine ⟨Peritext_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    exact Prod.ext (funext fun q => bor_comm (l.1 q) (a.1 q) (b.1 q))
      (Prod.ext (funext fun q => bor_comm (l.2.1 q) (a.2.1 q) (b.2.1 q))
        (funext fun q => bor_comm (l.2.2 q) (a.2.2 q) (b.2.2 q)))
  · intro s
    exact Prod.ext (funext fun q => bor_init (s.1 q))
      (Prod.ext (funext fun q => bor_init (s.2.1 q))
        (funext fun q => bor_init (s.2.2 q)))
  · rintro l a b ⟨ts, r, op⟩
    cases op <;>
      first
        | exact Prod.ext
            (funext fun q => bor_0op (l.1 q) (a.1 q) (b.1 q) _) rfl
        | exact Prod.ext rfl (Prod.ext
            (funext fun q => bor_0op (l.2.1 q) (a.2.1 q) (b.2.1 q) _) rfl)
        | exact Prod.ext rfl (Prod.ext rfl
            (funext fun q => bor_0op (l.2.2 q) (a.2.2 q) (b.2.2 q) _))
  · rintro a ⟨ts, r, op⟩ π₀ π₂ _ _
    cases op <;>
      first
        | exact Prod.ext (funext fun q =>
            bor_peel ((applySeq Peritext.toCRDTSig Peritext.init π₀).1 q)
              (a.1 q)
              ((applySeq Peritext.toCRDTSig Peritext.init π₂).1 q) _) rfl
        | exact Prod.ext rfl (Prod.ext (funext fun q =>
            bor_peel ((applySeq Peritext.toCRDTSig Peritext.init π₀).2.1 q)
              (a.2.1 q)
              ((applySeq Peritext.toCRDTSig Peritext.init π₂).2.1 q) _) rfl)
        | exact Prod.ext rfl (Prod.ext rfl (funext fun q =>
            bor_peel ((applySeq Peritext.toCRDTSig Peritext.init π₀).2.2 q)
              (a.2.2 q)
              ((applySeq Peritext.toCRDTSig Peritext.init π₂).2.2 q) _))

theorem Peritext_deltaVCs3 : DeltaVCs3 Peritext := by
  constructor
  · intro m x₀ x₁ x₂ c
    exact Prod.ext
      (funext fun q => bor_redis (m.1 q) (x₀.1 q) (x₁.1 q) (x₂.1 q) (c.1 q))
      (Prod.ext
        (funext fun q =>
          bor_redis (m.2.1 q) (x₀.2.1 q) (x₁.2.1 q) (x₂.2.1 q) (c.2.1 q))
        (funext fun q =>
          bor_redis (m.2.2 q) (x₀.2.2 q) (x₁.2.2 q) (x₂.2.2 q) (c.2.2 q)))
  · intro l m x c y
    exact Prod.ext
      (funext fun q => bor_lredis (l.1 q) (m.1 q) (x.1 q) (c.1 q) (y.1 q))
      (Prod.ext
        (funext fun q =>
          bor_lredis (l.2.1 q) (m.2.1 q) (x.2.1 q) (c.2.1 q) (y.2.1 q))
        (funext fun q =>
          bor_lredis (l.2.2 q) (m.2.2 q) (x.2.2 q) (c.2.2 q) (y.2.2 q)))

open LabeledTS in
/-- End-to-end RA-linearizability for the production Peritext. -/
theorem peritext_ra_linearizable3
    (C : Configuration Peritext)
    (hReach : (labeledTS3 Peritext).ReachableFrom
      (initConfig Peritext trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable_of_core_delta_cd3 Peritext_coreVCs3 Peritext_deltaVCs3
    (cdVC3_of_all_comm Peritext_coreVCs3 Peritext_all_comm) C hReach

end Sal.Metatheory
