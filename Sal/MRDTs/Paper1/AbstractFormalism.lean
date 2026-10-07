import Sal.MRDTs.Paper1.EventBridge

/-! Abstraction-based paper formalism and the earlier uniform-law adapter.
The guarded replay contract and direct semantic canonical states are developed
in `GuardedAbstraction`; the execution bridges below still use uniform laws.
All semantic state equations
are equality of abstractions. Concrete states and event identities are retained
in execution, and merge is justified through representation evidence. -/
namespace Sal.MRDTs.Paper1
open Foundation

namespace AbstractMRDT

/-- The semantic interface is explicit. It need not separate states by a
single immediate query; abstract state may retain information needed by future
updates. No abstract merge operation or merge congruence is required. -/
structure Model (D : MRDTSig) where
  Abstract : Type
  abs : D.State → Abstract
  step : Abstract → Op D.AppOp → Abstract
  read : Abstract → D.Query → D.Value
  update_abs : ∀ s e, abs (D.update s e) = step (abs s) e
  query_abs : ∀ s q, D.query s q = read (abs s) q

variable {D : MRDTSig}

def Equivalent (A : Model D) (s t : D.State) : Prop := A.abs s = A.abs t

def Commutes (A : Model D) (a b : Op D.AppOp) : Prop :=
  ∀ s, Equivalent A (D.update (D.update s a) b) (D.update (D.update s b) a)

theorem equivalent_refl (A : Model D) (s : D.State) : Equivalent A s s := rfl

theorem equivalent_symm {A : Model D} {s t : D.State} (h : Equivalent A s t) :
    Equivalent A t s := h.symm

theorem equivalent_trans {A : Model D} {s t u : D.State}
    (h : Equivalent A s t) (k : Equivalent A t u) : Equivalent A s u := h.trans k

theorem equivalent_query {A : Model D} {s t : D.State}
    (h : Equivalent A s t) (q : D.Query) : D.query s q = D.query t q := by
  rw [A.query_abs,A.query_abs,h]

theorem equivalent_update {A : Model D} {s t : D.State}
    (h : Equivalent A s t) (e : Op D.AppOp) :
    Equivalent A (D.update s e) (D.update t e) := by
  change A.abs (D.update s e) = A.abs (D.update t e)
  rw [A.update_abs,A.update_abs,h]

theorem Model.fold_abs (A : Model D) (s : D.State) (xs : List (Op D.AppOp)) :
    A.abs (applySeq D.toUpdateSig s xs) = xs.foldl A.step (A.abs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons e xs ih => simpa [A.update_abs] using ih (D.update s e)

theorem equivalent_future {A : Model D} {s t : D.State}
    (h : Equivalent A s t) :
    ∀ xs q, D.query (applySeq D.toUpdateSig s xs) q =
      D.query (applySeq D.toUpdateSig t xs) q := by
  intro xs q
  rw [A.query_abs,A.query_abs,A.fold_abs,A.fold_abs,h]

/-- Completeness identifies exactly future-query-indistinguishable concrete
states. It permits latent abstract information exposed only by later updates. -/
def Model.QueryComplete (A : Model D) : Prop :=
  ∀ s t, (∀ xs q, D.query (applySeq D.toUpdateSig s xs) q =
    D.query (applySeq D.toUpdateSig t xs) q) → Equivalent A s t

theorem equivalent_iff_future {A : Model D} (complete : A.QueryComplete)
    (s t : D.State) : Equivalent A s t ↔
      ∀ xs q, D.query (applySeq D.toUpdateSig s xs) q =
        D.query (applySeq D.toUpdateSig t xs) q :=
  ⟨equivalent_future,complete s t⟩

def setoid (A : Model D) : Setoid D.State where
  r := Equivalent A
  iseqv := ⟨equivalent_refl A, equivalent_symm, equivalent_trans⟩

abbrev State (A : Model D) := Quotient (setoid A)

def observe (A : Model D) (s : D.State) : State A := Quotient.mk _ s

def update (A : Model D) (s : State A) (e : Op D.AppOp) : State A :=
  Quotient.map (fun s => D.update s e) (fun _ _ h => equivalent_update h e) s

noncomputable def algebra (A : Model D) : UpdateSig where
  State := State A
  dec_state := Classical.decEq _
  init := observe A D.init
  AppOp := D.AppOp
  dec_op := D.dec_op
  update := update A

@[simp] theorem update_observe (A : Model D) (s : D.State) (e : Op D.AppOp) :
    update A (observe A s) e = observe A (D.update s e) := rfl

@[simp] theorem fold_observe (A : Model D) (s : D.State) (xs : List (Op D.AppOp)) :
    applySeq (algebra A) (observe A s) xs =
      observe A (applySeq D.toUpdateSig s xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons e xs ih => exact ih (D.update s e)

theorem commutes_iff (A : Model D) (a b : Op D.AppOp) :
    (algebra A).commutes a b ↔ Commutes A a b := by
  constructor
  · intro h s
    exact Quotient.exact (h (observe A s))
  · intro h s
    induction s using Quotient.inductionOn with
    | _ s => exact Quotient.sound (h s)

/-- State equality is sufficient, but no longer the definition of commutation. -/
theorem of_state_commutes {A : Model D} {a b : Op D.AppOp}
    (h : D.toUpdateSig.commutes a b) : Commutes A a b := by
  intro s
  have eq : D.update (D.update s a) b = D.update (D.update s b) a := h s
  rw [eq]
  exact equivalent_refl A _

/-- The implementation replay restrictions now use observable commutation and
observable conditional absorption. -/
structure Laws (A : Model D) (P : OperationPolicy D.AppOp) : Prop where
  noncomm_exact : ∀ a b, ¬ Commutes A a b ↔ P.before a.op b.op ∨ P.before b.op a.op
  no_chain : ∀ a b c, ¬ (P.before a b ∧ P.before b c)
  conditional_commutation : ∀ s a b c between,
    P.before a.op b.op → ¬ Commutes A b c →
    Equivalent A
      (D.update (applySeq D.toUpdateSig (D.update (D.update s b) a) between) c)
      (D.update (applySeq D.toUpdateSig (D.update (D.update s a) b) between) c)

theorem Laws.toRestricted {A : Model D} {P : OperationPolicy D.AppOp}
    (h : Laws A P) : RestrictedLaws (algebra A) P := by
  refine ⟨?_,h.no_chain,?_⟩
  · intro a b
    rw [commutes_iff]
    exact h.noncomm_exact a b
  · intro s a b c between before conflict
    induction s using Quotient.inductionOn with
    | _ s =>
      have hc : ¬ Commutes A b c := fun commute => conflict ((commutes_iff A b c).mpr commute)
      change update A (applySeq (algebra A)
          (observe A (D.update (D.update s b) a)) between) c =
        update A (applySeq (algebra A)
          (observe A (D.update (D.update s a) b)) between) c
      rw [fold_observe,fold_observe,update_observe,update_observe]
      exact Quotient.sound (h.conditional_commutation s a b c between before hc)

/-- Existing concrete proofs can be reused when both notions of commutation
coincide. This is sufficient for the exact tagged OR-set, but is deliberately
not required of the efficient representation. -/
theorem Laws.of_concrete {A : Model D} {P : OperationPolicy D.AppOp}
    (old : RestrictedLaws D.toUpdateSig P)
    (same : ∀ a b, Commutes A a b ↔ D.toUpdateSig.commutes a b) : Laws A P := by
  refine ⟨?_,old.no_chain,?_⟩
  · intro a b
    rw [same]
    exact old.noncomm_exact a b
  · intro s a b c xs hnc conflict
    have eq := old.conditional_commutation s a b c xs hnc
      (fun h => conflict ((same b c).mpr h))
    change D.update (applySeq D.toUpdateSig (D.update (D.update s b) a) xs) c =
      D.update (applySeq D.toUpdateSig (D.update (D.update s a) b) xs) c at eq
    rw [eq]
    exact equivalent_refl A _

/-- Every use of commutation in the paper order, including absorbers, is
query-relative. -/
def order (A : Model D) (P : OperationPolicy D.AppOp)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (a b : Op D.AppOp) : Prop :=
  (C.vis a b ∧ ¬ Commutes A a b) ∨
    (¬ C.vis a b ∧ ¬ C.vis b a ∧ P.before a.op b.op ∧
      ¬ ∃ c ∈ E, C.vis b c ∧ ¬ Commutes A b c)

def context (A : Model D) (C : ReplayContext D.toUpdateSig) : ReplayContext (algebra A) :=
  { L := C.L, vis := C.vis, timestamps_distinct := C.timestamps_distinct,
    vis_total_same_replica := C.vis_total_same_replica }

/-- Causal past through observable conflicts, using the same replay algebra
as the order and absorbers. Concrete noncommutation must not leak in here. -/
def causalPast (A : Model D) (C : ReplayContext D.toUpdateSig) (e : Op D.AppOp) :
    Set (Op D.AppOp) := downset (context A C) e

theorem causalPast_self (A : Model D) (C : ReplayContext D.toUpdateSig) (e : Op D.AppOp) :
    e ∈ causalPast A C e := Or.inl rfl

theorem causalPast_subset (A : Model D) (C : ReplayContext D.toUpdateSig)
    (E : Set (Op D.AppOp)) (e : Op D.AppOp)
    (closed : ∀ a b, C.vis a b → ¬ Commutes A a b → b ∈ E → a ∈ E)
    (mem : e ∈ E) : causalPast A C e ⊆ E := by
  rintro x (rfl | h)
  · exact mem
  · have close : ∀ a b, visNC (context A C) a b → b ∈ E → a ∈ E := by
      intro a b edge hb
      exact closed a b edge.1 (fun h => edge.2 ((commutes_iff A a b).mpr h)) hb
    induction h using Relation.TransGen.head_induction_on with
    | single edge => exact close _ _ edge mem
    | head edge _ ih => exact close _ _ edge ih

theorem order_eq (A : Model D) (P : OperationPolicy D.AppOp)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (a b : Op D.AppOp) :
    order A P C E a b ↔ paperOrder P (context A C) E a b := by
  simp only [order,paperOrder,commutes_iff,context]
  rfl

/-- Observable canonical state; concrete metadata is deliberately retained. -/
def Canonical (A : Model D) (P : OperationPolicy D.AppOp)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (s : D.State) : Prop :=
  @IsCanonicalState (algebra A) P.lift (context A C) E (observe A s)

theorem canonical_congr {A : Model D} {P : OperationPolicy D.AppOp}
    {C : ReplayContext D.toUpdateSig} {E : Set (Op D.AppOp)} {s t : D.State}
    (h : Canonical A P C E s) (same : Equivalent A s t) : Canonical A P C E t := by
  obtain ⟨π,hp,hr,hf⟩ := h
  exact ⟨π,hp,hr,hf.trans (Quotient.sound same)⟩

theorem canonical_of_concrete {A : Model D} {P : OperationPolicy D.AppOp}
    (old : RestrictedLaws D.toUpdateSig P) (new : Laws A P)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (s : D.State)
    (h : @IsCanonicalState D.toUpdateSig P.lift C E s) : Canonical A P C E s := by
  obtain ⟨π,hp,hr,hf⟩ := h
  have commutation : ∀ a b, (algebra A).commutes a b ↔ D.toUpdateSig.commutes a b := by
    intro a b
    exact not_iff_not.mp ((new.toRestricted.noncomm_exact a b).trans
      (old.noncomm_exact a b).symm)
  refine ⟨π,hp,?_,?_⟩
  · apply hr.imp
    intro a b h edge
    apply h
    apply (paperOrder_iff_loOn old C E _ _).mp
    have paper := (paperOrder_iff_loOn new.toRestricted (context A C) E _ _).mpr edge
    simpa only [paperOrder,context,commutation] using paper
  · change applySeq (algebra A) (observe A D.init) π = observe A s
    rw [fold_observe,hf]

theorem canonical_query_unique {A : Model D} {P : OperationPolicy D.AppOp}
    (laws : Laws A P) (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (supported : ∀ e ∈ E, e ∈ C.events) {s t : D.State}
    (hs : Canonical A P C E s) (ht : Canonical A P C E t) (q : D.Query) :
    D.query s q = D.query t q := by
  letI : ReplayPolicy (algebra A) := P.lift
  have eq := isCanonicalState_unique_of_replayLaws (C := context A C)
    laws.toRestricted.replayLaws supported hs ht
  exact equivalent_query (Quotient.exact eq) q

/-- Convergence is equality of semantic states, not merely one selected read. -/
theorem canonical_equivalent {A : Model D} {P : OperationPolicy D.AppOp}
    (laws : Laws A P) (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (supported : ∀ e ∈ E, e ∈ C.events) {s t : D.State}
    (hs : Canonical A P C E s) (ht : Canonical A P C E t) : Equivalent A s t := by
  letI : ReplayPolicy (algebra A) := P.lift
  exact Quotient.exact (isCanonicalState_unique_of_replayLaws (C := context A C)
    laws.toRestricted.replayLaws supported hs ht)

theorem canonical_iff {A : Model D} {P : OperationPolicy D.AppOp}
    (laws : Laws A P) (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (s : D.State) : Canonical A P C E s ↔
      ∃ π : List (Op D.AppOp), listPermOf π E ∧ respects π (order A P C E) ∧
        A.abs (applySeq D.toUpdateSig D.init π) = A.abs s := by
  constructor
  · rintro ⟨π,hp,hr,hf⟩
    refine ⟨π,hp,hr.imp (fun {a b} h edge => h
      ((paperOrder_iff_loOn laws.toRestricted _ _ _ _).mp
        ((order_eq A P _ _ _ _).mp edge))),?_⟩
    change applySeq (algebra A) (observe A D.init) π = observe A s at hf
    rw [fold_observe] at hf
    exact Quotient.exact hf
  · rintro ⟨π,hp,hr,hf⟩
    refine ⟨π,hp,hr.imp (fun {a b} h edge => h
      ((order_eq A P C E b a).mpr
        ((paperOrder_iff_loOn laws.toRestricted _ _ _ _).mpr edge))),?_⟩
    change applySeq (algebra A) (observe A D.init) π = observe A s
    rw [fold_observe]
    exact Quotient.sound hf

/-- The model itself supplies a total independent sequential-history machine.
Guarded languages may instead supply a separate history bridge. -/
def Model.specification (A : Model D) : DeterministicSpec (Op D.AppOp) D.Query D.Value where
  State := A.Abstract
  initial := A.abs D.init
  update := A.step
  query := A.read

theorem Model.historySound (A : Model D) :
    EventFoldHistorySound D A.specification.toSpec := by
  intro π q
  apply (A.specification.updates_query_iff π q _).mpr
  change D.query (applySeq D.toUpdateSig D.init π) q =
    A.read (π.foldl A.step (A.abs D.init)) q
  rw [A.query_abs,A.fold_abs]

/-- This cannot be inferred merely from read equivalence. -/
def MergeCongruence (A : Model D) : Prop :=
  ∀ l l' a a' b b', Equivalent A l l' → Equivalent A a a' → Equivalent A b b' →
    Equivalent A (D.merge l a b) (D.merge l' a' b')

def SpecificationCompatibility (A : Model D)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) : Prop :=
  ∀ a b, Commutes A a b → S.Commutes a b

/-- The witness clauses alone, distinguished from the full criterion. -/
def VersionsWitness (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s,E) → ∀ q, ∃ π : List (Op D.AppOp),
    listPermOf π E ∧ respects π (order A P C.replayContext E) ∧
    respects π (projectedSpecVisibility id S C.replayContext) ∧
    S.admits (projectedLabels id π ++ [.query q (D.query s q)])

def Witness (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ r v s E, C.head r = some v → C.ver v = some (s,E) → ∀ q,
    ∃ π : List (Op D.AppOp), listPermOf π E ∧
      respects π (order A P C.replayContext E) ∧
      respects π (projectedSpecVisibility id S C.replayContext) ∧
    S.admits (projectedLabels id π ++ [.query q (D.query s q)])

/-- The full criterion includes the datatype-side replay restrictions. This
prevents a witness-only proof from being reported as satisfying the definition
when rc-non-comm or conditional commutation is unavailable. -/
def VersionsRALinearizable (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) : Prop :=
  Laws A P ∧ VersionsWitness A P S C

def RALinearizable (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) : Prop :=
  Laws A P ∧ Witness A P S C

theorem VersionsRALinearizable.heads {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {C : Configuration D}
    (h : VersionsRALinearizable A P S C) : RALinearizable A P S C :=
  ⟨h.1,fun _ v s E _ hv q => h.2 v s E hv q⟩

/-- The generic history bridge now needs only observable canonicality.
No concrete-state equality or tag-erasing merge assumption is used. -/
theorem of_canonical {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {C : Configuration D}
    (laws : Laws A P)
    (canonical : ∀ v s E, C.ver v = some (s,E) → Canonical A P C.replayContext E s)
    (compatible : SpecificationCompatibility A S) (sound : EventFoldHistorySound D S) :
    VersionsRALinearizable A P S C := by
  letI : ReplayPolicy (algebra A) := P.lift
  refine ⟨laws,?_⟩
  intro v s E hv q
  obtain ⟨π,hp,hr,hf⟩ := canonical v s E hv
  have ho : respects π (order A P C.replayContext E) :=
    hr.imp (fun {_ _} h => h ∘ fun edge =>
      (paperOrder_iff_loOn laws.toRestricted _ _ _ _).mp
        ((order_eq A P _ _ _ _).mp edge))
  refine ⟨π,hp,ho,?_,?_⟩
  · exact ho.imp (fun {_ _} h => fun edge =>
      h (Or.inl ⟨edge.1,fun commute => edge.2 (compatible _ _ commute)⟩))
  · change applySeq (algebra A) (observe A D.init) π = observe A s at hf
    rw [fold_observe] at hf
    have answer := equivalent_query (Quotient.exact hf) q
    simpa [answer] using sound π q

end AbstractMRDT
end Sal.MRDTs.Paper1
