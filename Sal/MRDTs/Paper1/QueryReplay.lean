import Sal.MRDTs.Paper1.EventBridge

/-! Query-relative implementation replay. Observational equivalence includes
all subsequent update sequences and queries, so update substitution is sound.
Merge is not included implicitly: observational merge preservation is a
separate obligation, since tags invisible to a read can affect a later merge.
The old state-equality algebra remains an explicitly stronger proof tool. -/
namespace Sal.MRDTs.Paper1
open Foundation

namespace QueryReplay

def Equivalent (D : MRDTSig) (s t : D.State) : Prop :=
  ∀ suffix q, D.query (applySeq D.toUpdateSig s suffix) q =
    D.query (applySeq D.toUpdateSig t suffix) q

def Commutes (D : MRDTSig) (a b : Op D.AppOp) : Prop :=
  ∀ s, Equivalent D (D.update (D.update s a) b) (D.update (D.update s b) a)

theorem equivalent_refl (D : MRDTSig) (s : D.State) : Equivalent D s s :=
  fun _ _ => rfl

theorem equivalent_symm {D : MRDTSig} {s t : D.State} (h : Equivalent D s t) :
    Equivalent D t s := fun xs q => (h xs q).symm

theorem equivalent_trans {D : MRDTSig} {s t u : D.State}
    (h : Equivalent D s t) (k : Equivalent D t u) : Equivalent D s u :=
  fun xs q => (h xs q).trans (k xs q)

theorem equivalent_query {D : MRDTSig} {s t : D.State}
    (h : Equivalent D s t) (q : D.Query) : D.query s q = D.query t q := h [] q

theorem equivalent_update {D : MRDTSig} {s t : D.State}
    (h : Equivalent D s t) (e : Op D.AppOp) :
    Equivalent D (D.update s e) (D.update t e) :=
  fun suffix q => h (e :: suffix) q

/-- A concrete presentation of observational states. Query separation makes
equality of abstractions exactly the replay equivalence, rather than merely a
sufficient relation. Merge is a separate operation on concrete metadata. -/
structure Abstraction (D : MRDTSig) where
  Abstract : Type
  abs : D.State → Abstract
  step : Abstract → Op D.AppOp → Abstract
  read : Abstract → D.Query → D.Value
  update_abs : ∀ s e, abs (D.update s e) = step (abs s) e
  query_abs : ∀ s q, D.query s q = read (abs s) q
  separates : ∀ a b, (∀ q, read a q = read b q) → a = b

theorem Abstraction.fold_abs {D : MRDTSig} (A : Abstraction D)
    (s : D.State) (xs : List (Op D.AppOp)) :
    A.abs (applySeq D.toUpdateSig s xs) = xs.foldl A.step (A.abs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons e xs ih => simpa [A.update_abs] using ih (D.update s e)

theorem Abstraction.equivalent_iff {D : MRDTSig} (A : Abstraction D) (s t : D.State) :
    Equivalent D s t ↔ A.abs s = A.abs t := by
  constructor
  · intro h
    apply A.separates
    intro q
    simpa only [A.query_abs] using equivalent_query h q
  · intro h xs q
    rw [A.query_abs,A.query_abs,A.fold_abs,A.fold_abs,h]

def setoid (D : MRDTSig) : Setoid D.State where
  r := Equivalent D
  iseqv := ⟨equivalent_refl D, equivalent_symm, equivalent_trans⟩

abbrev State (D : MRDTSig) := Quotient (setoid D)

def observe (D : MRDTSig) (s : D.State) : State D := Quotient.mk _ s

def update (D : MRDTSig) (s : State D) (e : Op D.AppOp) : State D :=
  Quotient.map (fun s => D.update s e) (fun _ _ h => equivalent_update h e) s

noncomputable def algebra (D : MRDTSig) : UpdateSig where
  State := State D
  dec_state := Classical.decEq _
  init := observe D D.init
  AppOp := D.AppOp
  dec_op := D.dec_op
  update := update D

@[simp] theorem update_observe (D : MRDTSig) (s : D.State) (e : Op D.AppOp) :
    update D (observe D s) e = observe D (D.update s e) := rfl

@[simp] theorem fold_observe (D : MRDTSig) (s : D.State) (xs : List (Op D.AppOp)) :
    applySeq (algebra D) (observe D s) xs =
      observe D (applySeq D.toUpdateSig s xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons e xs ih => exact ih (D.update s e)

theorem commutes_iff (D : MRDTSig) (a b : Op D.AppOp) :
    (algebra D).commutes a b ↔ Commutes D a b := by
  constructor
  · intro h s
    exact Quotient.exact (h (observe D s))
  · intro h s
    induction s using Quotient.inductionOn with
    | _ s => exact Quotient.sound (h s)

/-- State equality is sufficient, but no longer the definition of commutation. -/
theorem of_state_commutes {D : MRDTSig} {a b : Op D.AppOp}
    (h : D.toUpdateSig.commutes a b) : Commutes D a b := by
  intro s
  have eq : D.update (D.update s a) b = D.update (D.update s b) a := h s
  rw [eq]
  exact equivalent_refl D _

/-- The implementation replay restrictions now use observable commutation and
observable conditional absorption. -/
structure Laws (D : MRDTSig) (P : OperationPolicy D.AppOp) : Prop where
  noncomm_exact : ∀ a b, ¬ Commutes D a b ↔ P.before a.op b.op ∨ P.before b.op a.op
  no_chain : ∀ a b c, ¬ (P.before a b ∧ P.before b c)
  conditional_commutation : ∀ s a b c between,
    P.before a.op b.op → ¬ Commutes D b c →
    Equivalent D
      (D.update (applySeq D.toUpdateSig (D.update (D.update s b) a) between) c)
      (D.update (applySeq D.toUpdateSig (D.update (D.update s a) b) between) c)

theorem Laws.toRestricted {D : MRDTSig} {P : OperationPolicy D.AppOp}
    (h : Laws D P) : RestrictedLaws (algebra D) P := by
  refine ⟨?_,h.no_chain,?_⟩
  · intro a b
    rw [commutes_iff]
    exact h.noncomm_exact a b
  · intro s a b c between before conflict
    induction s using Quotient.inductionOn with
    | _ s =>
      have hc : ¬ Commutes D b c := fun commute => conflict ((commutes_iff D b c).mpr commute)
      change update D (applySeq (algebra D)
          (observe D (D.update (D.update s b) a)) between) c =
        update D (applySeq (algebra D)
          (observe D (D.update (D.update s a) b)) between) c
      rw [fold_observe,fold_observe,update_observe,update_observe]
      exact Quotient.sound (h.conditional_commutation s a b c between before hc)

/-- Existing concrete proofs can be reused when both notions of commutation
coincide. This is sufficient for the exact tagged OR-set, but is deliberately
not required of the efficient representation. -/
theorem Laws.of_concrete {D : MRDTSig} {P : OperationPolicy D.AppOp}
    (old : RestrictedLaws D.toUpdateSig P)
    (same : ∀ a b, Commutes D a b ↔ D.toUpdateSig.commutes a b) : Laws D P := by
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
    exact equivalent_refl D _

/-- Every use of commutation in the paper order, including absorbers, is
query-relative. -/
def order {D : MRDTSig} (P : OperationPolicy D.AppOp)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (a b : Op D.AppOp) : Prop :=
  (C.vis a b ∧ ¬ Commutes D a b) ∨
    (¬ C.vis a b ∧ ¬ C.vis b a ∧ P.before a.op b.op ∧
      ¬ ∃ c ∈ E, C.vis b c ∧ ¬ Commutes D b c)

def context {D : MRDTSig} (C : ReplayContext D.toUpdateSig) : ReplayContext (algebra D) :=
  { L := C.L, vis := C.vis, timestamps_distinct := C.timestamps_distinct,
    vis_total_same_replica := C.vis_total_same_replica }

theorem order_eq {D : MRDTSig} (P : OperationPolicy D.AppOp)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (a b : Op D.AppOp) :
    order P C E a b ↔ paperOrder P (context C) E a b := by
  simp only [order,paperOrder,commutes_iff,context]
  rfl

/-- Observable canonical state; concrete metadata is deliberately retained. -/
def Canonical (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (s : D.State) : Prop :=
  @IsCanonicalState (algebra D) P.lift (context C) E (observe D s)

theorem canonical_of_concrete {D : MRDTSig} {P : OperationPolicy D.AppOp}
    (old : RestrictedLaws D.toUpdateSig P) (new : Laws D P)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (s : D.State)
    (h : @IsCanonicalState D.toUpdateSig P.lift C E s) : Canonical D P C E s := by
  obtain ⟨π,hp,hr,hf⟩ := h
  have commutation : ∀ a b, (algebra D).commutes a b ↔ D.toUpdateSig.commutes a b := by
    intro a b
    exact not_iff_not.mp ((new.toRestricted.noncomm_exact a b).trans
      (old.noncomm_exact a b).symm)
  refine ⟨π,hp,?_,?_⟩
  · apply hr.imp
    intro a b h edge
    apply h
    apply (paperOrder_iff_loOn old C E _ _).mp
    have paper := (paperOrder_iff_loOn new.toRestricted (context C) E _ _).mpr edge
    simpa only [paperOrder,context,commutation] using paper
  · change applySeq (algebra D) (observe D D.init) π = observe D s
    rw [fold_observe,hf]

theorem canonical_query_unique {D : MRDTSig} {P : OperationPolicy D.AppOp}
    (laws : Laws D P) (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (supported : ∀ e ∈ E, e ∈ C.events) {s t : D.State}
    (hs : Canonical D P C E s) (ht : Canonical D P C E t) (q : D.Query) :
    D.query s q = D.query t q := by
  letI : ReplayPolicy (algebra D) := P.lift
  have eq := isCanonicalState_unique_of_replayLaws (C := context C)
    laws.toRestricted.replayLaws supported hs ht
  exact equivalent_query (Quotient.exact eq) q

/-- This cannot be inferred merely from read equivalence. -/
def MergeCongruence (D : MRDTSig) : Prop :=
  ∀ l l' a a' b b', Equivalent D l l' → Equivalent D a a' → Equivalent D b b' →
    Equivalent D (D.merge l a b) (D.merge l' a' b')

def SpecificationCompatibility (D : MRDTSig)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) : Prop :=
  ∀ a b, Commutes D a b → S.Commutes a b

/-- Correctness criterion whose implementation ordering is query-relative. -/
def VersionsRALinearizable (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s,E) → ∀ q, ∃ π : List (Op D.AppOp),
    listPermOf π E ∧ respects π (order P C.replayContext E) ∧
    respects π (projectedSpecVisibility id S C.replayContext) ∧
    S.admits (projectedLabels id π ++ [.query q (D.query s q)])

def RALinearizable (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ r v s E, C.head r = some v → C.ver v = some (s,E) → ∀ q,
    ∃ π : List (Op D.AppOp), listPermOf π E ∧
      respects π (order P C.replayContext E) ∧
      respects π (projectedSpecVisibility id S C.replayContext) ∧
      S.admits (projectedLabels id π ++ [.query q (D.query s q)])

theorem VersionsRALinearizable.heads {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {C : Configuration D}
    (h : VersionsRALinearizable D P S C) : RALinearizable D P S C :=
  fun _ v s E _ hv q => h v s E hv q

/-- The generic history bridge now needs only observable canonicality.
No concrete-state equality or tag-erasing merge assumption is used. -/
theorem of_canonical {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {C : Configuration D}
    (laws : Laws D P)
    (canonical : ∀ v s E, C.ver v = some (s,E) → Canonical D P C.replayContext E s)
    (compatible : SpecificationCompatibility D S) (sound : EventFoldHistorySound D S) :
    VersionsRALinearizable D P S C := by
  letI : ReplayPolicy (algebra D) := P.lift
  intro v s E hv q
  obtain ⟨π,hp,hr,hf⟩ := canonical v s E hv
  have ho : respects π (order P C.replayContext E) :=
    hr.imp (fun {_ _} h => h ∘ fun edge =>
      (paperOrder_iff_loOn laws.toRestricted _ _ _ _).mp
        ((order_eq P _ _ _ _).mp edge))
  refine ⟨π,hp,ho,?_,?_⟩
  · exact ho.imp (fun {_ _} h => fun edge =>
      h (Or.inl ⟨edge.1,fun commute => edge.2 (compatible _ _ commute)⟩))
  · change applySeq (algebra D) (observe D D.init) π = observe D s at hf
    rw [fold_observe] at hf
    have answer := equivalent_query (Quotient.exact hf) q
    simpa [answer] using sound π q

end QueryReplay
end Sal.MRDTs.Paper1
