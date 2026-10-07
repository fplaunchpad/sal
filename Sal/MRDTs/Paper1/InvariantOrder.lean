import Sal.MRDTs.Paper1.EventBridge

/-! Invariant-scoped concrete commutation and the corresponding RA criterion.
The same state domain is used in the causal and absorber clauses. It is not a
simultaneous-issuability test: operations retain their original mint evidence.
Validity and its preservation are obligations of a certificate, not inferred
from the desired history or query answer. The earlier raw criterion is retained
unchanged for comparison. -/
namespace Sal.MRDTs.Paper1.InvariantOrder
open Foundation

/-- Concrete equality on an explicitly specified domain of representation
states. In particular, no readiness premise makes causal pairs vacuous. -/
def Commutes (D : UpdateSig) (Inv : D.State → Prop) (a b : Op D.AppOp) : Prop :=
  ∀ s, Inv s → D.update (D.update s a) b = D.update (D.update s b) a

theorem commutes_symm {D : UpdateSig} {Inv : D.State → Prop} {a b : Op D.AppOp}
    (h : Commutes D Inv a b) : Commutes D Inv b a :=
  fun s hs => (h s hs).symm

theorem commutes_of_raw {D : UpdateSig} {Inv : D.State → Prop} {a b : Op D.AppOp}
    (h : D.commutes a b) : Commutes D Inv a b := fun s _ => h s

/-- Smaller domains require fewer equalities. A port must justify its domain
independently; this lemma alone does not justify excluding any reachable state. -/
theorem commutes_mono {D : UpdateSig} {I J : D.State → Prop}
    (sub : ∀ s, I s → J s) {a b : Op D.AppOp} (h : Commutes D J a b) :
    Commutes D I a b := fun s hs => h s (sub s hs)

def order {D : UpdateSig} (Inv : D.State → Prop) (P : OperationPolicy D.AppOp)
    (C : ReplayContext D) (events : Set (Op D.AppOp)) (a b : Op D.AppOp) : Prop :=
  (C.vis a b ∧ ¬ Commutes D Inv a b) ∨
    (¬ C.vis a b ∧ ¬ C.vis b a ∧ P.before a.op b.op ∧
      ¬ ∃ c ∈ events, C.vis b c ∧ ¬ Commutes D Inv b c)

theorem order_universal {D : UpdateSig} (P : OperationPolicy D.AppOp)
    (C : ReplayContext D) (events : Set (Op D.AppOp)) (a b : Op D.AppOp) :
    order (fun _ => True) P C events a b ↔ paperOrder P C events a b := by
  have eq : ∀ x y, Commutes D (fun _ => True) x y ↔ D.commutes x y := by
    intro x y
    exact ⟨fun h s => h s trivial,fun h s _ => h s⟩
  simp only [order,paperOrder,eq]

/-- Restrict only the event set, keeping the valid-state domain fixed. -/
theorem order_restrict {D : UpdateSig} {Inv : D.State → Prop}
    {P : OperationPolicy D.AppOp} {C : ReplayContext D}
    {E F : Set (Op D.AppOp)} (sub : E ⊆ F) {a b : Op D.AppOp}
    (h : order Inv P C F a b) : order Inv P C E a b := by
  rcases h with causal | ⟨ab,ba,before,none⟩
  · exact Or.inl causal
  · exact Or.inr ⟨ab,ba,before,fun ⟨c,hc,vis,nc⟩ => none ⟨c,sub hc,vis,nc⟩⟩

/-- Nonvacuity and closure under already-issued effectors and merges. The
state predicate may overapproximate reachability. Eligibility belongs to the
fixed context; it does not require re-issuing an operation at each state. -/
structure Closed (D : MRDTSig) (C : ReplayContext D.toUpdateSig)
    (Inv : D.State → Prop) : Prop where
  initial : Inv D.init
  update : ∀ s, Inv s → ∀ e ∈ C.events, Inv (D.update s e)
  merge : ∀ l a b, Inv l → Inv a → Inv b → Inv (D.merge l a b)

/-- Closure includes arbitrary reordering and repetition of already-issued
events, not only fresh, visibility-respecting execution prefixes. -/
theorem Closed.applySeq {D : MRDTSig} {C : ReplayContext D.toUpdateSig}
    {Inv : D.State → Prop} (closed : Closed D C Inv)
    {s : D.State} (valid : Inv s) (ops : List (Op D.AppOp))
    (eligible : ∀ e ∈ ops, e ∈ C.events) :
    Inv (Foundation.applySeq D.toUpdateSig s ops) := by
  induction ops generalizing s with
  | nil => exact valid
  | cons e ops ih =>
    exact ih (closed.update s valid e (eligible e List.mem_cons_self))
      (fun x hx => eligible x (List.mem_cons_of_mem e hx))

/-- One and the same history must respect both orders and explain the query
in the unchanged independent full-event sequential language. -/
def VersionsRA (D : MRDTSig) (Inv : D.State → Prop) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s,E) → ∀ q, ∃ π : List (Op D.AppOp),
    listPermOf π E ∧ respects π (order Inv P C.replayContext E) ∧
    respects π (projectedSpecVisibility id S C.replayContext) ∧
    S.admits (projectedLabels id π ++ [.query q (D.query s q)])

/-- The universal domain recovers the original full-event witness criterion,
including its independent specification-visibility obligation. -/
theorem versions_universal (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) :
    VersionsRA D (fun _ => True) P S C ↔ EventVersionsSpecificationRA D P S C := by
  simp only [VersionsRA,EventVersionsSpecificationRA,respects,order_universal]

end Sal.MRDTs.Paper1.InvariantOrder
