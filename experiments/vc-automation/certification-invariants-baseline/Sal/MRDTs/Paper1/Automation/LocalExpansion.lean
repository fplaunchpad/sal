import Sal.MRDTs.Paper1.Automation.InductiveLeaves

/-! Inductive kernels for the ACTUAL nested local redistribution equation.
The equation-shaped IH quantifies the reconstructed local remainder t, so
coverage concerns only common l, causal past B, and opposite branch b. -/
namespace Sal.MRDTs.Paper1.Automation.Signature
open Sal.MRDTs.Foundation

def LocalEquation (D : Signature) (l B b : D.State) (e : Op D.AppOp) : Prop :=
  ∀ t, D.merge l (D.merge B t (D.step B e)) b =
    D.merge B (D.merge l t b) (D.step B e)

def Commute (D : Signature) (e h : Op D.AppOp) : Prop :=
  ∀ s, D.step (D.step s e) h = D.step (D.step s h) e

def local_base (D : Signature) : Prop := ∀ e,
  D.LocalEquation D.init D.init D.init e

def local_common_all (D : Signature) : Prop := ∀ l B b e h,
  D.LocalEquation l B b e →
  D.LocalEquation (D.step l h) (D.step B h) (D.step b h) e

def local_common_opposite (D : Signature) : Prop := ∀ l B b e h,
  D.LocalEquation l B b e →
  D.LocalEquation (D.step l h) B (D.step b h) e

def local_past_commuting (D : Signature) : Prop := ∀ l B b e h,
  D.Commute e h → D.LocalEquation l B b e →
  D.LocalEquation l (D.step B h) b e

def local_opposite_commuting (D : Signature) : Prop := ∀ l B b e h,
  D.Commute e h → D.LocalEquation l B b e →
  D.LocalEquation l B (D.step b h) e
/-- Equation-shaped freshness companion, proved by event-history expansion.
For Add it says the born tag is absent; Remove requires no birth evidence. -/
def FreshEquation (D : Signature) (s : D.State) (e : Op D.AppOp) : Prop :=
  D.merge s D.init (D.step s e) = D.step D.init e

def fresh_base (D : Signature) : Prop := ∀ e, D.FreshEquation D.init e

def fresh_step (D : Signature) : Prop := ∀ s e h,
  D.distinct e h → D.FreshEquation s e → D.FreshEquation (D.step s h) e

def local_past_fresh (D : Signature) : Prop := ∀ l B b e h,
  D.FreshEquation l e → D.FreshEquation b h → D.LocalEquation l B b e →
  D.LocalEquation l (D.step B h) b e

def local_opposite_fresh (D : Signature) : Prop := ∀ l B b e h,
  D.FreshEquation l e → D.FreshEquation B h → D.LocalEquation l B b e →
  D.LocalEquation l B (D.step b h) e

def local_empty_past (D : Signature) : Prop := ∀ l b e,
  D.FreshEquation l e → D.LocalEquation l D.init b e

def local_past_singleton (D : Signature) : Prop := ∀ l B b e h,
  D.FreshEquation l e → D.LocalEquation l B b e →
  D.LocalEquation l (D.step D.init h) b e →
  D.LocalEquation l (D.step B h) b e

end Sal.MRDTs.Paper1.Automation.Signature


namespace Sal.MRDTs.Paper1.Automation.Signature
open Sal.MRDTs.Foundation Classical

noncomputable def restrictedReplay (D : Signature)
    (π : List (Op D.AppOp)) (E : Set (Op D.AppOp)) : D.State :=
  (π.filter (fun h => decide (h ∈ E))).foldl D.step D.init

theorem restrictedReplay_append (D : Signature) (π : List (Op D.AppOp))
    (h : Op D.AppOp) (E : Set (Op D.AppOp)) :
    D.restrictedReplay (π ++ [h]) E =
      if h ∈ E then D.step (D.restrictedReplay π E) h else D.restrictedReplay π E := by
  by_cases member : h ∈ E <;>
    simp [restrictedReplay,List.filter_append,List.foldl_append,member]

theorem fresh_restrictedReplay (D : Signature) (base : D.fresh_base)
    (step : D.fresh_step) (π : List (Op D.AppOp)) (E : Set (Op D.AppOp))
    (e : Op D.AppOp) :
    (∀ h ∈ π, D.distinct e h) → D.FreshEquation (D.restrictedReplay π E) e := by
  induction π using List.reverseRecOn with
  | nil => intro _; exact base e
  | append_singleton π h ih =>
      intro fresh
      have prior := ih (fun x hx => fresh x (List.mem_append_left [h] hx))
      rw [restrictedReplay_append]
      split
      · exact step _ e h (fresh h (by simp)) prior
      · exact prior

/-- Genuine coverage of the finite local kernels for the five coherent index
membership transitions. Histories are restrictions of an explicit event list,
not an arbitrary relation defined using the desired target equation. Canonical
alignment must be established separately from representation/context evidence. -/
theorem local_restrictedReplay (D : Signature)
    (base : D.local_base) (all : D.local_common_all)
    (common : D.local_common_opposite) (pastStep : D.local_past_fresh)
    (opposite : D.local_opposite_fresh) (freshBase : D.fresh_base)
    (freshStep : D.fresh_step) (L K O : Set (Op D.AppOp))
    (subset : L ⊆ O) (coherent : K ∩ O ⊆ L)
    (e : Op D.AppOp) (π : List (Op D.AppOp)) :
    π.Pairwise (fun x y => D.distinct x y) →
    (∀ h ∈ π, D.distinct e h) →
    D.LocalEquation (D.restrictedReplay π L) (D.restrictedReplay π K)
      (D.restrictedReplay π O) e := by
  induction π using List.reverseRecOn with
  | nil => intro _ _; exact base e
  | append_singleton π h ih =>
      intro distinct fresh
      have hd := List.pairwise_append.mp distinct
      have previous := ih hd.1 (fun x hx => fresh x (List.mem_append_left [h] hx))
      have hFresh : ∀ x ∈ π, D.distinct h x := by
        intro x hx
        exact Ne.symm (hd.2.2 x hx h (by simp))
      have freshL := D.fresh_restrictedReplay freshBase freshStep π L e
        (fun x hx => fresh x (List.mem_append_left [h] hx))
      have freshB := D.fresh_restrictedReplay freshBase freshStep π K h hFresh
      have freshO := D.fresh_restrictedReplay freshBase freshStep π O h hFresh
      rw [restrictedReplay_append,restrictedReplay_append,restrictedReplay_append]
      by_cases hl : h ∈ L <;> by_cases hk : h ∈ K <;> by_cases ho : h ∈ O <;>
        simp only [hl,hk,ho,if_true,if_false]
      · exact all _ _ _ e h previous
      · exact False.elim (ho (subset hl))
      · exact common _ _ _ e h previous
      · exact False.elim (ho (subset hl))
      · exact False.elim (hl (coherent ⟨hk,ho⟩))
      · exact pastStep _ _ _ e h freshL freshO previous
      · exact opposite _ _ _ e h freshL freshB previous
      · exact previous

end Sal.MRDTs.Paper1.Automation.Signature

namespace Sal.MRDTs.Paper1.Automation.Signature
open Sal.MRDTs.Foundation

/-- Independent causal-past replay construction. The already built l and b
histories need not align with B. Each frozen past event contributes its own
singleton equation, which the finite step combines with the equation IH. -/
theorem local_independent_past (D : Signature)
    (empty : D.local_empty_past) (step : D.local_past_singleton)
    (l b : D.State) (e : Op D.AppOp) (fresh : D.FreshEquation l e)
    (π : List (Op D.AppOp)) :
    (∀ h ∈ π, D.LocalEquation l (D.step D.init h) b e) →
    D.LocalEquation l (π.foldl D.step D.init) b e := by
  induction π using List.reverseRecOn with
  | nil => intro _; exact empty l b e fresh
  | append_singleton π h ih =>
      intro singletons
      have previous := ih (fun x hx => singletons x (List.mem_append_left [h] hx))
      simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
      exact step l _ b e h fresh previous (singletons h (by simp))

end Sal.MRDTs.Paper1.Automation.Signature
