import Sal.CRDTs.Metatheory.RA_Linearizability
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-! Merge-independent list/fold tools for the corrected set-relative theory. -/

namespace Sal.MRDTs.Foundation

open Classical

section
variable {D : CRDTSig}

/-- Commutativity is symmetric because its defining state equation is. -/
theorem commutes_symm {a b : Op D.AppOp} (h : D.commutes a b) :
    D.commutes b a :=
  fun s => (h s).symm

theorem applySeq_swap_commute_basic
    {a b : Op D.AppOp} (h_comm : D.commutes a b)
    (pfx sfx : List (Op D.AppOp)) (s : D.State) :
    applySeq D s (pfx ++ a :: b :: sfx)
    = applySeq D s (pfx ++ b :: a :: sfx) := by
  simp only [applySeq, List.foldl_append, List.foldl_cons]
  rw [h_comm]

theorem applySeq_comm_extract_basic
    {e : Op D.AppOp} {π : List (Op D.AppOp)}
    (h_mem : e ∈ π) (h_nodup : π.Nodup)
    (h_comm : ∀ x ∈ π, x ≠ e → D.commutes e x)
    (s : D.State) :
    applySeq D s π = D.update (applySeq D s (π.filter (· ≠ e))) e := by
  induction π using List.reverseRecOn <;> simp_all +decide [applySeq]
  cases h_mem <;> simp_all +decide [List.nodup_append]
  · rename_i k hk
    cases eq_or_ne k e <;> simp_all +decide [CRDTSig.commutes]
    grind
  · rw [List.filter_eq_self.mpr]
    aesop

theorem filter_ne_listPermOf_basic
    {e : Op D.AppOp} {π : List (Op D.AppOp)} {ev : Set (Op D.AppOp)}
    (h_perm : listPermOf π ev) (h_mem : e ∈ π) :
    listPermOf (π.filter (· ≠ e)) (ev \ {e}) := by
  constructor
  · exact h_perm.1.filter _
  · intro a
    have h := h_perm.2 a
    aesop

/-! Stable compatibility names formerly supplied accidentally by the
global-`lo` file. Keeping them here makes the dependency boundary explicit. -/

theorem applySeq_swap_commute
    {a b : Op D.AppOp} (h_comm : D.commutes a b)
    (pfx sfx : List (Op D.AppOp)) (s : D.State) :
    applySeq D s (pfx ++ a :: b :: sfx)
    = applySeq D s (pfx ++ b :: a :: sfx) :=
  applySeq_swap_commute_basic h_comm pfx sfx s

theorem applySeq_comm_extract
    {e : Op D.AppOp} {π : List (Op D.AppOp)}
    (h_mem : e ∈ π) (h_nodup : π.Nodup)
    (h_comm : ∀ x ∈ π, x ≠ e → D.commutes e x)
    (s : D.State) :
    applySeq D s π = D.update (applySeq D s (π.filter (· ≠ e))) e :=
  applySeq_comm_extract_basic h_mem h_nodup h_comm s

theorem filter_ne_listPermOf
    {e : Op D.AppOp} {π : List (Op D.AppOp)} {ev : Set (Op D.AppOp)}
    (h_perm : listPermOf π ev) (h_mem : e ∈ π) :
    listPermOf (π.filter (· ≠ e)) (ev \ {e}) :=
  filter_ne_listPermOf_basic h_perm h_mem

end


end Sal.MRDTs.Foundation
