import Sal.MRDTs.Framework.Base.Replay
import Mathlib.Data.Finset.Dedup

/-! Transport honest-origin membership to a visibility-respecting replay prefix.
Only enumeration, causal closure and order evidence are used. -/
namespace Sal.MRDTs.Paper1.Automation.OriginPrefixEvidence
open Sal.MRDTs.Foundation

theorem origin_subset_prefix {α : Type} [DecidableEq α]
    {R : α → α → Prop} {E : Set α} {ops origin pre post : List α} {e : α}
    (perm : listPermOf ops E) (visible : respects ops R)
    (irrefl : ∀ a, ¬ R a a)
    (closed : ∀ a b, R a b → b ∈ E → a ∈ E)
    (before : ∀ a ∈ origin, R a e) (split : ops = pre ++ e :: post) :
    origin.toFinset ⊆ pre.toFinset := by
  intro old member
  have edge := before old (List.mem_toFinset.mp member)
  have he : e ∈ E := (perm.2 e).mp (by rw [split]; simp)
  have whole := (perm.2 old).mpr (closed old e edge he)
  rw [split] at whole
  rcases List.mem_append.mp whole with inPre | inRest
  · exact List.mem_toFinset.mpr inPre
  · rcases List.mem_cons.mp inRest with same | inPost
    · subst old
      exact False.elim (irrefl e edge)
    · rw [split] at visible
      have noBack := (List.pairwise_cons.mp
        (List.pairwise_append.mp visible).2.1).1 old inPost
      exact False.elim (noBack edge)

end Sal.MRDTs.Paper1.Automation.OriginPrefixEvidence
