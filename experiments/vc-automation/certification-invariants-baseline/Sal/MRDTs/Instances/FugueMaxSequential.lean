import Sal.MRDTs.Instances.FugueMaxReplayProof
import Sal.MRDTs.Instances.SidedEmbedRGASequential

namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax

open Sal.EmbedRGA (FMEntry FMChain fmEntryBefore fmEntryBefore_asymm
  fmEntryBefore_irrefl fmEntryBefore_total fmChainBefore fmChainBefore_inv keyLt_trans)

/-- Farther siblings must be constructed first so each ordinary splice
places the new child adjacent to its parent. Opposite sides are unrelated. -/
def siblingBuildBefore : FMEntry → FMEntry → Prop
  | .L d, .L e => d < e
  | .R t d, .R u e => fmEntryBefore (.R u e) (.R t d)
  | _, _ => False

private theorem entry_before_trans {a b c : FMEntry}
    (hab : fmEntryBefore a b) (hbc : fmEntryBefore b c) : fmEntryBefore a c := by
  cases a <;> cases b <;> cases c <;> simp only [fmEntryBefore] at *
  · rcases hab with hab | ⟨rfl, hab⟩ <;> rcases hbc with hbc | ⟨rfl, hbc⟩
    · exact Or.inl (keyLt_trans hab hbc)
    · exact Or.inl hab
    · exact Or.inl hbc
    · exact Or.inr ⟨rfl, Nat.lt_trans hab hbc⟩
  all_goals first | tauto | exact Nat.lt_trans hab hbc

theorem siblingBuildBefore_trans {a b c : FMEntry}
    (hab : siblingBuildBefore a b) (hbc : siblingBuildBefore b c) :
    siblingBuildBefore a c := by
  cases a <;> cases b <;> cases c <;> simp only [siblingBuildBefore] at *
  · exact entry_before_trans hbc hab
  all_goals first | contradiction | exact Nat.lt_trans hab hbc

theorem siblingBuildBefore_irrefl (a : FMEntry) : ¬ siblingBuildBefore a a := by
  cases a
  · exact fmEntryBefore_irrefl (.R _ _)
  · exact Nat.lt_irrefl _

/-- Proof-local construction order: increasing depth, then farther siblings
first. It does not replace the insertion-before-own-delete public `rc`. -/
def chainBuildBefore (a b : FMChain) : Prop :=
  a.length < b.length ∨
    ∃ p x y, a = p ++ [x] ∧ b = p ++ [y] ∧ siblingBuildBefore x y

theorem chainBuildBefore_length {a b : FMChain} (h : chainBuildBefore a b) :
    a.length ≤ b.length := by
  rcases h with h | ⟨p, x, y, rfl, rfl, _⟩
  · exact Nat.le_of_lt h
  · simp

theorem chainBuildBefore_trans {a b c : FMChain}
    (hab : chainBuildBefore a b) (hbc : chainBuildBefore b c) : chainBuildBefore a c := by
  have hablen := chainBuildBefore_length hab
  have hbclen := chainBuildBefore_length hbc
  rcases hab with hab | ⟨p, x, y, rfl, rfl, hxy⟩
  · exact Or.inl (Nat.lt_of_lt_of_le hab hbclen)
  rcases hbc with hbc | ⟨q, y', z, heq, rfl, hyz⟩
  · exact Or.inl (Nat.lt_of_le_of_lt hablen hbc)
  obtain ⟨rfl, hy⟩ := List.append_inj' heq rfl
  injection hy with hy
  subst hy
  exact Or.inr ⟨p, x, z, rfl, rfl, siblingBuildBefore_trans hxy hyz⟩

theorem chainBuildBefore_irrefl (a : FMChain) : ¬ chainBuildBefore a a := by
  rintro (h | ⟨p, x, y, rfl, heq, hxy⟩)
  · exact Nat.lt_irrefl _ h
  · have h := (List.append_inj' heq rfl).2
    injection h with h
    subst h
    exact siblingBuildBefore_irrefl _ hxy

theorem exists_chain_construction (ops : List MRec) :
    ∃ ordered, ops.Perm ordered ∧
      Sal.MRDTs.Foundation.respects ordered (fun a b => chainBuildBefore a.chain b.chain) := by
  exact Sal.MRDTs.exists_respecting_perm
    (R := fun (a b : MRec) => chainBuildBefore a.chain b.chain)
    (fun hab hbc => chainBuildBefore_trans hab hbc)
    (fun a => chainBuildBefore_irrefl a.chain) ops

/-- Earlier records in a construction have no greater depth. -/
theorem construction_depth {a b : FMChain} (h : ¬ chainBuildBefore b a) :
    a.length ≤ b.length := by
  by_contra hlen
  exact h (Or.inl (Nat.lt_of_not_ge hlen))

/-- A same-parent right continuation in the constructed prefix must be a
farther sibling, not a descendant. This supplies the right adjacency premise. -/
theorem construction_right {a p : FMChain} {t : List Nat} {d : Nat}
    (hne : a ≠ p ++ [.R t d])
    (h : ¬ chainBuildBefore (p ++ [.R t d]) a)
    {u : List Nat} {e : Nat} {rest : FMChain}
    (ha : a = p ++ .R u e :: rest) : fmEntryBefore (.R t d) (.R u e) := by
  have hlen := construction_depth h
  subst a
  have hrest : rest = [] := by
    have : rest.length = 0 := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    exact List.length_eq_zero_iff.mp this
  subst rest
  have hentry : FMEntry.R t d ≠ FMEntry.R u e := by
    intro heq
    exact hne (by rw [heq])
  rcases fmEntryBefore_total hentry with hlt | hlt
  · exact hlt
  · exact False.elim (h (Or.inr ⟨p, .R t d, .R u e, rfl, rfl, hlt⟩))

theorem construction_left {a p : FMChain} {d : Nat}
    (hne : a ≠ p ++ [.L d])
    (h : ¬ chainBuildBefore (p ++ [.L d]) a)
    {e : Nat} {rest : FMChain} (ha : a = p ++ .L e :: rest) : e < d := by
  have hlen := construction_depth h
  subst a
  have hrest : rest = [] := by
    have : rest.length = 0 := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    exact List.length_eq_zero_iff.mp this
  subst rest
  have hne' : e ≠ d := fun heq => hne (by rw [heq])
  have hnd : ¬ d < e := fun hlt =>
    h (Or.inr ⟨p, .L d, .L e, rfl, rfl, hlt⟩)
  omega

/-! Adjacency lemmas for constructing an ordinary-list replay. The right
alphabet differs from sided RGA: siblings are ordered by right-origin tag
and then increasing delta. Its construction order must therefore use the
opposite sibling order, not the sided-RGA freshness argument. -/

theorem fmChainBefore_snocR_iff {ca cr : FMChain} {tag : List Nat} {δ : Nat}
    (hne : cr ≠ ca)
    (hfar : ∀ t d rest, cr = ca ++ FMEntry.R t d :: rest →
      fmEntryBefore (.R tag δ) (.R t d)) :
    fmChainBefore cr (ca ++ [.R tag δ]) ↔ fmChainBefore cr ca := by
  constructor
  · intro h
    rcases fmChainBefore_inv h with ⟨d, rest, heq⟩ | ⟨t, d, rest, heq⟩ |
      ⟨q, e1, e2, t1, t2, hlt, hu, hv⟩
    · exact False.elim (fmEntryBefore_irrefl _
        (hfar tag δ (.L d :: rest) (by rw [heq]; simp)))
    · rcases List.eq_nil_or_concat rest with rfl | ⟨rest', lst, rfl⟩
      · exact absurd (List.append_inj' heq rfl).1.symm hne
      · simp only [List.concat_eq_append] at heq
        rw [show cr ++ .R t d :: (rest' ++ [lst]) =
          (cr ++ .R t d :: rest') ++ [lst] from by simp] at heq
        obtain ⟨hca, -⟩ := List.append_inj' heq rfl
        rw [hca]
        exact fmChainBefore.extR cr t d rest'
    · rcases List.eq_nil_or_concat t2 with rfl | ⟨t2', lst, rfl⟩
      · have h2 : q ++ [e2] = ca ++ [.R tag δ] := hv.symm
        obtain ⟨rfl, he⟩ := List.append_inj' h2 rfl
        injection he with he1
        subst he1
        cases e1 with
        | R t d => exact False.elim (fmEntryBefore_asymm (hfar t d t1 hu) hlt)
        | L d => rw [hu]; exact fmChainBefore.extL q d t1
      · simp only [List.concat_eq_append] at hv
        rw [show q ++ e2 :: (t2' ++ [lst]) = (q ++ e2 :: t2') ++ [lst]
          from by simp] at hv
        obtain ⟨hca, -⟩ := List.append_inj' hv rfl
        rw [hu, hca]
        exact fmChainBefore.diverge q e1 e2 t1 t2' hlt
  · intro h
    rcases fmChainBefore_inv h with ⟨d, rest, heq⟩ | ⟨t, d, rest, heq⟩ |
      ⟨q, e1, e2, t1, t2, hlt, hu, hv⟩
    · rw [heq]
      exact fmChainBefore.diverge ca (.L d) (.R tag δ) rest [] trivial
    · rw [heq, List.append_assoc]
      exact fmChainBefore.extR cr t d (rest ++ [.R tag δ])
    · rw [hu, hv, List.append_assoc]
      exact fmChainBefore.diverge q e1 e2 t1 (t2 ++ [.R tag δ]) hlt

theorem fmChainBefore_snocL_iff {ca cr : FMChain} {δ : Nat}
    (hne : cr ≠ ca)
    (hfar : ∀ d rest, cr = ca ++ FMEntry.L d :: rest → d < δ) :
    fmChainBefore (ca ++ [.L δ]) cr ↔ fmChainBefore ca cr := by
  constructor
  · intro h
    rcases fmChainBefore_inv h with ⟨d, rest, heq⟩ | ⟨t, d, rest, heq⟩ |
      ⟨q, e1, e2, t1, t2, hlt, hu, hv⟩
    · rcases List.eq_nil_or_concat rest with rfl | ⟨rest', lst, rfl⟩
      · exact absurd (List.append_inj' heq rfl).1.symm hne
      · simp only [List.concat_eq_append] at heq
        rw [show cr ++ .L d :: (rest' ++ [lst]) =
          (cr ++ .L d :: rest') ++ [lst] from by simp] at heq
        obtain ⟨hca, -⟩ := List.append_inj' heq rfl
        rw [hca]
        exact fmChainBefore.extL cr d rest'
    · have := hfar δ (.R t d :: rest) (by rw [heq]; simp)
      omega
    · rcases List.eq_nil_or_concat t1 with rfl | ⟨t1', lst, rfl⟩
      · have h2 : q ++ [e1] = ca ++ [.L δ] := hu.symm
        obtain ⟨rfl, he⟩ := List.append_inj' h2 rfl
        injection he with he1
        subst he1
        cases e2 with
        | R t d => rw [hv]; exact fmChainBefore.extR q t d t2
        | L d =>
            have hd := hfar d t2 hv
            have hδd : δ < d := hlt
            omega
      · simp only [List.concat_eq_append] at hu
        rw [show q ++ e1 :: (t1' ++ [lst]) = (q ++ e1 :: t1') ++ [lst]
          from by simp] at hu
        obtain ⟨hca, -⟩ := List.append_inj' hu rfl
        rw [hv, hca]
        exact fmChainBefore.diverge q e1 e2 t1' t2 hlt
  · intro h
    rcases fmChainBefore_inv h with ⟨d, rest, heq⟩ | ⟨t, d, rest, heq⟩ |
      ⟨q, e1, e2, t1, t2, hlt, hu, hv⟩
    · rw [heq, List.append_assoc]
      exact fmChainBefore.extL cr d (rest ++ [.L δ])
    · rw [heq]
      exact fmChainBefore.diverge ca (.L δ) (.R t d) [] rest trivial
    · rw [hu, hv, List.append_assoc]
      exact fmChainBefore.diverge q e1 e2 (t1 ++ [.L δ]) t2 hlt

#print axioms fmChainBefore_snocR_iff
#print axioms fmChainBefore_snocL_iff
#print axioms exists_chain_construction

end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
