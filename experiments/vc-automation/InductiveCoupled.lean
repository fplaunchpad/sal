import InductiveLeaves

/-! Actual Neem intermediate insertion leaves lift to arbitrary finite blocks.
The fixed predecessor r and common event h retain their insertion positions:
all block operations occur before r, and r occurs before h. These are equations
on replay states, not a relation with the target equation as its constructor.
The theorem does not assert compatible-history coverage or Sal's five VCs. -/
open Sal.MRDTs.Foundation
namespace NeemExpansion
namespace Signature
variable (D : Signature)

def BlockGuard1 (p r h o : Op D.AppOp) : Prop :=
  (D.order o r ≠ .Either ∨ D.order o h = .Fst_then_snd) ∧
  D.distinct p o ∧ D.distinct r o ∧ D.distinct h o ∧ o.2.1 ≠ h.2.1

def BlockGuard2 (p q r h o : Op D.AppOp) : Prop :=
  D.BlockGuard1 p r h o ∧ D.distinct q o

/-- Left one-op intermediate blocks, starting from the common-event IH. -/
theorem left_block1 (base : D.inter_left_base_1op) (extend : D.inter_left_1op)
    (l a b : D.State) (p r h : Op D.AppOp)
    (ord : D.order r h = .Fst_then_snd) (rid : r.2.1 ≠ h.2.1)
    (pr : D.distinct p r) (ph : D.distinct p h) (rh : D.distinct r h)
    (common : D.Q1 (D.step l h) (D.step a h) (D.step b h) p)
    (block : List (Op D.AppOp)) (guards : ∀ o ∈ block, D.BlockGuard1 p r h o) :
    D.Q1 (D.step l h) (D.step (D.step (block.foldl D.step a) r) h) (D.step b h) p := by
  induction block using List.reverseRecOn with
  | nil => exact base l a b p r h ⟨ord,rid,pr,ph,rh,common⟩
  | append_singleton block o ih =>
      have pre : ∀ x ∈ block, D.BlockGuard1 p r h x := by
        intro x hx; exact guards x (List.mem_append_left _ hx)
      obtain ⟨orr,po,ro,ho,oh⟩ := guards o (by simp)
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using
        extend l (block.foldl D.step a) b p r h o
          ⟨ord,rid,orr,pr,ph,po,rh,ro,ho,oh,ih pre⟩

/-- Right one-op blocks retain the F* conditional two-op base IH. -/
theorem right_block1 (base : D.inter_right_base_1op) (extend : D.inter_right_1op)
    (l a b : D.State) (p r h : Op D.AppOp)
    (ord : D.order r h = .Fst_then_snd) (rid : r.2.1 ≠ h.2.1)
    (pr : D.distinct p r) (ph : D.distinct p h) (rh : D.distinct r h)
    (conditional : D.order r p = .Fst_then_snd → D.Q2 l a b p r)
    (common : D.Q1 (D.step l h) (D.step a h) (D.step b h) p)
    (block : List (Op D.AppOp)) (guards : ∀ o ∈ block, D.BlockGuard1 p r h o) :
    D.Q1 (D.step l h) (D.step a h) (D.step (D.step (block.foldl D.step b) r) h) p := by
  induction block using List.reverseRecOn with
  | nil => exact base l a b p r h ⟨ord,rid,pr,ph,rh,conditional,common⟩
  | append_singleton block o ih =>
      have pre : ∀ x ∈ block, D.BlockGuard1 p r h x := by
        intro x hx; exact guards x (List.mem_append_left _ hx)
      obtain ⟨orr,po,ro,ho,oh⟩ := guards o (by simp)
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using
        extend l a (block.foldl D.step b) p r h o
          ⟨ord,rid,orr,pr,ph,po,rh,ro,ho,oh,ih pre⟩

/-- Strict p/q policy order is retained for the left two-op family. -/
theorem left_block2 (base : D.inter_left_base_2op) (extend : D.inter_left_2op)
    (l a b : D.State) (p q r h : Op D.AppOp)
    (pqord : D.order q p = .Fst_then_snd) (pqrep : q.2.1 ≠ p.2.1)
    (ord : D.order r h = .Fst_then_snd) (rid : r.2.1 ≠ h.2.1)
    (pq : D.distinct p q) (pr : D.distinct p r) (ph : D.distinct p h)
    (qr : D.distinct q r) (qh : D.distinct q h) (rh : D.distinct r h)
    (common : D.Q2 (D.step l h) (D.step a h) (D.step b h) p q)
    (block : List (Op D.AppOp)) (guards : ∀ o ∈ block, D.BlockGuard2 p q r h o) :
    D.Q2 (D.step l h) (D.step (D.step (block.foldl D.step a) r) h) (D.step b h) p q := by
  induction block using List.reverseRecOn with
  | nil => exact base l a b p q r h ⟨pqord,ord,pqrep,rid,pq,pr,ph,qr,qh,rh,common⟩
  | append_singleton block o ih =>
      have pre : ∀ x ∈ block, D.BlockGuard2 p q r h x := by
        intro x hx; exact guards x (List.mem_append_left _ hx)
      obtain ⟨⟨orr,po,ro,ho,oh⟩,qo⟩ := guards o (by simp)
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using
        extend l (block.foldl D.step a) b p q r h o
          ⟨pqord,ord,pqrep,rid,orr,pq,pr,ph,po,qr,qh,qo,rh,ro,ho,oh,ih pre⟩

/-- Right two-op blocks preserve all three F* base IH equations. -/
theorem right_block2 (base : D.inter_right_base_2op) (extend : D.inter_right_2op)
    (l a b : D.State) (p q r h : Op D.AppOp)
    (pqord : D.admissible p q) (pqrep : p.2.1 ≠ q.2.1)
    (ord : D.order r h = .Fst_then_snd) (rid : r.2.1 ≠ h.2.1)
    (pq : D.distinct p q) (pr : D.distinct p r) (ph : D.distinct p h)
    (qr : D.distinct q r) (qh : D.distinct q h) (rh : D.distinct r h)
    (before : D.Q2 l a b p q) (withR : D.Q2 l a (D.step b r) p q)
    (common : D.Q2 (D.step l h) (D.step a h) (D.step b h) p q)
    (block : List (Op D.AppOp)) (guards : ∀ o ∈ block, D.BlockGuard2 p q r h o) :
    D.Q2 (D.step l h) (D.step a h) (D.step (D.step (block.foldl D.step b) r) h) p q := by
  induction block using List.reverseRecOn with
  | nil => exact base l a b p q r h ⟨pqord,pqrep,ord,rid,pq,pr,ph,qr,qh,rh,before,withR,common⟩
  | append_singleton block o ih =>
      have pre : ∀ x ∈ block, D.BlockGuard2 p q r h x := by
        intro x hx; exact guards x (List.mem_append_left _ hx)
      obtain ⟨⟨orr,po,ro,ho,oh⟩,qo⟩ := guards o (by simp)
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using
        extend l a (block.foldl D.step b) p q r h o
          ⟨pqord,pqrep,ord,rid,orr,pq,pr,ph,po,qr,qh,qo,rh,ro,ho,oh,ih pre⟩

/-- Coupled one-op blocks on both sides of the same common event. The right
block is built first, and its equation supplies the exact left-base IH. -/
theorem both_blocks1
    (rightBase : D.inter_right_base_1op) (rightExtend : D.inter_right_1op)
    (leftBase : D.inter_left_base_1op) (leftExtend : D.inter_left_1op)
    (l a b : D.State) (p rA rB h : Op D.AppOp)
    (ordA : D.order rA h = .Fst_then_snd) (ridA : rA.2.1 ≠ h.2.1)
    (prA : D.distinct p rA) (rAh : D.distinct rA h)
    (ordB : D.order rB h = .Fst_then_snd) (ridB : rB.2.1 ≠ h.2.1)
    (prB : D.distinct p rB) (rBh : D.distinct rB h) (ph : D.distinct p h)
    (conditional : D.order rB p = .Fst_then_snd → D.Q2 l a b p rB)
    (common : D.Q1 (D.step l h) (D.step a h) (D.step b h) p)
    (blockA blockB : List (Op D.AppOp))
    (guardsA : ∀ o ∈ blockA, D.BlockGuard1 p rA h o)
    (guardsB : ∀ o ∈ blockB, D.BlockGuard1 p rB h o) :
    D.Q1 (D.step l h)
      (D.step (D.step (blockA.foldl D.step a) rA) h)
      (D.step (D.step (blockB.foldl D.step b) rB) h) p := by
  have right := D.right_block1 rightBase rightExtend l a b p rB h
    ordB ridB prB ph rBh conditional common blockB guardsB
  exact D.left_block1 leftBase leftExtend l a (D.step (blockB.foldl D.step b) rB)
    p rA h ordA ridA prA ph rAh right blockA guardsA

/-- Coupled two-op blocks likewise retain the strictly ordered p/q guard.
The extra right-base IHs are not discarded during composition. -/
theorem both_blocks2
    (rightBase : D.inter_right_base_2op) (rightExtend : D.inter_right_2op)
    (leftBase : D.inter_left_base_2op) (leftExtend : D.inter_left_2op)
    (l a b : D.State) (p q rA rB h : Op D.AppOp)
    (pqord : D.order q p = .Fst_then_snd) (pqrep : p.2.1 ≠ q.2.1)
    (pq : D.distinct p q) (ph : D.distinct p h) (qh : D.distinct q h)
    (ordA : D.order rA h = .Fst_then_snd) (ridA : rA.2.1 ≠ h.2.1)
    (prA : D.distinct p rA) (qrA : D.distinct q rA) (rAh : D.distinct rA h)
    (ordB : D.order rB h = .Fst_then_snd) (ridB : rB.2.1 ≠ h.2.1)
    (prB : D.distinct p rB) (qrB : D.distinct q rB) (rBh : D.distinct rB h)
    (before : D.Q2 l a b p q) (withR : D.Q2 l a (D.step b rB) p q)
    (common : D.Q2 (D.step l h) (D.step a h) (D.step b h) p q)
    (blockA blockB : List (Op D.AppOp))
    (guardsA : ∀ o ∈ blockA, D.BlockGuard2 p q rA h o)
    (guardsB : ∀ o ∈ blockB, D.BlockGuard2 p q rB h o) :
    D.Q2 (D.step l h)
      (D.step (D.step (blockA.foldl D.step a) rA) h)
      (D.step (D.step (blockB.foldl D.step b) rB) h) p q := by
  have right := D.right_block2 rightBase rightExtend l a b p q rB h
    (Or.inl pqord) pqrep ordB ridB pq prB ph qrB qh rBh before withR common blockB guardsB
  exact D.left_block2 leftBase leftExtend l a (D.step (blockB.foldl D.step b) rB)
    p q rA h pqord (Ne.symm pqrep) ordA ridA pq prA ph qrA qh rAh right blockA guardsA

end Signature
end NeemExpansion
