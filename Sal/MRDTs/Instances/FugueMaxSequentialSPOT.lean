import Sal.MRDTs.Instances.FugueMaxIssuerSPOT
import Sal.MRDTs.Instances.SidedEmbedRGASequential
import Sal.MRDTs.Instances.FugueMaxContract

namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.SequentialSPOT

open Sal.EmbedRGA (unaryCode FMEntry Side keyLt)

/-! Refutation gate for the ordinary-list witness construction. This order is
proof-local: it is not another public conflict relation. Construct parents
before children, and farther siblings before nearer siblings. Then delete.
The abstract buffer stores only identities/values and the root sentinel. -/

def step := listStep

def before (a b : MRec) : Bool :=
  if a.chain.length != b.chain.length then a.chain.length < b.chain.length
  else
    match a.op, b.op with
    | .ins p sa, .ins q sb =>
      if p != q then p < q
      else match sa, sb with
      | .L, .R => true
      | .R, .L => false
      | .L, .L => a.ts ≤ b.ts
      | .R, .R =>
        match a.chain.getLastD (.L 0), b.chain.getLastD (.L 0) with
        | .R ta da, .R tb db => if ta = tb then db ≤ da else keyLt tb ta
        | _, _ => a.ts ≤ b.ts
    | _, _ => a.ts ≤ b.ts

def witness (K : KnowM) : KnowM :=
  (mMinted K).mergeSort before ++ K.filter (fun g => !mIsIns g)

def read (K : KnowM) : List Nat :=
  ((witness K).foldl step [(0, 0)]).filterMap (fun p => if p.1 = 0 then none else some p.1)

def fork (choices : List Nat) : KnowM :=
  let (A, a, _) := IssuerSPOT.branch id 0 1 [] (summarize unaryCode []) (choices.take 2)
  let (K, _, _) := IssuerSPOT.branch id 1 3 A a ((choices.drop 2).take 2)
  let (L, _, _) := IssuerSPOT.branch id 2 5 A a ((choices.drop 4).take 2)
  syncM K L

def check (choices : List Nat) : Bool :=
  let K := fork choices
  decide (read K = mView unaryCode K)

def siblings : KnowM :=
  [mGenInsAt unaryCode [] 0 1 0, mGenInsAt unaryCode [] 1 2 0]

theorem siblings_pass : read siblings = [1, 2] := by native_decide

/-- Timestamp-ascending replay is wrong for naive insert-after: the later
root child would be placed before the earlier one. -/
theorem timestamp_sort_fails :
    (siblings.foldl step [(0, 0)]).map Prod.fst = [0, 2, 1] := by decide

theorem deleted_anchor_pass :
    read FugueMaxContractSPOT.deletedChild = [1] := by native_decide

def anchorBirth : MRec := ⟨1, 0, .ins 0 .R, 0, none, []⟩
def anchorDelete : MRec := ⟨2, 0, .del 1, 0, none, []⟩
def afterAnchor : MRec := ⟨3, 0, .ins 1 .R, 1, none, []⟩
def repeatedDelete : MRec := ⟨3, 1, .del 1, 0, none, []⟩

theorem plain_splice_pass :
    listRun [anchorBirth, afterAnchor] = [(0, 0), (1, 1), (3, 3)] := by decide

/-- The abstract guard rejects insertion after an already deleted parent;
the implementation's retained metadata does not leak into abstract legality. -/
theorem sequential_deleted_anchor_rejected :
    ¬ listLegal [anchorBirth, anchorDelete, afterAnchor] := by
  intro h
  have hg := h.2.2 [anchorBirth, anchorDelete] afterAnchor [] rfl
  change 1 = 0 ∨ (∃ b ∈ [anchorBirth, anchorDelete], mIsIns b = true ∧ b.ts = 1) ∧
    (∀ d ∈ [anchorBirth, anchorDelete], d.op ≠ .del 1) at hg
  rcases hg with hz | ⟨_, hd⟩
  · omega
  · exact hd anchorDelete (by simp) rfl

theorem duplicate_deletion_legal :
    listLegal [anchorBirth, anchorDelete, repeatedDelete] := by
  apply staged_legal (L := [anchorBirth]) (D := [anchorDelete, repeatedDelete])
  · decide
  · simp [anchorBirth, anchorDelete, repeatedDelete]
  · simp [anchorBirth, mIsIns]
  · simp [anchorDelete, repeatedDelete, mIsIns]
  · intro pre g post heq p sd hop
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      have hg : g = anchorBirth := heq.1.symm
      subst g
      have hp : p = 0 := by
        have h := congrArg (fun o => match o with | .ins p _ => p | .del _ => 0) hop.symm
        simpa [anchorBirth] using h
      exact Or.inl hp
    | cons b pre =>
      have hlen := congrArg List.length heq
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      omega
  · intro d hd x hx
    have hdel : d.op = .del 1 := by
      rcases List.mem_cons.mp hd with rfl | hd
      · rfl
      · have heq : d = repeatedDelete := List.mem_singleton.mp hd
        rw [heq]; rfl
    have hx1 : x = 1 := MOp.del.inj (hx.symm.trans hdel)
    exact Or.inr ⟨anchorBirth, by simp, rfl, hx1.symm⟩

theorem duplicate_deletion_read :
    listRun [anchorBirth, anchorDelete, repeatedDelete] = [(0, 0)] := by decide

open Plausible
def campaign (seed : Nat) : IO Unit := do
  match ← Testable.checkIO (NamedBinder "choices" (∀ choices : List Nat, check choices = true))
      { numInst := 500, maxSize := 10, randomSeed := some seed } with
  | .success _ => IO.println s!"FugueMax list witness seed={seed}: 500 passed; no gaveUp"
  | .gaveUp n => throw (IO.userError s!"FugueMax list witness gaveUp {n}")
  | .failure _ values shrinks =>
      throw (IO.userError s!"FugueMax list witness failure {values}; shrinks={shrinks}")

#eval campaign 1
#eval campaign 37
#eval campaign 2026
#eval do
  let cases := IssuerSPOT.words 6
  if cases.all check then IO.println s!"FugueMax list witness exhaustive forks: {cases.length} passed"
  else throw (IO.userError "FugueMax list witness exhaustive forks failed")

end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.SequentialSPOT
