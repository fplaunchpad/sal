import Mathlib.Data.List.Basic

/-! The pinned source's finite search-label chunk codec. Codes are offsets from
UTF-16 code unit 61. This file concerns canonical generated labels, not arbitrary
valid-character strings or JavaScript decoding. -/
namespace Sal.MRDTs.Instances.NotionCoreSearchLabels

/-- The source's six-bit node has at most five trailing one bits (31 is invalid). -/
def trailingOnes (node : Nat) : Nat :=
  if node % 2 = 0 then 0 else
  if node % 4 = 1 then 1 else
  if node % 8 = 3 then 2 else
  if node % 16 = 7 then 3 else
  if node % 32 = 15 then 4 else 5

/-- `false` is L and `true` is R, in the literal printableSearchLabel bit order. -/
def chunkPath (node : Nat) : List Bool :=
  ([5,4,3,2,1,0].filter (fun bit => trailingOnes node < bit)).map
    (fun bit => node / 2^bit % 2 = 1)

def valid (node : Nat) : Prop := node ≤ 62 ∧ node ≠ 31
instance (node : Nat) : Decidable (valid node) := inferInstanceAs (Decidable (_ ∧ _))

def children (node : Nat) : Nat × Nat :=
  let delta := 2^(trailingOnes node - 1)
  (node-delta,node+delta)

/-- All odd valid chunks split to valid chunks representing exactly one further
binary edge. The finite proof checks every source-admitted chunk, not examples. -/
theorem odd_chunk_split : ∀ node : Fin 63, valid node.val → node.val % 2 = 1 →
    valid (children node.val).1 ∧ valid (children node.val).2 ∧
    chunkPath (children node.val).1 = chunkPath node.val ++ [false] ∧
    chunkPath (children node.val).2 = chunkPath node.val ++ [true] := by
  decide

/-- An even final chunk is full, so source split appends the one-edge chunk. -/
theorem appended_chunks : chunkPath 15 = [false] ∧ chunkPath 47 = [true] ∧
    valid 15 ∧ valid 47 := by decide

/-- PASS+FAIL: depth-five left path is '=' (offset zero), and the next split
appends 'L' (offset15); a valid noncanonical string can alias a printable path. -/
theorem codec_control : chunkPath 0 = [false,false,false,false,false] ∧
    chunkPath 15 ++ chunkPath 15 = chunkPath 7 ∧
    ([15,15] : List Nat) ≠ [7] ∧ chunkPath 0 ≠ [false] := by decide

/-- Lift the actual last-chunk source branch to an arbitrary existing prefix.
No canonicality of that prefix is assumed or claimed. -/
def printable (label : List Nat) : List Bool := label.flatMap chunkPath

theorem split_last_chunk (head : List Nat) (node : Fin 63)
    (admitted : valid node.val) (odd : node.val % 2 = 1) :
    printable (head ++ [(children node.val).1]) =
      printable (head ++ [node.val]) ++ [false] ∧
    printable (head ++ [(children node.val).2]) =
      printable (head ++ [node.val]) ++ [true] := by
  obtain ⟨_,_,left,right⟩ := odd_chunk_split node admitted odd
  simp [printable,left,right,List.append_assoc]

theorem append_full_chunk (label : List Nat) :
    printable (label ++ [15]) = printable label ++ [false] ∧
    printable (label ++ [47]) = printable label ++ [true] := by
  have left := appended_chunks.1
  have right := appended_chunks.2.1
  simp [printable,left,right]

theorem chunk_bounds : ∀ n : Fin 63, valid n.val →
    0 < (chunkPath n.val).length ∧ (chunkPath n.val).length ≤ 5 := by decide

theorem chunk_injective : ∀ a b : Fin 63, valid a.val → valid b.val →
    chunkPath a.val = chunkPath b.val → a = b := by decide

theorem even_full : ∀ n : Fin 63, valid n.val → n.val % 2 = 0 →
    (chunkPath n.val).length = 5 := by decide

/-- Every nonfinal chunk is full; the final chunk has one to five edges. -/
inductive Canonical : List Nat → Prop
  | nil : Canonical []
  | one (n : Fin 63) (h : valid n.val) : Canonical [n.val]
  | cons (n : Fin 63) (h : valid n.val) (full : n.val % 2 = 0)
      (tail : List Nat) (nonempty : tail ≠ []) (rest : Canonical tail) :
      Canonical (n.val :: tail)

private theorem printable_positive {xs : List Nat} (h : Canonical xs) (ne : xs ≠ []) :
    0 < (printable xs).length := by
  cases h with
  | nil => contradiction
  | one n h => simpa [printable] using (chunk_bounds n h).1
  | cons n h full tail nonempty rest =>
    simp only [printable,List.flatMap_cons,List.length_append]
    have := (chunk_bounds n h).1
    omega

private theorem head_equal (a b : List Bool) (xs ys : List Bool)
    (ha : a.length = 5) (hb : b.length = 5)
    (eq : a ++ xs = b ++ ys) : a = b := by
  have taken := congrArg (List.take 5) eq
  have left : (a ++ xs).take 5 = a := by rw [←ha]; simp
  have right : (b ++ ys).take 5 = b := by rw [←hb]; simp
  simpa only [left,right] using taken

theorem canonical_injective {xs ys : List Nat} (hx : Canonical xs) (hy : Canonical ys)
    (eq : printable xs = printable ys) : xs = ys := by
  induction hx generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons n ns =>
      have pos := printable_positive hy (by simp)
      have len : (printable (n :: ns)).length = 0 := by
        simpa only [printable,List.flatMap_nil,List.length_nil] using congrArg List.length eq.symm
      omega
  | one a ha =>
    cases hy with
    | nil =>
      have pos := (chunk_bounds a ha).1
      have len := congrArg List.length eq
      simp only [printable,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_nil] at len
      omega
    | one b hb =>
      have ce : chunkPath a.val = chunkPath b.val := by simpa [printable] using eq
      have same := chunk_injective a b ha hb ce
      simp [same]
    | cons b hb full tail nonempty rest =>
      have pos := printable_positive rest nonempty
      have len := congrArg List.length eq
      simp only [printable,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append] at len
      rw [even_full b hb full] at len
      have bound := (chunk_bounds a ha).2
      change 0 < (tail.flatMap chunkPath).length at pos
      omega
  | cons a ha full tail nonempty rest ih =>
    cases hy with
    | nil =>
      have pos := printable_positive (Canonical.cons a ha full tail nonempty rest) (by simp)
      rw [eq] at pos
      simp [printable] at pos
    | one b hb =>
      have pos := printable_positive rest nonempty
      have len := congrArg List.length eq
      simp only [printable,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append] at len
      rw [even_full a ha full] at len
      have bound := (chunk_bounds b hb).2
      change 0 < (tail.flatMap chunkPath).length at pos
      omega
    | cons b hb bfull other otherne othercanon =>
      have raw : chunkPath a.val ++ printable tail = chunkPath b.val ++ printable other := eq
      have ce := head_equal _ _ _ _ (even_full a ha full) (even_full b hb bfull) raw
      have same := chunk_injective a b ha hb ce
      have tails : printable tail = printable other := by
        rw [ce] at raw
        exact List.append_cancel_left raw
      exact congrArg₂ List.cons (congrArg Fin.val same) (ih othercanon tails)

/-- Literal source last-chunk split, expressed recursively rather than with
JavaScript string slicing. UTF-16 offset conversion is external. -/
def splitLabel : List Nat → List Nat × List Nat
  | [] => ([15],[47])
  | n :: tail =>
      if tail = [] then
        if n % 2 = 1 then ([(children n).1],[(children n).2])
        else ([n,15],[n,47])
      else let pair := splitLabel tail
           (n :: pair.1,n :: pair.2)

theorem canonical_split {label : List Nat} (h : Canonical label) :
    Canonical (splitLabel label).1 ∧ Canonical (splitLabel label).2 ∧
    (splitLabel label).1 ≠ [] ∧ (splitLabel label).2 ≠ [] ∧
    printable (splitLabel label).1 = printable label ++ [false] ∧
    printable (splitLabel label).2 = printable label ++ [true] := by
  induction h with
  | nil =>
    refine ⟨Canonical.one ⟨15,by omega⟩ appended_chunks.2.2.1,
      Canonical.one ⟨47,by omega⟩ appended_chunks.2.2.2,by simp [splitLabel],by simp [splitLabel],?_,?_⟩ <;>
      simp [splitLabel,printable,appended_chunks.1,appended_chunks.2.1]
  | one n hn =>
    by_cases odd : n.val % 2 = 1
    · obtain ⟨lv,rv,lp,rp⟩ := odd_chunk_split n hn odd
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · simpa [splitLabel,odd] using Canonical.one ⟨(children n.val).1,by have := lv.1; omega⟩ lv
      · simpa [splitLabel,odd] using Canonical.one ⟨(children n.val).2,by have := rv.1; omega⟩ rv
      · simp [splitLabel,odd]
      · simp [splitLabel,odd]
      · simpa [splitLabel,odd,printable] using lp
      · simpa [splitLabel,odd,printable] using rp
    · have even : n.val % 2 = 0 := by omega
      refine ⟨?_,?_,by simp [splitLabel,odd],by simp [splitLabel,odd],?_,?_⟩
      · simpa [splitLabel,odd] using Canonical.cons n hn even [15] (by simp)
          (Canonical.one ⟨15,by omega⟩ appended_chunks.2.2.1)
      · simpa [splitLabel,odd] using Canonical.cons n hn even [47] (by simp)
          (Canonical.one ⟨47,by omega⟩ appended_chunks.2.2.2)
      · simp [splitLabel,odd,printable,appended_chunks.1]
      · simp [splitLabel,odd,printable,appended_chunks.2.1]
  | cons n hn full tail nonempty rest ih =>
    obtain ⟨left,right,ln,rn,lp,rp⟩ := ih
    refine ⟨?_,?_,by simp [splitLabel,nonempty],by simp [splitLabel,nonempty],?_,?_⟩
    · simpa [splitLabel,nonempty] using Canonical.cons n hn full _ ln left
    · simpa [splitLabel,nonempty] using Canonical.cons n hn full _ rn right
    · simp only [splitLabel,if_neg nonempty,printable,List.flatMap_cons]
      change chunkPath n.val ++ printable (splitLabel tail).1 = _
      rw [lp]
      simp [printable,List.append_assoc]
    · simp only [splitLabel,if_neg nonempty,printable,List.flatMap_cons]
      change chunkPath n.val ++ printable (splitLabel tail).2 = _
      rw [rp]
      simp [printable,List.append_assoc]

def Separated (a b : List Bool) : Prop := ¬ a <+: b ∧ ¬ b <+: a

theorem separated_extend {a b : List Bool} (h : Separated a b) (bit : Bool) :
    Separated a (b ++ [bit]) := by
  constructor
  · intro pref
    rcases List.prefix_or_prefix_of_prefix pref (List.prefix_append b [bit]) with before | after
    · exact h.1 before
    · exact h.2 after
  · intro pref
    exact h.2 ((List.prefix_append b [bit]).trans pref)

theorem siblings_separated (p : List Bool) : Separated (p ++ [false]) (p ++ [true]) := by
  simp [Separated,List.prefix_append_right_inj]

/-- The exact frontier operation: remove the selected leaf and add both children. -/
def refine (frontier : Set (List Bool)) (p : List Bool) : Set (List Bool) :=
  {a | (a ∈ frontier ∧ a ≠ p) ∨ a = p ++ [false] ∨ a = p ++ [true]}

def PrefixFree (frontier : Set (List Bool)) : Prop :=
  ∀ a ∈ frontier, ∀ b ∈ frontier, a ≠ b → Separated a b

theorem refine_prefixFree {frontier : Set (List Bool)} (free : PrefixFree frontier)
    {p : List Bool} (selected : p ∈ frontier) : PrefixFree (refine frontier p) := by
  intro a ha b hb distinct
  rcases ha with ⟨ha,an⟩ | rfl | rfl <;> rcases hb with ⟨hb,bn⟩ | rfl | rfl
  · exact free a ha b hb distinct
  · exact separated_extend (free a ha p selected an) false
  · exact separated_extend (free a ha p selected an) true
  · exact (separated_extend (free b hb p selected bn) false).symm
  · exact False.elim (distinct rfl)
  · exact siblings_separated p
  · exact (separated_extend (free b hb p selected bn) true).symm
  · exact (siblings_separated p).symm
  · exact False.elim (distinct rfl)

def LabelFrontier (frontier : Set (List Nat)) : Prop :=
  (∀ label ∈ frontier, Canonical label) ∧
  (∀ a ∈ frontier, ∀ b ∈ frontier, a ≠ b → Separated (printable a) (printable b))

def splitFrontier (frontier : Set (List Nat)) (selected : List Nat) : Set (List Nat) :=
  {a | (a ∈ frontier ∧ a ≠ selected) ∨ a = (splitLabel selected).1 ∨ a = (splitLabel selected).2}

theorem split_frontier_preserves {frontier : Set (List Nat)} (good : LabelFrontier frontier)
    {selected : List Nat} (member : selected ∈ frontier) :
    LabelFrontier (splitFrontier frontier selected) := by
  obtain ⟨lc,rc,_,_,lp,rp⟩ := canonical_split (good.1 selected member)
  constructor
  · intro a ha
    rcases ha with ⟨ha,_⟩ | rfl | rfl
    · exact good.1 a ha
    · exact lc
    · exact rc
  · intro a ha b hb distinct
    rcases ha with ⟨ha,an⟩ | rfl | rfl <;> rcases hb with ⟨hb,bn⟩ | rfl | rfl
    · exact good.2 a ha b hb distinct
    · rw [lp]; exact separated_extend (good.2 a ha selected member an) false
    · rw [rp]; exact separated_extend (good.2 a ha selected member an) true
    · rw [lp]; exact (separated_extend (good.2 b hb selected member bn) false).symm
    · exact False.elim (distinct rfl)
    · rw [lp,rp]; exact siblings_separated _
    · rw [rp]; exact (separated_extend (good.2 b hb selected member bn) true).symm
    · rw [lp,rp]; exact (siblings_separated _).symm
    · exact False.elim (distinct rfl)

/-- Repeated source-shaped label splits starting from the initial root. Selection
requires only an existing leaf, never the desired resulting invariant. -/
inductive Reach : Set (List Nat) → Prop
  | initial : Reach {[]}
  | split {frontier selected} : Reach frontier → selected ∈ frontier →
      Reach (splitFrontier frontier selected)

theorem reachable_frontier {frontier} (reachable : Reach frontier) : LabelFrontier frontier := by
  induction reachable with
  | initial =>
    constructor
    · intro label member
      have equal : label = [] := member
      subst label
      exact Canonical.nil
    · intro a ha b hb distinct
      have ae : a = [] := ha
      have be : b = [] := hb
      exact False.elim (distinct (ae.trans be.symm))
  | split before member ih => exact split_frontier_preserves ih member

/-- PASS+FAIL: five L steps fill '=', and splitting it appends L/R; repeated
splitting keeps the untouched right leaf, rather than collapsing the frontier. -/
theorem frontier_control : splitLabel [0] = ([0,15],[0,47]) ∧
    splitLabel [15] = ([7],[23]) ∧
    splitLabel [0] ≠ ([0],[47]) ∧
    ¬ Canonical [15,15] := by
  refine ⟨by decide,by decide,by decide,?_⟩
  intro h
  have equal := canonical_injective h (Canonical.one ⟨7,by omega⟩ (by decide))
    (by decide : printable [15,15] = printable [7])
  simp at equal

#print axioms canonical_injective
#print axioms canonical_split
#print axioms reachable_frontier
end Sal.MRDTs.Instances.NotionCoreSearchLabels
