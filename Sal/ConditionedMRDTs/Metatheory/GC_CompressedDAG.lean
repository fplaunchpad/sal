import Sal.ConditionedMRDTs.Metatheory.GC_Safety

/-!
# Root-free compressed commit DAG

This file isolates the graph theorem that the payload-only `gc_safety` proof
could not state: after choosing a retained set, discard every other vertex and
replace the old parent skeleton by reachability edges between retained
vertices.  The result stores no root unless the root is itself retained and no
identifier outside the retained set.

The graph representation deliberately uses a relation rather than a
`Version → List Version`: finiteness/enumeration is an implementation concern.
`compressedEdge` is the transitive reduction's safe (possibly redundant)
specification; an implementation may remove redundant edges without changing
its closure.
-/

namespace Sal.ConditionedMRDTs

open Classical

section Compression

variable (parents : Version → List Version) (Keep : Set Version)

/-- A retained edge summarizes an arbitrary nonempty-or-reflexive old path.
Both endpoints must be retained, so the compressed skeleton mentions no
dropped version. -/
def compressedEdge (a b : Version) : Prop :=
  a ∈ Keep ∧ b ∈ Keep ∧ Reaches parents a b

/-- Reachability in the root-free compressed graph. -/
def CompressedReaches (a b : Version) : Prop :=
  Relation.ReflTransGen (compressedEdge parents Keep) a b

theorem compressedReaches_sound {a b : Version}
    (h : CompressedReaches parents Keep a b) : Reaches parents a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hedge ih => exact ih.trans hedge.2.2

theorem compressedReaches_complete {a b : Version}
    (ha : a ∈ Keep) (hb : b ∈ Keep) (h : Reaches parents a b) :
    CompressedReaches parents Keep a b :=
  Relation.ReflTransGen.single ⟨ha, hb, h⟩

theorem compressedReaches_left {a b : Version} (hb : b ∈ Keep)
    (h : CompressedReaches parents Keep a b) : a ∈ Keep := by
  induction h with
  | refl => exact hb
  | tail _ hedge ih => exact ih hedge.1

/-- Exact retained-node reachability preservation. -/
theorem compressedReaches_iff {a b : Version} (ha : a ∈ Keep) (hb : b ∈ Keep) :
    CompressedReaches parents Keep a b ↔ Reaches parents a b :=
  ⟨compressedReaches_sound parents Keep,
   compressedReaches_complete parents Keep ha hb⟩

/-- Relational LCA predicate, identical to `IsLCA` except that it accepts an
arbitrary reachability relation. -/
def IsLCARel (R : Version → Version → Prop) (v₁ v₂ vT : Version) : Prop :=
  R vT v₁ ∧ R vT v₂ ∧ ∀ w, R w v₁ → R w v₂ → R w vT

/-- LCA inside the retained induced order.  Dropped ancestors are deliberately
outside the quantified carrier; this is the runtime query after collection. -/
def IsLCARetained (v₁ v₂ vT : Version) : Prop :=
  v₁ ∈ Keep ∧ v₂ ∈ Keep ∧ vT ∈ Keep ∧
  Reaches parents vT v₁ ∧ Reaches parents vT v₂ ∧
  ∀ w, w ∈ Keep → Reaches parents w v₁ → Reaches parents w v₂ →
    Reaches parents w vT

/-- No closure premise is needed for the exact induced-order statement: LCAs
*among retained versions* are invariant under compression. -/
theorem compressed_isLCARetained_iff {v₁ v₂ vT : Version}
    (h₁ : v₁ ∈ Keep) (h₂ : v₂ ∈ Keep) (hT : vT ∈ Keep) :
    IsLCARel (CompressedReaches parents Keep) v₁ v₂ vT ↔
      IsLCARetained parents Keep v₁ v₂ vT := by
  constructor
  · rintro ⟨hT1, hT2, hmax⟩
    refine ⟨h₁, h₂, hT, compressedReaches_sound parents Keep hT1,
      compressedReaches_sound parents Keep hT2, ?_⟩
    intro w hwK hw1 hw2
    exact compressedReaches_sound parents Keep
      (hmax w (compressedReaches_complete parents Keep hwK h₁ hw1)
        (compressedReaches_complete parents Keep hwK h₂ hw2))
  · rintro ⟨_, _, _, hT1, hT2, hmax⟩
    refine ⟨compressedReaches_complete parents Keep hT h₁ hT1,
      compressedReaches_complete parents Keep hT h₂ hT2, ?_⟩
    intro w hw1 hw2
    have hwK := compressedReaches_left parents Keep h₁ hw1
    exact compressedReaches_complete parents Keep hwK hT
      (hmax w hwK (compressedReaches_sound parents Keep hw1)
        (compressedReaches_sound parents Keep hw2))

theorem isLCARel_reaches_iff_isLCA (v₁ v₂ vT : Version) :
    IsLCARel (Reaches parents) v₁ v₂ vT ↔ IsLCA parents v₁ v₂ vT := Iff.rfl

/-- LCAs are exactly preserved when all quantified common ancestors are in
the retained set.  This is the precise closure obligation required of a GC
keep set; it is satisfied by the MCA-closed production keep set. -/
theorem compressed_isLCA_iff {v₁ v₂ vT : Version}
    (h₁ : v₁ ∈ Keep) (h₂ : v₂ ∈ Keep) (hT : vT ∈ Keep)
    (hCommon : ∀ w, Reaches parents w v₁ → Reaches parents w v₂ → w ∈ Keep) :
    IsLCARel (CompressedReaches parents Keep) v₁ v₂ vT ↔
      IsLCA parents v₁ v₂ vT := by
  constructor
  · rintro ⟨hT1, hT2, hmax⟩
    refine ⟨compressedReaches_sound parents Keep hT1,
      compressedReaches_sound parents Keep hT2, ?_⟩
    intro w hw1 hw2
    have hwK := hCommon w hw1 hw2
    exact compressedReaches_sound parents Keep
      (hmax w (compressedReaches_complete parents Keep hwK h₁ hw1)
        (compressedReaches_complete parents Keep hwK h₂ hw2))
  · rintro ⟨hT1, hT2, hmax⟩
    refine ⟨compressedReaches_complete parents Keep hT h₁ hT1,
      compressedReaches_complete parents Keep hT h₂ hT2, ?_⟩
    intro w hw1 hw2
    have ow1 := compressedReaches_sound parents Keep hw1
    have ow2 := compressedReaches_sound parents Keep hw2
    have hwK := hCommon w ow1 ow2
    exact compressedReaches_complete parents Keep hwK hT (hmax w ow1 ow2)

/-- The compressed skeleton has retained support only. -/
theorem compressedEdge_support {a b : Version}
    (h : compressedEdge parents Keep a b) : a ∈ Keep ∧ b ∈ Keep := ⟨h.1, h.2.1⟩

/-- Root retention is not built into compression. -/
theorem root_absent_when_dropped (h0 : (0 : Version) ∉ Keep) :
    ¬ ∃ b, compressedEdge parents Keep 0 b := by
  rintro ⟨b, h⟩
  exact h0 h.1

end Compression

section Lift

variable {D : ConditionedMRDTSig}

/-- The trace/read component inherited from the existing payload theorem. -/
def PayloadTraceSafe (C₀ : Configuration D)
    (hStore : StoreInv C₀.ver C₀.parents) : Prop :=
  ∀ {ℓs : List (Label3 D)} {C : Configuration D},
    (hRun : Steps D C₀ ℓs C) →
    Steps D (pruneKeep C₀ hStore) ℓs
      (dropVer C (droppedSet C₀) (zero_not_dropped C₀)
        (heads_kept (gcInv_steps hRun (gcInv_init C₀ hStore)))) ∧
    ∀ r, (dropVer C (droppedSet C₀) (zero_not_dropped C₀)
      (heads_kept (gcInv_steps hRun (gcInv_init C₀ hStore)))).N r = C.N r

theorem payloadTraceSafe (C₀ : Configuration D)
    (hStore : StoreInv C₀.ver C₀.parents) : PayloadTraceSafe C₀ hStore :=
  fun hRun => gc_safety C₀ hStore hRun

/-- Lift of `gc_safety` to the compressed representation: the old theorem
supplies label/read preservation, while the new representation theorem supplies
root-free retained reachability and retained-order LCA preservation. -/
theorem gc_safety_compressed (C₀ : Configuration D)
    (hStore : StoreInv C₀.ver C₀.parents) (Keep : Set Version) :
    PayloadTraceSafe C₀ hStore ∧
    (∀ a ∈ Keep, ∀ b ∈ Keep,
      CompressedReaches C₀.parents Keep a b ↔ Reaches C₀.parents a b) ∧
    (∀ v₁ ∈ Keep, ∀ v₂ ∈ Keep, ∀ vT ∈ Keep,
      IsLCARel (CompressedReaches C₀.parents Keep) v₁ v₂ vT ↔
        IsLCARetained C₀.parents Keep v₁ v₂ vT) := by
  refine ⟨payloadTraceSafe C₀ hStore, ?_, ?_⟩
  · intro a ha b hb
    exact compressedReaches_iff C₀.parents Keep ha hb
  · intro v₁ h₁ v₂ h₂ vT hT
    exact compressed_isLCARetained_iff C₀.parents Keep h₁ h₂ hT

end Lift

/-! ## Controls -/

namespace CompressedGCSpot

def chainParents : Version → List Version
  | 1 => [0]
  | 2 => [1]
  | 3 => [2]
  | _ => []

def retained : Set Version := {2, 3}

/-- PASS: the root and dropped interior `1` are absent, but retained ancestry
is preserved by the summarized edge. -/
example : (0 : Version) ∉ retained ∧ (1 : Version) ∉ retained ∧
    CompressedReaches chainParents retained 2 3 := by
  refine ⟨by simp [retained], by simp [retained], ?_⟩
  apply compressedReaches_complete
  · simp [retained]
  · simp [retained]
  · apply Relation.ReflTransGen.single
    simp [chainParents]

/-- FAIL control: compression does not manufacture reverse ancestry. -/
example : ¬ CompressedReaches chainParents retained 3 2 := by
  intro h
  have old := compressedReaches_sound chainParents retained h
  have le := reaches_le (parents := chainParents) (by
    intro v p hp
    cases v with
    | zero => simp [chainParents] at hp
    | succ v =>
      cases v with
      | zero => simpa [chainParents] using hp
      | succ v =>
        cases v with
        | zero =>
          have : p = 1 := by simpa [chainParents] using hp
          subst p
          decide
        | succ v =>
          cases v with
          | zero =>
            have : p = 2 := by simpa [chainParents] using hp
            subst p
            decide
          | succ v => simp [chainParents] at hp) old
  exact (by omega : ¬ (3 : Nat) ≤ 2) le

end CompressedGCSpot

end Sal.ConditionedMRDTs

#print axioms Sal.ConditionedMRDTs.compressed_isLCA_iff
#print axioms Sal.ConditionedMRDTs.gc_safety_compressed
