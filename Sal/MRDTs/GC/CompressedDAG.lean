import Sal.MRDTs.Metatheory.StoreInvariant

/-! # Root-free compressed commit DAG -/

namespace Sal.MRDTs.GC

open Classical Sal.MRDTs


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

/-- Relational GCA predicate, identical to `IsGCA` except that it accepts an
arbitrary reachability relation. -/
def IsGCARel (R : Version → Version → Prop) (v₁ v₂ vT : Version) : Prop :=
  R vT v₁ ∧ R vT v₂ ∧ ∀ w, R w v₁ → R w v₂ → R w vT

/-- GCA inside the retained induced order. Dropped ancestors are deliberately
outside the quantified carrier; this is the runtime query after collection. -/
def IsGCARetained (v₁ v₂ vT : Version) : Prop :=
  v₁ ∈ Keep ∧ v₂ ∈ Keep ∧ vT ∈ Keep ∧
  Reaches parents vT v₁ ∧ Reaches parents vT v₂ ∧
  ∀ w, w ∈ Keep → Reaches parents w v₁ → Reaches parents w v₂ →
    Reaches parents w vT

/-- No closure premise is needed for the exact induced-order statement: GCAs
*among retained versions* are invariant under compression. -/
theorem compressed_isGCARetained_iff {v₁ v₂ vT : Version}
    (h₁ : v₁ ∈ Keep) (h₂ : v₂ ∈ Keep) (hT : vT ∈ Keep) :
    IsGCARel (CompressedReaches parents Keep) v₁ v₂ vT ↔
      IsGCARetained parents Keep v₁ v₂ vT := by
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

theorem isGCARel_reaches_iff_isGCA (v₁ v₂ vT : Version) :
    IsGCARel (Reaches parents) v₁ v₂ vT ↔ IsGCA parents v₁ v₂ vT := Iff.rfl

/-- GCAs are exactly preserved when all quantified common ancestors are in
the retained set.  This is the precise closure obligation required of a GC
keep set; it is satisfied by closing the production keep set under pairwise
maximal common ancestors. -/
theorem compressed_isGCA_iff {v₁ v₂ vT : Version}
    (h₁ : v₁ ∈ Keep) (h₂ : v₂ ∈ Keep) (hT : vT ∈ Keep)
    (hCommon : ∀ w, Reaches parents w v₁ → Reaches parents w v₂ → w ∈ Keep) :
    IsGCARel (CompressedReaches parents Keep) v₁ v₂ vT ↔
      IsGCA parents v₁ v₂ vT := by
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

/-- Exact GCA preservation needs only closure under maximal common ancestors,
not retention of every common ancestor. This is the root-free condition used
by commit GC: a dropped path can be summarized, while every possible merge
base remains in the carrier. -/
theorem compressed_isGCA_iff_of_maximalCommonAncestorClosed
    {v₁ v₂ vT : Version}
    (hlt : ∀ v p, p ∈ parents v → p < v)
    (h₁ : v₁ ∈ Keep) (h₂ : v₂ ∈ Keep) (hT : vT ∈ Keep)
    (hMaximal : ∀ a ∈ Keep, ∀ b ∈ Keep, ∀ m,
      IsMaximalCommonAncestor parents a b m → m ∈ Keep) :
    IsGCARel (CompressedReaches parents Keep) v₁ v₂ vT ↔
      IsGCA parents v₁ v₂ vT := by
  constructor
  · rintro ⟨hT1, hT2, hmax⟩
    refine ⟨compressedReaches_sound parents Keep hT1,
      compressedReaches_sound parents Keep hT2, ?_⟩
    intro w hw1 hw2
    obtain ⟨m, hm, hwm⟩ := commonAncestor_reaches_maximal hlt
      (a := v₁) (b := v₂) (x := w) ⟨hw1, hw2⟩
    have hmK : m ∈ Keep := hMaximal v₁ h₁ v₂ h₂ m hm
    have hm1 : Reaches parents m v₁ := hm.1.1
    have hm2 : Reaches parents m v₂ := hm.1.2
    have hmT : Reaches parents m vT :=
      compressedReaches_sound parents Keep
        (hmax m
          (compressedReaches_complete parents Keep hmK h₁ hm1)
          (compressedReaches_complete parents Keep hmK h₂ hm2))
    exact hwm.trans hmT
  · rintro ⟨hT1, hT2, hmax⟩
    refine ⟨compressedReaches_complete parents Keep hT h₁ hT1,
      compressedReaches_complete parents Keep hT h₂ hT2, ?_⟩
    intro w hw1 hw2
    exact compressedReaches_complete parents Keep
      (compressedReaches_left parents Keep h₁ hw1) hT
      (hmax w (compressedReaches_sound parents Keep hw1)
        (compressedReaches_sound parents Keep hw2))

/-- The compressed skeleton has retained support only. -/
theorem compressedEdge_support {a b : Version}
    (h : compressedEdge parents Keep a b) : a ∈ Keep ∧ b ∈ Keep := ⟨h.1, h.2.1⟩

/-- Root retention is not built into compression. -/
theorem root_absent_when_dropped (h0 : (0 : Version) ∉ Keep) :
    ¬ ∃ b, compressedEdge parents Keep 0 b := by
  rintro ⟨b, h⟩
  exact h0 h.1

end Compression


end Sal.MRDTs.GC
