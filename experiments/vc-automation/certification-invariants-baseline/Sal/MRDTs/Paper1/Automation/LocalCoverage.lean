import Sal.MRDTs.Paper1.ConcreteJoin
import Sal.MRDTs.Framework.Base.FiniteOrder

/-! Scope-sensitive order facts for coverage of the strengthened local equation
`∀ t, merge l (merge B t (update B e)) b = merge B (merge l t b) (update B e)`.
These facts preserve history scopes; they do not supply an invariant or assume
Join/any merge VC. `nested_enumeration` constructs compatible replays for the
nested pair required by the strengthened local equation. -/
namespace Sal.MRDTs.Paper1.LocalCoverage
open Foundation ConcreteMRDT Classical
variable {D : UpdateSig} (P : OperationPolicy D.AppOp)
    (C : ReplayContext D)

/-- Enlarging a scope only removes policy edges. This is one-way reflection,
not the false assertion that every scope has the same ordering relation. -/
theorem order_reflects (L O : Set (Op D.AppOp)) (subset : L ⊆ O)
    (a b : Op D.AppOp) (edge : paperOrder P C O a b) : paperOrder P C L a b := by
  rcases edge with causal | ⟨ab,ba,policy,noAbsorber⟩
  · exact Or.inl causal
  · refine Or.inr ⟨ab,ba,policy,?_⟩
    rintro ⟨c,member,vis,noncomm⟩
    exact noAbsorber ⟨c,subset member,vis,noncomm⟩

/-- A policy edge's target has no outgoing edge within the same scope.
The chain premise is the exact local use of guarded policy no-chain. -/
theorem policy_target_sink (O : Set (Op D.AppOp)) (a b : Op D.AppOp)
    (policy : P.before a.op b.op)
    (unabsorbed : ¬ ∃ c ∈ O, C.vis b c ∧ ¬ D.commutes b c)
    (noChain : ∀ c ∈ O, c ≠ b → ¬ (P.before a.op b.op ∧ P.before b.op c.op)) :
    ∀ c ∈ O, c ≠ b → ¬ paperOrder P C O b c := by
  intro c member ne edge
  rcases edge with ⟨vis,noncomm⟩ | ⟨_,_,next,_⟩
  · exact unabsorbed ⟨c,member,vis,noncomm⟩
  · exact noChain c member ne ⟨policy,next⟩

/-- Metadata closure prevents a causal noncommutation path from leaving a
smaller history and later returning to it. This path fact is implementation
independent and does not mention a concrete state. -/
theorem noncomm_path_closed (before : Op D.AppOp → Op D.AppOp → Prop)
    (L : Set (Op D.AppOp)) (closed : ∀ a b, before a b → b ∈ L → a ∈ L)
    (covers : ∀ a b, C.vis a b → ¬ D.commutes a b → before a b)
    {a b : Op D.AppOp}
    (path : Relation.TransGen (fun x y => C.vis x y ∧ ¬ D.commutes x y) a b)
    (member : b ∈ L) : a ∈ L := by
  induction path with
  | single edge => exact closed _ _ (covers _ _ edge.1 edge.2) member
  | tail path edge ih =>
      exact ih (closed _ _ (covers _ _ edge.1 edge.2) member)

/-- A revived policy edge in L cannot be followed by a nonempty causal
noncommutation path ending back in L. This rules out the return segment that
made the incomparable-scope four-event cycle possible. -/
theorem revived_target_no_return (before : Op D.AppOp → Op D.AppOp → Prop)
    (L : Set (Op D.AppOp)) (closed : ∀ a b, before a b → b ∈ L → a ∈ L)
    (covers : ∀ a b, C.vis a b → ¬ D.commutes a b → before a b)
    (b : Op D.AppOp)
    (unabsorbed : ¬ ∃ c ∈ L, C.vis b c ∧ ¬ D.commutes b c) :
    ∀ c ∈ L, ¬ Relation.TransGen (fun x y => C.vis x y ∧ ¬ D.commutes x y) b c := by
  intro c member path
  induction path with
  | single edge => exact unabsorbed ⟨_,member,edge⟩
  | tail path edge ih =>
      exact ih (closed _ _ (covers _ _ edge.1 edge.2) member)

section Graph
variable {β : Type}

def Acyclic (R : β → β → Prop) : Prop := ∀ a, ¬ Relation.TransGen R a a

private theorem no_path_from_sink {R : β → β → Prop} {a b : β}
    (sink : ∀ c, ¬ R a c) (path : Relation.TransGen R a b) : False := by
  induction path with
  | single edge => exact sink _ edge
  | tail _ _ ih => exact ih

/-- Adding edges whose targets are sinks cannot introduce a directed cycle. -/
theorem add_sink_edges (R S : β → β → Prop) (acyclic : Acyclic R)
    (sink : ∀ a b, S a b → ∀ c, ¬ (R b c ∨ S b c)) :
    Acyclic (fun a b => R a b ∨ S a b) := by
  have classify : ∀ {a b}, Relation.TransGen (fun x y => R x y ∨ S x y) a b →
      Relation.TransGen R a b ∨ ∃ x, S x b := by
    intro a b path
    induction path with
    | single edge =>
      rcases edge with edge | edge
      · exact Or.inl (.single edge)
      · exact Or.inr ⟨_,edge⟩
    | tail path edge ih =>
      rcases ih with core | ⟨x,last⟩
      · rcases edge with edge | edge
        · exact Or.inl (.tail core edge)
        · exact Or.inr ⟨_,edge⟩
      · exact False.elim (sink x _ last _ edge)
  intro a path
  rcases classify path with core | ⟨x,last⟩
  · exact acyclic a core
  · exact no_path_from_sink (sink x a last) path

/-- Generic nested-scope graph principle. Inner policy targets are sinks inside
L; outer policy targets are sinks everywhere. Outside L only causal edges
remain, while backwards closure prevents a cycle from crossing its boundary. -/
theorem nested_graph_acyclic (A X Y : β → β → Prop) (L : Set β)
    (causal : Acyclic A)
    (closed : ∀ a b, A a b → b ∈ L → a ∈ L)
    (inside : ∀ a b, X a b → a ∈ L ∧ b ∈ L)
    (inner_sink : ∀ a b, X a b → ∀ c ∈ L, ¬ (A b c ∨ X b c))
    (outer_sink : ∀ a b, Y a b → ∀ c, ¬ (A b c ∨ X b c ∨ Y b c)) :
    Acyclic (fun a b => (A a b ∨ X a b) ∨ Y a b) := by
  let R := fun a b => A a b ∨ X a b
  have rclosed : ∀ a b, R a b → b ∈ L → a ∈ L := by
    intro a b edge hb
    rcases edge with edge | edge
    · exact closed a b edge hb
    · exact (inside a b edge).1
  have pclosed : ∀ {a b}, Relation.TransGen R a b → b ∈ L → a ∈ L := by
    intro a b path
    induction path with
    | single edge => exact rclosed _ _ edge
    | tail _ edge ih => exact fun hb => ih (rclosed _ _ edge hb)
  have innerA : Acyclic (fun a b => A a b ∧ a ∈ L ∧ b ∈ L) := by
    intro a path
    apply causal a
    exact path.mono (fun _ _ edge => edge.1)
  have innerR := add_sink_edges (fun a b => A a b ∧ a ∈ L ∧ b ∈ L) X innerA
    (by
      intro a b hx c edge
      rcases edge with ⟨edge,_,hc⟩ | edge
      · exact inner_sink a b hx c hc (Or.inl edge)
      · exact inner_sink a b hx c (inside b c edge).2 (Or.inr edge))
  have racyclic : Acyclic R := by
    intro a path
    by_cases ha : a ∈ L
    · apply innerR a
      have restricted : ∀ {x y}, Relation.TransGen R x y → y ∈ L →
          Relation.TransGen (fun u v => (A u v ∧ u ∈ L ∧ v ∈ L) ∨ X u v) x y := by
        intro x y chain
        induction chain with
        | single edge =>
          intro hy
          rcases edge with edge | edge
          · exact .single (Or.inl ⟨edge,closed _ _ edge hy,hy⟩)
          · exact .single (Or.inr edge)
        | tail chain edge ih =>
          intro hy
          have hx := rclosed _ _ edge hy
          rcases edge with edge | edge
          · exact .tail (ih hx) (Or.inl ⟨edge,hx,hy⟩)
          · exact .tail (ih hx) (Or.inr edge)
      exact restricted path ha
    · apply causal a
      have outside : ∀ {x y}, Relation.TransGen R x y → x ∉ L → Relation.TransGen A x y := by
        intro x y chain
        induction chain with
        | single edge =>
          intro hx
          rcases edge with edge | edge
          · exact .single edge
          · exact False.elim (hx (inside _ _ edge).1)
        | tail chain edge ih =>
          intro hx
          have hn : _ ∉ L := fun hy => hx (pclosed chain hy)
          rcases edge with edge | edge
          · exact .tail (ih hx) edge
          · exact False.elim (hn (inside _ _ edge).1)
      exact outside path ha
  exact add_sink_edges R Y racyclic (by
    intro a b edge c out
    rcases out with out | out
    · rcases out with out | out
      · exact outer_sink a b edge c (Or.inl out)
      · exact outer_sink a b edge c (Or.inr (Or.inl out))
    · exact outer_sink a b edge c (Or.inr (Or.inr out)))
end Graph

/-- A simultaneous ordering relation for nested scopes L⊆O. Membership guards
prevent unrelated events from silently entering either side order. -/
def jointOrder (L O : Set (Op D.AppOp)) (a b : Op D.AppOp) : Prop :=
  (a ∈ O ∧ b ∈ O ∧ paperOrder P C O a b) ∨
    (a ∈ L ∧ b ∈ L ∧ paperOrder P C L a b)

/-- Unlike incomparable side histories, a metadata-closed nested pair admits
an acyclic combined order. No equality of scope-dependent verdicts is assumed. -/
theorem nested_order_acyclic (L O : Set (Op D.AppOp)) (subset : L ⊆ O)
    (closed : ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ L → a ∈ L)
    (trans : Transitive C.vis) (irrefl : ∀ a, ¬ C.vis a a)
    (noChain : ∀ a b c : Op D.AppOp, ¬ (P.before a.op b.op ∧ P.before b.op c.op)) :
    Acyclic (jointOrder P C L O) := by
  let A := fun a b => a ∈ O ∧ b ∈ O ∧ C.vis a b ∧ ¬ D.commutes a b
  let X := fun a b => a ∈ L ∧ b ∈ L ∧ ¬ C.vis a b ∧ ¬ C.vis b a ∧
    P.before a.op b.op ∧ ¬ ∃ c ∈ L, C.vis b c ∧ ¬ D.commutes b c
  let Y := fun a b => a ∈ O ∧ b ∈ O ∧ ¬ C.vis a b ∧ ¬ C.vis b a ∧
    P.before a.op b.op ∧ ¬ ∃ c ∈ O, C.vis b c ∧ ¬ D.commutes b c
  have acA : Acyclic A := by
    intro a path
    have vp : Relation.TransGen C.vis a a := path.mono (fun _ _ edge => edge.2.2.1)
    have flatten : ∀ {x y}, Relation.TransGen C.vis x y → C.vis x y := by
      intro x y chain
      induction chain with
      | single h => exact h
      | tail _ h ih => exact trans ih h
    exact irrefl a (flatten vp)
  have ac := nested_graph_acyclic A X Y L acA
    (by intro a b edge hb; exact closed a b edge.2.2.1 edge.2.2.2 hb)
    (by intro a b edge; exact ⟨edge.1,edge.2.1⟩)
    (by
      intro a b edge c hc next
      rcases next with edgeA | edgeX
      · exact edge.2.2.2.2.2 ⟨c,hc,edgeA.2.2.1,edgeA.2.2.2⟩
      · exact noChain a b c ⟨edge.2.2.2.2.1,edgeX.2.2.2.2.1⟩)
    (by
      intro a b edge c next
      rcases next with edgeA | edgeX | edgeY
      · exact edge.2.2.2.2.2 ⟨c,edgeA.2.1,edgeA.2.2.1,edgeA.2.2.2⟩
      · exact noChain a b c ⟨edge.2.2.2.2.1,edgeX.2.2.2.2.1⟩
      · exact noChain a b c ⟨edge.2.2.2.2.1,edgeY.2.2.2.2.1⟩)
  intro a path
  apply ac a
  apply Relation.TransGen.mono ?_ path
  intro x y edge
  rcases edge with ⟨hx,hy,edge⟩ | ⟨hx,hy,edge⟩
  · rcases edge with causal | policy
    · exact Or.inl (Or.inl ⟨hx,hy,causal⟩)
    · exact Or.inr ⟨hx,hy,policy⟩
  · rcases edge with causal | policy
    · exact Or.inl (Or.inl ⟨subset hx,subset hy,causal⟩)
    · exact Or.inl (Or.inr ⟨hx,hy,policy⟩)


/-- A finite common ordering exists for a metadata-closed nested pair. Its
filter is a genuine smaller-scope replay, while the full sequence respects the
outer scope; restored policy edges are retained rather than discarded. -/
theorem nested_enumeration (L O : Set (Op D.AppOp)) (subset : L ⊆ O)
    (closed : ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ L → a ∈ L)
    (trans : Transitive C.vis) (irrefl : ∀ a, ¬ C.vis a a)
    (noChain : ∀ a b c : Op D.AppOp, ¬ (P.before a.op b.op ∧ P.before b.op c.op))
    (π : List (Op D.AppOp)) (perm : listPermOf π O) :
    ∃ σ : List (Op D.AppOp), listPermOf σ O ∧
      respects σ (paperOrder P C O) ∧
      listPermOf (σ.filter (fun x => decide (x ∈ L))) L ∧
      respects (σ.filter (fun x => decide (x ∈ L))) (paperOrder P C L) := by
  classical
  have ac := nested_order_acyclic P C L O subset closed trans irrefl noChain
  obtain ⟨σ,hp,hr⟩ := Sal.MRDTs.exists_respecting_perm
    (R := Relation.TransGen (jointOrder P C L O))
    (fun h1 h2 => h1.trans h2) ac π
  have ps : listPermOf σ O := by
    refine ⟨hp.nodup perm.1,?_⟩
    intro x
    exact hp.mem_iff.symm.trans (perm.2 x)
  have joint : respects σ (jointOrder P C L O) := by
    apply hr.imp
    intro x y no edge
    exact no (.single edge)
  have outer : respects σ (paperOrder P C O) := by
    apply joint.imp_of_mem
    intro x y hx hy no edge
    exact no (Or.inl ⟨(ps.2 y).mp hy,(ps.2 x).mp hx,edge⟩)
  have filtered : listPermOf (σ.filter (fun x => decide (x ∈ L))) L := by
    refine ⟨ps.1.filter _,?_⟩
    intro x
    simp only [List.mem_filter,decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨(ps.2 x).mpr (subset h),h⟩
  have inner : respects (σ.filter (fun x => decide (x ∈ L))) (paperOrder P C L) := by
    have jfiltered : respects (σ.filter (fun x => decide (x ∈ L))) (jointOrder P C L O) :=
      joint.filter _
    apply jfiltered.imp_of_mem
    intro x y hx hy no edge
    exact no (Or.inr ⟨(filtered.2 y).mp hy,(filtered.2 x).mp hx,edge⟩)
  exact ⟨σ,ps,outer,filtered,inner⟩

end Sal.MRDTs.Paper1.LocalCoverage
