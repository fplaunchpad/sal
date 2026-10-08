import InductiveCrossedBridge
import Sal.MRDTs.Paper1.ConcreteJoin

/-! A concrete local-redistribution counterexample for the merge-only ghost
extension. The canonical representation and all Raw.Context premises are
constructed independently of its finite merge-equation proofs. -/
namespace NeemExpansion.GhostVC
open Sal.MRDTs
set_option linter.unusedSimpArgs false
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open Sal.MRDTs.Paper1.ORSet
open Ghost

def datatype : MRDTSig where
  State := S
  dec_state := inferInstance
  init := (∅,false)
  AppOp := Update Unit
  dec_op := inferInstance
  Query := Unit
  Value := Bool
  update := upd
  merge := join
  query s _ := s.2

def d : Event := (1,1,.add ())
def b : Event := (2,0,.add ())
def a : Event := (3,1,.remove ())
def c : Event := (4,0,.remove ())
def whole : Set Event := {d,b,a,c}
def left : Set Event := {d,a,b}
def right : Set Event := {b,c,d}
def policy : OperationPolicy (Update Unit) where
  before x y := ∃ z, x = .remove z ∧ y = .add z

def context : ReplayContext datatype.toUpdateSig where
  L := fun _ => some whole
  vis x y := (x = d ∧ y = a) ∨ (x = b ∧ y = c)
  timestamps_distinct := by
    intro x y r s r' s' hs hx ht hy ne
    simp only [Option.some.injEq] at hs ht
    subst s; subst s'
    simp only [whole] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;> simp_all [d,b,a,c]
  vis_total_same_replica := by
    intro x y r s r' s' hs hx ht hy ne same
    simp only [Option.some.injEq] at hs ht
    subst s; subst s'
    simp only [whole] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;> simp_all [d,b,a,c]

/-- The very same concrete-conflict metadata scheme used by the two OR sets. -/
def scheme (C : ReplayContext datatype.toUpdateSig) : MetadataDependencies C :=
  MetadataDependencies.ofConcrete C

def represented : Representation datatype := Canonical policy

def base : S := ({((),1),((),2)},false)
def past : S := ({((),1)},false)
def other : S := ({((),1)},false)

private theorem bc_noncomm : ¬ datatype.toUpdateSig.commutes b c := by
  intro commute
  have bad := commute (∅,false)
  change upd (upd (∅,false) b) c = upd (upd (∅,false) c) b at bad
  have unequal : upd (upd (∅,false) b) c ≠ upd (upd (∅,false) c) b := by decide
  exact unequal bad

private theorem da_noncomm : ¬ datatype.toUpdateSig.commutes d a := by
  intro commute
  have bad := commute (∅,false)
  change upd (upd (∅,false) d) a = upd (upd (∅,false) a) d at bad
  have unequal : upd (upd (∅,false) d) a ≠ upd (upd (∅,false) a) d := by decide
  exact unequal bad

private theorem metadata_relation : (scheme context).before = context.vis := by
  funext x y
  apply propext
  constructor
  · exact fun h => h.1
  · intro edge
    refine ⟨edge,?_⟩
    rcases edge with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact da_noncomm
    · exact bc_noncomm

private theorem sides_union : left ∪ right = whole := by
  ext z; simp only [left,right,whole,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
  tauto

private theorem sides_intersection : left ∩ right = ({d,b} : Set Event) := by
  ext z; simp only [left,right,Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨hd | ha | hb, hr⟩
    · exact Or.inl hd
    · subst z; simp [a,b,c,d] at hr
    · exact Or.inr hb
  · rintro (rfl | rfl) <;> simp

theorem vc_context : Raw.Context policy scheme context left right a := by
  constructor
  · intro x y z hxy hyz
    rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [context,a,b,c,d] at hyz
  · intro x hx
    rcases hx with ⟨rfl,h⟩ | ⟨rfl,h⟩ <;> simp [a,b,c,d] at h
  · intro x hx; exact ⟨0,whole,rfl,by rw [← sides_union]; exact Or.inl hx⟩
  · intro x hx; exact ⟨0,whole,rfl,by rw [← sides_union]; exact Or.inr hx⟩
  · intro x y edge hy
    rcases edge.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simp [left]
    · simp [left,a,b,c,d] at hy
  · intro x y edge hy
    rcases edge.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simp [right,a,b,c,d] at hy
    · simp [right]
  · rw [sides_union]
    intro x hx ne
    rcases hx with rfl | rfl | rfl | rfl
    · simp [paperOrder,context,policy,a,b,c,d,Op.op]
    · rintro (⟨vis,_⟩ | ⟨_,_,_,noAbsorber⟩)
      · simp [context,a,b,c,d] at vis
      · exact noAbsorber ⟨c,by simp [whole],Or.inr ⟨rfl,rfl⟩,bc_noncomm⟩
    · exact False.elim (ne rfl)
    · simp [paperOrder,context,policy,a,b,c,d,Op.op]
  · intro x _ _ edge
    simp [scheme,MetadataDependencies.ofConcrete,context,a,b,c,d] at edge

private theorem canonical_base : represented context (left ∩ right) base := by
  refine ⟨[d,b],?_,?_,?_⟩
  · rw [sides_intersection]; simp [listPermOf,d,b]
  · simp [respects,paperOrder,context,policy,d,a,b,c,Op.op]
  · decide

private theorem canonical_pre : represented context (left \ {a}) base := by
  refine ⟨[d,b],?_,?_,?_⟩
  · simp [listPermOf,left,d,a,b,c]
    grind
  · simp [respects,paperOrder,context,policy,d,a,b,c,Op.op]
  · decide

private theorem canonical_other : represented context right other := by
  refine ⟨[b,c,d],?_,?_,?_⟩
  · simp [listPermOf,right,d,a,b,c,or_comm]
  · simp [respects,paperOrder,context,policy,d,a,b,c,Op.op]
  · decide

private theorem past_events : (scheme context).Past a = ({d,a} : Set Event) := by
  change {x | x = a ∨ Relation.TransGen (scheme context).before x a} = _
  rw [metadata_relation, Relation.transGen_eq_self vc_context.trans]
  ext x
  simp [context,a,b,c,d]
  tauto

private theorem canonical_past_pre :
    represented context ((scheme context).Past a \ {a}) past := by
  refine ⟨[d], ?_, ?_, ?_⟩
  · rw [past_events]
    simp [listPermOf,d,a]
  · simp [respects]
  · decide

private theorem canonical_past :
    represented context ((scheme context).Past a) (upd past a) := by
  refine ⟨[d,a], ?_, ?_, ?_⟩
  · rw [past_events]; simp [listPermOf,d,a]
  · simp [respects,paperOrder,context,policy,d,a,b,c,Op.op]
  · decide

private theorem canonical_reconstructed :
    represented context left (join past base (upd past a)) := by
  refine ⟨[d,a,b], ?_, ?_, ?_⟩
  · simp [listPermOf,left,d,a,b,c]
  · simp [respects,paperOrder,context,policy,d,a,b,c,Op.op]
  · decide

private theorem remainder_events : (left ∪ right) \ {a} = right := by
  rw [sides_union]
  ext z
  simp [whole,right,a,b,c,d]
  grind

private theorem canonical_smaller :
    represented context ((left ∪ right) \ {a}) (join base base other) := by
  rw [remainder_events]
  have value : join base base other = other := by decide
  rw [value]
  exact canonical_other

/-- Hand-derived values show that the proposed five-VC bridge would force a
false equality despite every representation/context premise being satisfied. -/
theorem local_value_control :
    join base (join past base (upd past a)) other = (∅,true) ∧
    join past (join base base other) (upd past a) = (∅,false) ∧
    join base (join past base (upd past a)) other ≠
      join past (join base base other) (upd past a) := by
  decide

/-- The ghost implementation cannot satisfy Sal's actual five-VC package.
The failure is specifically the local_redistribute field, not a reconstruction
premise, a malformed history, or an unchecked solver assertion. -/
theorem not_raw_merge_vcs : ¬ Raw.MergeVCs policy represented scheme := by
  intro vcs
  have equality := vcs.local_redistribute context left right base past base other a
    vc_context (by simp [left]) (by simp [right,a,b,c,d])
    canonical_base canonical_past_pre canonical_pre canonical_other canonical_past
    canonical_reconstructed canonical_smaller
  exact local_value_control.2.2 equality

theorem order_before (x y : Event) :
    Ghost.signature.order x y = .Fst_then_snd ↔ policy.before x.op y.op := by
  rcases x with ⟨xt,xr,xo⟩; rcases y with ⟨yt,yr,yo⟩
  cases xo <;> cases yo <;> simp [Ghost.signature,ORSet.order,policy,Op.op]

theorem guardedLaws : GuardedReplay.Laws datatype.toUpdateSig policy := by
  constructor
  · intro x y _ _
    change (¬ ∀ s : S, upd (upd s x) y = upd (upd s y) x) ↔ _
    rw [Ghost.commutes_iff,ORSet.noncomm_iff_rc]
    simp only [ORSet.rc_iff,policy,Op.op]
  · intro x y z _ _
    rcases x with ⟨xt,xr,xo⟩; rcases y with ⟨yt,yr,yo⟩
    rcases z with ⟨zt,zr,zo⟩
    cases xo <;> cases yo <;> cases zo <;> simp [policy,Op.op]
  · intro s x y z between _ _ _ order noncomm
    have rc : ORSet.order x y = .Fst_then_snd := (order_before x y).mpr order
    change (¬ ∀ t : S, upd (upd t y) z = upd (upd t z) y) at noncomm
    rw [Ghost.commutes_iff] at noncomm
    exact (Ghost.conditional_log s x y z between rc noncomm).symm

/-- The ghost is observational: every sequential history answers false,
whereas the crossed merge answers true. -/
theorem replay_flag_false (π : List Event) :
    (applySeq datatype.toUpdateSig datatype.init π).2 = false := by
  induction π using List.reverseRecOn with
  | nil => rfl
  | append_singleton π h _ =>
      rw [applySeq_append_single]
      rfl

theorem observable_failure :
    datatype.query (join base (join past base (upd past a)) other) () = true ∧
    ¬ ∃ π : List Event, applySeq datatype.toUpdateSig datatype.init π =
      join base (join past base (upd past a)) other := by
  constructor
  · change (join base (join past base (upd past a)) other).2 = true
    decide
  · rintro ⟨π,eq⟩
    have flag := replay_flag_false π
    rw [eq,local_value_control.1] at flag
    contradiction

end NeemExpansion.GhostVC
