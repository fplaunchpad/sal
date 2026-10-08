import InductiveLeaves

/-! Candidate generic insufficiency witness: the usual exact OR-set augmented
with a merge-only ghost bit. No conclusion is claimed until all contracts below
are checked. The bit is erased by every event, and preserved on diagonals. -/
set_option linter.unusedSimpArgs false
namespace NeemExpansion.Ghost
open Sal.MRDTs.Foundation
open Sal.MRDTs.Paper1.ORSet
abbrev Core := State Unit
abbrev S := Core × Bool
abbrev Event := Op (Update Unit)

def crossed (l a b : Core) : Prop :=
  a.Nonempty ∧ b.Nonempty ∧ Disjoint a b ∧ a ⊆ l ∧ b ⊆ l

instance (l a b : Core) : Decidable (crossed l a b) := by
  unfold crossed; infer_instance

def upd (s : S) (p : Event) : S := (step s.1 p, false)
def join (l a b : S) : S :=
  (merge l.1 a.1 b.1, (l.2 && a.2 && b.2) || decide (crossed l.1 a.1 b.1))
def signature : Signature := ⟨S,Update Unit,(∅,false),upd,join,order⟩

@[simp] theorem upd_fst (s : S) (p : Event) : (upd s p).1 = step s.1 p := rfl

/-- A crossed tuple cannot satisfy any transported-update equation: its last
Add would lie in the ancestor but not in the opposite branch. -/
theorem no_cross_of_transport (l a b : Core) (p : Event)
    (eq : merge l (step a p) b = step (merge l a b) p) :
    ¬ crossed l (step a p) b := by
  intro hc
  rcases hc with ⟨ha,hb,hd,hal,hbl⟩
  rcases p with ⟨t,r,op⟩
  cases op with
  | remove u =>
    cases u
    have empty : step a (t,r,Update.remove ()) = ∅ := by
      ext x; rcases x with ⟨u,tx⟩; cases u; simp [step]
    rw [empty] at ha
    exact Finset.not_nonempty_empty ha
  | add u =>
    cases u
    have hp : ((),t) ∈ step a (t,r,Update.add ()) := by simp [step]
    have hl : ((),t) ∈ l := hal hp
    have hnb : ((),t) ∉ b := Finset.disjoint_left.mp hd hp
    have eqp := Finset.ext_iff.mp eq ((),t)
    simp [merge,step,hl,hnb] at eqp

/-- Ghost equality is precisely the underlying equation on every Q1 tuple. -/
theorem transport_iff (l a b : S) (p : Event) :
    join l (upd a p) b = upd (join l a b) p ↔
      merge l.1 (step a.1 p) b.1 = step (merge l.1 a.1 b.1) p := by
  constructor
  · intro h; exact congrArg Prod.fst h
  · intro h
    have free := no_cross_of_transport l.1 a.1 b.1 p h
    apply Prod.ext
    · exact h
    · simp [join,upd,free]

/-- The same projection transfer covers mirrored right-one-op equations. -/
theorem right_transport_iff (l a b : S) (p : Event) :
    join l a (upd b p) = upd (join l a b) p ↔
      merge l.1 a.1 (step b.1 p) = step (merge l.1 a.1 b.1) p := by
  have commG (l a b : S) : join l a b = join l b a := by
    apply Prod.ext
    · exact NeemExpansion.Exact.comm l.1 a.1 b.1
    · simp only [join,crossed,Bool.and_assoc,Prod.snd]
      have swap : crossed l.1 a.1 b.1 ↔ crossed l.1 b.1 a.1 := by
        simp only [crossed,disjoint_comm]; tauto
      simp [swap, disjoint_comm, Bool.and_comm, Bool.and_left_comm]
  rw [commG l a (upd b p), commG l a b]
  have ht := transport_iff l b a p
  have c1 : merge l.1 (step b.1 p) a.1 = merge l.1 a.1 (step b.1 p) := NeemExpansion.Exact.comm _ _ _
  have c2 : merge l.1 b.1 a.1 = merge l.1 a.1 b.1 := NeemExpansion.Exact.comm _ _ _
  rw [c1,c2] at ht
  exact ht


theorem comm : signature.comm := by
  intro l a b
  apply Prod.ext
  · exact NeemExpansion.Exact.comm l.1 a.1 b.1
  · have swap : crossed l.1 a.1 b.1 ↔ crossed l.1 b.1 a.1 := by
      simp only [crossed,disjoint_comm]; tauto
    simp [signature,join,swap,Bool.and_assoc,Bool.and_comm,Bool.and_left_comm]

theorem idem : signature.idem := by
  intro s
  have free : ¬ crossed s.1 s.1 s.1 := by
    rintro ⟨⟨x,hx⟩,_,hd,_,_⟩
    exact Finset.disjoint_left.mp hd hx hx
  apply Prod.ext
  · exact NeemExpansion.Exact.idem s.1
  · simp [signature,join,free]

theorem no_cross_common (l a b : Core) (p : Event) :
    ¬ crossed (step l p) (step a p) (step b p) := by
  rcases p with ⟨t,r,op⟩
  cases op with
  | remove u =>
    cases u
    have he : step a (t,r,Update.remove ()) = ∅ := by
      ext x; rcases x with ⟨u,tx⟩; cases u; simp [step]
    simp [crossed,he]
  | add u =>
    rintro ⟨_,_,hd,_,_⟩
    have ha : (u,t) ∈ step a (t,r,Update.add u) := by simp [step]
    have hb : (u,t) ∈ step b (t,r,Update.add u) := by simp [step]
    exact Finset.disjoint_left.mp hd ha hb

theorem zero : signature.zero := by
  intro l a b p
  apply Prod.ext
  · exact NeemExpansion.Exact.zero l.1 a.1 b.1 p
  · simp [signature,join,upd,no_cross_common]

theorem base1 : signature.base1 := by
  unfold Signature.base1
  intro p
  simp only [Signature.Q1, Signature.Q2, signature, transport_iff, upd_fst]
  exact NeemExpansion.Exact.base1 p

theorem base2 : signature.base2 := by
  unfold Signature.base2
  intro p q ho hr ht
  simp only [Signature.Q1, Signature.Q2, signature, transport_iff, upd_fst]
  exact NeemExpansion.Exact.base2 p q ho hr ht

theorem common1 : signature.common1 := by
  unfold Signature.common1
  intro l p h hd hr ih
  simp only [Signature.Q1, Signature.Q2, signature, transport_iff, upd_fst] at ih ⊢
  exact NeemExpansion.Exact.common1 l.1 p h hd hr ih

theorem common2 : signature.common2 := by
  unfold Signature.common2
  intro l p q h ho hr ht hp hq ih1 ih2
  simp only [Signature.Q1, Signature.Q2, signature, transport_iff, upd_fst] at ih1 ih2 ⊢
  exact NeemExpansion.Exact.common2 l.1 p q h ho hr ht hp hq ih1 ih2

theorem inter_right_base_2op : signature.inter_right_base_2op := by
  unfold Signature.inter_right_base_2op
  intro l a b o1 o2 ob ol hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.inter_right_base_2op l.1 a.1 b.1 o1 o2 ob ol hp

theorem inter_left_base_2op : signature.inter_left_base_2op := by
  unfold Signature.inter_left_base_2op
  intro l a b o1 o2 ob ol hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.inter_left_base_2op l.1 a.1 b.1 o1 o2 ob ol hp

theorem inter_right_2op : signature.inter_right_2op := by
  unfold Signature.inter_right_2op
  intro l a b o1 o2 ob ol o hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.inter_right_2op l.1 a.1 b.1 o1 o2 ob ol o hp

theorem inter_left_2op : signature.inter_left_2op := by
  unfold Signature.inter_left_2op
  intro l a b o1 o2 ob ol o hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.inter_left_2op l.1 a.1 b.1 o1 o2 ob ol o hp

theorem inter_lca_2op : signature.inter_lca_2op := by
  unfold Signature.inter_lca_2op
  intro l a b o1 o2 ol hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.inter_lca_2op l.1 a.1 b.1 o1 o2 ol hp

theorem ind_right_2op : signature.ind_right_2op := by
  unfold Signature.ind_right_2op
  intro l a b o1 o2 o2' hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.ind_right_2op l.1 a.1 b.1 o1 o2 o2' hp

theorem ind_left_2op : signature.ind_left_2op := by
  unfold Signature.ind_left_2op
  intro l a b o1 o2 o1' hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.ind_left_2op l.1 a.1 b.1 o1 o2 o1' hp

theorem inter_right_base_1op : signature.inter_right_base_1op := by
  unfold Signature.inter_right_base_1op
  intro l a b o1 ob ol hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.inter_right_base_1op l.1 a.1 b.1 o1 ob ol hp

theorem inter_left_base_1op : signature.inter_left_base_1op := by
  unfold Signature.inter_left_base_1op
  intro l a b o1 ob ol hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.inter_left_base_1op l.1 a.1 b.1 o1 ob ol hp

theorem inter_right_1op : signature.inter_right_1op := by
  unfold Signature.inter_right_1op
  intro l a b o1 ob ol o hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.inter_right_1op l.1 a.1 b.1 o1 ob ol o hp

theorem inter_left_1op : signature.inter_left_1op := by
  unfold Signature.inter_left_1op
  intro l a b o1 ob ol o hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.inter_left_1op l.1 a.1 b.1 o1 ob ol o hp

theorem inter_lca_1op : signature.inter_lca_1op := by
  unfold Signature.inter_lca_1op
  intro l a b o1 ol oi hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.inter_lca_1op l.1 a.1 b.1 o1 ol oi hp

theorem ind_left_1op : signature.ind_left_1op := by
  unfold Signature.ind_left_1op
  intro l a b o1 o1' ol hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.ind_left_1op l.1 a.1 b.1 o1 o1' ol hp

theorem ind_right_1op : signature.ind_right_1op := by
  unfold Signature.ind_right_1op
  intro l a b o2 o2' ol hp
  simp only [signature, transport_iff, right_transport_iff, upd_fst] at hp ⊢
  exact NeemExpansion.Exact.ind_right_1op l.1 a.1 b.1 o2 o2' ol hp

/-- Update clears the ghost bit, so commutation is unchanged for every state. -/
theorem commutes_iff (p q : Event) :
    (∀ s : S, upd (upd s p) q = upd (upd s q) p) ↔
      (D Unit).toUpdateSig.commutes p q := by
  constructor
  · intro h s; exact congrArg Prod.fst (h (s,false))
  · intro h s
    apply Prod.ext
    · exact h s.1
    · rfl

theorem either_iff_no_conflict (p q : Event) :
    order p q = .Either ↔ ¬ ((D Unit).toUpdateSig.rc p q ∨ (D Unit).toUpdateSig.rc q p) := by
  rcases p with ⟨pt,pr,po⟩; rcases q with ⟨qt,qr,qo⟩
  cases po <;> cases qo <;>
    simp [UpdateSig.rc,ReplayPolicy.Before,Sal.MRDTs.Paper1.ORSet.policy,order]

/-- The precise F* guarded policy exactness law (a stronger unguarded version
happens to hold for the singleton exact OR-set countermodel). -/
theorem rc_non_comm (p q : Event) (_ : signature.distinct p q) (_ : p.2.1 ≠ q.2.1) :
    order p q = .Either ↔ ∀ s : S, upd (upd s p) q = upd (upd s q) p := by
  rw [commutes_iff,either_iff_no_conflict]
  have hn := Sal.MRDTs.Paper1.ORSet.noncomm_iff_rc p q
  tauto

theorem no_rc_chain (p q r : Event) (_ : signature.distinct p q) (_ : signature.distinct q r) :
    ¬ (order p q = .Fst_then_snd ∧ order q r = .Fst_then_snd) := by
  rcases p with ⟨pt,pr,po⟩; rcases q with ⟨qt,qr,qo⟩; rcases r with ⟨rt,rr,ro⟩
  cases po <;> cases qo <;> cases ro <;> simp [order]

theorem remove_all (s : S) (t r : Nat) : upd s (t,r,.remove ()) = (∅,false) := by
  apply Prod.ext
  · ext p; rcases p with ⟨u,pt⟩; cases u; simp [upd,step]
  · rfl

/-- Even the stronger actual-noncommutation absorber law is satisfied. This
also eliminates the separate F* base/inserted-operation conditional leaves. -/
theorem conditional_log (s : S) (p q r : Event) (between : List Event)
    (ord : order p q = .Fst_then_snd) (absorber : ¬ (D Unit).toUpdateSig.commutes q r) :
    upd (between.foldl upd (upd (upd s p) q)) r =
      upd (between.foldl upd (upd (upd s q) p)) r := by
  rcases p with ⟨pt,pr,po⟩; rcases q with ⟨qt,qr,qo⟩; rcases r with ⟨rt,rr,ro⟩
  cases po <;> cases qo <;> cases ro <;>
    simp [order] at ord
  · exfalso
    apply absorber
    apply Sal.MRDTs.Paper1.ORSet.commute_of_no_conflict
    simp [UpdateSig.rc,ReplayPolicy.Before,Sal.MRDTs.Paper1.ORSet.policy,order]
  · rename_i u v w
    cases w
    rw [remove_all,remove_all]

theorem conditional_policy_log (s : S) (p q r : Event) (between : List Event)
    (ord : order p q = .Fst_then_snd) (absorber : order q r ≠ .Either) :
    upd (between.foldl upd (upd (upd s p) q)) r =
      upd (between.foldl upd (upd (upd s q) p)) r := by
  apply conditional_log s p q r between ord
  intro hc
  have noConflict := Sal.MRDTs.Paper1.ORSet.noncomm_iff_rc q r
  have either : order q r = .Either := either_iff_no_conflict q r |>.mpr (by tauto)
  exact absorber either

/-- Exact F* conditional-commutation base contract. -/
theorem cond_comm_base (s : S) (p q r : Event)
    (_ : signature.distinct p q) (_ : signature.distinct q r) (_ : signature.distinct p r)
    (ord : order p q = .Fst_then_snd) (absorber : order q r ≠ .Either) :
    upd (upd (upd s p) q) r = upd (upd (upd s q) p) r := by
  exact conditional_policy_log s p q r [] ord absorber

/-- Exact F* inserted-operation conditional contract. Its IH is retained in
this statement; the countermodel satisfies the stronger unconditional log law. -/
theorem cond_comm_ind (s : S) (p q r o : Event) (between : List Event)
    (_ : signature.distinct p q) (_ : signature.distinct p r) (_ : signature.distinct q r)
    (ord : order p q = .Fst_then_snd) (absorber : order q r ≠ .Either)
    (_ : upd (between.foldl upd (upd (upd s p) q)) r =
      upd (between.foldl upd (upd (upd s q) p)) r) :
    upd (upd (between.foldl upd (upd (upd s p) q)) o) r =
      upd (upd (between.foldl upd (upd (upd s q) p)) o) r := by
  simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil] using
    conditional_policy_log s p q r (between ++ [o]) ord absorber

end NeemExpansion.Ghost
