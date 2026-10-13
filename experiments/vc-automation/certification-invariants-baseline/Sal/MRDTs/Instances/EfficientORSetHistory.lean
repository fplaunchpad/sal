import Sal.MRDTs.Instances.EfficientORSet

/-! Execution-history characterization for Neem's efficient OR-set.
No new public resolve-conflict policy is introduced here. The history
predicate records the causal replacements that the representation performs.
-/
namespace Sal.MRDTs.Instances.EfficientORSet

open Sal.MRDTs.Foundation
open Classical

variable {α : Type} [DecidableEq α]
abbrev Event (α : Type) := Op (SetOp α)

/-- Effects which can remove a record for one replica/element pair. -/
def kills (r : Replica) (x : α) (e : Event α) : Prop :=
  match e.2.2 with
  | .add y => e.2.1 = r ∧ y = x
  | .remove y => y = x

def dead (vis : Event α → Event α → Prop) (E : Set (Event α))
    (p : Record α) : Prop :=
  ∃ e ∈ E, vis (p.2.1, p.1, .add p.2.2) e ∧ kills p.1 p.2.2 e

def live (vis : Event α → Event α → Prop) (E : Set (Event α))
    (p : Record α) : Prop :=
  (p.2.1, p.1, SetOp.add p.2.2) ∈ E ∧ ¬ dead vis E p

def Represents (vis : Event α → Event α → Prop) (E : Set (Event α))
    (s : State α) : Prop := ∀ p, p ∈ s ↔ live vis E p

theorem dead_union (vis : Event α → Event α → Prop)
    (A B : Set (Event α)) (p : Record α) :
    dead vis (A ∪ B) p ↔ dead vis A p ∨ dead vis B p := by
  simp only [dead, Set.mem_union]
  aesop

theorem dead_mono (vis : Event α → Event α → Prop)
    {A B : Set (Event α)} (h : A ⊆ B) {p : Record α}
    (hd : dead vis A p) : dead vis B p := by
  obtain ⟨e, he, hv, hk⟩ := hd
  exact ⟨e, h he, hv, hk⟩

theorem live_merge (vis : Event α → Event α → Prop)
    (A B : Set (Event α))
    (closedA : ∀ a b, vis a b → b ∈ A → a ∈ A)
    (closedB : ∀ a b, vis a b → b ∈ B → a ∈ B)
    (p : Record α) :
    live vis (A ∪ B) p ↔
      (live vis (A ∩ B) p ∧ live vis A p ∧ live vis B p) ∨
      (live vis A p ∧ ¬ live vis (A ∩ B) p) ∨
      (live vis B p ∧ ¬ live vis (A ∩ B) p) := by
  have da : dead vis A p → (p.2.1, p.1, SetOp.add p.2.2) ∈ A := by
    rintro ⟨e, he, hv, _⟩; exact closedA _ e hv he
  have db : dead vis B p → (p.2.1, p.1, SetOp.add p.2.2) ∈ B := by
    rintro ⟨e, he, hv, _⟩; exact closedB _ e hv he
  have dia : dead vis (A ∩ B) p → dead vis A p :=
    dead_mono vis Set.inter_subset_left
  have dib : dead vis (A ∩ B) p → dead vis B p :=
    dead_mono vis Set.inter_subset_right
  simp only [live, Set.mem_union, Set.mem_inter_iff, dead_union]
  tauto

theorem represents_merge (vis : Event α → Event α → Prop)
    (A B : Set (Event α))
    (closedA : ∀ a b, vis a b → b ∈ A → a ∈ A)
    (closedB : ∀ a b, vis a b → b ∈ B → a ∈ B)
    {l a b : State α}
    (hl : Represents vis (A ∩ B) l)
    (ha : Represents vis A a) (hb : Represents vis B b) :
    Represents vis (A ∪ B) (merge l a b) := by
  intro p
  simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
    hl p, ha p, hb p]
  simpa only [and_assoc, or_assoc] using (live_merge vis A B closedA closedB p).symm

theorem represents_empty (vis : Event α → Event α → Prop) :
    Represents vis ∅ (∅ : State α) := by simp [Represents, live]

theorem mem_update_iff (p : Record α) (s : State α) (e : Event α) :
    p ∈ update s e ↔ e = (p.2.1,p.1,SetOp.add p.2.2) ∨
      (p ∈ s ∧ ¬ kills p.1 p.2.2 e) := by
  rcases p with ⟨r,t,x⟩
  rcases e with ⟨et,er,op⟩
  cases op <;> simp [update, kills, Prod.mk.injEq, eq_comm, and_comm, and_left_comm, and_assoc]

theorem mem_fold_iff (p : Record α) (ops : List (Event α)) :
    p ∈ ops.foldl update (∅ : State α) ↔
      ∃ pre post, ops = pre ++ (p.2.1,p.1,SetOp.add p.2.2) :: post ∧
        ∀ e ∈ post, ¬ kills p.1 p.2.2 e := by
  induction ops using List.reverseRecOn with
  | nil => simp
  | append_singleton ops e ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, mem_update_iff, ih]
    constructor
    · rintro (he | ⟨⟨pre,post,hops,hpost⟩,hne⟩)
      · exact ⟨ops, [], by simp [he], by simp⟩
      · refine ⟨pre, post ++ [e], ?_, ?_⟩
        · simp [hops, List.append_assoc]
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hpost a ha
          · simpa using (List.mem_singleton.mp ha ▸ hne)
    · rintro ⟨pre,post,hops,hpost⟩
      by_cases hp : post = []
      · subst post
        have he := congrArg List.getLast? hops
        simp at he
        exact Or.inl he
      · let post' := post.dropLast
        let last := post.getLast hp
        have hsplit : post = post' ++ [last] := (List.dropLast_concat_getLast hp).symm
        rw [hsplit] at hops hpost
        have heq : ops = pre ++ (p.2.1,p.1,SetOp.add p.2.2) :: post' ∧ e = last := by
          have hh : ops ++ [e] = (pre ++ (p.2.1,p.1,SetOp.add p.2.2) :: post') ++ [last] := by
            simpa only [List.append_assoc, List.cons_append] using hops
          simpa using List.append_inj' hh (by simp)
        rcases heq with ⟨hop, he⟩
        subst e
        exact Or.inr ⟨⟨pre,post',hop,fun a ha => hpost a (List.mem_append_left _ ha)⟩,
          hpost last (by simp)⟩

/-- Causal ordering of same-replica births makes their surviving records
unique. This is the invariant absent from arbitrary replay permutations. -/
theorem keyUnique_of_represents
    (vis : Event α → Event α → Prop) (E : Set (Event α))
    (total : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → a.2.1 = b.2.1 →
      vis a b ∨ vis b a)
    {s : State α} (h : Represents vis E s) : KeyUnique s := by
  intro r t u x ht hu
  obtain ⟨hat, hnt⟩ := (h (r,t,x)).mp ht
  obtain ⟨hau, hnu⟩ := (h (r,u,x)).mp hu
  by_contra hne
  have hev : (t,r,SetOp.add x) ≠ (u,r,SetOp.add x) := by
    intro heq; exact hne (congrArg Prod.fst heq)
  rcases total _ hat _ hau hev rfl with hv | hv
  · exact hnt ⟨_, hau, hv, by simp [kills]⟩
  · exact hnu ⟨_, hat, hv, by simp [kills]⟩

def element (e : Event α) : α := match e.2.2 with
  | .add x | .remove x => x

def Early (vis : Event α → Event α → Prop) (E : Set (Event α))
    (e : Event α) : Prop :=
  (∃ x, e.2.2 = .remove x) ∨
    ∃ z ∈ E, vis e z ∧ z.2.2 = .remove (element e)

/-- A proof-local sorting key, not an additional public policy. -/
noncomputable def rank (vis : Event α → Event α → Prop) (E : Set (Event α))
    (e : Event α) : Nat × Nat :=
  (if Early vis E e then 0 else 1, e.1)

def Before (vis : Event α → Event α → Prop) (E : Set (Event α))
    (a b : Event α) : Prop :=
  (rank vis E a).1 < (rank vis E b).1 ∨
    (rank vis E a).1 = (rank vis E b).1 ∧ a.1 < b.1

theorem early_backwards (vis : Event α → Event α → Prop) (E : Set (Event α))
    (ht : Transitive vis) {a b : Event α} (hb : b ∈ E)
    (hv : vis a b) (he : element a = element b) (h : Early vis E b) :
    Early vis E a := by
  rcases h with ⟨x,hx⟩ | ⟨z,hz,hbz,hzop⟩
  · right
    refine ⟨b,hb,hv,?_⟩
    have : element b = x := by simp [element,hx]
    simpa [he,this] using hx
  · exact Or.inr ⟨z,hz,ht hv hbz,by simpa [he] using hzop⟩

theorem before_of_vis (vis : Event α → Event α → Prop) (E : Set (Event α))
    (ht : Transitive vis) (hm : ∀ a b, vis a b → a.1 < b.1)
    {a b : Event α} (hb : b ∈ E) (hv : vis a b)
    (he : element a = element b) : Before vis E a b := by
  have hback := early_backwards vis E ht hb hv he
  have htime := hm a b hv
  unfold Before rank
  by_cases ha : Early vis E a <;> by_cases hb : Early vis E b <;> simp_all

theorem before_asymm (vis : Event α → Event α → Prop) (E : Set (Event α))
    {a b : Event α} (h : Before vis E a b) : ¬ Before vis E b a := by
  intro hba
  rcases h with h | ⟨h,h'⟩ <;> rcases hba with k | ⟨k,k'⟩
  · exact Nat.lt_asymm h k
  · exact (Nat.ne_of_lt h) k.symm
  · exact (Nat.ne_of_lt k) h.symm
  · exact Nat.lt_asymm h' k'

theorem before_trans (vis : Event α → Event α → Prop) (E : Set (Event α)) :
    Transitive (Before vis E) := by
  intro a b c hab hbc
  rcases hab with h | ⟨h,h'⟩ <;> rcases hbc with k | ⟨k,k'⟩
  · exact Or.inl (Nat.lt_trans h k)
  · exact Or.inl (k ▸ h)
  · exact Or.inl (h ▸ k)
  · exact Or.inr ⟨h.trans k,Nat.lt_trans h' k'⟩

theorem live_killer_before (vis : Event α → Event α → Prop) (E : Set (Event α))
    (ht : Transitive vis) (hm : ∀ a b, vis a b → a.1 < b.1)
    (total : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → a.2.1 = b.2.1 → vis a b ∨ vis b a)
    {p : Record α} (hp : live vis E p) {e : Event α} (he : e ∈ E)
    (hne : e ≠ (p.2.1,p.1,SetOp.add p.2.2)) (hk : kills p.1 p.2.2 e) :
    Before vis E e (p.2.1,p.1,SetOp.add p.2.2) := by
  have hn : ¬ Early vis E (p.2.1,p.1,SetOp.add p.2.2) := by
    rintro (⟨x,hx⟩ | ⟨z,hz,hvz,hzop⟩)
    · cases hx
    · exact hp.2 ⟨z,hz,hvz,by simp [kills,hzop,element]⟩
  rcases e with ⟨t,r,op⟩
  cases op with
  | remove x =>
    have hy : Early vis E (t,r,SetOp.remove x) := Or.inl ⟨x,rfl⟩
    simp [Before,rank,hy,hn]
  | add x =>
    obtain ⟨hr,hx⟩ := hk
    rcases total _ he _ hp.1 hne hr with hv | hv
    · exact before_of_vis vis E ht hm hp.1 hv (by simp [element,hx])
    · exact False.elim (hp.2 ⟨_,he,hv,⟨hr,hx⟩⟩)

theorem represents_sorted_fold
    (vis : Event α → Event α → Prop) (E : Set (Event α))
    (ht : Transitive vis) (hm : ∀ a b, vis a b → a.1 < b.1)
    (total : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → a.2.1 = b.2.1 → vis a b ∨ vis b a)
    (ops : List (Event α)) (hperm : listPermOf ops E)
    (hsort : ops.Pairwise (fun a b => ¬ Before vis E b a)) :
    Represents vis E (ops.foldl update ∅) := by
  intro p
  rw [mem_fold_iff]
  constructor
  · rintro ⟨pre,post,hops,hpost⟩
    have hbirth : (p.2.1,p.1,SetOp.add p.2.2) ∈ E :=
      (hperm.2 _).mp (by simp [hops])
    refine ⟨hbirth,?_⟩
    rintro ⟨e,he,hv,hk⟩
    have hbefore : Before vis E (p.2.1,p.1,SetOp.add p.2.2) e := by
      apply before_of_vis vis E ht hm he hv
      rcases e with ⟨t,r,op⟩
      cases op with
      | add x => exact hk.2.symm
      | remove x => exact hk.symm
    have hem : e ∈ pre ++ (p.2.1,p.1,SetOp.add p.2.2) :: post :=
      hops ▸ (hperm.2 e).mpr he
    rw [hops, List.pairwise_append, List.pairwise_cons] at hsort
    rcases List.mem_append.mp hem with hepre | hepost
    · exact hsort.2.2 e hepre _ (by simp) hbefore
    · rcases List.mem_cons.mp hepost with heq | hepost
      · subst e
        have hh := hm _ _ hv
        exact Nat.lt_irrefl _ hh
      · exact hpost e hepost hk
  · intro hp
    obtain ⟨pre,post,hops⟩ := List.mem_iff_append.mp ((hperm.2 _).mpr hp.1)
    refine ⟨pre,post,hops,?_⟩
    intro e he hk
    have hem : e ∈ E := (hperm.2 e).mp (by simp [hops,he])
    have hne : e ≠ (p.2.1,p.1,SetOp.add p.2.2) := by
      have hn := hperm.1
      rw [hops,List.nodup_append,List.nodup_cons] at hn
      intro heq
      exact hn.2.1.1 (heq ▸ he)
    have hb := live_killer_before vis E ht hm total hp hem hne hk
    rw [hops,List.pairwise_append,List.pairwise_cons] at hsort
    exact hsort.2.1.1 e he hb

theorem not_before_trans (vis : Event α → Event α → Prop) (E : Set (Event α)) :
    Transitive (fun a b => ¬ Before vis E b a) := by
  intro a b c hab hbc hca
  have habr : (rank vis E a).1 ≤ (rank vis E b).1 :=
    Nat.le_of_not_gt (fun h => hab (Or.inl h))
  have hbcr : (rank vis E b).1 ≤ (rank vis E c).1 :=
    Nat.le_of_not_gt (fun h => hbc (Or.inl h))
  rcases hca with h | ⟨h,h'⟩
  · exact Nat.not_lt_of_ge (Nat.le_trans habr hbcr) h
  · have habEq := Nat.le_antisymm habr (h ▸ hbcr)
    have hbcEq := habEq.symm.trans h.symm
    have habtime : a.1 ≤ b.1 := Nat.le_of_not_gt (fun h => hab (Or.inr ⟨habEq.symm,h⟩))
    have hbctime : b.1 ≤ c.1 := Nat.le_of_not_gt (fun h => hbc (Or.inr ⟨hbcEq.symm,h⟩))
    exact Nat.not_lt_of_ge (Nat.le_trans habtime hbctime) h'

theorem exists_sorted (vis : Event α → Event α → Prop) (E : Set (Event α))
    (ops : List (Event α)) (hp : listPermOf ops E) :
    ∃ sorted, listPermOf sorted E ∧ sorted.Pairwise (fun a b => ¬ Before vis E b a) := by
  let cmp := fun a b => decide (¬ Before vis E b a)
  refine ⟨ops.mergeSort cmp, ?_, ?_⟩
  · have hp' := List.mergeSort_perm ops cmp
    exact ⟨hp'.nodup_iff.mpr hp.1,fun a => hp'.mem_iff.trans (hp.2 a)⟩
  · have hh := List.pairwise_mergeSort (le := cmp)
      (fun a b c hab hbc => by
        simpa [cmp] using not_before_trans vis E
          (by simpa [cmp] using hab) (by simpa [cmp] using hbc))
      (fun a b => by
        simp only [cmp, Bool.or_eq_true, decide_eq_true_eq]
        by_cases h : Before vis E b a
        · exact Or.inr (before_asymm vis E h)
        · exact Or.inl h) ops
    simpa [cmp] using hh

theorem rc_iff (a b : Event α) :
    @UpdateSig.rc (D α).toUpdateSig rc a b ↔
      ∃ x, a.2.2 = .remove x ∧ b.2.2 = .add x := by
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  cases oa <;> cases ob <;> simp [UpdateSig.replayOrder,rc,eq_comm]
  split <;> simp

theorem before_of_loOn (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (ht : Transitive C.vis)
    (hm : ∀ a b, C.vis a b → a.1 < b.1)
    {a b : Event α} (hb : b ∈ E)
    (h : @loOn (D α).toUpdateSig rc C E a b) : Before C.vis E a b := by
  rcases h with ⟨hv,hr | hr⟩ | ⟨_,_,hr,hn⟩
  · obtain ⟨x,ha,hb'⟩ := (rc_iff a b).mp hr
    exact before_of_vis C.vis E ht hm hb hv (by simp [element,ha,hb'])
  · obtain ⟨x,hb',ha⟩ := (rc_iff b a).mp hr
    exact before_of_vis C.vis E ht hm hb hv (by simp [element,ha,hb'])
  · obtain ⟨x,ha,hb'⟩ := (rc_iff a b).mp hr
    have hea : Early C.vis E a := Or.inl ⟨x,ha⟩
    have heb : ¬ Early C.vis E b := by
      rintro (⟨y,hy⟩ | ⟨z,hz,hvz,hzop⟩)
      · rw [hb'] at hy; cases hy
      · apply hn ⟨z,hz,hvz,Or.inr ?_⟩
        apply (rc_iff z b).mpr
        exact ⟨x,by simpa [element,hb'] using hzop,hb'⟩
    simp [Before,rank,hea,heb]

theorem canonical_of_represents (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (ht : Transitive C.vis)
    (hm : ∀ a b, C.vis a b → a.1 < b.1)
    (total : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → a.2.1 = b.2.1 → C.vis a b ∨ C.vis b a)
    (ops : List (Event α)) (hp : listPermOf ops E)
    {s : State α} (hs : Represents C.vis E s) :
    @IsCanonicalState (D α).toUpdateSig rc C E s := by
  obtain ⟨sorted,hperm,hsort⟩ := exists_sorted C.vis E ops hp
  refine ⟨sorted,hperm,?_,?_⟩
  · apply hsort.imp_of_mem
    intro a b ha hb hn hlo
    exact hn (before_of_loOn C E ht hm ((hperm.2 a).mp ha) hlo)
  · have hf := represents_sorted_fold C.vis E ht hm total sorted hperm hsort
    apply Finset.ext
    intro p
    exact (hf p).trans (hs p).symm

theorem represents_congr {vis vis' : Event α → Event α → Prop}
    {E : Set (Event α)} {s : State α}
    (hv : ∀ a b, b ∈ E → (vis a b ↔ vis' a b))
    (hs : Represents vis E s) : Represents vis' E s := by
  intro p
  rw [hs p]
  simp only [live,dead]
  apply and_congr_right
  intro _
  apply not_congr
  constructor <;> rintro ⟨e,he,hv',hk⟩
  · exact ⟨e,he,(hv _ _ he).mp hv',hk⟩
  · exact ⟨e,he,(hv _ _ he).mpr hv',hk⟩

theorem represents_apply {vis : Event α → Event α → Prop}
    {E : Set (Event α)} {s : State α} {e : Event α}
    (hf : e ∉ E) (hn : ∀ b, ¬ vis e b) (hs : Represents vis E s) :
    Represents (fun a b => vis a b ∨ (a ∈ E ∧ b = e)) (E ∪ {e}) (update s e) := by
  intro p
  rw [mem_update_iff,hs p]
  let birth : Event α := (p.2.1,p.1,SetOp.add p.2.2)
  by_cases hb : birth = e
  · have hbirth : (p.2.1,p.1,SetOp.add p.2.2) = e := hb
    simp [live,dead,hbirth,hf,hn]
  · have hbirth : (p.2.1,p.1,SetOp.add p.2.2) ≠ e := hb
    simp only [live,Set.mem_union,Set.mem_singleton_iff,hbirth,or_false]
    constructor
    · rintro (he | ⟨⟨hmem,hdead⟩,hkill⟩)
      · exact False.elim (hbirth he.symm)
      · refine ⟨hmem,?_⟩
        rintro ⟨z,hz,hvz,hk⟩
        rcases hz with hz | hz
        · rcases hvz with hvz | ⟨_,hze⟩
          · exact hdead ⟨z,hz,hvz,hk⟩
          · exact hf (hze ▸ hz)
        · exact hkill (Set.mem_singleton_iff.mp hz ▸ hk)
    · rintro ⟨hmem,hdead⟩
      right
      refine ⟨⟨hmem,?_⟩,?_⟩
      · rintro ⟨z,hz,hvz,hk⟩
        exact hdead ⟨z,Or.inl hz,Or.inl hvz,hk⟩
      · intro hk
        exact hdead ⟨e,Or.inr rfl,Or.inr ⟨hmem,rfl⟩,hk⟩

#print axioms represents_merge
#print axioms canonical_of_represents
#print axioms keyUnique_of_represents
end Sal.MRDTs.Instances.EfficientORSet
