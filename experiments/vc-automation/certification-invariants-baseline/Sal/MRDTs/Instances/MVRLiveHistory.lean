import Sal.MRDTs.Instances.MVRLive
import Sal.MRDTs.Metatheory.VirtualAdequacy

namespace Sal.MRDTs.Instances.MVRLive
open Sal.MRDTs.Foundation
open Classical
local instance : ReplayPolicy D.toUpdateSig := rc
set_option maxHeartbeats 1000000

private theorem merge_logic (bl ba bb dl da db : Prop)
    (bi : bl ↔ ba ∧ bb) (d1 : dl → da) (d2 : dl → db)
    (a1 : bb → da → ba) (a2 : ba → db → bb) :
    (bl ∧ ¬dl ∧ ba ∧ ¬da ∧ bb ∧ ¬db) ∨
      (ba ∧ ¬da ∧ ¬(bl ∧ ¬dl)) ∨ (bb ∧ ¬db ∧ ¬(bl ∧ ¬dl)) ↔
      (ba ∨ bb) ∧ ¬(da ∨ db) := by tauto

def Represents (E : Set Event) (s : State) : Prop :=
  ∀ p, p ∈ s ↔ (∃ e ∈ E, (e.1, MVR.writeValue e) = p) ∧
    ¬ ∃ e ∈ E, p.1 ∈ MVR.overwrites e

theorem represents_empty : Represents ∅ ∅ := by simp [Represents]

theorem fold_born (ops : List Event) (p : ℕ × ℕ)
    (hp : p ∈ ops.foldl update ∅) :
    ∃ e ∈ ops, (e.1, MVR.writeValue e) = p := by
  induction ops using List.reverseRecOn with
  | nil => simp at hp
  | append_singleton ops e ih =>
    rw [List.foldl_append] at hp
    change p ∈ insert (e.1,MVR.writeValue e)
      ((ops.foldl update ∅).filter _) at hp
    rcases Finset.mem_insert.mp hp with he | ho
    · exact ⟨e,by simp,he.symm⟩
    · obtain ⟨a,ha,hp⟩ := ih (Finset.mem_filter.mp ho).1
      exact ⟨a,List.mem_append_left _ ha,hp⟩

theorem issued_overwrite {C : Configuration D}
    (mint : MintHonest D issuance.CanIssue C) {b : Event}
    (hb : b ∈ C.events) {n : ℕ} (hn : n ∈ MVR.overwrites b) :
    ∃ a ∈ C.events, C.vis a b ∧ a.1 = n := by
  obtain ⟨ops,hp,_,hg⟩ := mint b hb
  have heq := hg.2
  have hm : n ∈ (MVR.overwrites b).toFinset := List.mem_toFinset.mpr hn
  rw [heq] at hm
  obtain ⟨p,hps,ht⟩ := Finset.mem_image.mp hm
  obtain ⟨a,ha,hpair⟩ := fold_born ops p hps
  exact ⟨a,((hp.2 a).mp ha).1,((hp.2 a).mp ha).2,
    (congrArg (fun p : ℕ × ℕ => p.1) hpair).trans ht⟩

theorem issued_overwrite_lt {C : Configuration D}
    (mint : MintHonest D issuance.CanIssue C) {b : Event}
    (hb : b ∈ C.events) {n : ℕ} (hn : n ∈ MVR.overwrites b) : n < b.1 := by
  obtain ⟨a,_,hv,ht⟩ := issued_overwrite mint hb hn
  simpa [ht] using C.causal_mono hv

theorem represents_merge (C : Configuration D)
    (mint : MintHonest D issuance.CanIssue C) (A B : Set Event)
    (supA : A ⊆ C.events) (supB : B ⊆ C.events)
    (closedA : ∀ a b, C.vis a b → b ∈ A → a ∈ A)
    (closedB : ∀ a b, C.vis a b → b ∈ B → a ∈ B)
    {l a b : State} (hl : Represents (A ∩ B) l)
    (ha : Represents A a) (hb : Represents B b) :
    Represents (A ∪ B) (merge l a b) := by
  intro p
  let born := fun E : Set Event => ∃ e ∈ E, (e.1,MVR.writeValue e) = p
  let dead := fun E : Set Event => ∃ e ∈ E, p.1 ∈ MVR.overwrites e
  have bi : born (A ∩ B) ↔ born A ∧ born B := by
    constructor
    · rintro ⟨e,⟨heA,heB⟩,hp⟩; exact ⟨⟨e,heA,hp⟩,⟨e,heB,hp⟩⟩
    · rintro ⟨⟨x,hx,hxp⟩,⟨y,hy,hyp⟩⟩
      have heq := C.replayContext.ts_unique (supA hx) (supB hy)
        (congrArg (fun p : ℕ × ℕ => p.1) (hxp.trans hyp.symm))
      subst y
      exact ⟨x,⟨hx,hy⟩,hxp⟩
  have dl : dead (A ∩ B) → dead A := by rintro ⟨e,he,hn⟩; exact ⟨e,he.1,hn⟩
  have dr : dead (A ∩ B) → dead B := by rintro ⟨e,he,hn⟩; exact ⟨e,he.2,hn⟩
  have al : born B → dead A → born A := by
    rintro ⟨x,hx,hp⟩ ⟨e,he,hn⟩
    obtain ⟨birth,hm,hv,ht⟩ := issued_overwrite mint (supA he) hn
    have heq := C.replayContext.ts_unique hm (supB hx)
      (ht.trans (congrArg (fun p : ℕ × ℕ => p.1) hp).symm)
    exact ⟨x,closedA x e (heq ▸ hv) he,hp⟩
  have ar : born A → dead B → born B := by
    rintro ⟨x,hx,hp⟩ ⟨e,he,hn⟩
    obtain ⟨birth,hm,hv,ht⟩ := issued_overwrite mint (supB he) hn
    have heq := C.replayContext.ts_unique hm (supA hx)
      (ht.trans (congrArg (fun p : ℕ × ℕ => p.1) hp).symm)
    exact ⟨x,closedB x e (heq ▸ hv) he,hp⟩
  have bu : born (A ∪ B) ↔ born A ∨ born B := by
    simp [born, Set.mem_union, or_and_right, exists_or]
  have du : dead (A ∪ B) ↔ dead A ∨ dead B := by
    simp [dead, Set.mem_union, or_and_right, exists_or]
  change _ ↔ born (A ∪ B) ∧ ¬ dead (A ∪ B)
  simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
    hl p,ha p,hb p]
  simp only [and_assoc,or_assoc]
  change (born (A ∩ B) ∧ ¬dead (A ∩ B) ∧ born A ∧ ¬dead A ∧
      born B ∧ ¬dead B) ∨
    (born A ∧ ¬dead A ∧ ¬(born (A ∩ B) ∧ ¬dead (A ∩ B))) ∨
    (born B ∧ ¬dead B ∧ ¬(born (A ∩ B) ∧ ¬dead (A ∩ B))) ↔ _
  rw [bu,du]
  exact merge_logic _ _ _ _ _ _ bi dl dr al ar

theorem represents_update {E : Set Event} {s : State} (e : Event)
    (hs : Represents E s)
    (fresh : ∀ b ∈ E, e.1 ∉ MVR.overwrites b)
    (self : e.1 ∉ MVR.overwrites e) :
    Represents (E ∪ {e}) (update s e) := by
  intro p
  simp only [update, MVR.clientStep, Finset.mem_insert, Finset.mem_filter,hs p]
  by_cases hp : p = (e.1,MVR.writeValue e)
  · subst p
    simp only [Set.mem_union,Set.mem_singleton_iff,or_and_right,
      exists_or,exists_eq_left]
    simp [self]
    exact Or.inr (fun t r o h => fresh (t,r,o) h)
  · simp only [Set.mem_union, Set.mem_singleton_iff, or_and_right,
      exists_or, exists_eq_left]
    have hp' := Ne.symm hp
    simp [hp,hp',and_comm,and_left_comm]

theorem canonical_of_represents (C : Configuration D)
    (mint : MintHonest D issuance.CanIssue C) (E : Set Event)
    (sup : E ⊆ C.events) (ops : List Event) (hp : listPermOf ops E)
    {s : State} (hs : Represents E s) :
    IsCanonicalState C.replayContext E s := by
  let sorted := MVR.chronological ops
  have hperm : listPermOf sorted E :=
    ⟨(MVR.chronological_perm ops).symm.nodup hp.1,
      fun a => (MVR.chronological_perm ops).mem_iff.trans (hp.2 a)⟩
  refine ⟨sorted,hperm,?_,?_⟩
  · apply (MVR.chronological_sorted ops).imp
    intro a b hab hlo
    rcases hlo with hv | hr
    · exact (not_lt_of_ge hab) (C.causal_mono hv.1)
    · exact (not_lt_of_ge hab) ((MVR.rc_before_iff b a).mp hr.2.2.1).1
  · rw [fold_live sorted (MVR.chronological_sorted ops)
      (fun e he n hn => issued_overwrite_lt mint (sup ((hperm.2 e).mp he)) hn)]
    apply Finset.ext
    intro p
    rw [mem_live,hs p]
    simp only [Born,Dead,List.mem_toFinset,hperm.2]

def RepConfig (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s,E) → Represents E s

end Sal.MRDTs.Instances.MVRLive
