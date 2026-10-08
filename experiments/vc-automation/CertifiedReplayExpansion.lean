import Sal.MRDTs.Paper1.CertifiedRGAVCReplay

namespace NeemExpansion.CertifiedReplay
open Sal.MRDTs.Foundation

theorem provenance {E S R : Type} (step : S → E → S) (init : S)
    (mem : R → S → Prop) (born : E → R → Prop)
    (empty : ∀ p, ¬mem p init)
    (one : ∀ s e p, mem p (step s e) → born e p ∨ mem p s)
    (xs : List E) : ∀ p, mem p (xs.foldl step init) → ∃ e ∈ xs, born e p := by
  induction xs using List.reverseRecOn with
  | nil => intro p hp; exact False.elim (empty p hp)
  | append_singleton xs e ih =>
    intro p hp
    rw [List.foldl_append] at hp
    rcases one _ e p hp with h | h
    · exact ⟨e,by simp,h⟩
    · obtain ⟨q,hq,hb⟩ := ih p h
      exact ⟨q,List.mem_append_left _ hq,hb⟩

/-- New generic fold expansion; the only order premise excludes a killer
before a later birth of the same record. -/
theorem alive {E S R : Type} (step : S → E → S) (init : S)
    (mem : R → S → Prop) (born kill : E → R → Prop)
    (empty : ∀ p, ¬mem p init) (xs : List E)
    (one : ∀ pre e post, xs = pre ++ e :: post → ∀ p,
      mem p (step (pre.foldl step init) e) ↔ born e p ∨ (mem p (pre.foldl step init) ∧ ¬kill e p))
    (same : ∀ e p, born e p → ¬kill e p)
    (before : ∀ pre d mid e post, xs = pre ++ d :: (mid ++ e :: post) → ∀ p,
      kill d p → ¬born e p) :
    ∀ p, mem p (xs.foldl step init) ↔
      (∃ e ∈ xs, born e p) ∧ ∀ d ∈ xs, ¬kill d p := by
  induction xs using List.reverseRecOn with
  | nil => intro p; simp [empty]
  | append_singleton xs e ih =>
    have prefixOne : ∀ pre q post, xs = pre ++ q :: post → ∀ p,
        mem p (step (pre.foldl step init) q) ↔ born q p ∨ (mem p (pre.foldl step init) ∧ ¬kill q p) := by
      intro pre q post eq
      apply one pre q (post ++ [e])
      simp [eq,List.append_assoc]
    have prefixBefore : ∀ pre d mid q post, xs = pre ++ d :: (mid ++ q :: post) → ∀ p,
        kill d p → ¬born q p := by
      intro pre d mid q post eq
      apply before pre d mid q (post ++ [e])
      simp [eq,List.append_assoc]
    intro p
    rw [List.foldl_append]
    change mem p (step (xs.foldl step init) e) ↔ _
    rw [one xs e [] (by simp), ih prefixOne prefixBefore p]
    have newSafe : born e p → ∀ d ∈ xs, ¬kill d p := by
      intro hb d hd hk
      obtain ⟨pre,post,eq⟩ := List.mem_iff_append.mp hd
      exact before pre d post e [] (by simp [eq,List.append_assoc]) p hk hb
    simp only [List.mem_append,List.mem_singleton]
    constructor
    · rintro (hb | ⟨⟨birth,nokill⟩,he⟩)
      · exact ⟨⟨e,Or.inr rfl,hb⟩,fun d hd => hd.elim (newSafe hb d) (fun h => h ▸ same e p hb)⟩
      · exact ⟨by obtain ⟨q,hq,hb⟩ := birth; exact ⟨q,Or.inl hq,hb⟩,
          fun d hd => hd.elim (nokill d) (fun h => h ▸ he)⟩
    · rintro ⟨⟨q,hq,hb⟩,nk⟩
      rcases hq with hq | rfl
      · exact Or.inr ⟨⟨⟨q,hq,hb⟩,fun d hd => nk d (Or.inl hd)⟩,nk e (Or.inr rfl)⟩
      · exact Or.inl hb
end NeemExpansion.CertifiedReplay

namespace NeemExpansion.CertifiedSidedReplay
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Sal.MRDTs.Instances.SidedEmbedRGA

def Born (Γ : OrderedPrefixCode) (e : Op SOp) (p : SRec) := sIsIns e = true ∧ p = sRecOf Γ e
def Kill (e : Op SOp) (p : SRec) := e.2.2 = .del p.1

theorem update_provenance (Γ : OrderedPrefixCode) (s : SState) (e : Op SOp) (p : SRec) :
    p ∈ sUpdate Γ s e → Born Γ e p ∨ p ∈ s := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | del x => simp only [sUpdate,List.mem_filter]; tauto
  | ins x pref a side =>
    simp only [sUpdate]
    split
    · exact Or.inr
    · rw [mem_sInsert]
      intro h
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl ⟨rfl,h⟩

theorem provenance (Γ : OrderedPrefixCode) (xs : List (Op SOp)) (p : SRec) :
    p ∈ sFold Γ xs → ∃ e ∈ xs, Born Γ e p :=
  CertifiedReplay.provenance (sUpdate Γ) [] (fun p s => p ∈ s) (Born Γ)
    (by simp) (update_provenance Γ) xs p

theorem step_membership (Γ : OrderedPrefixCode) (s : SState) (e : Op SOp)
    (fresh : e.1 ∉ sIds s) (p : SRec) :
    p ∈ sUpdate Γ s e ↔ Born Γ e p ∨ (p ∈ s ∧ ¬Kill e p) := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | del x => simp [sUpdate,Born,Kill,sIsIns]; tauto
  | ins x pref a side =>
    simp only [sUpdate,if_neg fresh,mem_sInsert]
    simp [Born,Kill,sIsIns,sRecOf,sCoord]
    tauto

theorem membership (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) (xs : List (Op SOp)) (nodup : xs.Nodup)
    (support : ∀ e ∈ xs, e ∈ C.events) (ordered : respects xs C.vis) (p : SRec) :
    p ∈ sFold Γ xs ↔ (∃ e ∈ xs, Born Γ e p) ∧ ∀ d ∈ xs, ¬Kill d p := by
  apply CertifiedReplay.alive (sUpdate Γ) [] (fun p s => p ∈ s) (Born Γ) Kill (by simp) xs
  · intro pre e post eq p
    apply step_membership
    intro hid
    obtain ⟨q,hq,id⟩ := List.mem_map.mp hid
    obtain ⟨birth,hb,_,rec⟩ := provenance Γ pre q hq
    have hbAll : birth ∈ xs := by rw [eq]; exact List.mem_append_left _ hb
    have heAll : e ∈ xs := by rw [eq]; simp
    have same : birth = e := C.ts_unique (support birth hbAll) (support e heAll)
      (by simpa only [rec,sRecOf] using id)
    subst birth
    have nd : (pre ++ e :: post).Nodup := eq ▸ nodup
    have dis := (List.nodup_append.mp nd).2.2
    exact dis e hb e (List.mem_cons_self) rfl
  · intro e p hb
    rcases e with ⟨t,r,op⟩
    cases op <;> simp_all [Born,Kill,sIsIns]
  · intro pre d mid e post eq p hk hb
    obtain ⟨birth,hbirth,vis,time,_⟩ := honest.del_has_ins d
      (support d (by rw [eq]; simp)) p.1 hk
    have same : birth = e := C.ts_unique hbirth (support e (by rw [eq]; simp))
      (time.trans (by simpa only [hb.2,sRecOf] using (rfl : p.1 = p.1)))
    subst birth
    rw [eq] at ordered
    have pair := (List.pairwise_append.mp ordered).2.1
    exact (List.pairwise_cons.mp pair).1 e (by simp) vis
end NeemExpansion.CertifiedSidedReplay
