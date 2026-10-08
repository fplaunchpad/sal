import CertifiedReplayExpansion

namespace NeemExpansion.CertifiedEmbeddedReplay
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Sal.MRDTs.Instances.EmbedRGA
variable {α : Type} [DecidableEq α] [Inhabited α]

def Born (Γ : OrderedPrefixCode) (e : Op (EOp α)) (p : (ERec α)) := eIsIns e = true ∧ p = eRecOf Γ e
def Kill (e : Op (EOp α)) (p : (ERec α)) := e.2.2 = .del p.1

theorem update_provenance (Γ : OrderedPrefixCode) (s : (EState α)) (e : Op (EOp α)) (p : (ERec α)) :
    p ∈ eUpdate Γ s e → Born Γ e p ∨ p ∈ s := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | del x => simp only [eUpdate,List.mem_filter]; tauto
  | ins x pref a =>
    simp only [eUpdate]
    split
    · exact Or.inr
    · rw [mem_eInsert]
      intro h
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl ⟨rfl,h⟩

theorem provenance (Γ : OrderedPrefixCode) (xs : List (Op (EOp α))) (p : (ERec α)) :
    p ∈ eFold Γ xs → ∃ e ∈ xs, Born Γ e p :=
  CertifiedReplay.provenance (eUpdate Γ) [] (fun p s => p ∈ s) (Born Γ)
    (by simp) (update_provenance Γ) xs p

theorem step_membership (Γ : OrderedPrefixCode) (s : (EState α)) (e : Op (EOp α))
    (fresh : e.1 ∉ eIds s) (p : (ERec α)) :
    p ∈ eUpdate Γ s e ↔ Born Γ e p ∨ (p ∈ s ∧ ¬Kill e p) := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | del x => simp [eUpdate,Born,Kill,eIsIns]; tauto
  | ins x pref a =>
    simp only [eUpdate,if_neg fresh,mem_eInsert]
    simp [Born,Kill,eIsIns,eRecOf,eCoord]
    tauto

theorem membership (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (honest : EHonestCore Γ C) (xs : List (Op (EOp α))) (nodup : xs.Nodup)
    (support : ∀ e ∈ xs, e ∈ C.events) (ordered : respects xs C.vis) (p : (ERec α)) :
    p ∈ eFold Γ xs ↔ (∃ e ∈ xs, Born Γ e p) ∧ ∀ d ∈ xs, ¬Kill d p := by
  apply CertifiedReplay.alive (eUpdate Γ) [] (fun p s => p ∈ s) (Born Γ) Kill (by simp) xs
  · intro pre e post eq p
    apply step_membership
    intro hid
    obtain ⟨q,hq,id⟩ := List.mem_map.mp hid
    obtain ⟨birth,hb,_,rec⟩ := provenance Γ pre q hq
    have hbAll : birth ∈ xs := by rw [eq]; exact List.mem_append_left _ hb
    have heAll : e ∈ xs := by rw [eq]; simp
    have same : birth = e := C.ts_unique (support birth hbAll) (support e heAll)
      (by simpa only [rec,eRecOf] using id)
    subst birth
    have nd : (pre ++ e :: post).Nodup := eq ▸ nodup
    have dis := (List.nodup_append.mp nd).2.2
    exact dis e hb e (List.mem_cons_self) rfl
  · intro e p hb
    rcases e with ⟨t,r,op⟩
    cases op <;> simp_all [Born,Kill,eIsIns]
  · intro pre d mid e post eq p hk hb
    obtain ⟨birth,hbirth,vis,time,_⟩ := honest.del_has_ins d
      (support d (by rw [eq]; simp)) p.1 hk
    have same : birth = e := C.ts_unique hbirth (support e (by rw [eq]; simp))
      (time.trans (by simpa only [hb.2,eRecOf] using (rfl : p.1 = p.1)))
    subst birth
    rw [eq] at ordered
    have pair := (List.pairwise_append.mp ordered).2.1
    exact (List.pairwise_cons.mp pair).1 e (by simp) vis
end NeemExpansion.CertifiedEmbeddedReplay
