import CertifiedReplayExpansion
import Sal.MRDTs.Paper1.ConcreteJoin

/-! Generic issuance evidence from a finite preservation certificate.
Archive membership and live provenance establish the issuer's local premise;
causal timestamp decrease supplies the well-founded mint induction. -/
namespace NeemExpansion.CertifiedIssuance
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1

structure Model (D : MRDTSig) (Record Live : Type) [DecidableEq Record] where
  archive : D.State → Finset Record
  live : D.State → Finset Live
  record : Op D.AppOp → Record
  written : Op D.AppOp → Live
  insertion : Op D.AppOp → Bool
  marked : Record → Bool
  stamp : Record → Nat
  id : Live → Nat
  valid : Record → Prop
  guard : Op D.AppOp → D.State → Prop
  target : Op D.AppOp → Nat → Prop
  initial_archive : archive D.init = ∅
  initial_live : live D.init = ∅
  archive_step : ∀s e g,g∈archive (D.update s e) ↔
    (insertion e=true ∧ g=record e) ∨ g∈archive s
  live_step : ∀s e p,p∈live (D.update s e) →
    (insertion e=true ∧ p=written e) ∨ p∈live s
  record_stamp : ∀e,stamp (record e)=e.1
  record_marked : ∀e,marked (record e)=insertion e
  written_id : ∀e,id (written e)=e.1
  issue_valid : ∀s e,guard e s → (∀g∈archive s,valid g) →
    (∀p∈live s,∃g∈archive s,marked g=true ∧ stamp g=id p) → valid (record e)
  issue_target : ∀s e,guard e s → ∀n,target e n → n=0 ∨ ∃p∈live s,id p=n

variable {D : MRDTSig} {Record Live : Type} [DecidableEq Record]
variable (K : Model D Record Live)

theorem archive_membership (xs : List (Op D.AppOp)) (g : Record) :
    g∈K.archive (applySeq D.toUpdateSig D.init xs) ↔ ∃e∈xs,K.insertion e=true ∧ g=K.record e := by
  induction xs using List.reverseRecOn with
  | nil => simp [applySeq,K.initial_archive]
  | append_singleton xs e ih =>
    rw [applySeq_append_single,K.archive_step,ih]
    simp only [List.mem_append,List.mem_singleton]
    constructor
    · rintro (⟨ins,eq⟩ | ⟨a,ha,ins,eq⟩)
      · exact ⟨e,Or.inr rfl,ins,eq⟩
      · exact ⟨a,Or.inl ha,ins,eq⟩
    · rintro ⟨a,ha,ins,eq⟩
      rcases ha with old | rfl
      · exact Or.inr ⟨a,old,ins,eq⟩
      · exact Or.inl ⟨ins,eq⟩

theorem provenance (xs : List (Op D.AppOp)) (p : Live) :
    p∈K.live (applySeq D.toUpdateSig D.init xs) → ∃e∈xs,K.insertion e=true ∧ p=K.written e :=
  CertifiedReplay.provenance D.update D.init (fun p s=>p∈K.live s)
    (fun e p=>K.insertion e=true ∧ p=K.written e) (by simp [K.initial_live]) K.live_step xs p

theorem live_recorded (xs : List (Op D.AppOp)) :
    ∀p∈K.live (applySeq D.toUpdateSig D.init xs),
      ∃g∈K.archive (applySeq D.toUpdateSig D.init xs),K.marked g=true ∧ K.stamp g=K.id p := by
  intro p hp
  obtain ⟨e,he,ins,eq⟩ := provenance K xs p hp
  exact ⟨K.record e,(archive_membership K xs _).mpr ⟨e,he,ins,rfl⟩,
    (K.record_marked e).trans ins,by rw [eq,K.record_stamp,K.written_id]⟩

theorem valid_of_mint (C : Configuration D) (mint : MintHonest D K.guard C) :
    ∀e∈C.events,K.valid (K.record e) := by
  have main : ∀t,∀e:Op D.AppOp,e.1=t → e∈C.events → K.valid (K.record e) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro e time eligible
      obtain ⟨xs,perm,_,issued⟩ := mint e eligible
      apply K.issue_valid _ e issued
      · intro g hg
        obtain ⟨a,ha,_,eq⟩ := (archive_membership K xs g).mp hg
        have prior := (perm.2 a).mp ha
        rw [eq]
        exact ih a.1 (by rw [←time]; exact C.causal_mono prior.2) a rfl prior.1
      · exact live_recorded K xs
  exact fun e he=>main e.1 e rfl he

theorem target_of_mint (C : Configuration D) (mint : MintHonest D K.guard C)
    (e : Op D.AppOp) (eligible : e∈C.events) (n : Nat) (target : K.target e n) :
    n=0 ∨ ∃a∈C.events,C.vis a e ∧ K.insertion a=true ∧ a.1=n := by
  obtain ⟨xs,perm,_,issued⟩ := mint e eligible
  rcases K.issue_target _ e issued n target with zero | ⟨p,hp,id⟩
  · exact Or.inl zero
  · obtain ⟨a,ha,ins,eq⟩ := provenance K xs p hp
    have prior := (perm.2 a).mp ha
    exact Or.inr ⟨a,prior.1,prior.2,ins,by rw [eq,K.written_id] at id; exact id⟩
end NeemExpansion.CertifiedIssuance
