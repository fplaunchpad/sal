import CertifiedReplayExpansion
import CertifiedExpansion
import Sal.MRDTs.Paper1.ConcreteJoin

namespace NeemExpansion.OrderedRecords
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open Classical

structure Kit (D : MRDTSig) (Record : Type) [DecidableEq Record] where
  carrier : D.State → Finset Record
  id : Record → Nat
  Key : Type
  key : Record → Key
  insertion : Op D.AppOp → Bool
  written : Op D.AppOp → Record
  target : Op D.AppOp → Nat → Prop
  ordered : D.State → Prop
  init_carrier : carrier D.init = ∅
  init_ordered : ordered D.init
  written_id : ∀e,id (written e)=e.1
  update_provenance : ∀s e p,p∈carrier (D.update s e) →
    (insertion e=true ∧ p=written e) ∨ p∈carrier s
  update_mem : ∀s e,(∀p∈carrier s,id p≠e.1) → ∀p,
    p∈carrier (D.update s e) ↔ (insertion e=true ∧ p=written e) ∨
      (p∈carrier s ∧ ¬target e (id p))
  update_ordered : ∀s e,ordered s →
    (∀p∈carrier s,insertion e=true → key p≠key (written e)) → ordered (D.update s e)
  birth_not_killed : ∀e,insertion e=true → ¬target e (id (written e))
  merge_mem : ∀l a b,
    (∀p∈carrier a,∀q∈carrier l,id p=id q→p=q) →
    (∀p∈carrier b,∀q∈carrier l,id p=id q→p=q) →
    (∀p∈carrier a,∀q∈carrier b,id p=id q→p=q) →
    (∀p∈carrier b,∀q∈carrier a,id p=id q→p=q) → ∀p,
    p∈carrier (D.merge l a b) ↔ Certified.cell (p∈carrier l) (p∈carrier a) (p∈carrier b)
  merge_ordered : ∀l a b,ordered a → ordered b →
    (∀p∈carrier a,∀q∈carrier b,key p=key q→p=q) → ordered (D.merge l a b)
  ext : ∀s t,ordered s → ordered t → carrier s=carrier t → s=t

variable {D : MRDTSig} {Record : Type} [DecidableEq Record]
variable (K : Kit D Record)
def Born (e : Op D.AppOp) (p : Record) : Prop := K.insertion e=true ∧ p=K.written e

def ReplayEvidence (C : ReplayContext D.toUpdateSig) (H : Set (Op D.AppOp)) (s : D.State) : Prop :=
  H⊆C.events ∧ ∃xs,listPermOf xs H ∧ respects xs C.vis ∧ applySeq D.toUpdateSig D.init xs=s

structure IssuerEvidence (C : ReplayContext D.toUpdateSig) : Prop where
  creator : ∀d∈C.events,∀n,K.target d n → ∃a∈C.events,C.vis a d ∧ K.insertion a=true ∧ a.1=n
  unique_keys : ∀a∈C.events,∀b∈C.events,K.insertion a=true → K.insertion b=true →
    K.key (K.written a)=K.key (K.written b) → a.1=b.1

/-- The existing issuer's chain witnesses supply key separation through a
fixed coordinate injection, with no history invariant theorem as input. -/
structure ChainCertificate (C : ReplayContext D.toUpdateSig) (Chain : Type) where
  valid : Chain → Prop
  code : Chain → K.Key
  stamp : Chain → Nat
  injective : ∀a b,valid a → valid b → code a=code b → a=b
  witness : ∀e∈C.events,K.insertion e=true → ∃c,valid c ∧ K.key (K.written e)=code c ∧ stamp c=e.1

theorem ChainCertificate.key_unique {C : ReplayContext D.toUpdateSig} {Chain : Type}
    (cert : ChainCertificate K C Chain) :
    ∀a∈C.events,∀b∈C.events,K.insertion a=true → K.insertion b=true →
      K.key (K.written a)=K.key (K.written b) → a.1=b.1 := by
  intro a ha b hb ia ib equal
  obtain ⟨x,vx,cx,sx⟩ := cert.witness a ha ia
  obtain ⟨y,vy,cy,sy⟩ := cert.witness b hb ib
  have same := cert.injective x y vx vy (cx.symm.trans (equal.trans cy))
  exact sx.symm.trans (same ▸ sy)

theorem provenance (xs : List (Op D.AppOp)) (p : Record) :
    p∈K.carrier (applySeq D.toUpdateSig D.init xs) → ∃e∈xs,Born K e p :=
  CertifiedReplay.provenance D.update D.init (fun p s=>p∈K.carrier s) (Born K)
    (by simp [K.init_carrier]) K.update_provenance xs p

theorem replay_alive (C : ReplayContext D.toUpdateSig) (issuer : IssuerEvidence K C)
    (xs : List (Op D.AppOp)) (nodup : xs.Nodup) (support : ∀e∈xs,e∈C.events)
    (ordered : respects xs C.vis) (p : Record) :
    p∈K.carrier (applySeq D.toUpdateSig D.init xs) ↔
      (∃e∈xs,Born K e p) ∧ ∀d∈xs,¬K.target d (K.id p) := by
  apply CertifiedReplay.alive D.update D.init (fun p s=>p∈K.carrier s)
    (Born K) (fun e p=>K.target e (K.id p)) (by simp [K.init_carrier]) xs
  · intro pre e post eq p
    apply K.update_mem
    intro q hq ids
    obtain ⟨a,ha,ia,rec⟩ := provenance K pre q hq
    have ae : a=e := C.ts_unique (support a (by rw [eq]; exact List.mem_append_left _ ha))
      (support e (by rw [eq]; simp)) (by simpa [rec,K.written_id] using ids)
    subst a
    have nd : (pre++e::post).Nodup := eq ▸ nodup
    exact (List.nodup_append.mp nd).2.2 e ha e List.mem_cons_self rfl
  · intro e p birth
    rw [birth.2]
    exact K.birth_not_killed e birth.1
  · intro pre d mid e post eq p kill birth
    obtain ⟨a,ha,vis,_,stamp⟩ := issuer.creator d (support d (by rw [eq]; simp)) (K.id p) kill
    have ae : a=e := C.ts_unique ha (support e (by rw [eq]; simp))
      (stamp.trans (by rw [birth.2,K.written_id]))
    subst a
    rw [eq] at ordered
    exact (List.pairwise_cons.mp (List.pairwise_append.mp ordered).2.1).1 e (by simp) vis

theorem membership (C : ReplayContext D.toUpdateSig) (issuer : IssuerEvidence K C)
    (H : Set (Op D.AppOp)) (s : D.State) (rep : ReplayEvidence C H s) (p : Record) :
    p∈K.carrier s ↔ (∃e∈H,Born K e p) ∧ ∀d∈H,¬K.target d (K.id p) := by
  obtain ⟨support,xs,perm,ordered,fold⟩ := rep
  rw [←fold,replay_alive K C issuer xs perm.1 (fun e he=>support ((perm.2 e).mp he)) ordered p]
  simp only [perm.2]

theorem replay_ordered (C : ReplayContext D.toUpdateSig) (issuer : IssuerEvidence K C)
    (xs : List (Op D.AppOp)) (nodup : xs.Nodup) (support : ∀e∈xs,e∈C.events) :
    K.ordered (applySeq D.toUpdateSig D.init xs) := by
  induction xs using List.reverseRecOn with
  | nil => exact K.init_ordered
  | append_singleton xs e ih =>
    have prior := ih (List.nodup_append.mp nodup).1 (fun a ha=>support a (List.mem_append_left _ ha))
    change K.ordered ((xs++[e]).foldl D.update D.init)
    rw [List.foldl_append]
    apply K.update_ordered _ e prior
    intro p hp ie equal
    obtain ⟨a,ha,ia,rec⟩ := provenance K xs p hp
    have stamp := issuer.unique_keys a (support a (List.mem_append_left _ ha))
      e (support e (by simp)) ia ie (by simpa [rec] using equal)
    have same := C.ts_unique (support a (List.mem_append_left _ ha))
      (support e (by simp)) stamp
    subst a
    exact (List.nodup_append.mp nodup).2.2 e ha e (by simp) rfl

theorem represented_ordered (C : ReplayContext D.toUpdateSig) (issuer : IssuerEvidence K C)
    (H : Set (Op D.AppOp)) (s : D.State) (rep : ReplayEvidence C H s) : K.ordered s := by
  obtain ⟨sub,xs,perm,_,fold⟩ := rep
  rw [←fold]
  exact replay_ordered K C issuer xs perm.1 (fun e he=>sub ((perm.2 e).mp he))

/-- Any supported, causal-order-preserving replay permutation has the same
ordered normal form. The ambient issuer evidence is retained unchanged. -/
theorem replay_unique (C : ReplayContext D.toUpdateSig) (issuer : IssuerEvidence K C)
    (H : Set (Op D.AppOp)) (s t : D.State)
    (hs : ReplayEvidence C H s) (ht : ReplayEvidence C H t) : s=t := by
  apply K.ext s t (represented_ordered K C issuer H s hs)
    (represented_ordered K C issuer H t ht)
  apply Finset.ext
  intro p
  rw [membership K C issuer H s hs,membership K C issuer H t ht]

theorem compatible (C : ReplayContext D.toUpdateSig) (issuer : IssuerEvidence K C)
    (H J : Set (Op D.AppOp)) (s t : D.State) (hs : ReplayEvidence C H s) (ht : ReplayEvidence C J t) :
    ∀p∈K.carrier s,∀q∈K.carrier t,K.id p=K.id q→p=q := by
  intro p hp q hq ids
  obtain ⟨⟨a,ha,_,ra⟩,_⟩ := (membership K C issuer H s hs p).mp hp
  obtain ⟨⟨b,hb,_,rb⟩,_⟩ := (membership K C issuer J t ht q).mp hq
  have same := C.ts_unique (hs.1 ha) (ht.1 hb) (by simpa [ra,rb,K.written_id] using ids)
  simpa [ra,rb,same]

theorem keys_compatible (C : ReplayContext D.toUpdateSig) (issuer : IssuerEvidence K C)
    (H J : Set (Op D.AppOp)) (s t : D.State) (hs : ReplayEvidence C H s) (ht : ReplayEvidence C J t) :
    ∀p∈K.carrier s,∀q∈K.carrier t,K.key p=K.key q→p=q := by
  intro p hp q hq keys
  obtain ⟨⟨a,ha,ia,ra⟩,_⟩ := (membership K C issuer H s hs p).mp hp
  obtain ⟨⟨b,hb,ib,rb⟩,_⟩ := (membership K C issuer J t ht q).mp hq
  have stamp := issuer.unique_keys a (hs.1 ha) b (ht.1 hb) ia ib (by simpa [ra,rb] using keys)
  have same := C.ts_unique (hs.1 ha) (ht.1 hb) stamp
  simpa [ra,rb,same]

theorem merge_carrier (C : ReplayContext D.toUpdateSig) (issuer : IssuerEvidence K C)
    (L A B : Set (Op D.AppOp)) (l a b : D.State)
    (hl : ReplayEvidence C L l) (ha : ReplayEvidence C A a) (hb : ReplayEvidence C B b) :
    K.carrier (D.merge l a b)=Certified.merge (K.carrier l) (K.carrier a) (K.carrier b) := by
  apply Finset.ext
  intro p
  rw [Certified.merge_mem]
  exact K.merge_mem l a b (compatible K C issuer A L a l ha hl)
    (compatible K C issuer B L b l hb hl) (compatible K C issuer A B a b ha hb)
    (compatible K C issuer B A b a hb ha) p

theorem merged_ordered (C : ReplayContext D.toUpdateSig) (issuer : IssuerEvidence K C)
    (A B : Set (Op D.AppOp)) (l a b : D.State)
    (ha : ReplayEvidence C A a) (hb : ReplayEvidence C B b) : K.ordered (D.merge l a b) :=
  K.merge_ordered l a b (represented_ordered K C issuer A a ha)
    (represented_ordered K C issuer B b hb) (keys_compatible K C issuer A B a b ha hb)

theorem fresh (C : ReplayContext D.toUpdateSig) (issuer : IssuerEvidence K C)
    (H : Set (Op D.AppOp)) (s : D.State) (rep : ReplayEvidence C H s)
    (e : Op D.AppOp) (eligible : e∈C.events) (absent : e∉H) :
    ∀p∈K.carrier s,K.id p≠e.1 := by
  intro p hp stamp
  obtain ⟨⟨a,ha,_,rec⟩,_⟩ := (membership K C issuer H s rep p).mp hp
  have same := C.ts_unique (rep.1 ha) eligible (by simpa [rec,K.written_id] using stamp)
  exact absent (same ▸ ha)

theorem delta_evidence (C : ReplayContext D.toUpdateSig) (issuer : IssuerEvidence K C)
    (M : MetadataDependencies C) (beforeEq : ∀a b,M.before a b↔C.vis a b)
    (U : Set (Op D.AppOp)) (s B : D.State) (e : Op D.AppOp)
    (closed : M.Closed U) (member : e∈U) (eligible : e∈C.events)
    (hs : ReplayEvidence C (U\{e}) s) (hB : ReplayEvidence C (M.Past e\{e}) B) :
    Certified.DeltaEvidence (K.carrier B) (K.carrier s) (Born K e) (fun p=>K.target e (K.id p)) := by
  constructor
  · intro p birth hp
    have stamp : K.id p=e.1 := by rw [birth.2,K.written_id]
    exact fresh K C issuer _ B hB e eligible (by simp) p hp stamp
  · intro p hp kill
    obtain ⟨⟨a,ha,ia,rec⟩,noKill⟩ := (membership K C issuer _ s hs p).mp hp
    obtain ⟨birth,hbirth,vis,_,stamp⟩ := issuer.creator e eligible (K.id p) kill
    have same := C.ts_unique hbirth (hs.1 ha) (by simpa [rec,K.written_id] using stamp)
    subst birth
    apply (membership K C issuer _ B hB p).mpr
    refine ⟨⟨a,⟨Or.inr (.single ((beforeEq a e).mpr vis)),ha.2⟩,ia,rec⟩,?_⟩
    intro d hd
    exact noKill d ⟨M.past_subset U e closed member hd.1,hd.2⟩

theorem local_evidence (C : ReplayContext D.toUpdateSig) (issuer : IssuerEvidence K C)
    (M : MetadataDependencies C) (E₁ E₂ : Set (Op D.AppOp)) (l B b : D.State) (e : Op D.AppOp)
    (closed : M.Closed E₁) (member : e∈E₁) (eligible : e∈C.events) (absent : e∉E₁∩E₂)
    (hl : ReplayEvidence C (E₁∩E₂) l) (hB : ReplayEvidence C (M.Past e\{e}) B)
    (hb : ReplayEvidence C E₂ b) (d : Finset Record)
    (updated : ∀p,p∈d↔Born K e p∨(p∈K.carrier B∧¬K.target e (K.id p))) :
    Certified.LocalEvidence (K.carrier l) (K.carrier B) (K.carrier b) d := by
  constructor
  · intro p hp _ other
    obtain ⟨⟨a,ha,ia,ra⟩,_⟩ := (membership K C issuer _ B hB p).mp hp
    obtain ⟨⟨q,hq,iq,rq⟩,noKill⟩ := (membership K C issuer _ b hb p).mp other
    have same := C.ts_unique (hB.1 ha) (hb.1 hq) (by rw [←K.written_id a,←K.written_id q,←ra,←rq])
    apply (membership K C issuer _ l hl p).mpr
    exact ⟨⟨a,⟨M.past_subset E₁ e closed member ha.1,same ▸ hq⟩,ia,ra⟩,
      fun x hx=>noKill x hx.2⟩
  · intro p notB hd hlp
    have birth := ((updated p).mp hd).resolve_right (fun h=>notB h.1)
    exact fresh K C issuer _ l hl e eligible absent p hlp (by rw [birth.2,K.written_id])

/-- Complete unchanged five-VC bridge from finite carrier equations and direct
projections of existing issuance/replay evidence. All history inductions above
belong to this template, not its datatype interface. -/
theorem assemble (P : OperationPolicy D.AppOp) (R : Representation D)
    (M : ∀C:ReplayContext D.toUpdateSig,MetadataDependencies C)
    (beforeEq : ∀C a b,(M C).before a b↔C.vis a b)
    (adapter : ∀C H s,R C H s→IssuerEvidence K C ∧ ReplayEvidence C H s) :
    Raw.MergeVCs P R M := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro C E₁ E₂ l a b _ _ _ _ hl ha hb
    have issuer := (adapter C _ _ hl).1
    apply K.ext _ _ (merged_ordered K C issuer _ _ _ _ _ (adapter C _ _ ha).2 (adapter C _ _ hb).2)
      (merged_ordered K C issuer _ _ _ _ _ (adapter C _ _ hb).2 (adapter C _ _ ha).2)
    rw [merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ hl).2 (adapter C _ _ ha).2 (adapter C _ _ hb).2,
      merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ hl).2 (adapter C _ _ hb).2 (adapter C _ _ ha).2]
    exact Certified.comm _ _ _
  · intro C H s _ _ rep
    have issuer := (adapter C _ _ rep).1
    have empty : ReplayEvidence C ∅ D.init := ⟨by simp,[],⟨List.nodup_nil,by simp⟩,List.Pairwise.nil,rfl⟩
    apply K.ext _ _ (merged_ordered K C issuer _ _ _ _ _ empty (adapter C _ _ rep).2)
      (represented_ordered K C issuer H s (adapter C H s rep).2)
    rw [merge_carrier K C issuer _ _ _ _ _ _ empty empty (adapter C _ _ rep).2,K.init_carrier]
    exact Certified.initial _
  · intro C U s B e _ _ _ closed member _ _ hs hB hD hu
    have issuer := (adapter C _ _ hs).1
    have eligible := (adapter C _ _ hu).2.1 member
    have freshB := fresh K C issuer _ B (adapter C _ _ hB).2 e eligible (by simp)
    have freshS := fresh K C issuer _ s (adapter C _ _ hs).2 e eligible (by simp)
    apply K.ext _ _ (merged_ordered K C issuer _ _ _ _ _ (adapter C _ _ hs).2 (adapter C _ _ hD).2)
      (represented_ordered K C issuer _ _ (adapter C _ _ hu).2)
    rw [merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ hB).2 (adapter C _ _ hs).2 (adapter C _ _ hD).2]
    exact Certified.causal _ _ _ _ (Born K e) (fun p=>K.target e (K.id p))
      (delta_evidence K C issuer (M C) (beforeEq C) U s B e closed member eligible
        (adapter C _ _ hs).2 (adapter C _ _ hB).2)
      (K.update_mem B e freshB) (K.update_mem s e freshS)
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hD hi hm
    have issuer := (adapter C _ _ hl).1
    have eligible := (adapter C _ _ hi).2.1 member
    apply K.ext _ _ (merged_ordered K C issuer _ _ _ _ _ (adapter C _ _ hi).2 (adapter C _ _ hb).2)
      (merged_ordered K C issuer _ _ _ _ _ (adapter C _ _ hm).2 (adapter C _ _ hD).2)
    rw [merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ hl).2 (adapter C _ _ hi).2 (adapter C _ _ hb).2,
      merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ hB).2 (adapter C _ _ hm).2 (adapter C _ _ hD).2,
      merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ hB).2 (adapter C _ _ ht).2 (adapter C _ _ hD).2,
      merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ hl).2 (adapter C _ _ ht).2 (adapter C _ _ hb).2]
    exact Certified.local_redistribute _ _ _ _ _
      (local_evidence K C issuer (M C) E₁ E₂ l B b e ctx.closed₁ member eligible (fun h=>absent h.2)
        (adapter C _ _ hl).2 (adapter C _ _ hB).2 (adapter C _ _ hb).2 _
        (K.update_mem B e (fresh K C issuer _ B (adapter C _ _ hB).2 e eligible (by simp))))
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ h₀ hB h₁ h₂ hD hi₀ hi₁ hi₂ hm
    have issuer := (adapter C _ _ hB).1
    apply K.ext _ _ (merged_ordered K C issuer _ _ _ _ _ (adapter C _ _ hi₁).2 (adapter C _ _ hi₂).2)
      (merged_ordered K C issuer _ _ _ _ _ (adapter C _ _ hm).2 (adapter C _ _ hD).2)
    rw [merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ hi₀).2 (adapter C _ _ hi₁).2 (adapter C _ _ hi₂).2,
      merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ hB).2 (adapter C _ _ hm).2 (adapter C _ _ hD).2,
      merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ hB).2 (adapter C _ _ h₀).2 (adapter C _ _ hD).2,
      merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ hB).2 (adapter C _ _ h₁).2 (adapter C _ _ hD).2,
      merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ hB).2 (adapter C _ _ h₂).2 (adapter C _ _ hD).2,
      merge_carrier K C issuer _ _ _ _ _ _ (adapter C _ _ h₀).2 (adapter C _ _ h₁).2 (adapter C _ _ h₂).2]
    exact Certified.shared _ _ _ _ _
end NeemExpansion.OrderedRecords
