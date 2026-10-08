import GenericOrderedRecords
import Sal.MRDTs.Instances.FinsetStore
import Sal.MRDTs.Paper1.CertifiedRGAProducts

/-! Ordered immutable text together with two append-only evidence stores.
History projection, store replay, monotonicity and all five VC arguments belong
to this reusable product template. The instance supplies only finite text laws
and projections of its existing ambient issuance/replay evidence. -/
namespace NeemExpansion.MonotoneProduct
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT Classical
variable {Text : MRDTSig} {Record A B : Type} [DecidableEq Record] [DecidableEq A] [DecidableEq B]
abbrev product (Text : MRDTSig) (A B : Type) [DecidableEq A] [DecidableEq B] :=
  prodSig Text (prodSig (Instances.FinsetStore.D A) (Instances.FinsetStore.D B))
abbrev Norm (Record A B : Type) := Finset Record × Finset A × Finset B
variable (K : OrderedRecords.Kit Text Record)
def normalize (s : (product Text A B).State) : Norm Record A B := (K.carrier s.1,s.2)
def unite (s t : Norm Record A B) : Norm Record A B := (s.1∪t.1,s.2.1∪t.2.1,s.2.2∪t.2.2)

structure Evidence (C : ReplayContext (product Text A B).toUpdateSig)
    (H : Set (Op (product Text A B).AppOp)) (s : (product Text A B).State) : Prop where
  issuer : OrderedRecords.IssuerEvidence K (projReplayContext₁ C)
  native : ∀e∈(projReplayContext₁ C).events,∀n,¬K.target e n
  replay : OrderedRecords.ReplayEvidence C H s

theorem text_replay (C : ReplayContext (product Text A B).toUpdateSig)
    (H : Set (Op (product Text A B).AppOp)) (s : (product Text A B).State)
    (rep : Evidence K C H s) :
    OrderedRecords.ReplayEvidence (projReplayContext₁ C) (evRes₁ H) s.1 := by
  obtain ⟨sub,xs,perm,ordered,fold⟩ := rep.replay
  refine ⟨?_,projList₁ xs,listPermOf_projList₁ perm,?_,?_⟩
  · intro a ha
    exact mem_projReplayContext₁_events.mpr (sub ha)
  · exact respects_projList₁_of (fun _ _ h=>h) ordered
  · have f := congrArg Prod.fst fold
    simpa only [applySeq_prod] using f

theorem text_membership (C : ReplayContext (product Text A B).toUpdateSig)
    (H : Set (Op (product Text A B).AppOp)) (s : (product Text A B).State)
    (rep : Evidence K C H s) (p : Record) :
    p∈K.carrier s.1 ↔ ∃e∈evRes₁ H,OrderedRecords.Born K e p := by
  rw [OrderedRecords.membership K _ rep.issuer _ _ (text_replay K C H s rep) p]
  constructor
  · exact And.left
  · intro born
    exact ⟨born,fun d hd=>rep.native d ((text_replay K C H s rep).1 hd) (K.id p)⟩

theorem store_fold_mem {V : Type} [DecidableEq V] (s : Finset V) (xs : List (Op V)) (p : V) :
    p∈(show Finset V from applySeq (Instances.FinsetStore.D V).toUpdateSig s xs) ↔ p∈s ∨ ∃e∈xs,p=e.op := by
  induction xs generalizing s with
  | nil => simp [applySeq]
  | cons e xs ih =>
    change p∈(show Finset V from applySeq (Instances.FinsetStore.D V).toUpdateSig (insert e.op s : Finset V) xs) ↔ _
    rw [ih]
    simp only [Finset.mem_insert,List.mem_cons]
    aesop

theorem stores_membership (C : ReplayContext (product Text A B).toUpdateSig)
    (H : Set (Op (product Text A B).AppOp)) (s : (product Text A B).State)
    (rep : Evidence K C H s) :
    (∀p:A,p∈(show Finset A from s.2.1)↔∃e∈evRes₁ (evRes₂ H),p=e.op) ∧
    (∀p:B,p∈(show Finset B from s.2.2)↔∃e∈evRes₂ (evRes₂ H),p=e.op) := by
  obtain ⟨_,xs,perm,_,fold⟩ := rep.replay
  constructor
  · intro p
    have f := congrArg (fun s:(product Text A B).State=>s.2.1) fold
    simp only [applySeq_prod] at f
    rw [←f,store_fold_mem]
    have perm' := listPermOf_projList₁ (listPermOf_projList₂ perm)
    simp only [prodSig,Instances.FinsetStore.D,Finset.notMem_empty,false_or]
    exact exists_congr (fun e=>and_congr_left (fun _=>perm'.2 e))
  · intro p
    have f := congrArg (fun s:(product Text A B).State=>s.2.2) fold
    simp only [applySeq_prod] at f
    rw [←f,store_fold_mem]
    have perm' := listPermOf_projList₂ (listPermOf_projList₂ perm)
    simp only [prodSig,Instances.FinsetStore.D,Finset.notMem_empty,false_or]
    exact exists_congr (fun e=>and_congr_left (fun _=>perm'.2 e))

theorem mono (C : ReplayContext (product Text A B).toUpdateSig)
    (H J : Set (Op (product Text A B).AppOp)) (s t : (product Text A B).State)
    (hs : Evidence K C H s) (ht : Evidence K C J t) (sub : H⊆J) :
    (normalize K s).1⊆(normalize K t).1 ∧ (normalize K s).2.1⊆(normalize K t).2.1 ∧
      (normalize K s).2.2⊆(normalize K t).2.2 := by
  refine ⟨?_,?_,?_⟩
  · intro p hp
    obtain ⟨e,he,birth⟩ := (text_membership K C H s hs p).mp hp
    exact (text_membership K C J t ht p).mpr ⟨e,sub he,birth⟩
  · intro p hp
    obtain ⟨e,he,eq⟩ := (stores_membership K C H s hs).1 p |>.mp hp
    exact (stores_membership K C J t ht).1 p |>.mpr ⟨e,sub he,eq⟩
  · intro p hp
    obtain ⟨e,he,eq⟩ := (stores_membership K C H s hs).2 p |>.mp hp
    exact (stores_membership K C J t ht).2 p |>.mpr ⟨e,sub he,eq⟩

theorem sorted (C : ReplayContext (product Text A B).toUpdateSig)
    (H : Set (Op (product Text A B).AppOp)) (s : (product Text A B).State)
    (rep : Evidence K C H s) : K.ordered s.1 :=
  OrderedRecords.represented_ordered K _ rep.issuer _ _ (text_replay K C H s rep)

theorem merge_sorted (C : ReplayContext (product Text A B).toUpdateSig)
    (H J : Set (Op (product Text A B).AppOp)) (l a b : (product Text A B).State)
    (ha : Evidence K C H a) (hb : Evidence K C J b) : K.ordered ((product Text A B).merge l a b).1 :=
  OrderedRecords.merged_ordered K _ ha.issuer _ _ l.1 a.1 b.1
    (text_replay K C H a ha) (text_replay K C J b hb)

theorem eq_of_normalize (s t : (product Text A B).State)
    (hs : K.ordered s.1) (ht : K.ordered t.1) (eq : normalize K s=normalize K t) : s=t := by
  apply Prod.ext
  · exact K.ext _ _ hs ht (congrArg Prod.fst eq)
  · exact congrArg (fun n:Norm Record A B=>n.2) eq

theorem normalize_merge (C : ReplayContext (product Text A B).toUpdateSig)
    (L H J : Set (Op (product Text A B).AppOp)) (l a b : (product Text A B).State)
    (hl : Evidence K C L l) (ha : Evidence K C H a) (hb : Evidence K C J b)
    (left : L⊆H) (right : L⊆J) :
    normalize K ((product Text A B).merge l a b)=unite (normalize K a) (normalize K b) := by
  apply Prod.ext
  · change K.carrier (Text.merge l.1 a.1 b.1)=K.carrier a.1∪K.carrier b.1
    rw [OrderedRecords.merge_carrier K _ hl.issuer _ _ _ l.1 a.1 b.1
      (text_replay K C L l hl) (text_replay K C H a ha) (text_replay K C J b hb)]
    have le := (mono K C L H l a hl ha left).1
    have re := (mono K C L J l b hl hb right).1
    ext p
    have hle := le (a:=p)
    have hre := re (a:=p)
    simp only [Certified.merge_mem,Certified.cell,Finset.mem_union]
    tauto
  · rfl

def textStep (s : Finset Record) (e : Op Text.AppOp) : Finset Record :=
  if K.insertion e then insert (K.written e) s else s

def step (s : Norm Record A B) (e : Op (product Text A B).AppOp) : Norm Record A B :=
  match e.op with
  | .inl op => (textStep K s.1 (e.1,e.2.1,op),s.2)
  | .inr (.inl p) => (s.1,insert p s.2.1,s.2.2)
  | .inr (.inr p) => (s.1,s.2.1,insert p s.2.2)

theorem normalize_update (C : ReplayContext (product Text A B).toUpdateSig)
    (H : Set (Op (product Text A B).AppOp)) (s : (product Text A B).State)
    (rep : Evidence K C H s) (e : Op (product Text A B).AppOp)
    (eligible : e∈C.events) (absent : e∉H) :
    normalize K ((product Text A B).update s e)=step K (normalize K s) e := by
  rcases e with ⟨t,r,op|op⟩
  · apply Prod.ext
    · have fresh := OrderedRecords.fresh K _ rep.issuer _ _ (text_replay K C H s rep)
        (t,r,op) (mem_projReplayContext₁_events.mpr eligible) absent
      change K.carrier (Text.update s.1 (t,r,op))=textStep K (K.carrier s.1) (t,r,op)
      ext p
      rw [K.update_mem _ _ fresh]
      have alive := rep.native (t,r,op) (mem_projReplayContext₁_events.mpr eligible) (K.id p)
      cases hi:K.insertion (t,r,op) <;> simp [textStep,hi,alive]
    · rfl
  · cases op <;> rfl

theorem step_union (s b : Norm Record A B) (e : Op (product Text A B).AppOp)
    (sub : b.1⊆s.1 ∧ b.2.1⊆s.2.1 ∧ b.2.2⊆s.2.2) :
    unite s (step K b e)=step K s e := by
  rcases e with ⟨t,r,op|op⟩
  · apply Prod.ext
    · ext p
      have h : p∈b.1→p∈s.1 := fun hp=>sub.1 hp
      simp only [unite,step,textStep,Op.op]
      split <;> simp only [Finset.mem_union,Finset.mem_insert] <;> tauto
    · apply Prod.ext (Finset.union_eq_left.mpr sub.2.1) (Finset.union_eq_left.mpr sub.2.2)
  · cases op with
    | inl p =>
      apply Prod.ext (Finset.union_eq_left.mpr sub.1)
      apply Prod.ext
      · ext q
        have h : q∈b.2.1→q∈s.2.1 := fun hp=>sub.2.1 hp
        simp only [unite,step,Op.op,Finset.mem_union,Finset.mem_insert]
        tauto
      · exact Finset.union_eq_left.mpr sub.2.2
    | inr p =>
      apply Prod.ext (Finset.union_eq_left.mpr sub.1)
      apply Prod.ext (Finset.union_eq_left.mpr sub.2.1)
      ext q
      have h : q∈b.2.2→q∈s.2.2 := fun hp=>sub.2.2 hp
      simp only [unite,step,Op.op,Finset.mem_union,Finset.mem_insert]
      tauto
theorem initial (C : ReplayContext (product Text A B).toUpdateSig)
    (H : Set (Op (product Text A B).AppOp)) (s : (product Text A B).State)
    (rep : Evidence K C H s) : Evidence K C ∅ (product Text A B).init :=
  ⟨rep.issuer,rep.native,by simp,[],⟨List.nodup_nil,by simp⟩,List.Pairwise.nil,rfl⟩

theorem assemble (P : OperationPolicy (product Text A B).AppOp)
    (R : Representation (product Text A B))
    (M : ∀C,MetadataDependencies C)
    (adapter : ∀C H s,R C H s→Evidence K C H s) : Raw.MergeVCs P R M := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro C E₁ E₂ l a b _ _ _ _ hl ha hb
    have hl := adapter C _ _ hl
    have ha := adapter C _ _ ha
    have hb := adapter C _ _ hb
    apply eq_of_normalize K _ _ (merge_sorted K C _ _ l a b ha hb)
      (merge_sorted K C _ _ l b a hb ha)
    rw [normalize_merge K C _ _ _ l a b hl ha hb Set.inter_subset_left Set.inter_subset_right,
      normalize_merge K C _ _ _ l b a hl hb ha Set.inter_subset_right Set.inter_subset_left]
    simp [unite,Finset.union_comm]
  · intro C H s _ _ rep
    have rep := adapter C _ _ rep
    apply eq_of_normalize K _ _ (merge_sorted K C _ _ _ _ _ (initial K C H s rep) rep)
      (sorted K C H s rep)
    rw [normalize_merge K C _ _ _ _ _ s (initial K C H s rep) (initial K C H s rep) rep
      (by simp) (by simp)]
    simp [normalize,unite,product,prodSig,Instances.FinsetStore.D,K.init_carrier]
  · intro C U s B e _ _ _ closed member _ _ hs hB hD hu
    have hs := adapter C _ _ hs
    have hB := adapter C _ _ hB
    have hD := adapter C _ _ hD
    have hu := adapter C _ _ hu
    have pastSub := (M C).past_subset U e closed member
    have sub : (M C).Past e \ {e} ⊆ U \ {e} := fun _ h => ⟨pastSub h.1,h.2⟩
    have he := hu.replay.1 member
    apply eq_of_normalize K _ _ (merge_sorted K C _ _ B s _ hs hD) (sorted K C U _ hu)
    rw [normalize_merge K C _ _ _ B s _ hB hs hD sub Set.diff_subset,
      normalize_update K C _ B hB e he (by simp),normalize_update K C _ s hs e he (by simp)]
    exact step_union K _ _ e (mono K C _ _ B s hB hs sub)
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hD hi hm
    have hl := adapter C _ _ hl
    have hB := adapter C _ _ hB
    have ht := adapter C _ _ ht
    have hb := adapter C _ _ hb
    have hD := adapter C _ _ hD
    have hi := adapter C _ _ hi
    have hm := adapter C _ _ hm
    have pastSub := (M C).past_subset E₁ e ctx.closed₁ member
    have pb : (M C).Past e \ {e} ⊆ E₁ \ {e} := fun _ h => ⟨pastSub h.1,h.2⟩
    have pu : (M C).Past e \ {e} ⊆ (E₁ ∪ E₂) \ {e} := fun _ h => ⟨Or.inl (pastSub h.1),h.2⟩
    have lt : E₁ ∩ E₂ ⊆ E₁ \ {e} := by
      intro x h; exact ⟨h.1,fun eq => absent (eq ▸ h.2)⟩
    apply eq_of_normalize K _ _ (merge_sorted K C _ _ l _ b hi hb)
      (merge_sorted K C _ _ B _ _ hm hD)
    rw [normalize_merge K C _ _ _ l _ b hl hi hb Set.inter_subset_left Set.inter_subset_right,
      normalize_merge K C _ _ _ B _ _ hB hm hD pu Set.diff_subset,
      normalize_merge K C _ _ _ B t _ hB ht hD pb Set.diff_subset,
      normalize_merge K C _ _ _ l t b hl ht hb lt Set.inter_subset_right]
    simp [unite,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]
  · intro C E₁ E₂ t₀ t₁ t₂ B e ctx m₁ m₂ h₀ hB h₁ h₂ hD hi₀ hi₁ hi₂ hm
    have h₀ := adapter C _ _ h₀
    have hB := adapter C _ _ hB
    have h₁ := adapter C _ _ h₁
    have h₂ := adapter C _ _ h₂
    have hD := adapter C _ _ hD
    have hi₀ := adapter C _ _ hi₀
    have hi₁ := adapter C _ _ hi₁
    have hi₂ := adapter C _ _ hi₂
    have hm := adapter C _ _ hm
    have p₁ := (M C).past_subset E₁ e ctx.closed₁ m₁
    have p₂ := (M C).past_subset E₂ e ctx.closed₂ m₂
    have pu : (M C).Past e \ {e} ⊆ (E₁ ∪ E₂) \ {e} := fun _ h => ⟨Or.inl (p₁ h.1),h.2⟩
    apply eq_of_normalize K _ _ (merge_sorted K C _ _ _ _ _ hi₁ hi₂)
      (merge_sorted K C _ _ B _ _ hm hD)
    rw [normalize_merge K C _ _ _ _ _ _ hi₀ hi₁ hi₂ Set.inter_subset_left Set.inter_subset_right,
      normalize_merge K C _ _ _ B _ _ hB hm hD pu Set.diff_subset,
      normalize_merge K C _ _ _ B t₁ _ hB h₁ hD (fun _ h => ⟨p₁ h.1,h.2⟩) Set.diff_subset,
      normalize_merge K C _ _ _ B t₂ _ hB h₂ hD (fun _ h => ⟨p₂ h.1,h.2⟩) Set.diff_subset,
      normalize_merge K C _ _ _ t₀ t₁ t₂ h₀ h₁ h₂ (fun _ h => ⟨h.1.1,h.2⟩) (fun _ h => ⟨h.1.2,h.2⟩)]
    simp [unite,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]


end NeemExpansion.MonotoneProduct
