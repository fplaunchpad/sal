import Sal.MRDTs.Instances.FugueMaxContract
import Sal.MRDTs.Paper1.CertifiedHistoryDecoding
import Mathlib.Data.List.Permutation

namespace Sal.MRDTs.Paper1.CertifiedFugueRawOrderObstruction
open Foundation Sal.EmbedRGA
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax
abbrev RGAM := datatype unaryCode
abbrev Event := Op Payload
abbrev V := Fin 4
abbrev R := Fin 1
abbrev I := Fin 3

def seed : MRec := ⟨1,0,.ins 0 .R,0,none,[.R [0] 1]⟩
def deletion : MRec := ⟨2,0,.del 1,0,none,[]⟩
def replacement : MRec := ⟨3,0,.ins 1 .L,0,some 1,[.R [0] 1,.L 2]⟩
def event (i : I) : Event := eventOf (match i.val with | 0 => seed | 1 => deletion | _ => replacement)
def state (v : V) : State := match v.val with
  | 0 => ⟨[],∅⟩
  | 1 => ⟨[(1,1,fmCoordOf unaryCode seed.chain)],{seed}⟩
  | 2 => ⟨[],{seed}⟩
  | _ => ⟨[(3,3,fmCoordOf unaryCode replacement.chain)],{seed,replacement}⟩

theorem original_preparation :
    prepareInsert unaryCode ⟨[],[]⟩ 0 1 0 = seed ∧
    prepareDelete ⟨(state 1).live,[seed]⟩ 0 2 0 = deletion ∧
    prepareInsert unaryCode ⟨[],[seed]⟩ 0 3 0 = replacement ∧
    replacement.op ≠ .ins 0 .R := by decide +kernel

theorem original_guards :
    applicable unaryCode (event 0) (state 0) ∧
    applicable unaryCode (event 1) (state 1) ∧
    applicable unaryCode (event 2) (state 2) := by
  refine ⟨⟨[],?_,?_⟩,⟨[seed],?_,?_⟩,⟨[seed],?_,?_⟩⟩ <;> decide +kernel

def indices (v : V) : Finset I := match v.val with
  | 0 => ∅ | 1 => {0} | 2 => {0,1} | _ => Finset.univ
def records (v : V) : RGAM.State × Finset I := (state v,indices v)
def parentList (v : V) : List V := match v.val with
  | 0 => [] | 1 => [0] | 2 => [1] | _ => [2]
def parentTable (v : V) : Finset V := (parentList v).toFinset

private theorem parentList_mem (v p : V) :
    p ∈ parentList v ↔ p ∈ parentTable v := by simp [parentTable]

def ancestors (v : V) : Finset V := Finset.univ.filter (fun w => w.val≤v.val)
def heads (k : V) (_ : R) : Option V := some k

def issued (k : V) (i : I) : Prop := i.val < k.val
instance (k : V) (i : I) : Decidable (issued k i) := by unfold issued; infer_instance

def past (i : I) : Finset I := Finset.univ.filter (fun j => j.val < i.val)
def visIndex (k : V) (i j : I) : Prop := issued k j ∧ i∈past j
instance (k : V) (i j : I) : Decidable (visIndex k i j) := by unfold visIndex; infer_instance

def vis (k : V) (a b : Event) : Prop := ∃i j:I,a=event i ∧ b=event j ∧ visIndex k i j
instance (k : V) (a b : Event) : Decidable (vis k a b) := by unfold vis; infer_instance

private theorem parent_rank : ∀ v p : V, p ∈ parentTable v → p.val < v.val := by decide
private theorem ancestor_refl : ∀ v : V, v ∈ ancestors v := by decide
private theorem ancestor_trans : ∀ a b c : V,
    a ∈ ancestors b → b ∈ ancestors c → a ∈ ancestors c := by decide
private theorem parent_ancestor : ∀ v p : V, p ∈ parentTable v → p ∈ ancestors v := by decide
private theorem ancestor_step : ∀ a b : V, a ∈ ancestors b →
    a = b ∨ ∃ p ∈ parentTable b, a ∈ ancestors p := by decide
private theorem head_bound : ∀ k : V, ∀ r : R, ∀ v : V,
    heads k r = some v → v.val ≤ k.val := by decide
private theorem record_issued : ∀ k v : V, v.val ≤ k.val →
    ∀ i ∈ (records v).2, issued k i := by decide
private theorem origin_present : ∀ k : V, ∀ i : I, issued k i →
    ∃ v : V, heads k ⟨(event i).2.1, by fin_cases i <;> decide⟩ = some v ∧
      i ∈ (records v).2 := by decide
private theorem record_causal : ∀ v : V, ∀ i j : I,
    j ∈ indices v → i ∈ past j → i ∈ indices v := by decide
private theorem past_issued : ∀ k : V, ∀ i j : I,
    visIndex k i j → issued k i := by decide
private theorem same_replica : ∀ k : V, ∀ i j : I,
    issued k i → issued k j → i ≠ j → (event i).2.1 = (event j).2.1 →
      visIndex k i j ∨ visIndex k j i := by decide
private theorem index_mono : ∀ k : V, ∀ i j : I,
    visIndex k i j → (event i).time < (event j).time := by decide
private theorem gca_record : ∀ a b c : V,
    c ∈ ancestors a → c ∈ ancestors b →
    (∀ w : V, w ∈ ancestors a → w ∈ ancestors b → w ∈ ancestors c) →
    (records c).2 = (records a).2 ∩ (records b).2 := by decide

private theorem event_injective : Function.Injective event := by
  intro i j h
  have time : ∀ i : I, (event i).1 = i.val + 1 := by intro i; fin_cases i <;> rfl
  have ht := congrArg Prod.fst h
  rw [time,time] at ht
  exact Fin.ext (Nat.add_right_cancel ht)

def ver (k : V) (v : Nat) : Option (RGAM.State × Set Event) :=
  if h : v < 4 ∧ v ≤ k.val then
    some ((records ⟨v,h.1⟩).1, ↑((records ⟨v,h.1⟩).2.image event)) else none

def head (k : V) (r : Nat) : Option Nat :=
  if h : r < 1 then (heads k ⟨r,h⟩).map Fin.val else none

def parents (k : V) (v : Nat) : List Nat :=
  if h : v < 4 ∧ v ≤ k.val then (parentList ⟨v,h.1⟩).map Fin.val else []

private theorem ver_cases {k : V} {v : Nat} {s : RGAM.State} {E : Set Event}
    (h : ver k v = some (s,E)) :
    ∃ w : V, w.val = v ∧ w.val ≤ k.val ∧ s = (records w).1 ∧
      E = ↑((records w).2.image event) := by
  unfold ver at h
  split at h
  · rename_i hb
    have he := Option.some.inj h
    exact ⟨⟨v,hb.1⟩, rfl, hb.2, (congrArg Prod.fst he).symm,
      (congrArg Prod.snd he).symm⟩
  · simp at h

private theorem head_cases {k : V} {r v : Nat} (h : head k r = some v) :
    ∃ rr : R, ∃ w : V, rr.val = r ∧ w.val = v ∧ heads k rr = some w := by
  unfold head at h
  split at h
  · rename_i hr
    obtain ⟨w, hw, hv⟩ := Option.map_eq_some_iff.mp h
    exact ⟨⟨r,hr⟩, w, rfl, hv, hw⟩
  · simp at h

private theorem parent_cases {k : V} {v p : Nat} (h : p ∈ parents k v) :
    ∃ vv pp : V, vv.val = v ∧ pp.val = p ∧ vv.val ≤ k.val ∧ pp ∈ parentTable vv := by
  unfold parents at h
  split at h
  · rename_i hb
    obtain ⟨pp, hp, he⟩ := List.mem_map.mp h
    exact ⟨⟨v,hb.1⟩, pp, rfl, he, hb.2, by simpa only [parentList_mem] using hp⟩
  · simp at h

private theorem parents_rank (k : V) : ∀ v p, p ∈ parents k v → p < v := by
  intro v p hp
  obtain ⟨vv, pp, rfl, rfl, _, hp⟩ := parent_cases hp
  exact parent_rank vv pp hp

private def NatAncestor (a b : Nat) : Prop :=
  a = b ∨ ∃ aa bb : V, aa.val = a ∧ bb.val = b ∧ aa ∈ ancestors bb

private theorem natAncestor_trans {a b c : Nat}
    (hab : NatAncestor a b) (hbc : NatAncestor b c) : NatAncestor a c := by
  rcases hab with rfl | ⟨aa, bb, rfl, rfl, hab⟩
  · exact hbc
  · rcases hbc with heq | ⟨bb', cc, heq, rfl, hbc⟩
    · exact Or.inr ⟨aa, bb, rfl, heq, hab⟩
    · have hbb : bb' = bb := Fin.ext heq
      subst bb'
      exact Or.inr ⟨aa, cc, rfl, rfl, ancestor_trans aa bb cc hab hbc⟩

private theorem reaches_sound {k : V} {a b : V}
    (h : Reaches (parents k) a.val b.val) : a ∈ ancestors b := by
  have gen : ∀ {m n : Nat}, Reaches (parents k) m n → NatAncestor m n := by
    intro m n hr
    induction hr with
    | refl => exact Or.inl rfl
    | @tail mid c _ hmc ih =>
        obtain ⟨vv, pp, rfl, rfl, _, hp⟩ := parent_cases hmc
        exact natAncestor_trans ih (Or.inr ⟨pp,vv,rfl,rfl,parent_ancestor vv pp hp⟩)
  have hs := gen h
  rcases hs with heq | ⟨aa,bb,ha,hb,hmem⟩
  · have hab : a = b := Fin.ext heq
    subst a; exact ancestor_refl b
  · have haa : aa = a := Fin.ext ha
    have hbb : bb = b := Fin.ext hb
    simpa only [haa,hbb] using hmem

private theorem reaches_complete (k : V) (a b : V) (hb : b.val ≤ k.val)
    (h : a ∈ ancestors b) : Reaches (parents k) a.val b.val := by
  suffices go : ∀ b : V, b.val ≤ k.val → a ∈ ancestors b → Reaches (parents k) a.val b.val by
    exact go b hb h
  intro b
  induction b using (measure Fin.val).wf.induction with
  | h b ih =>
      intro hb h
      rcases ancestor_step a b h with heq | ⟨p,hp,hap⟩
      · subst a; exact .refl
      · have hpb := parent_rank b p hp
        have hpath := ih p hpb (Nat.le_trans (Nat.le_of_lt hpb) hb) hap
        apply hpath.tail
        simp only [parents, b.isLt, hb, and_self, dite_true]
        apply List.mem_map.mpr
        exact ⟨p, (parentList_mem b p).mpr hp, rfl⟩

private theorem headEvents_cases {k : V} {r : Nat} {E : Set Event}
    (h : headEventsFrom (D := RGAM) (ver k) (head k) r = some E) :
    ∃ rr : R, ∃ w : V, heads k rr = some w ∧ E = ↑((records w).2.image event) := by
  unfold headEventsFrom at h
  cases hh : head k r with
  | none => simp [hh] at h
  | some v =>
      obtain ⟨rr,w,_,rfl,hw⟩ := head_cases hh
      have hv : ver k w.val = some ((records w).1, ↑((records w).2.image event)) := by
        simp [ver, w.isLt, head_bound k rr w hw]
      simp [Option.bind, hh, hv] at h
      exact ⟨rr,w,hw,by simpa using h.symm⟩

private theorem support_event {k : V} {r : Nat} {E : Set Event} {e : Event}
    (hE : headEventsFrom (D := RGAM) (ver k) (head k) r = some E) (he : e ∈ E) :
    ∃ i : I, e = event i ∧ issued k i := by
  obtain ⟨rr,w,hw,rfl⟩ := headEvents_cases hE
  obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp he
  exact ⟨i,heq.symm,record_issued k w (head_bound k rr w hw) i hi⟩

private theorem origin_support {k : V} {i : I} (hi : issued k i) :
    ∃ r E, headEventsFrom (D := RGAM) (ver k) (head k) r = some E ∧ event i ∈ E := by
  obtain ⟨w,hw,hiw⟩ := origin_present k i hi
  let rr : R := ⟨(event i).2.1, by fin_cases i <;> decide⟩
  have hw' : heads k rr = some w := hw
  refine ⟨rr.val, (↑((records w).2.image event) : Set Event), ?_, ?_⟩
  · have equal : w=k := Option.some.inj hw.symm
    subst w
    fin_cases i <;> simp [headEventsFrom, head, heads, rr, event, seed, deletion, replacement, eventOf, ver, k.isLt, Option.bind]
  · exact Finset.mem_image_of_mem event hiw

/-- Every prefix satisfies the unchanged store coherence requirements. -/
def config (k : V) : Configuration RGAM where
  vis := vis k
  ver := ver k
  head := head k
  parents := parents k
  parents_lt := parents_rank k
  ver_init := by simp [ver,records,indices,state,RGAM,datatype]
  head_alloc := by
    intro r v h
    obtain ⟨rr,w,_,rfl,hw⟩ := head_cases h
    simp [ver,w.isLt,head_bound k rr w hw]
  vis_src := by
    rintro a b ⟨i,j,rfl,rfl,h⟩
    exact origin_support (past_issued k i j h)
  vis_tgt := by
    rintro a b ⟨i,j,rfl,rfl,h⟩
    exact origin_support h.1
  vis_causal := by
    intro a b r E hv hE hb
    obtain ⟨rr,w,hw,rfl⟩ := headEvents_cases hE
    obtain ⟨i,j,rfl,rfl,hvis⟩ := hv
    obtain ⟨jj,hjj,he⟩ := Finset.mem_image.mp hb
    have hj : jj = j := event_injective he
    subst jj
    exact Finset.mem_image_of_mem event (record_causal w i j hjj hvis.2)
  timestamps_distinct := by
    intro a b r E r' E' hE ha hE' hb hne ht
    obtain ⟨i,rfl,_⟩ := support_event hE ha
    obtain ⟨j,rfl,_⟩ := support_event hE' hb
    have time : ∀ i : I, (event i).1 = i.val + 1 := by intro i; fin_cases i <;> rfl
    rw [time,time] at ht
    have hij : i = j := Fin.ext (Nat.add_right_cancel ht)
    exact hne (hij ▸ rfl)
  causal_mono := by
    rintro a b ⟨i,j,rfl,rfl,h⟩
    exact index_mono k i j h
  vis_total_same_replica := by
    intro a b r E r' E' hE ha hE' hb hne hrep
    obtain ⟨i,rfl,hi⟩ := support_event hE ha
    obtain ⟨j,rfl,hj⟩ := support_event hE' hb
    have hij : i ≠ j := fun heq => hne (heq ▸ rfl)
    rcases same_replica k i j hi hj hij hrep with h | h
    · exact Or.inl ⟨i,j,rfl,rfl,h⟩
    · exact Or.inr ⟨j,i,rfl,rfl,h⟩
  gca_events := by
    intro v₁ v₂ vt s₁ E₁ s₂ E₂ st Et hg hv₁ hv₂ hvt
    obtain ⟨a,rfl,ha,_,rfl⟩ := ver_cases hv₁
    obtain ⟨b,rfl,hb,_,rfl⟩ := ver_cases hv₂
    obtain ⟨c,rfl,_,_,rfl⟩ := ver_cases hvt
    have hca := reaches_sound hg.1
    have hcb := reaches_sound hg.2.1
    have hgreatest : ∀ w : V, w ∈ ancestors a → w ∈ ancestors b → w ∈ ancestors c := by
      intro w hwa hwb
      exact reaches_sound (hg.2.2 w.val (reaches_complete k w a ha hwa)
        (reaches_complete k w b hb hwb))
    have hc := gca_record a b c hca hcb hgreatest
    ext e
    simp only [Set.mem_inter_iff,Finset.mem_coe]
    rw [hc,Finset.image_inter _ _ event_injective]
    simp

private theorem ver_at (k v : V) (h : v.val ≤ k.val) :
    ver k v.val = some ((records v).1, ↑((records v).2.image event)) := by
  simp [ver,v.isLt,h]

private theorem ver_absent (k : V) : ver k (k.val + 1) = none := by simp [ver]

private theorem ver_extend (k k' : V) (h : k'.val = k.val + 1) :
    ver k' = fun w => if w = k'.val then
      some ((records k').1, ↑((records k').2.image event)) else ver k w := by
  funext w
  by_cases heq : w = k'.val
  · subst w; simp [ver_at]
  · simp only [ver,if_neg heq]
    split_ifs <;> first | rfl | omega

private theorem parents_extend (k k' : V) (h : k'.val = k.val + 1) :
    parents k' = fun w => if w = k'.val then
      (parentList k').map Fin.val else parents k w := by
  funext w
  by_cases heq : w = k'.val
  · subst w; simp [parents,k'.isLt]
  · simp only [parents,if_neg heq]
    split_ifs <;> first | rfl | omega

private theorem head_finite (k : V) (r : R) : head k r.val = (heads k r).map Fin.val := by
  simp [head,heads]

private theorem head_extend (k k' : V) (r : R)
    (h : ∀ rr : R, heads k' rr = if rr = r then some k' else heads k rr) :
    head k' = fun rr => if rr = r.val then some k'.val else head k rr := by
  have zero : r.val=0 := Nat.lt_one_iff.mp r.isLt
  funext rr
  by_cases hzero : rr=0 <;> simp [head,heads,zero,Nat.lt_one_iff,hzero]

private theorem gca (k : V) (a b c : V)
    (ha : a.val ≤ k.val) (hb : b.val ≤ k.val)
    (hc : c ∈ ancestors a ∧ c ∈ ancestors b ∧
      ∀ w : V, w ∈ ancestors a → w ∈ ancestors b → w ∈ ancestors c) :
    IsGCA (parents k) a.val b.val c.val := by
  refine ⟨reaches_complete k c a ha hc.1, reaches_complete k c b hb hc.2.1, ?_⟩
  intro w hwa hwb
  have hw : w < 4 := lt_of_le_of_lt (reaches_le (parents_rank k) hwa) a.isLt
  let wf : V := ⟨w,hw⟩
  have hwa' : wf ∈ ancestors a := reaches_sound hwa
  have hwb' : wf ∈ ancestors b := reaches_sound hwb
  have hck : c.val ≤ k.val := (reaches_le (parents_rank k)
    (reaches_complete k c a ha hc.1)).trans ha
  exact reaches_complete k wf c hck (hc.2.2 wf hwa' hwb')


private theorem ver_extend_values (k k' : V) (h : k'.val = k.val + 1)
    {s : RGAM.State} {E : Set Event}
    (hs : s = (records k').1) (he : E = ↑((records k').2.image event)) :
    (config k').ver = fun w => if w = k'.val then some (s,E) else (config k).ver w := by
  rw [hs,he]
  exact ver_extend k k' h

private theorem configuration_ext {C C' : Configuration RGAM}
    (hv : C.vis = C'.vis) (hs : C.ver = C'.ver)
    (hh : C.head = C'.head) (hp : C.parents = C'.parents) : C = C' := by
  cases C; cases C'
  cases hv; cases hs; cases hh; cases hp
  rfl

theorem config_zero : config 0 = initConfig RGAM := by
  apply configuration_ext
  · have hz : ∀ i j : I, ¬ visIndex 0 i j := by decide
    funext a b; simp [config,vis,initConfig,hz]
  · funext v; by_cases hv : v = 0 <;> simp [config,ver,initConfig,records,indices,state,RGAM,datatype,hv]
  · funext r
    by_cases hr : r < 1
    · interval_cases r <;> rfl
    · have hr0 : r ≠ 0 := by intro h; subst r; exact hr (by decide)
      simp [config,head,hr,initConfig,hr0]
  · funext v; by_cases hv : v = 0 <;> simp [config,parents,parentList,initConfig,hv]

private theorem fresh_time (k : V) (t : Nat)
    (h : ∀ i : I, issued k i → (event i).time ≠ t) :
    ∀ e ∈ (config k).events, e.time ≠ t := by
  intro e he
  obtain ⟨r,E,hE,he⟩ := he
  obtain ⟨i,rfl,hi⟩ := support_event hE he
  exact h i hi

private theorem fresh_store (k : V) (t : Nat)
    (h : ∀ i : I, issued k i → (event i).time ≠ t) :
    ∀ v s E, (config k).ver v = some (s,E) → ∀ e ∈ E, e.time ≠ t := by
  intro v s E hv e he
  obtain ⟨w,_,hw,_,rfl⟩ := ver_cases hv
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
  exact h i (record_issued k w hw i hi)



theorem event_supported_issued {k : V} {e : Event}
    (he : e ∈ (config k).events) : ∃ i : I, e = event i ∧ issued k i := by
  obtain ⟨r,E,hE,he⟩ := he
  exact support_event hE he

def before (i : I) : V := ⟨i.val,by omega⟩
def issuer (i : I) : V := before i
def newVersion (i : I) : V := ⟨i.val+1,by omega⟩
def origin (_ : I) : R := 0
private theorem update_table (i : I) :
    RGAM.update (records (issuer i)).1 (event i) = (records (newVersion i)).1 := by
  fin_cases i <;> simp [RGAM,datatype,rawUpdate,records,issuer,before,newVersion,state,event,eventOf,recordOf,seed,deletion,replacement,mStep,mIsIns,sIds,sInsert,Finset.insert_comm] <;> ext g <;> simp [or_comm]

private theorem vis_ext {k k' : V}
    (h : ∀ i j : I, visIndex k i j ↔ visIndex k' i j) : vis k = vis k' := by
  funext a b
  apply propext
  constructor <;> rintro ⟨i,j,rfl,rfl,hv⟩
  · exact ⟨i,j,rfl,rfl,(h i j).mp hv⟩
  · exact ⟨i,j,rfl,rfl,(h i j).mpr hv⟩

private theorem vis_extend (i : I)
    (h : ∀ j l : I, visIndex (newVersion i) j l ↔
      visIndex (before i) j l ∨ (j ∈ indices (issuer i) ∧ l = i)) :
    vis (newVersion i) = fun a b => vis (before i) a b ∨
      (a ∈ (↑((indices (issuer i)).image event) : Set Event) ∧ b = event i) := by
  funext a b
  apply propext
  constructor
  · rintro ⟨j,l,rfl,rfl,hv⟩
    rcases (h j l).mp hv with hv | ⟨hj,rfl⟩
    · exact Or.inl ⟨j,l,rfl,rfl,hv⟩
    · exact Or.inr ⟨Finset.mem_image_of_mem event hj,rfl⟩
  · rintro (⟨j,l,rfl,rfl,hv⟩ | ⟨ha,rfl⟩)
    · exact ⟨j,l,rfl,rfl,(h j l).mpr (Or.inl hv)⟩
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
      exact ⟨j,i,rfl,rfl,(h j i).mpr (Or.inr ⟨hj,rfl⟩)⟩

/-- Each labelled apply is an actual timestamp-fresh store rule. -/
theorem apply_step (i : I) :
    Step RGAM (config (before i))
      (.apply (event i).time (event i).2.1 (event i).op) (config (newVersion i)) := by
  apply Step.apply (D := RGAM) (v := (issuer i).val) (vnew := (newVersion i).val)
    (s := (records (issuer i)).1) (ev := (↑((records (issuer i)).2.image event) : Set Event))
  · fin_cases i <;> rfl
  · exact ver_at (before i) (issuer i) (by fin_cases i <;> decide)
  · apply fresh_time; fin_cases i <;> decide
  · apply fresh_store; fin_cases i <;> decide
  · fin_cases i <;> rfl
  · fin_cases i <;> decide
  · exact vis_extend i (by fin_cases i <;> decide)
  · apply ver_extend_values (before i) (newVersion i) (by fin_cases i <;> rfl)
    · exact update_table i
    · have hi : ∀ i : I, indices (newVersion i) = insert i (indices (issuer i)) := by decide
      change (↑((indices (issuer i)).image event) : Set Event) ∪ {event i} =
        ↑((indices (newVersion i)).image event)
      rw [hi i,Finset.image_insert]
      ext e
      simp only [Set.mem_union,Set.mem_singleton_iff,Finset.mem_coe,Finset.mem_insert]
      exact or_comm
  · have ho : ∀ i : I, (origin i).val = (event i).2.1 := by decide
    rw [← ho i]
    apply head_extend
    fin_cases i <;> decide
  · have hp : ∀ i : I, parentList (newVersion i) = [issuer i] := by decide
    have he := parents_extend (before i) (newVersion i) (by fin_cases i <;> rfl)
    simpa [config,hp i] using he

abbrev issuance := Instances.SidedEmbedRGA.FugueMax.generation unaryCode
/-- An independently listed mint-time past, in causal order. -/
def pastIndices (i : I) : List I := match i.val with
  | 0 => [] | 1 => [0] | _ => [0,1]

def pastOps (i : I) : List Event := (pastIndices i).map event

private theorem pastIndices_mem : ∀ i j : I,
    j ∈ pastIndices i ↔ j ∈ past i := by decide

/-- The mint past replays to the state actually held at the issuing head. -/
theorem past_fold_issuer (i : I) :
    applySeq RGAM.toUpdateSig RGAM.init (pastOps i) = (records (issuer i)).1 := by
  fin_cases i <;> decide +kernel

theorem issuer_guard (i : I) : applicable unaryCode (event i) (records (issuer i)).1 := by
  fin_cases i
  · exact original_guards.1
  · exact original_guards.2.1
  · exact original_guards.2.2

/-- The same guard holds at an exact causal enumeration of the mint past. -/
theorem mint_guard (i : I) :
    applicable unaryCode (event i) (applySeq RGAM.toUpdateSig RGAM.init (pastOps i)) := by
  rw [past_fold_issuer]
  exact issuer_guard i

private theorem past_nodup : ∀ i : I, (pastOps i).Nodup := by decide
private theorem past_respects : ∀ k : V, ∀ i : I,
    respects (pastOps i) (vis k) := by
  unfold respects
  decide +kernel

/-- Timestamp projection provides an exact causal-past event enumeration. -/
theorem past_enum (k : V) (i : I) (hi : issued k i) :
    listPermOf (pastOps i) {e ∈ (config k).events | (config k).vis e (event i)} := by
  refine ⟨past_nodup i, ?_⟩
  intro e
  constructor
  · intro he
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    have hvis : (config k).vis (event j) (event i) :=
      ⟨j, i, rfl, rfl, hi, (pastIndices_mem i j).mp hj⟩
    exact ⟨(config k).vis_src hvis, hvis⟩
  · rintro ⟨_, j, ii, he, hiEq, hvis⟩
    have hieq : ii = i := event_injective hiEq.symm
    subst ii
    exact List.mem_map.mpr ⟨j, (pastIndices_mem i j).mpr hvis.2, he.symm⟩

/-- Every observed event has its exact mint past and honest guard at every
prefix where it is supported. This is stronger than checking only the endpoint. -/
theorem mint_honest (k : V) : MintHonest RGAM issuance.CanIssue (config k) := by
  intro e he
  obtain ⟨i, rfl, hi⟩ := event_supported_issued he
  exact ⟨pastOps i, past_enum k i hi, past_respects k i, mint_guard i⟩

/-- A timestamp-fresh raw apply also carries its actual issuer-head guard. -/
theorem issued_apply (i : I) :
    IssuedStep RGAM issuance (config (before i))
      (.apply (event i).time (event i).2.1 (event i).op) (config (newVersion i)) := by
  apply IssuedStep.apply (v := (issuer i).val) (s := (records (issuer i)).1)
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · exact issuer_guard i
  · exact apply_step i

theorem mint_certified : MintCertifiedReach RGAM issuance (config 3) := by
  have h0 : MintCertifiedReach RGAM issuance (config 0) := by rw [config_zero]; exact .init
  have h1 := MintCertifiedReach.step h0 (mint_honest 0) (issued_apply 0) (mint_honest 1)
  have h2 := MintCertifiedReach.step h1 (mint_honest 1) (issued_apply 1) (mint_honest 2)
  exact .step h2 (mint_honest 2) (issued_apply 2) (mint_honest 3)


def allOps : List Event := [event 0,event 1,event 2]
def required (a b : Event) : Prop := a=event 1 ∧ b=event 2
instance (a b : Event) : Decidable (required a b) := by unfold required; infer_instance

private theorem allOps_enum : listPermOf allOps (↑((indices 3).image event) : Set Event) := by
  refine ⟨by decide,?_⟩
  intro e
  simp only [allOps,List.mem_cons,List.not_mem_nil,or_false,Finset.mem_coe,Finset.mem_image]
  constructor
  · intro h
    rcases h with rfl|rfl|rfl <;> exact ⟨_,by decide,rfl⟩
  · rintro ⟨i,_,rfl⟩
    fin_cases i <;> simp

private def PrefixChecks {E : Type} (check : List E → E → Prop) : List E → List E → Prop
  | _, [] => True
  | pre, e :: rest => check pre e ∧ PrefixChecks check (pre ++ [e]) rest

private theorem checks_splits {E : Type} (check : List E → E → Prop)
    (pre xs : List E) :
    PrefixChecks check pre xs ↔
      ∀ before e after, xs = before ++ e :: after → check (pre ++ before) e := by
  induction xs generalizing pre with
  | nil => simp [PrefixChecks]
  | cons x xs ih =>
    constructor
    · intro h before e after eq
      cases before with
      | nil => simp only [List.nil_append,List.cons.injEq] at eq; obtain ⟨rfl,rfl⟩ := eq; simpa using h.1
      | cons b bs =>
        simp only [List.cons_append,List.cons.injEq] at eq
        obtain ⟨rfl,eq⟩ := eq
        simpa [List.append_assoc] using (ih (pre ++ [x])).mp h.2 bs e after eq
    · intro h
      refine ⟨by simpa using h [] x xs rfl, (ih _).mpr ?_⟩
      intro before e after eq
      simpa [List.append_assoc] using h (x :: before) e after (by simp [eq])

private def mCheck (pre : KnowM) (g : MRec) : Prop :=
  match g.op with
  | .ins p _ => p=0 ∨ (∃b∈pre,mIsIns b=true ∧ b.ts=p) ∧ ∀d∈pre,d.op≠.del p
  | .del x => x=0 ∨ ∃b∈pre,mIsIns b=true ∧ b.ts=x

private theorem checks_legal (ops : KnowM) :
    (ops.map MRec.ts).Nodup ∧ (∀g∈ops,0<g.ts) ∧ PrefixChecks mCheck [] ops ↔ listLegal ops := by
  rw [checks_splits]
  simp only [List.nil_append]
  rfl

private def checksDecidable {E : Type} (check : List E → E → Prop)
    (dec : ∀ pre e, Decidable (check pre e)) (pre xs : List E) :
    Decidable (PrefixChecks check pre xs) :=
  match xs with
  | [] => isTrue True.intro
  | e :: rest => @instDecidableAnd (check pre e) (PrefixChecks check (pre ++ [e]) rest)
      (dec pre e) (checksDecidable check dec (pre ++ [e]) rest)

instance list_legal_decidable (ops : KnowM) : Decidable (listLegal ops) := by
  letI := checksDecidable mCheck (fun pre g => by unfold mCheck; split <;> infer_instance) [] ops
  exact decidable_of_iff ((ops.map MRec.ts).Nodup ∧ (∀g∈ops,0<g.ts) ∧ PrefixChecks mCheck [] ops)
    (checks_legal ops)

instance spec_legal_decidable (ops : List Event) : Decidable ((listSpec unaryCode).Legal ops) :=
  list_legal_decidable (ops.map recordOf)

private theorem finite_history_rejection : ∀π∈allOps.permutations',
    respects π required → ¬(listSpec unaryCode).Legal π := by
  unfold respects
  decide +kernel

def scratch : State := ⟨[(1,1,[0]),(100,100,[])],∅⟩

private theorem deletion_insertion_raw_conflict : ¬RGAM.toUpdateSig.commutes (event 1) (event 2) := by
  intro commute
  have neq : RGAM.update (RGAM.update scratch (event 2)) (event 1) ≠
      RGAM.update (RGAM.update scratch (event 1)) (event 2) := by
    decide +kernel
  exact neq (commute scratch).symm

private theorem required_paperOrder (P : OperationPolicy Payload) : ∀a b, required a b →
    paperOrder P (config 3).replayContext (↑((indices 3).image event) : Set Event) a b := by
  rintro a b ⟨rfl,rfl⟩
  exact Or.inl ⟨by change vis 3 (event 1) (event 2); decide,deletion_insertion_raw_conflict⟩

theorem final_read : RGAM.query (records 3).1 ()=[3] ∧ RGAM.query (records 3).1 ()≠[] := by
  change sIds (state 3).live=[3] ∧ sIds (state 3).live≠[]
  decide +kernel

private theorem list_legal_prefix (pre suf : KnowM) (legal : listLegal (pre++suf)) : listLegal pre := by
  obtain ⟨nd,positive,checks⟩ := legal
  refine ⟨?_,?_,?_⟩
  · exact (List.nodup_append.mp (by simpa only [List.map_append] using nd)).1
  · intro g hg
    exact positive g (List.mem_append_left _ hg)
  · intro before g after split
    exact checks before g (after++suf) (by simp only [split,List.append_assoc,List.cons_append])

private theorem spec_legal_prefix (pre suf : List Event)
    (legal : (listSpec unaryCode).Legal (pre++suf)) : (listSpec unaryCode).Legal pre := by
  exact list_legal_prefix (pre.map recordOf) (suf.map recordOf)
    (by simpa only [listSpec,List.map_append] using legal)

private theorem empty_legal : (listSpec unaryCode).Legal [] := by
  simp [listSpec,listLegal]

theorem no_raw_order_history (P : OperationPolicy Payload) (answer : List Nat) :
    ¬∃π : List Event, listPermOf π (↑((indices 3).image event) : Set Event) ∧
      respects π (paperOrder P (config 3).replayContext (↑((indices 3).image event) : Set Event)) ∧
      (GuardedHistory.language (listSpec unaryCode)).admits (projectedLabels id π ++ [.query () answer]) := by
  rintro ⟨π,perm,ordered,admitted⟩
  have permutation : π.Perm allOps :=
    (List.perm_ext_iff_of_nodup perm.1 allOps_enum.1).mpr
      (fun e => (perm.2 e).trans (allOps_enum.2 e).symm)
  have requiredOrder : respects π required := ordered.imp fun {_ _} no edge =>
    no (required_paperOrder P _ _ edge)
  have decoded := (GuardedHistory.admits_updates_query_iff (listSpec unaryCode)
    empty_legal spec_legal_prefix π () answer).mp admitted
  exact finite_history_rejection π (List.mem_permutations'.mpr permutation) requiredOrder decoded.1

theorem certified_raw_criterion_failure (P : OperationPolicy Payload) :
    MintCertifiedReach RGAM issuance (config 3) ∧
    ¬EventVersionsSpecificationRA RGAM P (GuardedHistory.language (listSpec unaryCode)) (config 3) := by
  refine ⟨mint_certified,?_⟩
  intro witness
  obtain ⟨π,perm,ordered,_,admitted⟩ := witness 3 (records 3).1
    (↑((indices 3).image event) : Set Event) (ver_at 3 3 (by decide)) ()
  exact no_raw_order_history P _ ⟨π,perm,ordered,admitted⟩

def goodHistory : List Event := [event 0,event 2,event 1]

theorem admitted_history_control :
    (GuardedHistory.language (listSpec unaryCode)).admits (projectedLabels id goodHistory ++ [.query () [3]]) ∧
    ¬respects goodHistory (paperOrder (commutingPolicy Payload) (config 3).replayContext
      (↑((indices 3).image event) : Set Event)) := by
  constructor
  · apply (GuardedHistory.admits_updates_query_iff (listSpec unaryCode)
      empty_legal spec_legal_prefix goodHistory () [3]).mpr
    constructor
    · decide +kernel
    · change [3]=((listRun (goodHistory.map recordOf)).filter (fun p => p.1 != 0)).map Prod.fst
      decide +kernel
  · intro ordered
    have requiredOrder : respects goodHistory required := ordered.imp fun {_ _} no edge =>
      no (required_paperOrder (commutingPolicy Payload) _ _ edge)
    have wrong : ¬respects goodHistory required := by unfold respects; decide
    exact wrong requiredOrder

#print axioms certified_raw_criterion_failure
#print axioms admitted_history_control
#print axioms mint_certified
#print axioms original_guards
end Sal.MRDTs.Paper1.CertifiedFugueRawOrderObstruction
