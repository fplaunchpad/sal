import Sal.MRDTs.Paper1.RGAStrict
import Sal.MRDTs.Paper1.RGAActive

/-! A fully reachable crossed-delete experiment with two children on each
branch. Finite event/ancestor tables describe the execution; the actual state
is the unchanged production RGA. Expected query [5,4,8,7] is hand-derived. -/
namespace Sal.MRDTs.Paper1.RGA.CrossedExecution
open Foundation
open Sal.MRDTs.Instances.RGA

abbrev Event := Op RGAOp
abbrev V := Fin 11
abbrev R := Fin 2
abbrev I := Fin 8

def event (i : I) : Event := match i.val with
  | 0 => (1,0,.addAfter 0)
  | 1 => (2,0,.addAfter 0)
  | 2 => (3,0,.remove 1)
  | 3 => (4,0,.addAfter 2)
  | 4 => (5,0,.addAfter 2)
  | 5 => (6,1,.remove 2)
  | 6 => (7,1,.addAfter 1)
  | _ => (8,1,.addAfter 1)

def indices (v : V) : Finset I := match v.val with
  | 0 => ∅
  | 1 => {0}
  | 2 | 3 => {0,1}
  | 4 => {0,1,2}
  | 5 => {0,1,2,3}
  | 6 => {0,1,2,3,4}
  | 7 => {0,1,5}
  | 8 => {0,1,5,6}
  | 9 => {0,1,5,6,7}
  | _ => Finset.univ

def data (v : V) : BirthGraveState := match v.val with
  | 0 => ⟨∅,∅⟩
  | 1 => ⟨{(1,0)},∅⟩
  | 2 | 3 => ⟨{(1,0),(2,0)},∅⟩
  | 4 => ⟨{(1,0),(2,0)},{1}⟩
  | 5 => ⟨{(1,0),(2,0),(4,2)},{1}⟩
  | 6 => ⟨{(1,0),(2,0),(4,2),(5,2)},{1}⟩
  | 7 => ⟨{(1,0),(2,0)},{2}⟩
  | 8 => ⟨{(1,0),(2,0),(7,1)},{2}⟩
  | 9 => ⟨{(1,0),(2,0),(7,1),(8,1)},{2}⟩
  | _ => ⟨{(1,0),(2,0),(4,2),(5,2),(7,1),(8,1)},{1,2}⟩

def stateFor (q : BirthGraveState) : RGAM.State :=
  (fun p => decide (p ∈ q.adds), fun id => decide (id ∈ q.grave))

def records (v : V) : RGAM.State × Finset I := (stateFor (data v), indices v)

def parentList (v : V) : List V := match v.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 | 4 => [2]
  | 5 => [4]
  | 6 => [5]
  | 7 => [3]
  | 8 => [7]
  | 9 => [8]
  | _ => [6,9]

def parentTable (v : V) : Finset V := (parentList v).toFinset

private theorem parentList_mem (v p : V) :
    p ∈ parentList v ↔ p ∈ parentTable v := by simp [parentTable]

def ancestors (v : V) : Finset V := match v.val with
  | 0 => {0}
  | 1 => {0,1}
  | 2 => {0,1,2}
  | 3 => {0,1,2,3}
  | 4 => {0,1,2,4}
  | 5 => {0,1,2,4,5}
  | 6 => {0,1,2,4,5,6}
  | 7 => {0,1,2,3,7}
  | 8 => {0,1,2,3,7,8}
  | 9 => {0,1,2,3,7,8,9}
  | _ => Finset.univ

def heads (k : V) (r : R) : Option V := match k.val, r.val with
  | 0,0 => some 0
  | 1,0 => some 1
  | 2,0 => some 2
  | 3,0 => some 2
  | 3,1 => some 3
  | 4,0 => some 4
  | 4,1 => some 3
  | 5,0 => some 5
  | 5,1 => some 3
  | 6,0 => some 6
  | 6,1 => some 3
  | 7,0 => some 6
  | 7,1 => some 7
  | 8,0 => some 6
  | 8,1 => some 8
  | 9,0 => some 6
  | 9,1 => some 9
  | 10,0 => some 10
  | 10,1 => some 9
  | _,_ => none

def issued (k : V) (i : I) : Prop := match i.val with
  | 0 => 1 ≤ k.val
  | 1 => 2 ≤ k.val
  | 2 => 4 ≤ k.val
  | 3 => 5 ≤ k.val
  | 4 => 6 ≤ k.val
  | 5 => 7 ≤ k.val
  | 6 => 8 ≤ k.val
  | _ => 9 ≤ k.val

instance (k : V) (i : I) : Decidable (issued k i) := by
  unfold issued; split <;> infer_instance

def past (i : I) : Finset I := match i.val with
  | 0 => ∅
  | 1 => {0}
  | 2 => {0,1}
  | 3 => {0,1,2}
  | 4 => {0,1,2,3}
  | 5 => {0,1}
  | 6 => {0,1,5}
  | _ => {0,1,5,6}

def visIndex (k : V) (i j : I) : Prop := issued k j ∧ i ∈ past j
instance (k : V) (i j : I) : Decidable (visIndex k i j) := by
  unfold visIndex; infer_instance

def vis (k : V) (a b : Event) : Prop :=
  ∃ i j : I, a = event i ∧ b = event j ∧ visIndex k i j
instance (k : V) (a b : Event) : Decidable (vis k a b) := by
  unfold vis; infer_instance

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
  if h : v < 11 ∧ v ≤ k.val then
    some ((records ⟨v,h.1⟩).1, ↑((records ⟨v,h.1⟩).2.image event)) else none

def head (k : V) (r : Nat) : Option Nat :=
  if h : r < 2 then (heads k ⟨r,h⟩).map Fin.val else none

def parents (k : V) (v : Nat) : List Nat :=
  if h : v < 11 ∧ v ≤ k.val then (parentList ⟨v,h.1⟩).map Fin.val else []

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
  · simp [headEventsFrom, head, rr.isLt, hw', ver, w.isLt, head_bound k rr w hw', Option.bind]
  · exact Finset.mem_image_of_mem event hiw

/-- Every prefix satisfies the unchanged store coherence requirements. -/
def config (k : V) : Configuration RGAM where
  vis := vis k
  ver := ver k
  head := head k
  parents := parents k
  parents_lt := parents_rank k
  ver_init := by simp [ver,records,indices,data,stateFor,RGAM]
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
  simp [head,r.isLt]

private theorem head_extend (k k' : V) (r : R)
    (h : ∀ rr : R, heads k' rr = if rr = r then some k' else heads k rr) :
    head k' = fun rr => if rr = r.val then some k'.val else head k rr := by
  funext rr
  by_cases hr : rr < 2
  · let rrf : R := ⟨rr,hr⟩
    have hh := h rrf
    have heq : rrf = r ↔ rr = r.val := ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
    simp only [head,hr,dite_true]
    rw [hh]
    by_cases he : rr = r.val <;> simp [he,heq,rrf]
  · have hne : rr ≠ r.val := by intro he; rw [he] at hr; exact hr r.isLt
    simp [head,hr,hne]

private theorem gca (k : V) (a b c : V)
    (ha : a.val ≤ k.val) (hb : b.val ≤ k.val)
    (hc : c ∈ ancestors a ∧ c ∈ ancestors b ∧
      ∀ w : V, w ∈ ancestors a → w ∈ ancestors b → w ∈ ancestors c) :
    IsGCA (parents k) a.val b.val c.val := by
  refine ⟨reaches_complete k c a ha hc.1, reaches_complete k c b hb hc.2.1, ?_⟩
  intro w hwa hwb
  have hw : w < 11 := lt_of_le_of_lt (reaches_le (parents_rank k) hwa) a.isLt
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
  · funext v; by_cases hv : v = 0 <;> simp [config,ver,initConfig,records,indices,data,stateFor,RGAM,hv]
  · funext r
    by_cases hr : r < 2
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

def before (i : I) : V := match i.val with
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 7 | _ => 8

def issuer (i : I) : V := match i.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3 | 6 => 7 | _ => 8

def newVersion (i : I) : V := match i.val with
  | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 5 | 4 => 6 | 5 => 7 | 6 => 8 | _ => 9

def origin (i : I) : R := if i.val < 5 then 0 else 1

private theorem update_table (i : I) :
    RGAM.update (records (issuer i)).1 (event i) = (records (newVersion i)).1 := by
  fin_cases i <;> apply Prod.ext <;> funext x <;>
    dsimp only [RGAM,rgaUpdate,records,stateFor,data,event,issuer,newVersion] <;>
    apply Bool.eq_iff_iff.mpr <;>
    simp only [Bool.or_eq_true,decide_eq_true_eq,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false] <;> tauto

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

/-- Fork copies the two-root shared snapshot to a distinct replica. -/
theorem fork_step : Step RGAM (config 2) (.fork 1 0) (config 3) := by
  apply Step.fork (D := RGAM) (v := 2) (vnew := 3)
    (s := (records 2).1) (ev := (↑((records 2).2.image event) : Set Event))
  · rfl
  · rfl
  · exact ver_at 2 2 (by decide)
  · rfl
  · decide
  · exact vis_ext (by decide)
  · exact ver_extend_values 2 3 rfl rfl rfl
  · exact head_extend 2 3 1 (by decide)
  · simpa [config,parentList] using parents_extend 2 3 rfl

/-- The final merge uses the shared two-root version as its greatest common ancestor. -/
theorem merge_step : Step RGAM (config 9) (.merge 0 1) (config 10) := by
  apply Step.merge (D := RGAM) (v₁ := 6) (v₂ := 9) (vT := 2) (vm := 10)
    (s₁ := (records 6).1) (s₂ := (records 9).1) (sT := (records 2).1)
    (ev₁ := (↑((records 6).2.image event) : Set Event))
    (ev₂ := (↑((records 9).2.image event) : Set Event))
    (evT := (↑((records 2).2.image event) : Set Event))
  · rfl
  · rfl
  · exact ver_at 9 6 (by decide)
  · exact ver_at 9 9 (by decide)
  · exact gca 9 6 9 2 (by decide) (by decide) (by decide)
  · exact ver_at 9 2 (by decide)
  · rfl
  · decide
  · decide
  · exact vis_ext (by decide)
  · apply ver_extend_values 9 10 rfl
    · apply Prod.ext <;> funext x <;> apply Bool.eq_iff_iff.mpr <;>
        simp [RGAM,records,stateFor,data,Bool.or_eq_true,or_assoc,or_left_comm]
    · have hi : indices 10 = indices 6 ∪ indices 9 := by decide
      change (↑((indices 6).image event) : Set Event) ∪ ↑((indices 9).image event) =
        ↑((indices 10).image event)
      rw [hi,Finset.image_union,Finset.coe_union]
  · exact head_extend 9 10 0 (by decide)
  · simpa [config,parentList] using parents_extend 9 10 rfl

/-- The actual store trace, before adding the final observation. -/
def trace : List (Label RGAM × Configuration RGAM) :=
  [(.apply 1 0 (.addAfter 0),config 1), (.apply 2 0 (.addAfter 0),config 2),
   (.fork 1 0,config 3), (.apply 3 0 (.remove 1),config 4),
   (.apply 4 0 (.addAfter 2),config 5), (.apply 5 0 (.addAfter 2),config 6),
   (.apply 6 1 (.remove 2),config 7), (.apply 7 1 (.addAfter 1),config 8),
   (.apply 8 1 (.addAfter 1),config 9), (.merge 0 1,config 10)]

theorem execution : (labeledTS RGAM).Execution (initConfig RGAM) trace := by
  rw [← config_zero]
  exact .cons (apply_step 0) (.cons (apply_step 1) (.cons fork_step
    (.cons (apply_step 2) (.cons (apply_step 3) (.cons (apply_step 4)
      (.cons (apply_step 5) (.cons (apply_step 6) (.cons (apply_step 7)
        (.cons merge_step (.nil _))))))))))

#print axioms execution

end Sal.MRDTs.Paper1.RGA.CrossedExecution
