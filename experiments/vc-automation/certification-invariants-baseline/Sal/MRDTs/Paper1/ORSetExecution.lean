import Sal.MRDTs.Paper1.Capstone
import Sal.MRDTs.Paper1.ORSetSPOT

/-! The motivating defeater as an actual execution of the store.
The two initial forks allocate versions 1 and 2, so the figure's operation
versions 1…8 are represented by allocated versions 3,4,6,7,8,9,10,11;
version 5 copies the first add into the third replica by a root-based merge.
Thus this is a retained-semantics realization with explicit fork/copy versions,
rather than an identification with the figure's shared root aliases. -/
namespace Sal.MRDTs.Paper1.ORSet.Execution
open Foundation

abbrev Event := Op (Update Nat)
abbrev V := Fin 12
abbrev R := Fin 3
abbrev I := Fin 4

def event (i : I) : Event := match i.val with
  | 0 => (1, 0, .add 7)
  | 1 => (2, 1, .add 7)
  | 2 => (3, 0, .remove 7)
  | _ => (4, 1, .remove 7)

def records (v : V) : State Nat × Finset I := match v.val with
  | 0 | 1 | 2 => (∅, ∅)
  | 3 | 5 => ({(7,1)}, {0})
  | 4 => ({(7,2)}, {1})
  | 6 => ({(7,1),(7,2)}, {0,1})
  | 7 => (∅, {0,2})
  | 8 => (∅, {1,3})
  | 9 => ({(7,2)}, {0,1,2})
  | 10 => ({(7,1)}, {0,1,3})
  | _ => (∅, {0,1,2,3})

def parentList (v : V) : List V := match v.val with
  | 0 => []
  | 1 | 2 | 3 => [0]
  | 4 => [1]
  | 5 => [2,3]
  | 6 => [5,4]
  | 7 => [3]
  | 8 => [4]
  | 9 => [7,6]
  | 10 => [8,6]
  | _ => [10,9]

def parentTable (v : V) : Finset V := match v.val with
  | 0 => ∅
  | 1 | 2 | 3 => {0}
  | 4 => {1}
  | 5 => {2,3}
  | 6 => {5,4}
  | 7 => {3}
  | 8 => {4}
  | 9 => {7,6}
  | 10 => {8,6}
  | _ => {10,9}

/-- Reflexive ancestor closure, supplied independently of reachability. -/
def ancestors (v : V) : Finset V := match v.val with
  | 0 => {0}
  | 1 => {0,1}
  | 2 => {0,2}
  | 3 => {0,3}
  | 4 => {0,1,4}
  | 5 => {0,2,3,5}
  | 6 => {0,1,2,3,4,5,6}
  | 7 => {0,3,7}
  | 8 => {0,1,4,8}
  | 9 => {0,1,2,3,4,5,6,7,9}
  | 10 => {0,1,2,3,4,5,6,8,10}
  | _ => Finset.univ

def heads (k : V) (r : R) : Option V := match k.val, r.val with
  | 0, 0 => some 0
  | 1, 0 => some 0
  | 1, 1 => some 1
  | 2, 0 => some 0
  | 2, 1 => some 1
  | 2, 2 => some 2
  | 3, 0 => some 3
  | 3, 1 => some 1
  | 3, 2 => some 2
  | 4, 0 => some 3
  | 4, 1 => some 4
  | 4, 2 => some 2
  | 5, 0 => some 3
  | 5, 1 => some 4
  | 5, 2 => some 5
  | 6, 0 => some 3
  | 6, 1 => some 4
  | 6, 2 => some 6
  | 7, 0 => some 7
  | 7, 1 => some 4
  | 7, 2 => some 6
  | 8, 0 => some 7
  | 8, 1 => some 8
  | 8, 2 => some 6
  | 9, 0 => some 9
  | 9, 1 => some 8
  | 9, 2 => some 6
  | 10, 0 => some 9
  | 10, 1 => some 10
  | 10, 2 => some 6
  | 11, 0 => some 9
  | 11, 1 => some 11
  | 11, 2 => some 6
  | _, _ => none

def issued (k : V) (i : I) : Prop := match i.val with
  | 0 => 3 ≤ k.val
  | 1 => 4 ≤ k.val
  | 2 => 7 ≤ k.val
  | _ => 8 ≤ k.val

instance (k : V) (i : I) : Decidable (issued k i) := by
  unfold issued; split <;> infer_instance

private theorem parentList_mem : ∀ v p : V, p ∈ parentList v ↔ p ∈ parentTable v := by decide
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
private theorem head_causal : ∀ k : V, ∀ r : R, ∀ v : V,
    heads k r = some v →
    (7 ≤ k.val → (2 : I) ∈ (records v).2 → (0 : I) ∈ (records v).2) ∧
    (8 ≤ k.val → (3 : I) ∈ (records v).2 → (1 : I) ∈ (records v).2) := by decide
private theorem same_replica : ∀ k : V, ∀ i j : I,
    issued k i → issued k j → i ≠ j → (event i).2.1 = (event j).2.1 →
      (7 ≤ k.val ∧ i = 0 ∧ j = 2) ∨ (8 ≤ k.val ∧ i = 1 ∧ j = 3) ∨
      (7 ≤ k.val ∧ i = 2 ∧ j = 0) ∨ (8 ≤ k.val ∧ i = 3 ∧ j = 1) := by decide
private theorem gca_record : ∀ a b c : V,
    c ∈ ancestors a → c ∈ ancestors b →
    (∀ w : V, w ∈ ancestors a → w ∈ ancestors b → w ∈ ancestors c) →
    (records c).2 = (records a).2 ∩ (records b).2 := by decide

private theorem event_injective : Function.Injective event := by
  intro i j h
  have time : ∀ i : I, (event i).1 = i.val + 1 := by intro i; fin_cases i <;> rfl
  have ht := congrArg Prod.fst h
  rw [time, time] at ht
  apply Fin.ext
  exact Nat.add_right_cancel ht

def ver (k : V) (v : Nat) : Option ((D Nat).State × Set Event) :=
  if h : v < 12 ∧ v ≤ k.val then
    some ((records ⟨v,h.1⟩).1, ↑((records ⟨v,h.1⟩).2.image event)) else none

def head (k : V) (r : Nat) : Option Nat :=
  if h : r < 3 then (heads k ⟨r,h⟩).map Fin.val else none

def parents (k : V) (v : Nat) : List Nat :=
  if h : v < 12 ∧ v ≤ k.val then
    ((parentList ⟨v,h.1⟩).map Fin.val) else []

def vis (k : V) (a b : Event) : Prop :=
  (7 ≤ k.val ∧ a = event 0 ∧ b = event 2) ∨
  (8 ≤ k.val ∧ a = event 1 ∧ b = event 3)

private theorem ver_cases {k : V} {v : Nat} {s : (D Nat).State} {E : Set Event}
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
    (h : headEventsFrom (D := D Nat) (ver k) (head k) r = some E) :
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
    (hE : headEventsFrom (D := D Nat) (ver k) (head k) r = some E) (he : e ∈ E) :
    ∃ i : I, e = event i ∧ issued k i := by
  obtain ⟨rr,w,hw,rfl⟩ := headEvents_cases hE
  obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp he
  exact ⟨i,heq.symm,record_issued k w (head_bound k rr w hw) i hi⟩

private theorem origin_support {k : V} {i : I} (hi : issued k i) :
    ∃ r E, headEventsFrom (D := D Nat) (ver k) (head k) r = some E ∧ event i ∈ E := by
  obtain ⟨w,hw,hiw⟩ := origin_present k i hi
  let rr : R := ⟨(event i).2.1, by fin_cases i <;> decide⟩
  have hw' : heads k rr = some w := hw
  refine ⟨rr.val, (↑((records w).2.image event) : Set Event), ?_, ?_⟩
  · simp [headEventsFrom, head, rr.isLt, hw', ver, w.isLt, head_bound k rr w hw', Option.bind]
  · exact Finset.mem_image_of_mem event hiw

/-- Every prefix has a fully coherent configuration, including exact GCA/event
intersection correspondence. The finite certificates above are kernel checked. -/
def config (k : V) : Configuration (D Nat) where
  vis := vis k
  ver := ver k
  head := head k
  parents := parents k
  parents_lt := parents_rank k
  ver_init := by simp [ver, records, D]
  head_alloc := by
    intro r v h
    obtain ⟨rr,w,_,rfl,hw⟩ := head_cases h
    simp [ver, w.isLt, head_bound k rr w hw]
  vis_src := by
    intro a b h
    rcases h with ⟨hk,rfl,rfl⟩ | ⟨hk,rfl,rfl⟩
    · exact origin_support (by change 3 ≤ k.val; omega)
    · exact origin_support (by change 4 ≤ k.val; omega)
  vis_tgt := by
    intro a b h
    rcases h with ⟨hk,rfl,rfl⟩ | ⟨hk,rfl,rfl⟩
    · exact origin_support hk
    · exact origin_support hk
  vis_causal := by
    intro a b r E hv hE hb
    obtain ⟨rr,w,hw,rfl⟩ := headEvents_cases hE
    have hc := head_causal k rr w hw
    rcases hv with ⟨hk,rfl,rfl⟩ | ⟨hk,rfl,rfl⟩
    · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hb
      have hieq := event_injective he
      subst i
      exact Finset.mem_image_of_mem event (hc.1 hk hi)
    · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hb
      have hieq := event_injective he
      subst i
      exact Finset.mem_image_of_mem event (hc.2 hk hi)
  timestamps_distinct := by
    intro a b r E r' E' hE ha hE' hb hne ht
    obtain ⟨i,rfl,_⟩ := support_event hE ha
    obtain ⟨j,rfl,_⟩ := support_event hE' hb
    have time : ∀ i : I, (event i).1 = i.val + 1 := by intro i; fin_cases i <;> rfl
    rw [time,time] at ht
    have hij : i = j := Fin.ext (Nat.add_right_cancel ht)
    exact hne (hij ▸ rfl)
  causal_mono := by
    intro a b h
    rcases h with ⟨_,rfl,rfl⟩ | ⟨_,rfl,rfl⟩ <;> decide
  vis_total_same_replica := by
    intro a b r E r' E' hE ha hE' hb hne hrep
    obtain ⟨i,rfl,hi⟩ := support_event hE ha
    obtain ⟨j,rfl,hj⟩ := support_event hE' hb
    have hij : i ≠ j := fun heq => hne (heq ▸ rfl)
    rcases same_replica k i j hi hj hij hrep with
      ⟨hk,rfl,rfl⟩ | ⟨hk,rfl,rfl⟩ | ⟨hk,rfl,rfl⟩ | ⟨hk,rfl,rfl⟩
    · exact Or.inl (Or.inl ⟨hk,rfl,rfl⟩)
    · exact Or.inl (Or.inr ⟨hk,rfl,rfl⟩)
    · exact Or.inr (Or.inl ⟨hk,rfl,rfl⟩)
    · exact Or.inr (Or.inr ⟨hk,rfl,rfl⟩)
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
    simp only [Set.mem_inter_iff, Finset.mem_coe]
    rw [hc, Finset.image_inter _ _ event_injective]
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
  by_cases hr : rr < 3
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
  have hw : w < 12 := lt_of_le_of_lt (reaches_le (parents_rank k) hwa) a.isLt
  let wf : V := ⟨w,hw⟩
  have hwa' : wf ∈ ancestors a := reaches_sound hwa
  have hwb' : wf ∈ ancestors b := reaches_sound hwb
  have hck : c.val ≤ k.val := (reaches_le (parents_rank k)
    (reaches_complete k c a ha hc.1)).trans ha
  exact reaches_complete k wf c hck (hc.2.2 wf hwa' hwb')


private theorem ver_extend_values (k k' : V) (h : k'.val = k.val + 1)
    {s : State Nat} {E : Set Event}
    (hs : s = (records k').1) (he : E = ↑((records k').2.image event)) :
    (config k').ver = fun w => if w = k'.val then some (s,E) else (config k).ver w := by
  rw [hs,he]
  exact ver_extend k k' h

private theorem configuration_ext {C C' : Configuration (D Nat)}
    (hv : C.vis = C'.vis) (hs : C.ver = C'.ver)
    (hh : C.head = C'.head) (hp : C.parents = C'.parents) : C = C' := by
  cases C; cases C'
  cases hv; cases hs; cases hh; cases hp
  rfl

private theorem config_zero : config 0 = initConfig (D Nat) := by
  apply configuration_ext
  · funext a b; simp [config,vis,initConfig]
  · funext v; by_cases hv : v = 0 <;> simp [config,ver,initConfig,records,D,hv]
  · funext r
    by_cases hr : r < 3
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

private theorem fork_q : Step (D Nat) (config 0) (.fork 1 0) (config 1) := by
  apply Step.fork (D := D Nat) (v := 0) (vnew := 1) (s := (∅ : State Nat)) (ev := (∅ : Set Event))
  · rfl
  · rfl
  · simp [config,ver,records]
  · rfl
  · decide
  · funext a b; simp [config,vis]
  · simpa [config,records] using ver_extend 0 1 rfl
  · exact head_extend 0 1 1 (by decide)
  · simpa [config,parentList] using parents_extend 0 1 rfl

private theorem fork_r : Step (D Nat) (config 1) (.fork 2 0) (config 2) := by
  apply Step.fork (D := D Nat) (v := 0) (vnew := 2) (s := (∅ : State Nat)) (ev := (∅ : Set Event))
  · rfl
  · rfl
  · simp [config,ver,records]
  · rfl
  · decide
  · funext a b; simp [config,vis]
  · simpa [config,records] using ver_extend 1 2 rfl
  · exact head_extend 1 2 2 (by decide)
  · simpa [config,parentList] using parents_extend 1 2 rfl

private theorem add_p : Step (D Nat) (config 2) (.apply 1 0 (.add 7)) (config 3) := by
  apply Step.apply (D := D Nat) (v := 0) (vnew := 3) (s := (∅ : State Nat)) (ev := (∅ : Set Event))
  · rfl
  · simp [config,ver,records]
  · exact fresh_time 2 1 (by decide)
  · exact fresh_store 2 1 (by decide)
  · rfl
  · decide
  · funext a b; apply propext
    change vis 3 a b ↔ vis 2 a b ∨ (a ∈ (∅ : Set Event) ∧ b = (1,0,.add 7))
    simp [vis]
  · simpa [config,records,D,step] using ver_extend 2 3 rfl
  · exact head_extend 2 3 0 (by decide)
  · simpa [config,parentList] using parents_extend 2 3 rfl

private theorem add_q : Step (D Nat) (config 3) (.apply 2 1 (.add 7)) (config 4) := by
  apply Step.apply (D := D Nat) (v := 1) (vnew := 4) (s := (∅ : State Nat)) (ev := (∅ : Set Event))
  · rfl
  · simp [config,ver,records]
  · exact fresh_time 3 2 (by decide)
  · exact fresh_store 3 2 (by decide)
  · rfl
  · decide
  · funext a b; apply propext
    change vis 4 a b ↔ vis 3 a b ∨ (a ∈ (∅ : Set Event) ∧ b = (2,1,.add 7))
    simp [vis]
  · simpa [config,records,D,step] using ver_extend 3 4 rfl
  · exact head_extend 3 4 1 (by decide)
  · simpa [config,parentList] using parents_extend 3 4 rfl



private theorem copy_p_to_r : Step (D Nat) (config 4) (.merge 2 0) (config 5) := by
  apply Step.merge (D := D Nat) (v₁ := 2) (v₂ := 3) (vT := 0) (vm := 5)
    (s₁ := (records 2).1) (s₂ := (records 3).1) (sT := (records 0).1)
    (ev₁ := (↑((records 2).2.image event) : Set Event))
    (ev₂ := (↑((records 3).2.image event) : Set Event))
    (evT := (↑((records 0).2.image event) : Set Event))
  · rfl
  · rfl
  · exact ver_at 4 2 (by decide)
  · exact ver_at 4 3 (by decide)
  · exact gca 4 2 3 0 (by decide) (by decide) (by decide)
  · exact ver_at 4 0 (by decide)
  · rfl
  · decide
  · decide
  · funext a b; apply propext; change vis 5 a b ↔ vis 4 a b; simp [vis]
  · apply ver_extend_values 4 5 rfl
    · decide
    · ext e; simp [records,event] <;> tauto
  · exact head_extend 4 5 2 (by decide)
  · simpa [config,parentList] using parents_extend 4 5 rfl

private theorem merge_adds : Step (D Nat) (config 5) (.merge 2 1) (config 6) := by
  apply Step.merge (D := D Nat) (v₁ := 5) (v₂ := 4) (vT := 0) (vm := 6)
    (s₁ := (records 5).1) (s₂ := (records 4).1) (sT := (records 0).1)
    (ev₁ := (↑((records 5).2.image event) : Set Event))
    (ev₂ := (↑((records 4).2.image event) : Set Event))
    (evT := (↑((records 0).2.image event) : Set Event))
  · rfl
  · rfl
  · exact ver_at 5 5 (by decide)
  · exact ver_at 5 4 (by decide)
  · exact gca 5 5 4 0 (by decide) (by decide) (by decide)
  · exact ver_at 5 0 (by decide)
  · rfl
  · decide
  · decide
  · funext a b; apply propext; change vis 6 a b ↔ vis 5 a b; simp [vis]
  · apply ver_extend_values 5 6 rfl
    · decide
    · ext e; simp [records,event] <;> tauto
  · exact head_extend 5 6 2 (by decide)
  · simpa [config,parentList] using parents_extend 5 6 rfl

private theorem merge_left : Step (D Nat) (config 8) (.merge 0 2) (config 9) := by
  apply Step.merge (D := D Nat) (v₁ := 7) (v₂ := 6) (vT := 3) (vm := 9)
    (s₁ := (records 7).1) (s₂ := (records 6).1) (sT := (records 3).1)
    (ev₁ := (↑((records 7).2.image event) : Set Event))
    (ev₂ := (↑((records 6).2.image event) : Set Event))
    (evT := (↑((records 3).2.image event) : Set Event))
  · rfl
  · rfl
  · exact ver_at 8 7 (by decide)
  · exact ver_at 8 6 (by decide)
  · exact gca 8 7 6 3 (by decide) (by decide) (by decide)
  · exact ver_at 8 3 (by decide)
  · rfl
  · decide
  · decide
  · funext a b; apply propext; change vis 9 a b ↔ vis 8 a b; simp [vis]
  · apply ver_extend_values 8 9 rfl
    · decide
    · ext e; simp [records,event] <;> tauto
  · exact head_extend 8 9 0 (by decide)
  · simpa [config,parentList] using parents_extend 8 9 rfl

private theorem merge_right : Step (D Nat) (config 9) (.merge 1 2) (config 10) := by
  apply Step.merge (D := D Nat) (v₁ := 8) (v₂ := 6) (vT := 4) (vm := 10)
    (s₁ := (records 8).1) (s₂ := (records 6).1) (sT := (records 4).1)
    (ev₁ := (↑((records 8).2.image event) : Set Event))
    (ev₂ := (↑((records 6).2.image event) : Set Event))
    (evT := (↑((records 4).2.image event) : Set Event))
  · rfl
  · rfl
  · exact ver_at 9 8 (by decide)
  · exact ver_at 9 6 (by decide)
  · exact gca 9 8 6 4 (by decide) (by decide) (by decide)
  · exact ver_at 9 4 (by decide)
  · rfl
  · decide
  · decide
  · funext a b; apply propext; change vis 10 a b ↔ vis 9 a b; simp [vis]
  · apply ver_extend_values 9 10 rfl
    · decide
    · ext e; simp [records,event] <;> tauto
  · exact head_extend 9 10 1 (by decide)
  · simpa [config,parentList] using parents_extend 9 10 rfl

private theorem merge_final : Step (D Nat) (config 10) (.merge 1 0) (config 11) := by
  apply Step.merge (D := D Nat) (v₁ := 10) (v₂ := 9) (vT := 6) (vm := 11)
    (s₁ := (records 10).1) (s₂ := (records 9).1) (sT := (records 6).1)
    (ev₁ := (↑((records 10).2.image event) : Set Event))
    (ev₂ := (↑((records 9).2.image event) : Set Event))
    (evT := (↑((records 6).2.image event) : Set Event))
  · rfl
  · rfl
  · exact ver_at 10 10 (by decide)
  · exact ver_at 10 9 (by decide)
  · exact gca 10 10 9 6 (by decide) (by decide) (by decide)
  · exact ver_at 10 6 (by decide)
  · rfl
  · decide
  · decide
  · funext a b; apply propext; change vis 11 a b ↔ vis 10 a b; simp [vis]
  · apply ver_extend_values 10 11 rfl
    · decide
    · ext e; simp [records,event] <;> tauto
  · exact head_extend 10 11 1 (by decide)
  · simpa [config,parentList] using parents_extend 10 11 rfl

private theorem remove_p : Step (D Nat) (config 6) (.apply 3 0 (.remove 7)) (config 7) := by
  apply Step.apply (D := D Nat) (v := 3) (vnew := 7)
    (s := (records 3).1) (ev := (↑((records 3).2.image event) : Set Event))
  · rfl
  · exact ver_at 6 3 (by decide)
  · exact fresh_time 6 3 (by decide)
  · exact fresh_store 6 3 (by decide)
  · rfl
  · decide
  · funext a b
    apply propext
    change vis 7 a b ↔ vis 6 a b ∨ (a ∈ (↑((records 3).2.image event) : Set Event) ∧ b = (3,0,.remove 7))
    simp [vis,records,event]
  · apply ver_extend_values 6 7 rfl
    · decide
    · ext e; simp [records,event] <;> tauto
  · exact head_extend 6 7 0 (by decide)
  · simpa [config,parentList] using parents_extend 6 7 rfl

private theorem remove_q : Step (D Nat) (config 7) (.apply 4 1 (.remove 7)) (config 8) := by
  apply Step.apply (D := D Nat) (v := 4) (vnew := 8)
    (s := (records 4).1) (ev := (↑((records 4).2.image event) : Set Event))
  · rfl
  · exact ver_at 7 4 (by decide)
  · exact fresh_time 7 4 (by decide)
  · exact fresh_store 7 4 (by decide)
  · rfl
  · decide
  · funext a b
    apply propext
    change vis 8 a b ↔ vis 7 a b ∨ (a ∈ (↑((records 4).2.image event) : Set Event) ∧ b = (4,1,.remove 7))
    simp [vis,records,event]
  · apply ver_extend_values 7 8 rfl
    · decide
    · ext e; simp [records,event] <;> tauto
  · exact head_extend 7 8 1 (by decide)
  · simpa [config,parentList] using parents_extend 7 8 rfl


private theorem read_left : Step (D Nat) (config 9) (.query 0 (7 : Nat) true) (config 9) := by
  apply Step.query (D := D Nat) (s := (records 9).1)
  · simp [Configuration.headState,headStateFrom,config,head,heads,ver,records,Option.bind]
  · change true = query (records 9).1 7
    decide

private theorem read_right : Step (D Nat) (config 10) (.query 1 (7 : Nat) true) (config 10) := by
  apply Step.query (D := D Nat) (s := (records 10).1)
  · simp [Configuration.headState,headStateFrom,config,head,heads,ver,records,Option.bind]
  · change true = query (records 10).1 7
    decide

private theorem read_final : Step (D Nat) (config 11) (.query 1 (7 : Nat) false) (config 11) := by
  apply Step.query (D := D Nat) (s := (records 11).1)
  · simp [Configuration.headState,headStateFrom,config,head,heads,ver,records,Option.bind]
  · change false = query (records 11).1 7
    decide

/-- The figure's computation, including observations at both crossed branches
and the final merge. Queries allocate no additional version. -/
def trace : List (Label (D Nat) × Configuration (D Nat)) :=
  [(.fork 1 0, config 1), (.fork 2 0, config 2),
   (.apply 1 0 (.add 7), config 3), (.apply 2 1 (.add 7), config 4),
   (.merge 2 0, config 5), (.merge 2 1, config 6),
   (.apply 3 0 (.remove 7), config 7), (.apply 4 1 (.remove 7), config 8),
   (.merge 0 2, config 9), (.query 0 (7 : Nat) true, config 9),
   (.merge 1 2, config 10), (.query 1 (7 : Nat) true, config 10),
   (.merge 1 0, config 11), (.query 1 (7 : Nat) false, config 11)]

/-- Actual raw execution: timestamps are globally fresh, all merges have their
stated GCA, and the query labels contain the actual implementation answers. -/
theorem defeater_execution : (labeledTS (D Nat)).Execution (initConfig (D Nat)) trace := by
  rw [← config_zero]
  unfold trace
  refine .cons fork_q ?_
  refine .cons fork_r ?_
  refine .cons add_p ?_
  refine .cons add_q ?_
  refine .cons copy_p_to_r ?_
  refine .cons merge_adds ?_
  refine .cons remove_p ?_
  refine .cons remove_q ?_
  refine .cons merge_left ?_
  refine .cons read_left ?_
  refine .cons merge_right ?_
  refine .cons read_right ?_
  refine .cons merge_final ?_
  refine .cons read_final ?_
  exact .nil _

/-- Every reached configuration in the concrete defeater has an admitted
ordinary-set history for every active replica and every query. -/
theorem defeater_ra_execution :
    RAExecution (D Nat) (conflict Nat) (spec Nat).toSpec (initConfig (D Nat)) trace :=
  rawRA trace defeater_execution

theorem defeater_final_ra :
    RALinearizable (D Nat) (conflict Nat) (spec Nat).toSpec (config 11) := by
  exact defeater_ra_execution.2 (.query 1 (7 : Nat) false, config 11) (by simp [trace])

/-- Literal state table agrees with every operation version drawn in the
manuscript. The intermediate copy/fork vertices are separately allocated. -/
theorem figure_states :
    (records 3).1 = SPOT.v₁ ∧ (records 4).1 = SPOT.v₂ ∧
    (records 6).1 = SPOT.v₃ ∧ (records 7).1 = SPOT.v₄ ∧
    (records 8).1 = SPOT.v₅ ∧ (records 9).1 = SPOT.v₆ ∧
    (records 10).1 = SPOT.v₇ ∧ (records 11).1 = SPOT.v₈ := by decide

/-- The concrete trace records both add-wins branch answers and the final
absence; the final state cannot be either branch projection. -/
theorem figure_observations :
    (config 9).headState 0 = some ({(7,2)} : State Nat) ∧
    (config 10).headState 1 = some ({(7,1)} : State Nat) ∧
    (config 11).headState 1 = some (∅ : State Nat) ∧
    (records 11).1 ≠ (records 9).1 ∧ (records 11).1 ≠ (records 10).1 := by
  simp [Configuration.headState,headStateFrom,config,head,heads,ver,records,Option.bind]

#print axioms defeater_execution
#print axioms defeater_ra_execution
#print axioms figure_states
end Sal.MRDTs.Paper1.ORSet.Execution
