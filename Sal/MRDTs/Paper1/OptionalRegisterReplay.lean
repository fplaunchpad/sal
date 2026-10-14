import Sal.MRDTs.Paper1.OptionalRegisterPolicy
import Sal.MRDTs.Paper1.OptionalRegisterCounts
import Sal.MRDTs.Paper1.OptionalRegisterAlgebra

namespace Sal.MRDTs.Paper1.OptionalRegister
open Foundation ConcreteMRDT Instances.OptionalRegister
open Classical
abbrev Event := Op Action

/-- Timestamp monotonicity is supplied by actual configurations, independently
of the source merge. Bare ReplayContext does not include this fact. -/
structure GoodContext (C : ReplayContext D.toUpdateSig) : Prop where
  trans : Transitive C.vis
  irrefl : ∀ e, ¬ C.vis e e
  mono : ∀ {a b}, C.vis a b → a.time < b.time

def scheme (C : ReplayContext D.toUpdateSig) : MetadataDependencies C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

def LiveEvent (C : ReplayContext D.toUpdateSig) (E : Set Event) (w : Event) : Prop :=
  w.op.isSet = true ∧ ∀ d ∈ E, d.op = .unset → ¬ C.vis w d

def Live (C : ReplayContext D.toUpdateSig) (E : Set Event) (r : Nat) : Prop :=
  ∃ w ∈ E, w.rep = r ∧ LiveEvent C E w

def rows (F : Finset Event) : Finset Nat := (F.filter (fun e => e.op.isSet)).image Op.rep

/-- Independent finite-event meaning of every source map field. The payload
witness is the latest Set at its issuer; an active witness survives resets.
No merge equation or Join is a field of this relation. -/
structure Represents (C : ReplayContext D.toUpdateSig) (E : Set Event) (s : State) : Prop where
  good : GoodContext C
  supported : Supported C E
  finite : ∃ F : Finset Event, (↑F : Set Event) = E
  domain : ∀ F : Finset Event, (↑F : Set Event) = E → s.domain = rows F
  counts : ∀ F : Finset Event, (↑F : Set Event) = E → ∀ r, (s.cells r).1.1 = OptionalRegisterCounts.count F r
  active : ∀ r, (s.cells r).1.2 = true ↔ Live C E r
  inactive : ∀ r, (s.cells r).1.2 = false → (s.cells r).2 = (0,0)
  payload : ∀ r, (s.cells r).1.2 = true →
    ∃ w ∈ E, w.rep = r ∧ LiveEvent C E w ∧ (s.cells r).2 = (w.time,valueOf w) ∧
      ∀ x ∈ E, x.rep = r → x.op.isSet = true → x.time ≤ w.time

abbrev representation : Representation D := Represents

theorem timestamp_unique {C : ReplayContext D.toUpdateSig} {E : Set Event}
    (sup : Supported C E) {a b : Event} (ha : a ∈ E) (hb : b ∈ E)
    (same : a.time = b.time) : a = b := by
  by_contra ne
  obtain ⟨r,S,hr,hs⟩ := sup a ha
  obtain ⟨r',S',hr',hs'⟩ := sup b hb
  exact C.timestamps_distinct hr hs hr' hs' ne same

theorem latest_live {C : ReplayContext D.toUpdateSig} {E : Set Event}
    (good : GoodContext C) (sup : Supported C E) {w x : Event}
    (hw : w ∈ E) (hx : x ∈ E) (same : w.rep = x.rep)
    (win : x.op.isSet = true) (le : w.time ≤ x.time) (live : LiveEvent C E w) :
    LiveEvent C E x := by
  refine ⟨win,?_⟩
  intro d hd reset edge
  by_cases eq : w = x
  · subst x; exact live.2 d hd reset edge
  obtain ⟨r,S,hr,hs⟩ := sup w hw
  obtain ⟨r',S',hr',hs'⟩ := sup x hx
  rcases C.vis_total_same_replica hr hs hr' hs' eq same with before | after
  · exact live.2 d hd reset (good.trans before edge)
  · exact (not_lt_of_ge le) (good.mono after)

theorem initial_rep (C : ReplayContext D.toUpdateSig) (good : GoodContext C) :
    representation C ∅ initial := by
  refine ⟨good,by simp [Supported],⟨∅,by simp⟩,?_,?_,?_,?_,?_⟩
  · intro F hF
    have eq : F = ∅ := Finset.coe_injective (by simpa only [Finset.coe_empty] using hF)
    subst F; rfl
  · intro F hF r
    have eq : F = ∅ := Finset.coe_injective (by simpa only [Finset.coe_empty] using hF)
    subst F; simp [initial,zero,OptionalRegisterCounts.count,OptionalRegisterCounts.winners]
  · intro r; simp [initial,zero,Live]
  · intro r _; rfl
  · intro r h; simp [initial,zero] at h

theorem unique : Raw.Unique representation := by
  intro C E s t hs ht
  obtain ⟨F,hF⟩ := hs.finite
  apply State.ext ((hs.domain F hF).trans (ht.domain F hF).symm)
  intro r
  apply Prod.ext
  · apply Prod.ext
    · exact (hs.counts F hF r).trans (ht.counts F hF r).symm
    · have eq := (hs.active r).trans (ht.active r).symm
      cases a : (s.cells r).1.2 <;> cases b : (t.cells r).1.2 <;> simp_all
  · by_cases active : (s.cells r).1.2 = true
    · have active' := (ht.active r).mpr ((hs.active r).mp active)
      obtain ⟨w,hw,own,live,payload,latest⟩ := hs.payload r active
      obtain ⟨x,hx,own',live',payload',latest'⟩ := ht.payload r active'
      have eq : w = x := timestamp_unique hs.supported hw hx (by
        have wx := latest x hx own' live'.1
        have xw := latest' w hw own live.1
        exact Nat.le_antisymm xw wx)
      subst x
      exact payload.trans payload'.symm
    · have inactive : (s.cells r).1.2 = false := Bool.eq_false_of_not_eq_true active
      have inactive' : (t.cells r).1.2 = false := by
        cases h : (t.cells r).1.2
        · rfl
        · exact (active ((hs.active r).mpr ((ht.active r).mp h))).elim
      rw [hs.inactive r inactive,ht.inactive r inactive']

theorem latest_witness (C : ReplayContext D.toUpdateSig) (E : Set Event)
    (good : GoodContext C) (sup : Supported C E) (F : Finset Event)
    (hF : (↑F : Set Event) = E) (r : Nat) (live : Live C E r) :
    ∃ w ∈ E, w.rep = r ∧ LiveEvent C E w ∧
      ∀ x ∈ E, x.rep = r → x.op.isSet = true → x.time ≤ w.time := by
  obtain ⟨u,hu,own,alive⟩ := live
  have huF : u ∈ F := by rw [← hF] at hu; exact hu
  have hn : (OptionalRegisterCounts.winners F r).Nonempty :=
    ⟨u,Finset.mem_filter.mpr ⟨huF,own,alive.1⟩⟩
  obtain ⟨w,hw,maximal⟩ := (OptionalRegisterCounts.winners F r).exists_max_image Op.time hn
  obtain ⟨hwF,wown,wwin⟩ := Finset.mem_filter.mp hw
  have hwE : w ∈ E := by rw [← hF]; exact hwF
  have uw := maximal u (Finset.mem_filter.mpr ⟨huF,own,alive.1⟩)
  refine ⟨w,hwE,wown,latest_live good sup hu hwE (own.trans wown.symm) wwin uw alive,?_⟩
  intro x hx xo xs
  have hxF : x ∈ F := by rw [← hF] at hx; exact hx
  exact maximal x (Finset.mem_filter.mpr ⟨hxF,xo,xs⟩)

private theorem no_row (F : Finset Event) (r : Nat) (absent : r ∉ rows F) :
    OptionalRegisterCounts.winners F r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,own,win⟩ := Finset.mem_filter.mp he
  apply absent
  exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,win⟩,own⟩

theorem represented (C : ReplayContext D.toUpdateSig) (E : Set Event)
    (good : GoodContext C) (sup : Supported C E) (F : Finset Event)
    (hF : (↑F : Set Event) = E) : ∃ s, representation C E s := by
  let choose (r : Nat) (live : Live C E r) : Event :=
    (latest_witness C E good sup F hF r live).choose
  have chosen (r : Nat) (live : Live C E r) :=
    (latest_witness C E good sup F hF r live).choose_spec
  let cells : Nat → Cell := fun r =>
    ((OptionalRegisterCounts.count F r,decide (Live C E r)),
      if h : Live C E r then ((choose r h).time,valueOf (choose r h)) else (0,0))
  have outside : ∀ r, r ∉ rows F → cells r = zero := by
    intro r absent
    have empty := no_row F r absent
    have dead : ¬ Live C E r := by
      rintro ⟨w,hw,own,live⟩
      have hwF : w ∈ F := by rw [← hF] at hw; exact hw
      have mem : w ∈ OptionalRegisterCounts.winners F r := Finset.mem_filter.mpr ⟨hwF,own,live.1⟩
      rw [empty] at mem; exact Finset.notMem_empty _ mem
    simp [cells,zero,dead,OptionalRegisterCounts.count,empty]
  let s : State := ⟨rows F,cells,outside⟩
  refine ⟨s,good,sup,⟨F,hF⟩,?_,?_,?_,?_,?_⟩
  · intro G hG
    have eq : F = G := Finset.coe_injective (hF.trans hG.symm)
    simp [s,eq]
  · intro G hG r
    have eq : F = G := Finset.coe_injective (hF.trans hG.symm)
    simp [s,cells,eq]
  · intro r; simp [s,cells]
  · intro r inactive
    have dead : ¬ Live C E r := by simpa [s,cells] using inactive
    simp [s,cells,dead]
  · intro r active
    have live : Live C E r := by simpa [s,cells] using active
    refine ⟨choose r live,(chosen r live).1,(chosen r live).2.1,(chosen r live).2.2.1,?_,(chosen r live).2.2.2⟩
    simp [s,cells,live,choose]

private theorem noncomm_set_kind (b c : Event) (win : b.op.isSet = true)
    (conflict : ¬ D.toUpdateSig.commutes b c) : c.op = .unset ∨ c.rep = b.rep := by
  cases hb : b.op with
  | unset => simp [hb,Action.isSet] at win
  | set v =>
    cases hc : c.op with
    | unset => exact Or.inl rfl
    | set w =>
      right; by_contra ne
      rcases b with ⟨tb,rb,ob⟩; rcases c with ⟨tc,rc,oc⟩
      simp only [Op.op] at hb hc
      subst ob; subst oc
      exact conflict (sets_commute tb rb v tc rc w (by simpa [Op.rep,ne_comm] using ne))

/-- A semantically maximal Unset kills every live Set. The absorber check uses
actual Set/Set same-issuer conflicts and the independently latest row Set. -/
theorem reset_kills_live (C : ReplayContext D.toUpdateSig) (E : Set Event)
    (good : GoodContext C) (sup : Supported C E) (F : Finset Event) (hF : (↑F : Set Event) = E)
    (e : Event) (supported : e ∈ C.events) (reset : e.op = .unset)
    (semantic : ∀ x ∈ E, x ≠ e → ¬ paperOrder policy C (insert e E) e x)
    (metadata : ∀ x ∈ E, ¬ C.vis e x) (fresh : e ∉ E) (r : Nat) :
    ¬ Live C (insert e E) r := by
  rintro ⟨u,hu,own,alive⟩
  have une : u ≠ e := by intro eq; subst u; simp [LiveEvent,reset,Action.isSet] at alive
  have huE : u ∈ E := (Set.mem_insert_iff.mp hu).resolve_left une
  have liveE : Live C E r := ⟨u,huE,own,alive.1,fun d hd => alive.2 d (Or.inr hd)⟩
  obtain ⟨w,hw,wown,walive,latest⟩ := latest_witness C E good sup F hF r liveE
  have sup' : Supported C (insert e E) := fun x hx => hx.elim (fun eq => eq ▸ supported) (sup x)
  have alive' : LiveEvent C (insert e E) w := latest_live good sup' hu (Or.inr hw)
    (own.trans wown.symm) walive.1 (latest u huE own alive.1) alive
  have we : w ≠ e := fun eq => fresh (eq ▸ hw)
  apply semantic w hw we
  refine Or.inr ⟨metadata w hw,alive'.2 e (Or.inl rfl) reset,?_,?_⟩
  · exact ⟨reset,by cases hop : w.op <;> simp [LiveEvent,hop,Action.isSet] at walive ⊢⟩
  · rintro ⟨d,hd,edge,conflict⟩
    have dne : d ≠ e := by intro eq; subst d; exact alive'.2 e (Or.inl rfl) reset edge
    have hdE : d ∈ E := (Set.mem_insert_iff.mp hd).resolve_left dne
    rcases noncomm_set_kind w d walive.1 conflict with rd | same
    · exact walive.2 d hdE rd edge
    · have dset : d.op.isSet = true := by
        cases hop : d.op <;> simp [hop,Action.isSet]
        exact False.elim (walive.2 d hdE hop edge)
      have le := latest d hdE (same.trans wown) dset
      exact (not_lt_of_ge le) (good.mono edge)

theorem live_insert_set (C : ReplayContext D.toUpdateSig) (E : Set Event) (e : Event)
    (win : e.op.isSet = true) (metadata : ∀ x ∈ E, ¬ C.vis e x) (r : Nat) :
    Live C (insert e E) r ↔ r = e.rep ∨ Live C E r := by
  constructor
  · rintro ⟨w,hw,own,alive⟩
    rcases hw with rfl | hw
    · exact Or.inl own.symm
    · exact Or.inr ⟨w,hw,own,alive.1,fun d hd => alive.2 d (Or.inr hd)⟩
  · rintro (own | ⟨w,hw,wown,alive⟩)
    · refine ⟨e,Or.inl rfl,own.symm,win,?_⟩
      intro d hd reset
      rcases hd with rfl | hd
      · simp [reset,Action.isSet] at win
      · exact metadata d hd
    · refine ⟨w,Or.inr hw,wown,alive.1,?_⟩
      intro d hd reset
      rcases hd with rfl | hd
      · simp [reset,Action.isSet] at win
      · exact alive.2 d hd reset

theorem insert_rep (C : ReplayContext D.toUpdateSig) (E : Set Event) (s : State) (e : Event)
    (hs : representation C E s) (supported : e ∈ C.events) (fresh : e ∉ E)
    (semantic : ∀ x ∈ E, x ≠ e → ¬ paperOrder policy C (insert e E) e x)
    (metadata : ∀ x ∈ E, ¬ C.vis e x) :
    representation C (insert e E) (update s e) := by
  obtain ⟨F,hF⟩ := hs.finite
  have absent : e ∉ F := by intro he; exact fresh (by rw [← hF]; exact he)
  have hIns : (↑(insert e F) : Set Event) = insert e E := by simp [hF]
  have sup : Supported C (insert e E) := fun x hx => hx.elim (fun eq => eq ▸ supported) (hs.supported x)
  refine ⟨hs.good,sup,⟨insert e F,hIns⟩,?_,?_,?_,?_,?_⟩
  · intro G hG
    have eq : G = insert e F := Finset.coe_injective (hG.trans hIns.symm)
    subst G
    cases hop : e.op with
    | set v => simp [update,hop,hs.domain F hF,rows,Finset.filter_insert,Action.isSet]
    | unset => simp [update,hop,hs.domain F hF,rows,Finset.filter_insert,Action.isSet]
  · intro G hG r
    have eq : G = insert e F := Finset.coe_injective (hG.trans hIns.symm)
    subst G
    cases hop : e.op <;> by_cases own : r = e.rep
    all_goals simp [update,hop,own,hs.counts F hF,OptionalRegisterCounts.count,
      OptionalRegisterCounts.winners,OptionalRegisterCounts.winningAt,
      Finset.filter_insert,Action.isSet,absent,eq_comm]
  · intro r
    cases hop : e.op with
    | set v =>
      rw [live_insert_set C E e (by simp [hop,Action.isSet]) metadata r]
      simp only [update,hop]
      split_ifs <;> simp_all [hs.active]
    | unset =>
      have dead := reset_kills_live C E hs.good hs.supported F hF e supported hop semantic metadata fresh r
      simp [update,hop,dead]
  · intro r inactive
    cases hop : e.op with
    | set v =>
      by_cases own : r = e.rep
      · simp [update,hop,own] at inactive
      · simpa [update,hop,own] using hs.inactive r (by simpa [update,hop,own] using inactive)
    | unset => simp [update,hop]
  · intro r active
    cases hop : e.op with
    | unset => simp [update,hop] at active
    | set v =>
      by_cases own : r = e.rep
      · have latest : ∀ x ∈ E, x.rep = e.rep → x.op.isSet = true → x.time < e.time := by
          intro x hx same _
          have ne : x ≠ e := fun eq => fresh (eq ▸ hx)
          obtain ⟨rx,Sx,hLx,hxS⟩ := hs.supported x hx
          obtain ⟨re,Se,hLe,heS⟩ := supported
          have vis := (C.vis_total_same_replica hLx hxS hLe heS ne same).resolve_right (metadata x hx)
          exact hs.good.mono vis
        refine ⟨e,Or.inl rfl,own.symm,?_,?_,?_⟩
        · refine ⟨by simp [hop,Action.isSet],?_⟩
          intro d hd reset
          rcases hd with rfl | hd
          · simp [hop] at reset
          · exact metadata d hd
        · simp [update,hop,own,valueOf]
        · intro x hx same win
          rcases hx with rfl | hx
          · exact le_rfl
          · exact le_of_lt (latest x hx (same.trans own) win)
      · have alive : (s.cells r).1.2 = true := by simpa [update,hop,own] using active
        obtain ⟨w,hw,wown,walive,payload,latest⟩ := hs.payload r alive
        refine ⟨w,Or.inr hw,wown,?_,?_,?_⟩
        · exact ⟨walive.1,fun d hd reset => hd.elim (fun eq => by subst d; simp [hop] at reset) (fun hd => walive.2 d hd reset)⟩
        · simpa [update,hop,own] using payload
        · intro x hx same win
          rcases hx with rfl | hx
          · exact (own same.symm).elim
          · exact latest x hx same win

theorem finite_rep (C : ReplayContext D.toUpdateSig) (E : Set Event) (s : State)
    (hs : representation C E s) : ∃ π, listPermOf π E := by
  obtain ⟨F,hF⟩ := hs.finite
  refine ⟨F.toList,Finset.nodup_toList _,?_⟩
  intro e
  simp only [Finset.mem_toList]
  change e ∈ F ↔ e ∈ E
  rw [← hF]; rfl

theorem joint_maximal (C : ReplayContext D.toUpdateSig) (E : Set Event) (s : State)
    (hs : representation C E s) (nonempty : E.Nonempty) :
    ∃ e ∈ E, (∀ x ∈ E, x ≠ e → ¬ paperOrder policy C E e x) ∧
      (∀ x ∈ E, x ≠ e → ¬ C.vis e x) := by
  obtain ⟨F,hF⟩ := hs.finite
  let A := F.filter (LiveEvent C E)
  by_cases alive : A.Nonempty
  · obtain ⟨e,he,maximal⟩ := A.exists_max_image Op.time alive
    obtain ⟨heF,heLive⟩ := Finset.mem_filter.mp he
    have heE : e ∈ E := by rw [← hF]; exact heF
    have maxvis : ∀ x ∈ E, x ≠ e → ¬ C.vis e x := by
      intro x hx ne edge
      have xwin : x.op.isSet = true := by
        cases hop : x.op
        · rfl
        · exact (heLive.2 x hx hop edge).elim
      have xLive : LiveEvent C E x := ⟨xwin,fun d hd reset next => heLive.2 d hd reset (hs.good.trans edge next)⟩
      have hxF : x ∈ F := by rw [← hF] at hx; exact hx
      have le := maximal x (Finset.mem_filter.mpr ⟨hxF,xLive⟩)
      exact (not_lt_of_ge le) (hs.good.mono edge)
    refine ⟨e,heE,?_,maxvis⟩
    intro x hx ne order
    rcases order with causal | conflict
    · exact maxvis x hx ne causal.1
    · have reset := conflict.2.2.1.1
      simp [LiveEvent,reset,Action.isSet] at heLive
  · have hn : F.Nonempty := by
      obtain ⟨e,he⟩ := nonempty
      exact ⟨e,by rw [← hF] at he; exact he⟩
    obtain ⟨e,he,maximal⟩ := F.exists_max_image Op.time hn
    have heE : e ∈ E := by rw [← hF]; exact he
    have maxvis : ∀ x ∈ E, x ≠ e → ¬ C.vis e x := by
      intro x hx _ edge
      have hxF : x ∈ F := by rw [← hF] at hx; exact hx
      exact (not_lt_of_ge (maximal x hxF)) (hs.good.mono edge)
    refine ⟨e,heE,?_,maxvis⟩
    intro x hx ne order
    rcases order with causal | conflict
    · exact maxvis x hx ne causal.1
    · obtain ⟨v,xset⟩ := conflict.2.2.1.2
      have xLive : LiveEvent C E x := by
        refine ⟨by simp [xset,Action.isSet],?_⟩
        intro d hd reset edge
        apply conflict.2.2.2
        refine ⟨d,hd,edge,?_⟩
        rcases x with ⟨tx,rx,ox⟩; rcases d with ⟨td,rd,od⟩
        simp only [Op.op] at xset reset
        subst ox; subst od
        exact set_unset_noncomm tx rx v td rd
      have hxF : x ∈ F := by rw [← hF] at hx; exact hx
      exact alive ⟨x,Finset.mem_filter.mpr ⟨hxF,xLive⟩⟩

private theorem paperOrder_shrink {C : ReplayContext D.toUpdateSig} {E U : Set Event}
    (sub : E ⊆ U) {a b : Event} (h : paperOrder policy C U a b) : paperOrder policy C E a b := by
  rcases h with h | ⟨hab,hba,pol,unabsorbed⟩
  · exact Or.inl h
  · exact Or.inr ⟨hab,hba,pol,fun ⟨c,hc,edge,nc⟩ => unabsorbed ⟨c,sub hc,edge,nc⟩⟩

theorem canonical_with_vis (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (s : State) (hs : representation C E s) :
    ∃ π : List Event, listPermOf π E ∧ respects π (paperOrder policy C E) ∧
      respects π C.vis ∧ applySeq D.toUpdateSig (initial) π = s := by
  obtain ⟨F,hF⟩ := hs.finite
  have hsF : representation C (↑F : Set Event) s := by
    rw [hF]; exact hs
  suffices result : ∀ (F : Finset Event) (s : State),
      representation C (↑F : Set Event) s →
      ∃ π : List Event, listPermOf π (↑F : Set Event) ∧
        respects π (paperOrder policy C (↑F : Set Event)) ∧ respects π C.vis ∧
        applySeq D.toUpdateSig (initial) π = s by
    simpa [hF] using result F s hsF
  intro F
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    intro s hs
    by_cases empty : F = ∅
    · subst F
      have eq := unique C ∅ s (initial) (by simpa using hs) (initial_rep C hs.good)
      refine ⟨[],by simp [listPermOf],by simp [respects],by simp [respects],?_⟩
      simpa [applySeq] using eq.symm
    · have nonempty : (↑F : Set Event).Nonempty := by
        obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
        exact ⟨e,he⟩
      obtain ⟨e,he,semantic,metadata⟩ := joint_maximal C _ s hs nonempty
      have heF : e ∈ F := he
      have erased : (↑(F.erase e) : Set Event) = (↑F : Set Event) \ {e} := by ext x; simp
      have supported : Supported C (↑(F.erase e) : Set Event) := by
        intro x hx; exact hs.supported x (Finset.mem_of_mem_erase hx)
      obtain ⟨t,ht⟩ := represented C _ hs.good supported (F.erase e) rfl
      obtain ⟨π,hp,order,vis,fold⟩ := ih (F.erase e) (Finset.erase_ssubset heF) t ht
      have fresh : e ∉ (↑(F.erase e) : Set Event) := by simp
      have unionEq : insert e (↑(F.erase e) : Set Event) = (↑F : Set Event) := by
        ext x
        simp only [Set.mem_insert_iff,Finset.mem_coe,Finset.mem_erase]
        constructor
        · rintro (rfl | hx); exact heF; exact hx.2
        · intro hx; by_cases same : x = e
          · exact Or.inl same
          · exact Or.inr ⟨same,hx⟩
      have updated := insert_rep C _ t e ht (hs.supported e he) fresh
        (fun x hx ne => by rw [unionEq]; exact semantic x (Finset.mem_of_mem_erase hx) ne)
        (fun x hx => metadata x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx))
      rw [unionEq] at updated
      have eq := unique C _ (update t e) s updated hs
      refine ⟨π ++ [e],?_,?_,?_,?_⟩
      · refine ⟨?_,?_⟩
        · rw [List.nodup_append]
          refine ⟨hp.1,by simp,?_⟩
          intro x hx y hy same
          have ye : y = e := by simpa using hy
          subst y; subst x
          exact fresh ((hp.2 e).mp hx)
        · intro x
          simp only [List.mem_append,List.mem_singleton]
          rw [hp.2 x]
          change (x ∈ F.erase e ∨ x = e) ↔ x ∈ F
          simp only [Finset.mem_erase]
          constructor
          · rintro (hx | rfl); exact hx.2; exact heF
          · intro hx; by_cases same : x = e
            · exact Or.inr same
            · exact Or.inl ⟨same,hx⟩
      · change (π ++ [e]).Pairwise _
        rw [List.pairwise_append]
        refine ⟨order.imp (fun {_ _} no edge => no (paperOrder_shrink
          (fun _ hx => Finset.mem_of_mem_erase hx) edge)),by simp,?_⟩
        intro x hx y hy
        have ye : y = e := by simpa using hy
        subst y
        have hxF := Finset.mem_of_mem_erase ((hp.2 x).mp hx)
        exact semantic x hxF (Finset.ne_of_mem_erase ((hp.2 x).mp hx))
      · change (π ++ [e]).Pairwise _
        rw [List.pairwise_append]
        refine ⟨vis,by simp,?_⟩
        intro x hx y hy
        have ye : y = e := by simpa using hy
        subst y
        exact metadata x (Finset.mem_of_mem_erase ((hp.2 x).mp hx))
          (Finset.ne_of_mem_erase ((hp.2 x).mp hx))
      · rw [applySeq_append_single,fold]
        exact eq

theorem canonical (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (s : State) (hs : representation C E s) :
    Canonical policy C E s := by
  obtain ⟨π,hp,order,_,fold⟩ := canonical_with_vis C E s hs
  exact ⟨π,hp,order,fold⟩


theorem representedList (C : ReplayContext D.toUpdateSig) (E : Set Event)
    (good : GoodContext C) (π : List Event) (hp : listPermOf π E) (sup : Supported C E) :
    ∃ s, representation C E s := by
  apply represented C E good sup π.toFinset
  ext e; simp [hp.2 e]

theorem replaySupply (C : ReplayContext D.toUpdateSig) (good : GoodContext C) :
    Raw.ReplaySupply policy representation scheme C := by
  refine ⟨fun E π hp sup => representedList C E good π hp sup,?_⟩
  intro E s hs support nonempty closed
  obtain ⟨e,member,semantic,metadata⟩ := joint_maximal C E s hs nonempty
  obtain ⟨π,hp⟩ := finite_rep C E s hs
  have pastSub := (scheme C).past_subset E e closed member
  obtain ⟨pre,hpre⟩ := enumeration_subset hp (show E \ {e} ⊆ E from Set.diff_subset)
  obtain ⟨past,hpast⟩ := enumeration_subset hp
    (show (scheme C).Past e \ {e} ⊆ E from fun _ h => pastSub h.1)
  obtain ⟨t,ht⟩ := representedList C _ good pre hpre (fun x hx => support x hx.1)
  obtain ⟨B,hB⟩ := representedList C _ good past hpast (fun x hx => support x (pastSub hx.1))
  have unionEq : insert e (E \ {e}) = E := by ext x; simp; tauto
  have pastEq : insert e ((scheme C).Past e \ {e}) = (scheme C).Past e := by
    ext x
    simp only [Set.mem_insert_iff,Set.mem_diff,Set.mem_singleton_iff]
    constructor
    · rintro (rfl | hx)
      · exact Or.inl rfl
      · exact hx.1
    · intro hx
      by_cases same : x = e
      · exact Or.inl same
      · exact Or.inr ⟨hx,same⟩
  refine ⟨⟨e,member,semantic,metadata,t,B,ht,hB,?_,?_⟩⟩
  · rw [← pastEq]
    apply insert_rep C _ B e hB (support e member) (by simp)
    · intro x hx ne
      rw [pastEq]
      exact (scheme C).past_semantic_maximal policy good.trans good.irrefl e x hx.1 ne
    · intro x hx edge
      exact good.irrefl e (good.trans edge ((scheme C).past_vis good.trans hx.1 hx.2))
  · rw [← unionEq]
    apply insert_rep C _ t e ht (support e member) (by simp)
    · intro x hx ne
      rw [unionEq]
      exact semantic x hx.1 ne
    · intro x hx
      exact metadata x hx.1 hx.2

#print axioms latest_live
#print axioms unique
end Sal.MRDTs.Paper1.OptionalRegister
