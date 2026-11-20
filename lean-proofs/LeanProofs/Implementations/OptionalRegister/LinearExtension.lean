import LeanProofs.Implementations.OptionalRegister.Laws
import Artifact.MRDTs.Paper1.CertifiedClosedExecution

/-!
# The optional register: clause 1

Convergence. The replay argument, the coherence invariant along every
certified execution, the verification conditions in their concrete form,
and the execution-level consequences.
-/

namespace LeanProofs.Implementations.OptionalRegister
open Artifact.MRDTs
open Artifact.MRDTs.Paper1
open Artifact.MRDTs.Foundation ConcreteMRDT
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
  counts : ∀ F : Finset Event, (↑F : Set Event) = E → ∀ r, (s.cells r).1.1 = Counts.count F r
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
    subst F; simp [initial,zero,Counts.count,Counts.winners]
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
  have hn : (Counts.winners F r).Nonempty :=
    ⟨u,Finset.mem_filter.mpr ⟨huF,own,alive.1⟩⟩
  obtain ⟨w,hw,maximal⟩ := (Counts.winners F r).exists_max_image Op.time hn
  obtain ⟨hwF,wown,wwin⟩ := Finset.mem_filter.mp hw
  have hwE : w ∈ E := by rw [← hF]; exact hwF
  have uw := maximal u (Finset.mem_filter.mpr ⟨huF,own,alive.1⟩)
  refine ⟨w,hwE,wown,latest_live good sup hu hwE (own.trans wown.symm) wwin uw alive,?_⟩
  intro x hx xo xs
  have hxF : x ∈ F := by rw [← hF] at hx; exact hx
  exact maximal x (Finset.mem_filter.mpr ⟨hxF,xo,xs⟩)

private theorem no_row (F : Finset Event) (r : Nat) (absent : r ∉ rows F) :
    Counts.winners F r = ∅ := by
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
    ((Counts.count F r,decide (Live C E r)),
      if h : Live C E r then ((choose r h).time,valueOf (choose r h)) else (0,0))
  have outside : ∀ r, r ∉ rows F → cells r = zero := by
    intro r absent
    have empty := no_row F r absent
    have dead : ¬ Live C E r := by
      rintro ⟨w,hw,own,live⟩
      have hwF : w ∈ F := by rw [← hF] at hw; exact hw
      have mem : w ∈ Counts.winners F r := Finset.mem_filter.mpr ⟨hwF,own,live.1⟩
      rw [empty] at mem; exact Finset.notMem_empty _ mem
    simp [cells,zero,dead,Counts.count,empty]
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
    all_goals simp [update,hop,own,hs.counts F hF,Counts.count,
      Counts.winners,Counts.winningAt,
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
end LeanProofs.Implementations.OptionalRegister

namespace LeanProofs.Implementations.OptionalRegister
open Artifact.MRDTs
open Artifact.MRDTs.Paper1
open Artifact.MRDTs.Foundation ConcreteMRDT Counts
open Classical

private theorem winner_mem {E : Set Event}
    {F : Finset Event} (hF : (↑F : Set Event) = E) {w : Event} (hw : w ∈ E)
    {r : Nat} (own : w.rep = r) (set : w.op.isSet = true) : w ∈ winners F r := by
  have hf : w ∈ F := by rw [← hF] at hw; exact hw
  exact Finset.mem_filter.mpr ⟨hf,own,set⟩

private theorem latest_growth (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (F G : Finset Event)
    (hF : (↑F : Set Event) = E₁) (hG : (↑G : Set Event) = E₂)
    (good : GoodContext C) (sup₁ : Supported C E₁) (sup₂ : Supported C E₂)
    (closed₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (r : Nat) (w v : Event) (hw : w ∈ E₁) (hv : v ∈ E₂)
    (ownW : w.rep = r) (ownV : v.rep = r) (setW : w.op.isSet = true)
    (latestV : ∀ x ∈ E₂, x.rep = r → x.op.isSet = true → x.time ≤ v.time)
    (growth : count F r < count G r) : w.time < v.time := by
  have notsub : ¬ winners G r ⊆ winners F r := by
    intro sub
    have bound := Finset.card_le_card sub
    unfold count at growth
    omega
  obtain ⟨x,hx,absent⟩ := Finset.not_subset.mp notsub
  obtain ⟨hxG,ownX,setX⟩ := Finset.mem_filter.mp hx
  have hxE : x ∈ E₂ := by rw [← hG]; exact hxG
  have ne : w ≠ x := by
    intro same
    exact absent (same ▸ winner_mem hF hw ownW setW)
  obtain ⟨rw,Sw,hLw,hwS⟩ := sup₁ w hw
  obtain ⟨rx,Sx,hLx,hxS⟩ := sup₂ x hxE
  have forward : C.vis w x := by
    rcases C.vis_total_same_replica hLw hwS hLx hxS ne (ownW.trans ownX.symm) with h | h
    · exact h
    · have inF := closed₁ x w h hw
      exact (absent (winner_mem hF inF ownX setX)).elim
  exact lt_of_lt_of_le (good.mono forward) (latestV x hxE ownX setX)

/-- All payload side conditions used by the source averaging branch are
proved from the represented histories, rather than assumed as invariants. -/
theorem represented_coherent (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (a b : State)
    (closed₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (closed₂ : ∀ x y, C.vis x y → y ∈ E₂ → x ∈ E₂)
    (ha : representation C E₁ a) (hb : representation C E₂ b) (r : Nat) :
    CoherentCells (a.cells r) (b.cells r) := by
  refine ⟨?_,ha.inactive r,hb.inactive r⟩
  intro af bf
  obtain ⟨F,hF⟩ := ha.finite
  obtain ⟨G,hG⟩ := hb.finite
  obtain ⟨w,hw,ownW,liveW,payloadW,latestW⟩ := ha.payload r af
  obtain ⟨v,hv,ownV,liveV,payloadV,latestV⟩ := hb.payload r bf
  have countA := ha.counts F hF r
  have countB := hb.counts G hG r
  refine ⟨?_,?_,?_⟩
  · intro growth
    rw [payloadW,payloadV]
    exact latest_growth C E₁ E₂ F G hF hG ha.good ha.supported hb.supported closed₁
      r w v hw hv ownW ownV liveW.1 latestV (by simpa only [← countA,← countB] using growth)
  · intro growth
    rw [payloadW,payloadV]
    exact latest_growth C E₂ E₁ G F hG hF hb.good hb.supported ha.supported closed₂
      r v w hv hw ownV ownW liveV.1 latestW (by simpa only [← countA,← countB] using growth)
  · intro equal
    have cards : (winners F r).card = (winners G r).card := by
      have eq : count F r = count G r := countA.symm.trans (equal.trans countB)
      unfold count at eq
      exact_mod_cast eq
    have same : winners F r = winners G r := by
      rcases prefixes_comparable C E₁ E₂ F G hF hG ha.supported hb.supported closed₁ closed₂ r with sub | sub
      · exact Finset.eq_of_subset_of_card_le sub (by omega)
      · exact (Finset.eq_of_subset_of_card_le sub (by omega)).symm
    have wG : w ∈ G := (Finset.mem_filter.mp (same ▸ winner_mem hF hw ownW liveW.1)).1
    have vF : v ∈ F := (Finset.mem_filter.mp (same.symm ▸ winner_mem hG hv ownV liveV.1)).1
    have wE : w ∈ E₂ := by rw [← hG]; exact wG
    have vE : v ∈ E₁ := by rw [← hF]; exact vF
    have times : w.time = v.time := le_antisymm (latestV w wE ownW liveW.1)
      (latestW v vE ownV liveV.1)
    have sameEvent : w = v := C.ts_unique (ha.supported w hw) (hb.supported v hv) times
    rw [payloadW,payloadV,sameEvent]

/-- A full represented intersection contains exactly the minimum Set count
at each issuer, independently of payloads or flag values. -/
theorem intersection_counts (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (l a b : State)
    (closed₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (closed₂ : ∀ x y, C.vis x y → y ∈ E₂ → x ∈ E₂)
    (hl : representation C (E₁ ∩ E₂) l)
    (ha : representation C E₁ a) (hb : representation C E₂ b) :
    ∀ r, (l.cells r).1.1 = min (a.cells r).1.1 (b.cells r).1.1 := by
  obtain ⟨F,hF⟩ := ha.finite
  obtain ⟨G,hG⟩ := hb.finite
  have hI : (↑(F ∩ G) : Set Event) = E₁ ∩ E₂ := by simp [hF,hG]
  intro r
  rw [hl.counts (F ∩ G) hI,ha.counts F hF,hb.counts G hG]
  exact count_min_of_comparable F G r
    (prefixes_comparable C E₁ E₂ F G hF hG ha.supported hb.supported closed₁ closed₂ r)

/-- Comparison join is a proof algebra, while the executable merge remains
Neem's arithmetic and averaging algorithm. -/
def join (a b : State) : State :=
  ⟨a.domain ∪ b.domain,fun r => joinCell (a.cells r) (b.cells r),by
    intro r absent
    have absent' : r ∉ a.domain ∧ r ∉ b.domain := by simpa using absent
    change joinCell (a.cells r) (b.cells r) = zero
    rw [a.outside r absent'.1,b.outside r absent'.2]
    simp⟩

theorem join_comm (a b : State) : join a b = join b a := by
  apply State.ext
  · simp [join,Finset.union_comm]
  · intro r; exact joinCell_comm _ _
theorem join_assoc (a b c : State) : join (join a b) c = join a (join b c) := by
  apply State.ext
  · simp [join,Finset.union_assoc]
  · intro r; exact joinCell_assoc _ _ _
@[simp] theorem join_idem (a : State) : join a a = a := by
  apply State.ext
  · simp [join]
  · intro r; exact joinCell_idem _

theorem join_local (t b d : State) : join (join t d) b = join (join t b) d := by
  rw [join_assoc,join_comm d b,← join_assoc]

theorem join_shared (a b d : State) : join (join a d) (join b d) = join (join a b) d := by
  rw [join_assoc,← join_assoc d b d,join_comm d b,join_assoc b d d,join_idem,← join_assoc]

/-- The represented ancestor contributes no extra domain entries; each row
uses the derived count minimum and payload coherence. -/
theorem source_as_join (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (l a b : State)
    (closed₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (closed₂ : ∀ x y, C.vis x y → y ∈ E₂ → x ∈ E₂)
    (hl : representation C (E₁ ∩ E₂) l)
    (ha : representation C E₁ a) (hb : representation C E₂ b) :
    merge l a b = join a b := by
  obtain ⟨F,hF⟩ := ha.finite
  obtain ⟨G,hG⟩ := hb.finite
  have hI : (↑(F ∩ G) : Set Event) = E₁ ∩ E₂ := by simp [hF,hG]
  have dom : l.domain ⊆ a.domain := by
    rw [hl.domain (F ∩ G) hI,ha.domain F hF]
    unfold rows
    exact Finset.image_subset_image (Finset.filter_subset_filter _ Finset.inter_subset_left)
  apply State.ext
  · change l.domain ∪ (a.domain ∪ b.domain) = a.domain ∪ b.domain
    exact Finset.union_eq_right.mpr (dom.trans Finset.subset_union_left)
  · intro r
    exact sourceCell_as_join _ _ _ (intersection_counts C E₁ E₂ l a b closed₁ closed₂ hl ha hb r)
      (represented_coherent C E₁ E₂ a b closed₁ closed₂ ha hb r)

#print axioms represented_coherent
#print axioms source_as_join
end LeanProofs.Implementations.OptionalRegister

namespace LeanProofs.Implementations.OptionalRegister
open Artifact.MRDTs
open Artifact.MRDTs.Paper1
open Artifact.MRDTs.Foundation ConcreteMRDT Counts
open Classical

private theorem finset_subset {F G : Finset Event} {A B : Set Event}
    (hF : (↑F : Set Event) = A) (hG : (↑G : Set Event) = B) (sub : A ⊆ B) : F ⊆ G := by
  intro e he
  have hx : e ∈ A := by rw [← hF]; exact he
  have hy := sub hx
  rw [← hG] at hy; exact hy

private theorem domain_subset {C : ReplayContext D.toUpdateSig} {A B : Set Event}
    {a b : State} (ha : representation C A a) (hb : representation C B b) (sub : A ⊆ B) :
    a.domain ⊆ b.domain := by
  obtain ⟨F,hF⟩ := ha.finite
  obtain ⟨G,hG⟩ := hb.finite
  rw [ha.domain F hF,hb.domain G hG]
  unfold rows
  exact Finset.image_subset_image (Finset.filter_subset_filter _ (finset_subset hF hG sub))

theorem past_count_facts (C : ReplayContext D.toUpdateSig)
    (U : Set Event) (s B : State) (e : Event)
    (supported : Supported C U) (closed : (scheme C).Closed U) (member : e ∈ U)
    (maximal : ∀ x ∈ U, x ≠ e → ¬ (scheme C).before e x)
    (hs : representation C (U \ {e}) s)
    (hB : representation C ((scheme C).Past e \ {e}) B) :
    (∀ r, (B.cells r).1.1 ≤ (s.cells r).1.1) ∧
      (s.cells e.rep).1.1 = (B.cells e.rep).1.1 := by
  obtain ⟨F,hF⟩ := hs.finite
  obtain ⟨G,hG⟩ := hB.finite
  have pastSub := (scheme C).past_subset U e closed member
  have sub : G ⊆ F := finset_subset hG hF (fun x hx => ⟨pastSub hx.1,hx.2⟩)
  refine ⟨?_,?_⟩
  · intro r; rw [hB.counts G hG,hs.counts F hF]; exact count_mono G F sub r
  · rw [hs.counts F hF,hB.counts G hG]
    apply congrArg (fun A : Finset Event => (A.card : Int))
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨hxF,own⟩ := Finset.mem_filter.mp hx
      have hxU : x ∈ U \ {e} := by rw [← hF]; exact hxF
      obtain ⟨rx,Sx,hLx,hxS⟩ := supported x hxU.1
      obtain ⟨re,Se,hLe,heS⟩ := supported e member
      have vis := (C.vis_total_same_replica hLx hxS hLe heS hxU.2 own.1).resolve_right
        (maximal x hxU.1 hxU.2)
      have hxG : x ∈ G := by
        change x ∈ (↑G : Set Event)
        rw [hG]; exact ⟨Or.inr (.single vis),hxU.2⟩
      exact Finset.mem_filter.mpr ⟨hxG,own⟩
    · exact Finset.filter_subset_filter _ sub

private theorem true_of_equal_count_subset {C : ReplayContext D.toUpdateSig}
    {E F : Set Event} {a b : State}
    (ha : representation C E a) (hb : representation C F b)
    (sub : E ⊆ F) (r : Nat) (same : (a.cells r).1.1 = (b.cells r).1.1)
    (bit : (b.cells r).1.2 = true) : (a.cells r).1.2 = true := by
  obtain ⟨A,hA⟩ := ha.finite
  obtain ⟨B,hB⟩ := hb.finite
  have subset : winners A r ⊆ winners B r := Finset.filter_subset_filter _ (finset_subset hA hB sub)
  have cardeq : (winners A r).card = (winners B r).card := by
    rw [ha.counts A hA,hb.counts B hB] at same
    unfold count at same; exact_mod_cast same
  have eqsets := Finset.eq_of_subset_of_card_le subset (Nat.le_of_eq cardeq.symm)
  obtain ⟨w,hw,own,live⟩ := (hb.active r).mp bit
  have hwB : w ∈ winners B r := by
    apply Finset.mem_filter.mpr; refine ⟨?_,own,live.1⟩
    rw [← hB] at hw; exact hw
  rw [← eqsets] at hwB
  have hwE : w ∈ E := by rw [← hA]; exact (Finset.mem_filter.mp hwB).1
  exact (ha.active r).mpr ⟨w,hwE,own,live.1,fun d hd => live.2 d (sub hd)⟩

private theorem winners_before_reset {C : ReplayContext D.toUpdateSig}
    {E : Set Event} {e : Event} (good : GoodContext C) (sup : Supported C E)
    (reset : e.op = .unset) (r : Nat) (bit : Live C E r)
    (killed : ¬ Live C (insert e E) r) :
    ∀ w ∈ E, w.rep = r → w.op.isSet = true → C.vis w e := by
  have before {w : Event} (hw : w ∈ E) (own : w.rep = r) (live : LiveEvent C E w) : C.vis w e := by
    by_contra hn
    apply killed
    refine ⟨w,Or.inr hw,own,live.1,?_⟩
    intro d hd hop
    rcases hd with rfl | hd
    · exact hn
    · exact live.2 d hd hop
  intro w hw own win
  obtain ⟨u,hu,uown,ulive⟩ := bit
  have ue := before hu uown ulive
  by_cases same : w = u
  · exact same ▸ ue
  obtain ⟨rw,Sw,hLw,hwS⟩ := sup w hw
  obtain ⟨ru,Su,hLu,huS⟩ := sup u hu
  rcases C.vis_total_same_replica hLw hwS hLu huS same (own.trans uown.symm) with wu | uw
  · exact good.trans wu ue
  · apply before hw own
    exact ⟨win,fun d hd hop wd => ulive.2 d hd hop (good.trans uw wd)⟩

private theorem joinCell_of_past (s B : Cell) (lower : B.1.1 ≤ s.1.1)
    (coherent : CoherentCells s B)
    (tied : s.1.1 = B.1.1 → s.1.2 = true → B.1.2 = true) : joinCell s B = s := by
  rcases lt_or_eq_of_le lower with less | same
  · have keylt : cellKey B < cellKey s := Prod.Lex.toLex_lt_toLex.mpr (Or.inl less)
    simp [joinCell,max_eq_left (le_of_lt keylt)]
  · rcases coherent with ⟨payload,sz,Bz⟩
    rcases s with ⟨⟨sc,sf⟩,sp⟩
    rcases B with ⟨⟨Bc,Bf⟩,Bp⟩
    simp only [Prod.fst,Prod.snd] at *
    subst Bc
    cases sf <;> cases Bf
    · have eq := (sz rfl).trans (Bz rfl).symm
      subst Bp; exact joinCell_idem _
    · rw [joinCell_comm]
      have keylt : cellKey ((sc,true),Bp) < cellKey ((sc,false),sp) := by
        apply Prod.Lex.toLex_lt_toLex.mpr
        right; refine ⟨rfl,?_⟩
        apply Prod.Lex.toLex_lt_toLex.mpr
        left; simp
      simp [joinCell,max_eq_right (le_of_lt keylt)]
    · exact False.elim (Bool.noConfusion (tied rfl rfl))
    · have eq := (payload rfl rfl).2.2 rfl
      subst Bp; exact joinCell_idem _

/-- The causal equation uses reconstructed field evidence and single-writer
Set prefixes. It does not invoke representation Join. -/
theorem causal_delta (C : ReplayContext D.toUpdateSig) (U : Set Event)
    (s B : State) (e : Event) (sup : Supported C U) (closed : (scheme C).Closed U)
    (member : e ∈ U)
    (semantic : ∀ x ∈ U, x ≠ e → ¬ paperOrder policy C U e x)
    (metadata : ∀ x ∈ U, x ≠ e → ¬ (scheme C).before e x)
    (hs : representation C (U \ {e}) s)
    (hB : representation C ((scheme C).Past e \ {e}) B) :
    merge B s (update B e) = update s e := by
  have sub : ((scheme C).Past e \ {e}) ⊆ (U \ {e}) :=
    fun x hx => ⟨(scheme C).past_subset U e closed member hx.1,hx.2⟩
  have Bdom := domain_subset hB hs sub
  obtain ⟨lower,same⟩ := past_count_facts C U s B e sup closed member metadata hs hB
  have tied : ∀ r, (s.cells r).1.1 = (B.cells r).1.1 →
      (s.cells r).1.2 = true → (B.cells r).1.2 = true :=
    fun r eq bit => true_of_equal_count_subset hB hs sub r eq.symm bit
  have preClosed := (scheme C).closed_diff_of_max U U e Set.Subset.rfl closed metadata
  have pastClosed := (scheme C).closed_diff_of_max U ((scheme C).Past e) e
    ((scheme C).past_subset U e closed member) ((scheme C).past_closed e) metadata
  have coherent := represented_coherent C (U \ {e}) ((scheme C).Past e \ {e}) s B preClosed pastClosed hs hB
  have count_if_true : e.op = .unset → ∀ r, (s.cells r).1.2 = true →
      (s.cells r).1.1 = (B.cells r).1.1 := by
    intro reset r bit
    have ins : insert e (U \ {e}) = U := by
      simpa [Set.insert_eq_of_mem member] using (Set.insert_diff_singleton : insert e (U \ {e}) = insert e U)
    obtain ⟨F,hF⟩ := hs.finite
    obtain ⟨G,hG⟩ := hB.finite
    have killed : ¬ Live C (insert e (U \ {e})) r :=
      reset_kills_live C _ hs.good hs.supported F hF e (sup e member) reset
        (fun x hx ne => by rw [ins]; exact semantic x hx.1 ne)
        (fun x hx => metadata x hx.1 hx.2) (by simp) r
    have before := winners_before_reset hs.good hs.supported reset r ((hs.active r).mp bit) killed
    have eqwins : winners F r = winners G r := by
      ext w
      constructor
      · intro hw
        obtain ⟨hw,own,win⟩ := Finset.mem_filter.mp hw
        have hwU : w ∈ U \ {e} := by rw [← hF]; exact hw
        have wp : w ∈ (scheme C).Past e \ {e} := ⟨Or.inr (.single (before w hwU own win)),hwU.2⟩
        rw [← hG] at wp
        exact Finset.mem_filter.mpr ⟨wp,own,win⟩
      · intro hw
        obtain ⟨hw,own,win⟩ := Finset.mem_filter.mp hw
        have wp : w ∈ (scheme C).Past e \ {e} := by rw [← hG]; exact hw
        have wu := sub wp
        rw [← hF] at wu
        exact Finset.mem_filter.mpr ⟨wu,own,win⟩
    rw [hs.counts F hF,hB.counts G hG]
    unfold count; rw [eqwins]
  apply State.ext
  · cases hop : e.op
    all_goals ext r; simp only [merge,update,hop,Finset.mem_union,Finset.mem_insert]
    all_goals have dom := fun h : r ∈ B.domain => Bdom h
    all_goals tauto
  · intro r
    cases hop : e.op with
    | set value =>
      by_cases own : r = e.rep
      · subst r
        have ts : (s.cells e.rep).1.2 = true → (s.cells e.rep).2.1 < e.time := by
          intro bit
          obtain ⟨w,hw,wown,live,payload,_⟩ := hs.payload e.rep bit
          obtain ⟨rw,Sw,hLw,hwS⟩ := sup w hw.1
          obtain ⟨re,Se,hLe,heS⟩ := sup e member
          have before := (C.vis_total_same_replica hLw hwS hLe heS hw.2 wown).resolve_right
            (metadata w hw.1 hw.2)
          rw [payload]; exact hs.good.mono before
        change mergeCell (B.cells e.rep) (s.cells e.rep) ((update B e).cells e.rep) = ((update s e).cells e.rep)
        simp only [update,hop,ite_true]
        cases bit : (s.cells e.rep).1.2
        · simp [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,bit,same]
        · have growth := ts bit
          simp [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,bit,same,mergePayload,
            ne_of_lt growth,not_lt_of_ge (le_of_lt growth)]
      · change mergeCell (B.cells r) (s.cells r) ((update B e).cells r) = ((update s e).cells r)
        simp only [update,hop,if_neg own]
        rw [sourceCell_as_join _ _ _ (min_eq_right (lower r)).symm (coherent r)]
        exact joinCell_of_past _ _ (lower r) (coherent r) (tied r)
    | unset =>
      have ct := count_if_true hop r
      change mergeCell (B.cells r) (s.cells r) ((update B e).cells r) = ((update s e).cells r)
      simp only [update,hop]
      cases bit : (s.cells r).1.2
      · simp [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,bit]
      · have eq := ct bit
        simp [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,bit,eq]


/-- The causal slice is the represented intersection with the remainder. -/
private theorem past_merge_as_join (C : ReplayContext D.toUpdateSig)
    (U : Set Event) (s B d : State) (e : Event)
    (closed : (scheme C).Closed U) (member : e ∈ U)
    (metadata : ∀ x ∈ U, x ≠ e → ¬ (scheme C).before e x)
    (hs : representation C (U \ {e}) s)
    (hB : representation C ((scheme C).Past e \ {e}) B)
    (hd : representation C ((scheme C).Past e) d) : merge B s d = join s d := by
  have sub := (scheme C).past_subset U e closed member
  have intersection : (U \ {e}) ∩ (scheme C).Past e = (scheme C).Past e \ {e} := by
    ext x
    constructor
    · exact fun h => ⟨h.2,h.1.2⟩
    · exact fun h => ⟨⟨sub h.1,h.2⟩,h.1⟩
  apply source_as_join C (U \ {e}) ((scheme C).Past e) B s d
    ((scheme C).closed_diff_of_max U U e Set.Subset.rfl closed metadata)
    ((scheme C).past_closed e) _ hs hd
  simpa only [intersection] using hB

theorem local_equation (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (l B t b : State) (e : Event)
    (ctx : Raw.Context policy scheme C E₁ E₂ e)
    (member : e ∈ E₁) (absent : e ∉ E₂)
    (hl : representation C (E₁ ∩ E₂) l)
    (hB : representation C ((scheme C).Past e \ {e}) B)
    (ht : representation C (E₁ \ {e}) t) (hb : representation C E₂ b)
    (hc : representation C ((scheme C).Past e) (update B e))
    (ha : representation C E₁ (merge B t (update B e)))
    (hm : representation C ((E₁ ∪ E₂) \ {e}) (merge l t b)) :
    merge l (merge B t (update B e)) b = merge B (merge l t b) (update B e) := by
  have preClosed := (scheme C).closed_diff_of_max (E₁ ∪ E₂) E₁ e
    Set.subset_union_left ctx.closed₁ ctx.metadata
  have eq : (E₁ \ {e}) ∩ E₂ = E₁ ∩ E₂ := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_diff,Set.mem_singleton_iff]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · exact fun h => ⟨⟨h.1,fun same => absent (same ▸ h.2)⟩,h.2⟩
  have base : representation C ((E₁ \ {e}) ∩ E₂) l := by rw [eq]; exact hl
  have outer := source_as_join C E₁ E₂ l _ b ctx.closed₁ ctx.closed₂ hl ha hb
  have inner := past_merge_as_join C E₁ t B (update B e) e ctx.closed₁ member
    (fun x hx ne => ctx.metadata x (Or.inl hx) ne) ht hB hc
  have middle := source_as_join C (E₁ \ {e}) E₂ l t b preClosed ctx.closed₂ base ht hb
  have right := past_merge_as_join C (E₁ ∪ E₂) (merge l t b) B (update B e) e
    (fun a b edge hx => hx.elim
      (fun h => Or.inl (ctx.closed₁ a b edge h))
      (fun h => Or.inr (ctx.closed₂ a b edge h)))
    (Or.inl member) ctx.metadata hm hB hc
  rw [outer,inner,right,middle]
  exact join_local t b (update B e)

theorem shared_equation (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (t₀ t₁ t₂ B : State) (e : Event)
    (ctx : Raw.Context policy scheme C E₁ E₂ e)
    (member₁ : e ∈ E₁) (member₂ : e ∈ E₂)
    (h₀ : representation C ((E₁ ∩ E₂) \ {e}) t₀)
    (hB : representation C ((scheme C).Past e \ {e}) B)
    (h₁ : representation C (E₁ \ {e}) t₁) (h₂ : representation C (E₂ \ {e}) t₂)
    (hc : representation C ((scheme C).Past e) (update B e))
    (ha₀ : representation C (E₁ ∩ E₂) (merge B t₀ (update B e)))
    (ha₁ : representation C E₁ (merge B t₁ (update B e)))
    (ha₂ : representation C E₂ (merge B t₂ (update B e)))
    (hm : representation C ((E₁ ∪ E₂) \ {e}) (merge t₀ t₁ t₂)) :
    merge (merge B t₀ (update B e)) (merge B t₁ (update B e))
      (merge B t₂ (update B e)) = merge B (merge t₀ t₁ t₂) (update B e) := by
  have pre₁ := (scheme C).closed_diff_of_max (E₁ ∪ E₂) E₁ e
    Set.subset_union_left ctx.closed₁ ctx.metadata
  have pre₂ := (scheme C).closed_diff_of_max (E₁ ∪ E₂) E₂ e
    Set.subset_union_right ctx.closed₂ ctx.metadata
  have eq : (E₁ \ {e}) ∩ (E₂ \ {e}) = (E₁ ∩ E₂) \ {e} := by ext x; simp; tauto
  have base : representation C ((E₁ \ {e}) ∩ (E₂ \ {e})) t₀ := by rw [eq]; exact h₀
  have outer := source_as_join C E₁ E₂ _ _ _ ctx.closed₁ ctx.closed₂ ha₀ ha₁ ha₂
  have inner₁ := past_merge_as_join C E₁ t₁ B (update B e) e ctx.closed₁ member₁
    (fun x hx ne => ctx.metadata x (Or.inl hx) ne) h₁ hB hc
  have inner₂ := past_merge_as_join C E₂ t₂ B (update B e) e ctx.closed₂ member₂
    (fun x hx ne => ctx.metadata x (Or.inr hx) ne) h₂ hB hc
  have middle := source_as_join C (E₁ \ {e}) (E₂ \ {e}) t₀ t₁ t₂ pre₁ pre₂ base h₁ h₂
  have right := past_merge_as_join C (E₁ ∪ E₂) (merge t₀ t₁ t₂) B (update B e) e
    (fun a b edge hx => hx.elim
      (fun h => Or.inl (ctx.closed₁ a b edge h))
      (fun h => Or.inr (ctx.closed₂ a b edge h)))
    (Or.inl member₁) ctx.metadata hm hB hc
  rw [outer,inner₁,inner₂,right,middle]
  exact join_shared t₁ t₂ (update B e)


private theorem active_count_positive (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (s : State) (hs : representation C E s) (r : Nat)
    (bit : (s.cells r).1.2 = true) : 0 < (s.cells r).1.1 := by
  obtain ⟨F,hF⟩ := hs.finite
  obtain ⟨w,hw,own,live⟩ := (hs.active r).mp bit
  have hwF : w ∈ F := by rw [← hF] at hw; exact hw
  have hwW : w ∈ winners F r := Finset.mem_filter.mpr ⟨hwF,own,live.1⟩
  have positive := Finset.card_pos.mpr (show (winners F r).Nonempty from ⟨w,hwW⟩)
  rw [hs.counts F hF]
  unfold count; exact_mod_cast positive

theorem initial_equation (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (s : State) (hs : representation C E s) : merge initial initial s = s := by
  apply State.ext
  · simp [merge,initial]
  · intro r
    change mergeCell zero zero (s.cells r) = s.cells r
    cases bit : (s.cells r).1.2
    · have payload := hs.inactive r bit
      apply Prod.ext
      · apply Prod.ext
        · simp [mergeCell,zero]
        · simp [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,zero,bit]
      · simp [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,zero,bit,payload]
    · have positive := active_count_positive C E s hs r bit
      apply Prod.ext
      · apply Prod.ext
        · simp [mergeCell,zero]
        · simp [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,zero,bit,positive]
      · simp [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,zero,bit,positive]

/-- Source arithmetic, finite domain, flag, and averaging branches satisfy
all five equations. Payload coherence is derived in each represented triple. -/
theorem fiveVC : Raw.MergeVCs policy representation scheme := by
  constructor
  · intro C E₁ E₂ l a b _ _ _ _ _ _ _
    exact source_comm l a b
  · intro C E s _ _ hs
    exact initial_equation C E s hs
  · intro C U s B e _ _ sup closed member semantic metadata hs hB _ _
    exact causal_delta C U s B e sup closed member semantic metadata hs hB
  · exact local_equation
  · exact shared_equation

/-- The complete source Join is obtained by the framework's strict finite
history induction, independently of the proof algebra called `join`. -/
theorem representationJoin : RepresentationJoin representation := by
  apply Raw.representationJoin_of_vcs fiveVC unique
    (fun C E s h => initial_rep C h.good) finite_rep
  intro C _ _ _ _ _ _ _ _ ha _
  exact replaySupply C ha.good

#print axioms causal_delta
#print axioms fiveVC
#print axioms representationJoin
end LeanProofs.Implementations.OptionalRegister

namespace LeanProofs.Implementations.OptionalRegister
open Artifact.MRDTs
open Artifact.MRDTs.Paper1
open Artifact.MRDTs.Foundation ConcreteMRDT Classical

noncomputable def executionOrder : EventOrder D.toUpdateSig where
  order a b := match a.op,b.op with
    | .unset,.set _ => .Fst_then_snd
    | .set _,.unset => .Snd_then_fst
    | .set _,.set _ => if a.rep = b.rep then
        if a.time < b.time then .Fst_then_snd
        else if b.time < a.time then .Snd_then_fst else .Either
      else .Either
    | _,_ => .Either

noncomputable local instance executionData : EventOrder D.toUpdateSig := executionOrder

@[simp] theorem execution_before (a b : Event) : D.toUpdateSig.replayBefore a b ↔
    policy.before a.op b.op ∨
      ((∃ v, a.op = .set v) ∧ (∃ v, b.op = .set v) ∧ a.rep = b.rep ∧ a.time < b.time) := by
  rcases a with ⟨ta,ra,oa⟩; rcases b with ⟨tb,rb,ob⟩
  cases oa <;> cases ob <;>
    simp [UpdateSig.replayBefore,EventOrder.Before,executionData,executionOrder,policy,Op.op,Op.rep,Op.time]
  split_ifs <;> simp_all <;> omega

theorem same_rep_sets_noncomm (ta r va tb vb : Nat) (different : ta ≠ tb) :
    ¬ D.toUpdateSig.commutes (ta,r,.set va) (tb,r,.set vb) := by
  intro comm
  have h := congrArg (fun s => (s.cells r).2.1) (comm initial)
  simp [D,update,Op.op,Op.rep,Op.time] at h
  exact different h.symm

theorem execution_noncomm_exact (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (support : Supported C E) (a b : Event) (ha : a ∈ E) (hb : b ∈ E) :
    ¬ D.toUpdateSig.commutes a b ↔
      D.toUpdateSig.replayBefore a b ∨ D.toUpdateSig.replayBefore b a := by
  simp only [execution_before]
  by_cases same : a = b
  · subst b
    have comm : D.toUpdateSig.commutes a a := fun _ => rfl
    rcases a with ⟨ta,ra,oa⟩
    cases oa <;> simp only [policy,Op.op,Op.rep,Op.time,comm,not_true_eq_false,false_or,or_false]
    all_goals simp
  · have time : a.time ≠ b.time := by
      intro eq
      exact same (timestamp_unique support ha hb eq)
    rcases a with ⟨ta,ra,oa⟩; rcases b with ⟨tb,rb,ob⟩
    simp only [Op.time] at time
    cases oa <;> cases ob
    · rename_i va vb
      by_cases own : ra = rb
      · subst rb
        have nc := same_rep_sets_noncomm ta ra va tb vb time
        simp [execution_before,policy,Op.op,Op.rep,Op.time,nc]
        omega
      · simp [execution_before,policy,Op.op,Op.rep,Op.time,own,Ne.symm own,
          sets_commute _ _ _ _ _ _ own]
    · rename_i v
      have nc := set_unset_noncomm ta ra v tb rb
      simp [policy,Op.op,Op.rep,Op.time,nc]
    · rename_i v
      have nc : ¬ D.toUpdateSig.commutes (ta,ra,.unset) (tb,rb,.set v) := by
        intro comm
        exact set_unset_noncomm tb rb v ta ra (fun s => (comm s).symm)
      simp [execution_before,policy,Op.op,Op.rep,Op.time,nc]
    · simp [execution_before,policy,Op.op,Op.rep,Op.time,
        unsets_commute (ta,ra,.unset) (tb,rb,.unset) rfl rfl]

theorem execution_concurrent_before (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (support : Supported C E) (a b : Event) (ha : a ∈ E) (hb : b ∈ E)
    (forward : ¬ C.vis a b) (backward : ¬ C.vis b a) :
    D.toUpdateSig.replayBefore a b ↔ policy.before a.op b.op := by
  rw [execution_before]
  constructor
  · rintro (edge | ⟨_,_,own,time⟩)
    · exact edge
    · have different : a ≠ b := by intro eq; subst b; exact Nat.lt_irrefl _ time
      obtain ⟨r,F,head,member⟩ := support a ha
      obtain ⟨q,G,other,mem⟩ := support b hb
      exact False.elim ((C.vis_total_same_replica head member other mem different own).elim forward backward)
  · exact Or.inl

theorem execution_order_iff (C : ReplayContext D.toUpdateSig) (E : Set Event)
    (support : Supported C E) (a b : Event) (ha : a ∈ E) (hb : b ∈ E) :
    loOn C E a b ↔ paperOrder policy C E a b := by
  have exactab := execution_noncomm_exact C E support a b ha hb
  have exactbz : ∀ z ∈ E, (D.toUpdateSig.replayBefore b z ∨ D.toUpdateSig.replayBefore z b) ↔
      ¬ D.toUpdateSig.commutes b z := fun z hz => (execution_noncomm_exact C E support b z hb hz).symm
  simp only [loOn,paperOrder,← exactab]
  constructor
  · rintro (causal | ⟨forward,backward,edge,noAbsorber⟩)
    · exact Or.inl causal
    · exact Or.inr ⟨forward,backward,(execution_concurrent_before C E support a b ha hb forward backward).mp edge,
        fun ⟨z,hz,vis,nc⟩ => noAbsorber ⟨z,hz,vis,(exactbz z hz).mpr nc⟩⟩
  · rintro (causal | ⟨forward,backward,edge,noAbsorber⟩)
    · exact Or.inl causal
    · exact Or.inr ⟨forward,backward,(execution_concurrent_before C E support a b ha hb forward backward).mpr edge,
        fun ⟨z,hz,vis,nc⟩ => noAbsorber ⟨z,hz,vis,(exactbz z hz).mp nc⟩⟩

theorem executionCanonical_to_paper (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (s : State) (sup : Supported C E) (h : IsCanonicalState C E s) :
    Canonical policy C E s := by
  obtain ⟨π,hp,ordered,fold⟩ := h
  refine ⟨π,hp,?_,fold⟩
  apply ordered.imp_of_mem
  intro a b ha hb no edge
  exact no ((execution_order_iff C E sup b a ((hp.2 b).mp hb) ((hp.2 a).mp ha)).mpr edge)

theorem paperCanonical_to_execution (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (s : State) (sup : Supported C E) (h : Canonical policy C E s) :
    IsCanonicalState C E s := by
  obtain ⟨π,hp,ordered,fold⟩ := h
  refine ⟨π,hp,?_,fold⟩
  apply ordered.imp_of_mem
  intro a b ha hb no edge
  exact no ((execution_order_iff C E sup b a ((hp.2 b).mp hb) ((hp.2 a).mp ha)).mp edge)

theorem representation_of_executionCanonical (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (s : State) (good : GoodContext C) (sup : Supported C E)
    (h : IsCanonicalState C E s) : representation C E s := by
  obtain ⟨π,hp,ordered,fold⟩ := h
  obtain ⟨t,ht⟩ := representedList C E good π hp sup
  have same : t = s := canonical_unique laws C E sup (canonical C E t ht)
    (executionCanonical_to_paper C E s sup ⟨π,hp,ordered,fold⟩)
  simpa only [same] using ht

variable (join : RepresentationJoin representation)
include join

theorem execution_closedJoin (C : Configuration D) :
    CertifiedClosedExecution.ClosedJoinAt D C.replayContext := by
  intro E₁ E₂ l a b trans irr sup₁ sup₂ closed₁ closed₂ hl ha hb
  have good : GoodContext C.replayContext := ⟨fun _ _ _ => trans,irr,fun h => C.causal_mono h⟩
  have rl := representation_of_executionCanonical C.replayContext _ l good (fun x hx => sup₁ x hx.1) hl
  have ra := representation_of_executionCanonical C.replayContext _ a good sup₁ ha
  have rb := representation_of_executionCanonical C.replayContext _ b good sup₂ hb
  have merged := join C.replayContext E₁ E₂ l a b good.trans irr sup₁ sup₂ closed₁ closed₂ rl ra rb
  exact paperCanonical_to_execution C.replayContext _ _ merged.supported
    (canonical C.replayContext _ _ merged)

theorem executionCanonicalConfig {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C) :
    @CanonicalConfig D executionOrder C :=
  CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV
    (fun C _ => execution_closedJoin join C) reach

theorem representedVersionsOfJoin {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C)
    (v : Version) (s : State) (E : Set Event) (hv : C.ver v = some (s,E)) :
    representation C.replayContext E s := by
  have good := executionCanonicalConfig join reach
  exact representation_of_executionCanonical C.replayContext E s
    ⟨fun _ _ _ => good.vis_trans,good.vis_irrefl,fun h => C.causal_mono h⟩
    (good.version_events_supported v s E hv) (good.canonical v s E hv)

#print axioms execution_order_iff
#print axioms representedVersionsOfJoin
end LeanProofs.Implementations.OptionalRegister
