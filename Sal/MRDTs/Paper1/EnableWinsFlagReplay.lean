import Sal.MRDTs.Paper1.EnableWinsFlagCounts

/-! Independent event-indexed semantics for Neem's corrected row flag.
Winning events contribute one to their issuer's counter. A physical bit is
true exactly when a winning event survives all visible resets, or when the
universal initial true bit has not encountered a reset. -/
namespace Sal.MRDTs.Paper1.NeemFlagReplay
open Foundation ConcreteMRDT Instances.NeemFlag
open Classical

abbrev Event := Op Action

def policy : OperationPolicy Action where
  before a b := a = .reset ∧ b = .winning

def scheme (initialFlag : Bool) (C : ReplayContext (D initialFlag).toUpdateSig) :
    MetadataDependencies C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

abbrev winningAt := NeemFlagCounts.winningAt
abbrev count := NeemFlagCounts.count

def Live {initialFlag : Bool} (C : ReplayContext (D initialFlag).toUpdateSig)
    (E : Set Event) (r : Nat) : Prop :=
  ∃ w ∈ E, w.2.1 = r ∧ w.op = .winning ∧
    ∀ d ∈ E, d.op = .reset → ¬ C.vis w d

def NoReset (E : Set Event) : Prop := ∀ d ∈ E, d.op ≠ .reset

def Bit {initialFlag : Bool} (C : ReplayContext (D initialFlag).toUpdateSig)
    (E : Set Event) (r : Nat) : Prop := Live C E r ∨ initialFlag = true ∧ NoReset E

def representation (initialFlag : Bool) : Representation (D initialFlag) := fun C E s =>
  Supported C E ∧ ∃ F : Finset Event, (↑F : Set Event) = E ∧
    (∀ r, (s r).1 = count F r) ∧
    (∀ r, (s r).2 = true ↔ Bit C E r)

theorem initial_rep (initialFlag : Bool) (C : ReplayContext (D initialFlag).toUpdateSig) :
    representation initialFlag C ∅ (initial initialFlag) := by
  refine ⟨by simp [Supported],∅,by simp,?_,?_⟩
  · intro r; simp [initial,NeemFlagCounts.count,NeemFlagCounts.winners]
  · intro r; simp [initial,Bit,Live,NoReset]

theorem unique (initialFlag : Bool) : Raw.Unique (representation initialFlag) := by
  intro C E a b ha hb
  obtain ⟨_,F,hF,aCount,aBit⟩ := ha
  obtain ⟨_,G,hG,bCount,bBit⟩ := hb
  have same : F = G := by
    apply Finset.coe_injective
    exact hF.trans hG.symm
  subst G
  funext r
  apply Prod.ext
  · exact (aCount r).trans (bCount r).symm
  · have eqtrue : (a r).2 = true ↔ (b r).2 = true := (aBit r).trans (bBit r).symm
    cases hA : (a r).2 <;> cases hB : (b r).2 <;> simp_all

theorem represented (initialFlag : Bool) (C : ReplayContext (D initialFlag).toUpdateSig)
    (E : Set Event) (π : List Event) (hp : listPermOf π E) (sup : Supported C E) :
    ∃ s, representation initialFlag C E s := by
  let s : State := fun r => (count π.toFinset r,decide (Bit C E r))
  refine ⟨s,sup,π.toFinset,?_,by simp [s],?_⟩
  · ext e; simp [hp.2 e]
  · intro r; simp [s]

theorem different_noncommutes (initialFlag : Bool) (a b : Event)
    (different : a.op ≠ b.op) : ¬ (D initialFlag).toUpdateSig.commutes a b := by
  intro comm
  have h := congrArg (fun s => (s a.2.1).2) (comm (initial initialFlag))
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  cases oa <;> cases ob <;> simp [Op.op] at different
  · simp [D,update,Op.op] at h
  · have h' := congrArg (fun s => (s rb).2) (comm (initial initialFlag))
    simp [D,update,Op.op] at h'

private theorem live_insert_winning {initialFlag : Bool}
    {C : ReplayContext (D initialFlag).toUpdateSig} {E : Set Event} {e : Event}
    (win : e.op = .winning)
    (maximal : ∀ x ∈ E, ¬ C.vis e x) (r : Nat) :
    Live C (insert e E) r ↔ r = e.2.1 ∨ Live C E r := by
  constructor
  · rintro ⟨w,hw,hr,hop,live⟩
    rcases hw with rfl | hw
    · exact Or.inl hr.symm
    · exact Or.inr ⟨w,hw,hr,hop,fun d hd => live d (Or.inr hd)⟩
  · rintro (same | ⟨w,hw,hr,hop,live⟩)
    · refine ⟨e,Or.inl rfl,same.symm,win,?_⟩
      intro d hd reset
      rcases hd with rfl | hd
      · simp [win] at reset
      · exact maximal d hd
    · refine ⟨w,Or.inr hw,hr,hop,?_⟩
      intro d hd reset
      rcases hd with rfl | hd
      · simp [win] at reset
      · exact live d hd reset

theorem reset_kills_live {initialFlag : Bool}
    {C : ReplayContext (D initialFlag).toUpdateSig} {E : Set Event} {e : Event}
    (reset : e.op = .reset)
    (semantic : ∀ x ∈ E, x ≠ e → ¬ paperOrder policy C (insert e E) e x)
    (metadata : ∀ x ∈ E, ¬ C.vis e x) (r : Nat) :
    ¬ Live C (insert e E) r := by
  rintro ⟨w,hw,hr,win,live⟩
  have ne : w ≠ e := by intro eq; subst w; simp [reset] at win
  have hwE : w ∈ E := hw.elim (fun eq => (ne eq).elim) id
  have notbefore := live e (Or.inl rfl) reset
  apply semantic w hwE ne
  refine Or.inr ⟨metadata w hwE,notbefore,by simp [policy,reset,win],?_⟩
  rintro ⟨d,hd,hwd,nc⟩
  have dreset : d.op = .reset := by
    cases hop : d.op with
    | reset => rfl
    | winning =>
      apply False.elim
      apply nc
      intro s
      rcases w with ⟨tw,rw,ow⟩
      rcases d with ⟨td,rd,od⟩
      simp only [Op.op] at win hop
      subst ow; subst od
      funext k
      simp only [D,update,Op.op]
      split_ifs <;> simp_all <;> omega
  exact live d hd dreset hwd

/-- Semantic and metadata maximality establish the effect of the peeled event;
there is no assumed final merge equation in this reconstruction rule. -/
theorem insert_rep (initialFlag : Bool)
    (C : ReplayContext (D initialFlag).toUpdateSig) (E : Set Event) (s : State) (e : Event)
    (hs : representation initialFlag C E s) (supported : e ∈ C.events) (fresh : e ∉ E)
    (semantic : ∀ x ∈ E, x ≠ e → ¬ paperOrder policy C (insert e E) e x)
    (metadata : ∀ x ∈ E, ¬ C.vis e x) :
    representation initialFlag C (insert e E) (update s e) := by
  obtain ⟨sup,F,hF,counts,bits⟩ := hs
  have absent : e ∉ F := by
    intro he
    apply fresh
    rw [← hF]
    exact he
  refine ⟨?_,insert e F,by simp [hF],?_,?_⟩
  · intro x hx; exact hx.elim (fun h => h ▸ supported) (sup x)
  · intro r
    rcases e with ⟨ts,rep,op⟩
    cases op <;> by_cases same : r = rep
    all_goals simp [update,Op.op,counts,NeemFlagCounts.count,NeemFlagCounts.winners,Finset.filter_insert,NeemFlagCounts.winningAt,Op.rep,absent,same,eq_comm]
  · intro r
    cases hop : e.op with
    | winning =>
      have live := live_insert_winning hop metadata r
      have noreset : NoReset (insert e E) ↔ NoReset E := by
        simp [NoReset,hop]
      simp only [Bit,live,noreset]
      rcases e with ⟨ts,rep,op⟩
      simp only [Op.op] at hop
      subst op
      by_cases same : r = rep
      · simp [update,Op.op,same]
      · simpa [update,Op.op,same] using bits r
    | reset =>
      have dead := reset_kills_live hop semantic metadata r
      have noreset : ¬ NoReset (insert e E) := by
        intro h; exact h e (Or.inl rfl) hop
      simp only [Bit,dead,noreset,and_false,or_self]
      rcases e with ⟨ts,rep,op⟩
      simp only [Op.op] at hop
      subst op
      simp [update,Op.op]

theorem finite_rep (initialFlag : Bool) (C : ReplayContext (D initialFlag).toUpdateSig)
    (E : Set Event) (s : State) (hs : representation initialFlag C E s) :
    ∃ π, listPermOf π E := by
  obtain ⟨_,F,hF,_,_⟩ := hs
  refine ⟨F.toList,Finset.nodup_toList _,?_⟩
  intro e
  simp only [Finset.mem_toList]
  change e ∈ F ↔ e ∈ E
  rw [← hF]
  rfl

theorem count_update (F : Finset Event) (s : State) (e : Event) (fresh : e ∉ F)
    (hs : ∀ r, (s r).1 = count F r) :
    ∀ r, (update s e r).1 = count (insert e F) r := by
  intro r
  rcases e with ⟨ts,rep,op⟩
  cases op <;> by_cases same : r = rep
  all_goals simp [update,Op.op,hs,NeemFlagCounts.count,NeemFlagCounts.winners,
    Finset.filter_insert,NeemFlagCounts.winningAt,Op.rep,fresh,same,eq_comm]

theorem replay_counts (initialFlag : Bool) (π : List Event) (nd : π.Nodup) :
    ∀ r, (applySeq (D initialFlag).toUpdateSig (initial initialFlag) π r).1 = count π.toFinset r := by
  induction π using List.reverseRecOn with
  | nil => simp [applySeq,initial,NeemFlagCounts.count,NeemFlagCounts.winners]
  | append_singleton pre e ih =>
    obtain ⟨ndpre,_,disjoint⟩ := List.nodup_append.mp nd
    have absent : e ∉ pre.toFinset := by
      simpa using (fun h : e ∈ pre => disjoint e h e (by simp) rfl)
    rw [applySeq_append_single]
    simpa [List.toFinset_append] using count_update pre.toFinset
      (applySeq (D initialFlag).toUpdateSig (initial initialFlag) pre) e absent (ih ndpre)

theorem same_action_commutes (initialFlag : Bool) (a b : Event)
    (same : a.op = b.op) : (D initialFlag).toUpdateSig.commutes a b := by
  intro s
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  simp only [Op.op] at same
  subst ob
  cases oa <;> funext r <;> simp only [D,update,Op.op]
  all_goals split_ifs <;> simp_all <;> omega

private theorem order_insert_winning {initialFlag : Bool}
    {C : ReplayContext (D initialFlag).toUpdateSig} {E : Set Event} {e a b : Event}
    (win : e.op = .winning) (h : paperOrder policy C E a b) :
    paperOrder policy C (insert e E) a b := by
  rcases h with causal | ⟨hab,hba,pol,unabsorbed⟩
  · exact Or.inl causal
  · refine Or.inr ⟨hab,hba,pol,?_⟩
    rintro ⟨c,hc,hbc,nc⟩
    rcases hc with rfl | hc
    · have bw : b.op = .winning := pol.2
      exact nc (same_action_commutes initialFlag b c (bw.trans win.symm))
    · exact unabsorbed ⟨c,hc,hbc,nc⟩

/-- A concrete sorted replay realizes the independent live-event predicate.
Reset-last histories need no canonical-prefix assumption: reset erases bits.
Winning-last histories preserve policy order when the winning event is peeled.
-/
theorem replay_rep (initialFlag : Bool) (C : ReplayContext (D initialFlag).toUpdateSig)
    (π : List Event) (nd : π.Nodup) (sup : ∀ e ∈ π, e ∈ C.events)
    (vis : respects π C.vis)
    (ordered : respects π (paperOrder policy C (↑π.toFinset : Set Event))) :
    representation initialFlag C (↑π.toFinset : Set Event)
      (applySeq (D initialFlag).toUpdateSig (initial initialFlag) π) := by
  induction π using List.reverseRecOn with
  | nil => simpa [applySeq] using initial_rep initialFlag C
  | append_singleton pre e ih =>
    obtain ⟨ndpre,_,disjoint⟩ := List.nodup_append.mp nd
    have absent : e ∉ pre.toFinset := by
      simpa using (fun h : e ∈ pre => disjoint e h e (by simp) rfl)
    have vp : respects pre C.vis := (List.pairwise_append.mp vis).1
    have metadata : ∀ x ∈ (↑pre.toFinset : Set Event), ¬ C.vis e x := by
      intro x hx
      exact (List.pairwise_append.mp vis).2.2 x (by simpa using hx) e (by simp)
    have semantic : ∀ x ∈ (↑pre.toFinset : Set Event), x ≠ e →
        ¬ paperOrder policy C (insert e (↑pre.toFinset : Set Event)) e x := by
      intro x hx _
      have h := (List.pairwise_append.mp ordered).2.2 x (by simpa using hx) e (by simp)
      simpa [List.toFinset_append] using h
    have fresh : e ∉ (↑pre.toFinset : Set Event) := absent
    have se : e ∈ C.events := sup e (by simp)
    cases hop : e.op with
    | winning =>
      have opre : respects pre (paperOrder policy C (↑pre.toFinset : Set Event)) := by
        apply ((List.pairwise_append.mp ordered).1).imp
        intro a b h hab
        apply h
        simpa [List.toFinset_append] using order_insert_winning hop hab
      have hs := ih ndpre (fun x hx => sup x (by simp [hx])) vp opre
      have ins := insert_rep initialFlag C _ _ e hs se fresh semantic metadata
      rw [applySeq_append_single]
      simpa [List.toFinset_append] using ins
    | reset =>
      refine ⟨?_,(pre ++ [e]).toFinset,rfl,replay_counts initialFlag _ nd,?_⟩
      · intro x hx; exact sup x (by simpa [or_comm] using hx)
      · intro r
        have dead := reset_kills_live hop semantic metadata r
        have noreset : ¬ NoReset (insert e (↑pre.toFinset : Set Event)) := by
          intro h; exact h e (Or.inl rfl) hop
        rw [applySeq_append_single]
        have sets : (↑(pre ++ [e]).toFinset : Set Event) = insert e (↑pre.toFinset : Set Event) := by
          simp [List.toFinset_append]
        rw [sets]
        change (update _ e r).2 = true ↔ Bit C (insert e (↑pre.toFinset : Set Event)) r
        simp only [Bit,dead,noreset,and_false,or_self]
        rcases e with ⟨ts,rep,op⟩
        simp only [Op.op] at hop
        subst op
        simp [update,Op.op]

private theorem finite_maximal {β : Type} (R : β → β → Prop)
    (trans : Transitive R) (irr : ∀ x, ¬ R x x)
    (F : Finset β) (nonempty : F.Nonempty) :
    ∃ e ∈ F, ∀ x ∈ F, x ≠ e → ¬ R e x := by
  classical
  induction F using Finset.induction_on with
  | empty => simp at nonempty
  | @insert a F absent ih =>
    by_cases hn : F.Nonempty
    · obtain ⟨e,he,maximal⟩ := ih hn
      by_cases edge : R e a
      · refine ⟨a,by simp,?_⟩
        intro x hx ne forward
        have hxF : x ∈ F := (Finset.mem_insert.mp hx).resolve_left ne
        by_cases eq : x = e
        · subst x; exact irr e (trans edge forward)
        · exact maximal x hxF eq (trans edge forward)
      · refine ⟨e,Finset.mem_insert_of_mem he,?_⟩
        intro x hx ne forward
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact edge forward
        · exact maximal x hx ne forward
    · have empty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst F
      refine ⟨a,by simp,?_⟩
      intros x hx ne
      simp at hx
      exact (ne hx).elim

private def Alive {initialFlag : Bool} (C : ReplayContext (D initialFlag).toUpdateSig)
    (E : Set Event) (e : Event) : Prop :=
  e.op = .winning ∧ ∀ d ∈ E, d.op = .reset → ¬ C.vis e d

theorem joint_maximal (initialFlag : Bool) (C : ReplayContext (D initialFlag).toUpdateSig)
    (E : Set Event) (s : State) (hs : representation initialFlag C E s)
    (trans : Transitive C.vis) (irr : ∀ x, ¬ C.vis x x) (nonempty : E.Nonempty) :
    ∃ e ∈ E, (∀ x ∈ E, x ≠ e → ¬ paperOrder policy C E e x) ∧
      (∀ x ∈ E, x ≠ e → ¬ C.vis e x) := by
  obtain ⟨_,F,hF,_,_⟩ := hs
  have hn : F.Nonempty := by
    obtain ⟨e,he⟩ := nonempty
    refine ⟨e,?_⟩
    rw [← hF] at he
    exact he
  let A := F.filter (Alive C E)
  by_cases alive : A.Nonempty
  · obtain ⟨e,he,maximal⟩ := finite_maximal C.vis trans irr A alive
    obtain ⟨heF,hew,heLive⟩ := Finset.mem_filter.mp he
    have heE : e ∈ E := by rw [← hF]; exact heF
    have maxvis : ∀ x ∈ E, x ≠ e → ¬ C.vis e x := by
      intro x hx ne edge
      have xwin : x.op = .winning := by
        cases hop : x.op with
        | winning => rfl
        | reset => exact (heLive x hx hop edge).elim
      have xalive : Alive C E x := ⟨xwin,fun d hd reset next => heLive d hd reset (trans edge next)⟩
      have hxF : x ∈ F := by rw [← hF] at hx; exact hx
      exact maximal x (Finset.mem_filter.mpr ⟨hxF,xalive⟩) ne edge
    refine ⟨e,heE,?_,maxvis⟩
    intro x hx ne order
    rcases order with causal | conflict
    · exact maxvis x hx ne causal.1
    · have bad := conflict.2.2.1.1
      simp [policy,hew] at bad
  · obtain ⟨e,he,maxvis⟩ := finite_maximal C.vis trans irr F hn
    have heE : e ∈ E := by rw [← hF]; exact he
    refine ⟨e,heE,?_,?_⟩
    · intro x hx ne order
      have hxF : x ∈ F := by rw [← hF] at hx; exact hx
      rcases order with causal | conflict
      · exact maxvis x hxF ne causal.1
      · have xwin : x.op = .winning := conflict.2.2.1.2
        have xalive : Alive C E x := by
          refine ⟨xwin,?_⟩
          intro d hd reset edge
          exact conflict.2.2.2 ⟨d,hd,edge,different_noncommutes initialFlag x d (by simp [xwin,reset])⟩
        have mem : x ∈ A := Finset.mem_filter.mpr ⟨hxF,xalive⟩
        exact alive ⟨x,mem⟩
    · intro x hx ne
      have hxF : x ∈ F := by rw [← hF] at hx; exact hx
      exact maxvis x hxF ne

theorem replaySupply (initialFlag : Bool) (C : ReplayContext (D initialFlag).toUpdateSig)
    (trans : Transitive C.vis) (irr : ∀ x, ¬ C.vis x x) :
    Raw.ReplaySupply policy (representation initialFlag) (scheme initialFlag) C := by
  refine ⟨represented initialFlag C,?_⟩
  intro E s hs support nonempty closed
  obtain ⟨e,member,semantic,metadata⟩ := joint_maximal initialFlag C E s hs trans irr nonempty
  obtain ⟨π,hp⟩ := finite_rep initialFlag C E s hs
  have pastSub := (scheme initialFlag C).past_subset E e closed member
  obtain ⟨pre,hpre⟩ := enumeration_subset hp (show E \ {e} ⊆ E from Set.diff_subset)
  obtain ⟨past,hpast⟩ := enumeration_subset hp
    (show (scheme initialFlag C).Past e \ {e} ⊆ E from fun _ h => pastSub h.1)
  obtain ⟨t,ht⟩ := represented initialFlag C _ pre hpre (fun x hx => support x hx.1)
  obtain ⟨B,hB⟩ := represented initialFlag C _ past hpast (fun x hx => support x (pastSub hx.1))
  have unionEq : insert e (E \ {e}) = E := by ext x; simp; tauto
  have pastEq : insert e ((scheme initialFlag C).Past e \ {e}) = (scheme initialFlag C).Past e := by
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
    apply insert_rep initialFlag C _ B e hB (support e member) (by simp)
    · intro x hx ne
      rw [pastEq]
      exact (scheme initialFlag C).past_semantic_maximal policy trans irr e x hx.1 ne
    · intro x hx edge
      exact irr e (trans edge ((scheme initialFlag C).past_vis trans hx.1 hx.2))
  · rw [← unionEq]
    apply insert_rep initialFlag C _ t e ht (support e member) (by simp)
    · intro x hx ne
      rw [unionEq]
      exact semantic x hx.1 ne
    · intro x hx
      exact metadata x hx.1 hx.2

private theorem paperOrder_shrink {initialFlag : Bool}
    {C : ReplayContext (D initialFlag).toUpdateSig} {E U : Set Event} (sub : E ⊆ U)
    {a b : Event} (h : paperOrder policy C U a b) : paperOrder policy C E a b := by
  rcases h with h | ⟨hab,hba,pol,unabsorbed⟩
  · exact Or.inl h
  · exact Or.inr ⟨hab,hba,pol,fun ⟨c,hc,edge,nc⟩ => unabsorbed ⟨c,sub hc,edge,nc⟩⟩

theorem canonical_with_vis (initialFlag : Bool)
    (C : ReplayContext (D initialFlag).toUpdateSig)
    (trans : Transitive C.vis) (irr : ∀ x, ¬ C.vis x x)
    (E : Set Event) (s : State) (hs : representation initialFlag C E s) :
    ∃ π : List Event, listPermOf π E ∧ respects π (paperOrder policy C E) ∧
      respects π C.vis ∧ applySeq (D initialFlag).toUpdateSig (initial initialFlag) π = s := by
  obtain ⟨sup,F,hF,counts,bits⟩ := hs
  have hsF : representation initialFlag C (↑F : Set Event) s := by
    rw [hF]; exact ⟨sup,F,hF,counts,bits⟩
  suffices result : ∀ (F : Finset Event) (s : State),
      representation initialFlag C (↑F : Set Event) s →
      ∃ π : List Event, listPermOf π (↑F : Set Event) ∧
        respects π (paperOrder policy C (↑F : Set Event)) ∧ respects π C.vis ∧
        applySeq (D initialFlag).toUpdateSig (initial initialFlag) π = s by
    simpa [hF] using result F s hsF
  intro F
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    intro s hs
    by_cases empty : F = ∅
    · subst F
      have eq := unique initialFlag C ∅ s (initial initialFlag) (by simpa using hs) (initial_rep initialFlag C)
      refine ⟨[],by simp [listPermOf],by simp [respects],by simp [respects],?_⟩
      simpa [applySeq] using eq.symm
    · have nonempty : (↑F : Set Event).Nonempty := by
        obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
        exact ⟨e,he⟩
      obtain ⟨e,he,semantic,metadata⟩ := joint_maximal initialFlag C _ s hs trans irr nonempty
      have heF : e ∈ F := he
      have erased : (↑(F.erase e) : Set Event) = (↑F : Set Event) \ {e} := by ext x; simp
      have supported : Supported C (↑(F.erase e) : Set Event) := by
        intro x hx; exact hs.1 x (Finset.mem_of_mem_erase hx)
      obtain ⟨t,ht⟩ := represented initialFlag C _ (F.erase e).toList
        ⟨Finset.nodup_toList _,by simp [and_comm]⟩ supported
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
      have updated := insert_rep initialFlag C _ t e ht (hs.1 e he) fresh
        (fun x hx ne => by rw [unionEq]; exact semantic x (Finset.mem_of_mem_erase hx) ne)
        (fun x hx => metadata x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx))
      rw [unionEq] at updated
      have eq := unique initialFlag C _ (update t e) s updated hs
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

theorem canonical (initialFlag : Bool) (C : ReplayContext (D initialFlag).toUpdateSig)
    (trans : Transitive C.vis) (irr : ∀ x, ¬ C.vis x x)
    (E : Set Event) (s : State) (hs : representation initialFlag C E s) :
    Canonical policy C E s := by
  obtain ⟨π,hp,order,_,fold⟩ := canonical_with_vis initialFlag C trans irr E s hs
  exact ⟨π,hp,order,fold⟩

#print axioms replay_rep
#print axioms replaySupply
end Sal.MRDTs.Paper1.NeemFlagReplay
