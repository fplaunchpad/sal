import Sal.MRDTs.Paper1.OptionalRegisterReplay
import Sal.MRDTs.Paper1.ConcreteHistoryBridge

/-! The independent client machine is a scalar optional register: Set assigns
Some value and Unset assigns None. It retains no counters, rows, timestamps,
or live-write candidates. The source read is chosen separately; chronological
choices of the surviving writes are therefore a scoped history obligation. -/
namespace Sal.MRDTs.Paper1.OptionalRegister
open Foundation Instances.OptionalRegister

def scalarStep (_ : Option Nat) (a : Action) : Option Nat := match a with
  | .set v => some v
  | .unset => none

def model : DeterministicSpec (Op Action) Unit (Option Nat) where
  State := Option Nat
  initial := none
  update s e := scalarStep s e.op
  query s _ := s

def spec := model.toSpec

@[simp] theorem scalarStep_set (s : Option Nat) (v : Nat) : scalarStep s (.set v) = some v := rfl
@[simp] theorem scalarStep_unset (s : Option Nat) : scalarStep s .unset = none := rfl

/-- A nonempty scalar replay observes precisely its last update. -/
theorem run_snoc (ops : List (Op Action)) (e : Op Action) :
    (ops ++ [e]).foldl model.update model.initial = scalarStep none e.op := by
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,model]
  cases e.op <;> rfl

/-- The chosen chronology can be supplied directly at the scoped bridge. -/
theorem admits_snoc (ops : List (Op Action)) (e : Op Action) :
    spec.admits (DeterministicSpec.updateLabels (ops ++ [e]) ++
      [.query () (scalarStep none e.op)]) := by
  change model.toSpec.admits _
  rw [DeterministicSpec.updates_query_iff]
  exact (run_snoc ops e).symm

/-- Scalar histories witness distinct Set values failing to commute. This is
why the source's commuting different-issuer Sets need scoped chronology. -/
theorem scalar_sets_noncommute (ta ra va tb rb vb : Nat) (different : va ≠ vb) :
    ¬ spec.Commutes (ta,ra,.set va) (tb,rb,.set vb) := by
  intro h
  have yes := admits_snoc [(ta,ra,Action.set va)] (tb,rb,Action.set vb)
  have no : ¬ spec.admits
      (DeterministicSpec.updateLabels [(tb,rb,Action.set vb),(ta,ra,Action.set va)] ++
        [.query () (some vb)]) := by
    change ¬ model.toSpec.admits _
    rw [DeterministicSpec.updates_query_iff]
    simp [model,scalarStep,Op.op,different,ne_comm]
  apply no
  simpa [DeterministicSpec.updateLabels] using (h [] [.query () (some vb)]).mp
    (by simpa [DeterministicSpec.updateLabels] using yes)

open Classical

def Early (C : ReplayContext D.toUpdateSig) (E : Set (Op Action)) (e : Op Action) : Prop :=
  e.op = .unset ∨ ∃ d ∈ E, C.vis e d ∧ d.op = .unset

noncomputable def rank (C : ReplayContext D.toUpdateSig) (E : Set (Op Action))
    (e : Op Action) : Lex (Nat × Nat) := toLex (if Early C E e then 0 else 1,e.time)

def Before (C : ReplayContext D.toUpdateSig) (E : Set (Op Action)) (a b : Op Action) : Prop :=
  rank C E a < rank C E b

theorem early_backwards (C : ReplayContext D.toUpdateSig) (E : Set (Op Action))
    (good : GoodContext C) {a b : Op Action} (hb : b ∈ E) (vis : C.vis a b)
    (early : Early C E b) : Early C E a := by
  rcases early with reset | ⟨d,hd,edge,reset⟩
  · exact Or.inr ⟨b,hb,vis,reset⟩
  · exact Or.inr ⟨d,hd,good.trans vis edge,reset⟩

theorem before_of_vis (C : ReplayContext D.toUpdateSig) (E : Set (Op Action))
    (good : GoodContext C) {a b : Op Action} (hb : b ∈ E) (vis : C.vis a b) :
    Before C E a b := by
  have time := good.mono vis
  have back := early_backwards C E good hb vis
  unfold Before rank
  rw [Prod.Lex.toLex_lt_toLex]
  by_cases ea : Early C E a <;> by_cases eb : Early C E b
  all_goals simp [ea,eb] at back ⊢
  all_goals omega

theorem exists_sorted (C : ReplayContext D.toUpdateSig) (E : Set (Op Action))
    (ops : List (Op Action)) (hp : listPermOf ops E) :
    ∃ sorted, listPermOf sorted E ∧ respects sorted (Before C E) := by
  let cmp := fun a b => decide (rank C E a ≤ rank C E b)
  refine ⟨ops.mergeSort cmp,?_,?_⟩
  · have perm := List.mergeSort_perm ops cmp
    exact ⟨perm.nodup_iff.mpr hp.1,fun e => perm.mem_iff.trans (hp.2 e)⟩
  · have sorted := List.pairwise_mergeSort (le := cmp)
      (fun a b c ab bc => by simpa [cmp] using le_trans (of_decide_eq_true ab) (of_decide_eq_true bc))
      (fun a b => by simpa [cmp] using le_total (rank C E a) (rank C E b)) ops
    exact sorted.imp (fun {_ _} h => not_lt_of_ge (of_decide_eq_true h))

theorem sorted_respects_vis (C : ReplayContext D.toUpdateSig) (E : Set (Op Action))
    (good : GoodContext C) (ops : List (Op Action)) (perm : listPermOf ops E)
    (sorted : respects ops (Before C E)) : respects ops C.vis := by
  apply sorted.imp_of_mem
  intro a b ha hb hn edge
  exact hn (before_of_vis C E good ((perm.2 a).mp ha) edge)

theorem sorted_respects_paper (C : ReplayContext D.toUpdateSig) (E : Set (Op Action))
    (good : GoodContext C) (ops : List (Op Action)) (perm : listPermOf ops E)
    (sorted : respects ops (Before C E)) : respects ops (paperOrder policy C E) := by
  apply sorted.imp_of_mem
  intro a b ha hb hn edge
  apply hn
  rcases edge with ⟨vis,_⟩ | ⟨_,_,⟨reset,v,set⟩,noAbsorber⟩
  · exact before_of_vis C E good ((perm.2 a).mp ha) vis
  · have eb : Early C E b := Or.inl reset
    have ea : ¬ Early C E a := by
      rintro (reset' | ⟨d,hd,vis,reset'⟩)
      · simp [set] at reset'
      · apply noAbsorber ⟨d,hd,vis,?_⟩
        rcases a with ⟨ta,ra,oa⟩; rcases d with ⟨td,rd,od⟩
        simp only [Op.op] at set reset'
        subst oa; subst od
        exact set_unset_noncomm ta ra v td rd
    simp [Before,rank,ea,eb,Prod.Lex.toLex_lt_toLex]

private theorem active_domain (s : State) (r : Nat) (active : (s.cells r).1.2 = true) :
    r ∈ s.domain := by
  by_contra absent
  have := s.outside r absent
  simp [this,zero] at active

theorem query_none_of_no_live (C : ReplayContext D.toUpdateSig) (E : Set Event) (s : State)
    (rep : Represents C E s) (noLive : ∀ w ∈ E, ¬ LiveEvent C E w) : query s = none := by
  have empty : candidates s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨_,active⟩ := Finset.mem_filter.mp hr
    obtain ⟨w,hw,_,live,_⟩ := rep.payload r active
    exact noLive w hw live
  simp [query,winner,empty]

theorem query_greatest_live (C : ReplayContext D.toUpdateSig) (E : Set Event) (s : State)
    (rep : Represents C E s) (w : Event) (member : w ∈ E) (live : LiveEvent C E w)
    (greatest : ∀ x ∈ E, LiveEvent C E x → x.time ≤ w.time) :
    query s = some (valueOf w) := by
  have active : (s.cells w.rep).1.2 = true := (rep.active w.rep).mpr ⟨w,member,rfl,live⟩
  obtain ⟨x,hx,own,lx,payload,latest⟩ := rep.payload w.rep active
  have same : x = w := timestamp_unique rep.supported hx member (by
    have wx := latest w member rfl live.1
    have xw := greatest x hx lx
    exact Nat.le_antisymm xw wx)
  subst x
  let key : Write := toLex (w.time,toLex (w.rep,valueOf w))
  have mem : key ∈ candidates s := by
    apply Finset.mem_image.mpr
    refine ⟨w.rep,Finset.mem_filter.mpr ⟨active_domain s _ active,active⟩,?_⟩
    simp [key,payload]
  have upper : ∀ c ∈ candidates s, c ≤ key := by
    intro c hc
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨_,ar⟩ := Finset.mem_filter.mp hr
    obtain ⟨y,hy,yr,ly,py,_⟩ := rep.payload r ar
    have le := greatest y hy ly
    rcases Nat.lt_or_eq_of_le le with lt | eq
    · apply le_of_lt
      apply Prod.Lex.toLex_lt_toLex.mpr
      exact Or.inl (by simpa [py,key] using lt)
    · have equal : y = w := timestamp_unique rep.supported hy member eq
      subst y
      subst r
      simp [py,key]
  have maximum (nonempty : (candidates s).Nonempty) : (candidates s).max' nonempty = key := by
    apply le_antisymm
    · exact Finset.max'_le _ nonempty key upper
    · exact Finset.le_max' _ key mem
  simp [query,winner,show (candidates s).Nonempty from ⟨key,mem⟩,maximum,key]

theorem late_of_live (C : ReplayContext D.toUpdateSig) (E : Set Event) (w : Event)
    (live : LiveEvent C E w) : ¬ Early C E w := by
  rintro (reset | ⟨d,hd,vis,reset⟩)
  · have win := live.1
    simp [reset,Action.isSet] at win
  · exact live.2 d hd reset vis

/-- Sorting is proof-local chronology. The abstract machine remains scalar. -/
theorem sorted_refines (C : ReplayContext D.toUpdateSig) (E : Set Event) (s : State)
    (rep : Represents C E s) (ops : List Event) (perm : listPermOf ops E)
    (sorted : respects ops (Before C E)) :
    query s = ops.foldl model.update model.initial := by
  induction ops using List.reverseRecOn with
  | nil =>
    apply query_none_of_no_live C E s rep
    intro w hw
    have := (perm.2 w).mpr hw
    simp at this
  | append_singleton pre e _ =>
    have member : e ∈ E := (perm.2 e).mp (by simp)
    have last : ∀ x ∈ E, ¬ Before C E e x := by
      intro x hx
      have mem := (perm.2 x).mpr hx
      rcases List.mem_append.mp mem with old | final
      · exact (List.pairwise_append.mp sorted).2.2 x old e (by simp)
      · have equal : x = e := by simpa using final
        subst x
        exact lt_irrefl _
    rw [run_snoc]
    cases he : e.op with
    | unset =>
      apply query_none_of_no_live C E s rep
      intro w hw live
      have late := late_of_live C E w live
      have early : Early C E e := Or.inl he
      have before : Before C E e w := by simp [Before,rank,late,early,Prod.Lex.toLex_lt_toLex]
      exact last w hw before
    | set v =>
      have late : ¬ Early C E e := by
        rintro (reset | ⟨d,hd,vis,reset⟩)
        · simp [he] at reset
        · have early : Early C E e := Or.inr ⟨d,hd,vis,reset⟩
          have earlyD : Early C E d := Or.inl reset
          have before : Before C E e d := by
            simp [Before,rank,early,earlyD,Prod.Lex.toLex_lt_toLex]
            exact rep.good.mono vis
          exact last d hd before
      have live : LiveEvent C E e := by
        refine ⟨by simp [he,Action.isSet],?_⟩
        intro d hd reset vis
        exact late (Or.inr ⟨d,hd,vis,reset⟩)
      have greatest : ∀ x ∈ E, LiveEvent C E x → x.time ≤ e.time := by
        intro x hx lx
        have lateX := late_of_live C E x lx
        have notLater := last x hx
        simp [Before,rank,late,lateX,Prod.Lex.toLex_lt_toLex] at notLater
        omega
      simpa [he,scalarStep,valueOf] using query_greatest_live C E s rep e member live greatest

theorem sorted_admits (C : ReplayContext D.toUpdateSig) (E : Set Event) (s : State)
    (rep : Represents C E s) (ops : List Event) (perm : listPermOf ops E)
    (sorted : respects ops (Before C E)) (q : Unit) :
    spec.admits (projectedLabels (D := D) id ops ++ [.query q (D.query s q)]) := by
  cases q
  change model.toSpec.admits (DeterministicSpec.updateLabels ops ++ [.query () (query s)])
  rw [DeterministicSpec.updates_query_iff]
  exact sorted_refines C E s rep ops perm sorted

/-- Scoped assembly consumes separately derived source representation and
canonical execution evidence. It does not assume a scalar read certificate. -/
theorem history_from_representation
    (represented : ∀ C, CertifiedExecution D generation C → ∀ v s E,
      C.ver v = some (s,E) → Represents C.replayContext E s)
    (canonical : ∀ C, CertifiedExecution D generation C → ∀ v s E,
      C.ver v = some (s,E) → ConcreteMRDT.Canonical policy C.replayContext E s) :
    EventExecutionHistoryAdequacy D policy spec generation := by
  intro C execution v s E hv q
  have rep := represented C execution v s E hv
  obtain ⟨F,hF⟩ := rep.finite
  have enumeration : listPermOf F.toList E := by
    refine ⟨Finset.nodup_toList _,?_⟩
    intro e
    simp only [Finset.mem_toList]
    change e ∈ F ↔ e ∈ E
    rw [←hF]
    rfl
  obtain ⟨ops,perm,sorted⟩ := exists_sorted C.replayContext E F.toList enumeration
  have paper := sorted_respects_paper C.replayContext E rep.good ops perm sorted
  have visibility := sorted_respects_vis C.replayContext E rep.good ops perm sorted
  have equality : applySeq D.toUpdateSig D.init ops = s :=
    ConcreteMRDT.canonical_unique laws C.replayContext E rep.supported
      ⟨ops,perm,paper,rfl⟩ (canonical C execution v s E hv)
  refine ⟨ops,perm,paper,visibility.imp (fun {_ _} h edge => h edge.1),?_⟩
  rw [equality]
  exact sorted_admits C.replayContext E s rep ops perm sorted q

#print axioms scalar_sets_noncommute
#print axioms query_greatest_live
#print axioms sorted_refines
#print axioms history_from_representation
end Sal.MRDTs.Paper1.OptionalRegister
