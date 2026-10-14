import Sal.MRDTs.Instances.AddWinsPriorityQueue

/-! Canonical Add survival and retained increment membership. The proofs
inspect replay suffixes and causal removal, without invoking Join. -/
namespace Sal.MRDTs.Paper1.AddWinsPriorityQueue
open Instances.AddWinsPriorityQueue
open Sal.MRDTs.Foundation
variable {α : Type} [DecidableEq α]

abbrev Run (ops : List (Op (Update α))) : State α :=
  applySeq (D α).toUpdateSig (D α).init ops

def NoRemove (ops : List (Op (Update α))) (x : α) : Prop :=
  ∀ e ∈ ops, e.2.2 ≠ .remove x

theorem pair_preserved {s : State α} {p : AddRecord α} (hs : p ∈ s.1)
    (ops : List (Op (Update α))) (hn : NoRemove ops p.1) :
    p ∈ (show State α from applySeq (D α).toUpdateSig s ops).1 := by
  induction ops generalizing s with
  | nil => exact hs
  | cons e ops ih =>
      have he := hn e (by simp)
      have hn' : NoRemove ops p.1 := fun a ha => hn a (by simp [ha])
      apply ih (s := step s e) _ hn'
      rcases e with ⟨t, r, op⟩
      cases op with
      | add x v => simp [step, hs]
      | inc x n => simp [step,hs]
      | remove x =>
          have hx : p.1 ≠ x := by intro h; exact he (by simp [h])
          simp [step, hs, hx]

theorem mem_run_iff_suffix (ops : List (Op (Update α))) (p : AddRecord α) :
    p ∈ (Run ops).1 ↔ ∃ pre a post, ops = pre ++ a :: post ∧
      a.2.2 = .add p.1 p.2.2 ∧ a.1 = p.2.1 ∧ NoRemove post p.1 := by
  constructor
  · induction ops using List.reverseRecOn with
    | nil => simp [Run, applySeq, D]
    | append_singleton ops e ih =>
        intro hm
        change p ∈ (show State α from applySeq (D α).toUpdateSig (D α).init (ops ++ [e])).1 at hm
        rw [applySeq_append_single] at hm
        change p ∈ (step (Run ops) e).1 at hm
        rcases hop : e.2.2 with ⟨x,v⟩ | ⟨x,n⟩ | ⟨x⟩
        · simp only [step, hop, Finset.mem_insert] at hm
          rcases hm with h | h
          · have hx : x = p.1 := (congrArg Prod.fst h).symm
            have ht : e.1 = p.2.1 := (congrArg (fun q : AddRecord α => q.2.1) h).symm
            have hv : v = p.2.2 := (congrArg (fun q : AddRecord α => q.2.2) h).symm
            exact ⟨ops, e, [], by simp, by simpa only [hx,hv] using hop, ht, by simp [NoRemove]⟩
          · obtain ⟨pre, a, post, hsplit, ha, ht, hn⟩ := ih h
            refine ⟨pre, a, post ++ [e], by simp [hsplit, List.append_assoc], ha, ht, ?_⟩
            intro r hr
            rcases List.mem_append.mp hr with hr | hr
            · exact hn r hr
            · have hre : r = e := List.mem_singleton.mp hr
              subst r
              simp [hop]
        · simp only [step, hop] at hm
          obtain ⟨pre,a,post,hsplit,ha,ht,hn⟩ := ih hm
          refine ⟨pre,a,post ++ [e],by simp [hsplit,List.append_assoc],ha,ht,?_⟩
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact hn r hr
          · have hre : r = e := List.mem_singleton.mp hr
            subst r; simp [hop]
        · simp only [step, hop, Finset.mem_filter] at hm
          obtain ⟨pre, a, post, hsplit, ha, ht, hn⟩ := ih hm.1
          refine ⟨pre, a, post ++ [e], by simp [hsplit, List.append_assoc], ha, ht, ?_⟩
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact hn r hr
          · have hre : r = e := List.mem_singleton.mp hr
            subst r
            intro hrem
            rw [hop] at hrem
            injection hrem with hx
            exact hm.2 hx.symm
  · rintro ⟨pre, a, post, rfl, ha, ht, hn⟩
    have hp : p ∈ (step (Run pre) a).1 := by
      have heq : (p.1, a.1,p.2.2) = p := by rw [ht]
      simp [step, ha, heq]
    have hpost := pair_preserved hp post hn
    simpa [Run, applySeq, D, List.foldl_append] using hpost

/-- A relation edge cannot point from a suffix into a preceding position. -/
theorem not_edge_to_prefix {R : Op (Update α) → Op (Update α) → Prop}
    {pre post : List (Op (Update α))} {a r : Op (Update α)}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ pre) : ¬ R a r := by
  exact (List.pairwise_append.mp hr).2.2 r hm a (by simp)

theorem not_edge_from_suffix {R : Op (Update α) → Op (Update α) → Prop}
    {pre post : List (Op (Update α))} {a r : Op (Update α)}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ post) : ¬ R r a := by
  exact (List.pairwise_cons.mp (List.pairwise_append.mp hr).2.1).1 r hm

def Survives (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (a : Op (Update α)) (x : α) : Prop :=
  ¬ ∃ r ∈ E, C.vis a r ∧ r.2.2 = .remove x

def Live (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (p : AddRecord α) : Prop :=
  ∃ a ∈ E, a.2.2 = .add p.1 p.2.2 ∧ a.1 = p.2.1 ∧ Survives C E a p.1

theorem mem_run_iff_live {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} {ops : List (Op (Update α))}
    (hp : listPermOf ops E) (hr : respects ops (loOn C E)) (p : AddRecord α) :
    p ∈ (Run ops).1 ↔ Live C E p := by
  rw [mem_run_iff_suffix]
  constructor
  · rintro ⟨pre, a, post, hs, ha, ht, hn⟩
    subst ops
    refine ⟨a, (hp.2 a).mp (by simp), ha, ht, ?_⟩
    rintro ⟨r, hre, hv, hrem⟩
    have hm : r ∈ pre ++ a :: post := (hp.2 r).mpr hre
    rcases List.mem_append.mp hm with hm | hm
    · apply not_edge_to_prefix hr hm
      exact Or.inl ⟨hv, Or.inr ((replayOrder_iff r a).mpr ⟨p.1,p.2.2, hrem, ha⟩)⟩
    · rcases List.mem_cons.mp hm with heq | hm
      · rw [heq, ha] at hrem; cases hrem
      · exact hn r hm hrem
  · rintro ⟨a, hae, ha, ht, hn⟩
    obtain ⟨pre, post, hs⟩ := List.append_of_mem ((hp.2 a).mpr hae)
    refine ⟨pre, a, post, hs, ha, ht, ?_⟩
    subst ops
    intro r hm hrem
    apply not_edge_from_suffix hr hm
    have hre : r ∈ E := (hp.2 r).mp (by simp [hm])
    have hrc : (D α).toUpdateSig.replayBefore r a := (replayOrder_iff r a).mpr ⟨p.1,p.2.2, hrem, ha⟩
    by_cases hva : C.vis r a
    · exact Or.inl ⟨hva, Or.inl hrc⟩
    · refine Or.inr ⟨hva, ?_, hrc, ?_⟩
      · exact fun hv => hn ⟨r, hre, hv, hrem⟩
      · rintro ⟨c, hce, hvc, hc⟩
        rcases hc with hc | hc
        · obtain ⟨x,v, ha', _⟩ := (replayOrder_iff a c).mp hc
          rw [ha] at ha'; cases ha'
        · obtain ⟨x,v, hc, ha'⟩ := (replayOrder_iff c a).mp hc
          rw [ha] at ha'; injection ha' with hx
          subst x
          exact hn ⟨c, hce, hvc, hc⟩

theorem canonical_mem_iff {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} {s : State α}
    (hs : IsCanonicalState C E s) (p : AddRecord α) : p ∈ s.1 ↔ Live C E p := by
  obtain ⟨ops, hp, hr, hf⟩ := hs
  rw [← hf]
  exact mem_run_iff_live hp hr p


theorem live_iff_fixed_add {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} (hsub : E ⊆ C.events)
    {p : AddRecord α} {a : Op (Update α)}
    (hac : a ∈ C.events) (ha : a.2.2 = .add p.1 p.2.2) (ht : a.1 = p.2.1) :
    Live C E p ↔ a ∈ E ∧ Survives C E a p.1 := by
  constructor
  · rintro ⟨b, hb, _, hbt, hs⟩
    have heq : b = a := C.ts_unique (hsub hb) hac (hbt.trans ht.symm)
    subst b
    exact ⟨hb, hs⟩
  · rintro ⟨he, hs⟩
    exact ⟨a, he, ha, ht, hs⟩

/-- All increment events survive, including increments before a removal. -/
def IncLive (E : Set (Op (Update α))) (p : IncRecord α) : Prop :=
  ∃ e ∈ E, e.op = .inc p.1 p.2.2 ∧ e.time = p.2.1

theorem mem_incs_run (ops : List (Op (Update α))) (p : IncRecord α) :
    p ∈ (Run ops).2 ↔ IncLive {e | e ∈ ops} p := by
  induction ops using List.reverseRecOn with
  | nil => simp [Run,applySeq,D,IncLive]
  | append_singleton ops e ih =>
    change p ∈ (applySeq (D α).toUpdateSig (D α).init (ops ++ [e])).2 ↔ _
    rw [applySeq_append_single]
    change p ∈ (step (Run ops) e).2 ↔ _
    rcases e with ⟨t,r,op⟩
    cases op <;> simp [step,IncLive,Op.op,Op.time] at ih ⊢ <;> grind

theorem canonical_incs {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} {s : State α}
    (hs : IsCanonicalState C E s) (p : IncRecord α) : p ∈ s.2 ↔ IncLive E p := by
  obtain ⟨ops,hp,hr,hf⟩ := hs
  rw [← hf,mem_incs_run]
  simp only [IncLive,Set.mem_setOf_eq]
  exact exists_congr (fun e => and_congr (hp.2 e) Iff.rfl)

/-- Ancestor event inclusion supplies the retained-increment preconditions of
`historical_increment_merge`; no monotonicity is assumed for live Add records. -/
theorem increments_mono {C : ReplayContext (D α).toUpdateSig}
    {A B : Set (Op (Update α))} {s t : State α}
    (subset : A ⊆ B) (hs : IsCanonicalState C A s) (ht : IsCanonicalState C B t) :
    s.2 ⊆ t.2 := by
  intro p hp
  obtain ⟨e,he,inc,time⟩ := (canonical_incs hs p).mp hp
  exact (canonical_incs ht p).mpr ⟨e,subset he,inc,time⟩

end Sal.MRDTs.Paper1.AddWinsPriorityQueue
