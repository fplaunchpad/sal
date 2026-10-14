import Sal.MRDTs.Instances.RemoveWinsSet
import Sal.MRDTs.Paper1.ConcreteReplay

/-! Canonical survival of removal tags, including initial zero tags. -/
namespace Sal.MRDTs.Paper1.RemoveWinsSet
open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.RemoveWinsSet
variable {α : Type} [DecidableEq α] [Fintype α]

abbrev BornRun (ops : List (Op (Update α))) : State α :=
  applySeq (D α).toUpdateSig (∅ : State α) ops

def NoAdd (ops : List (Op (Update α))) (x : α) : Prop :=
  ∀ e ∈ ops, e.2.2 ≠ .add x

theorem tag_preserved {s : State α} {p : α × Timestamp} (hs : p ∈ s)
    (ops : List (Op (Update α))) (hn : NoAdd ops p.1) :
    p ∈ (show State α from applySeq (D α).toUpdateSig s ops) := by
  induction ops generalizing s with
  | nil => exact hs
  | cons e ops ih =>
      have he := hn e (by simp)
      have hn' : NoAdd ops p.1 := fun a ha => hn a (by simp [ha])
      apply ih (s := step s e) _ hn'
      rcases e with ⟨t, r, op⟩
      cases op with
      | remove x => simp [step, hs]
      | add x =>
          have hx : p.1 ≠ x := by intro h; exact he (by simp [h])
          simp [step, hs, hx]

theorem born_mem_iff_suffix (ops : List (Op (Update α))) (p : α × Timestamp) :
    p ∈ BornRun ops ↔ ∃ pre a post, ops = pre ++ a :: post ∧
      a.2.2 = .remove p.1 ∧ a.1 = p.2 ∧ NoAdd post p.1 := by
  constructor
  · induction ops using List.reverseRecOn with
    | nil => simp [BornRun, applySeq, D]
    | append_singleton ops e ih =>
        intro hm
        change p ∈ (show State α from applySeq (D α).toUpdateSig (∅ : State α) (ops ++ [e])) at hm
        rw [applySeq_append_single] at hm
        change p ∈ step (BornRun ops) e at hm
        rcases hop : e.2.2 with ⟨x⟩ | ⟨x⟩
        · simp only [step, hop, Finset.mem_insert] at hm
          rcases hm with h | h
          · have hx : x = p.1 := (congrArg Prod.fst h).symm
            have ht : e.1 = p.2 := (congrArg Prod.snd h).symm
            exact ⟨ops, e, [], by simp, hx ▸ hop, ht, by simp [NoAdd]⟩
          · obtain ⟨pre, a, post, hsplit, ha, ht, hn⟩ := ih h
            refine ⟨pre, a, post ++ [e], by simp [hsplit, List.append_assoc], ha, ht, ?_⟩
            intro r hr
            rcases List.mem_append.mp hr with hr | hr
            · exact hn r hr
            · have hre : r = e := List.mem_singleton.mp hr
              subst r
              simp [hop]
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
    have hp : p ∈ step (BornRun pre) a := by
      have heq : (p.1, a.1) = p := by rw [ht]
      simp [step, ha, heq]
    have hpost := tag_preserved hp post hn
    simpa [BornRun, applySeq, D, List.foldl_append] using hpost

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
  ¬ ∃ r ∈ E, C.vis a r ∧ r.2.2 = .add x

def Live (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (p : α × Timestamp) : Prop :=
  ∃ a ∈ E, a.2.2 = .remove p.1 ∧ a.1 = p.2 ∧ Survives C E a p.1

theorem born_mem_iff_live {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} {ops : List (Op (Update α))}
    (hp : listPermOf ops E) (hr : respects ops (loOn C E)) (p : α × Timestamp) :
    p ∈ BornRun ops ↔ Live C E p := by
  rw [born_mem_iff_suffix]
  constructor
  · rintro ⟨pre, a, post, hs, ha, ht, hn⟩
    subst ops
    refine ⟨a, (hp.2 a).mp (by simp), ha, ht, ?_⟩
    rintro ⟨r, hre, hv, hrem⟩
    have hm : r ∈ pre ++ a :: post := (hp.2 r).mpr hre
    rcases List.mem_append.mp hm with hm | hm
    · apply not_edge_to_prefix hr hm
      exact Or.inl ⟨hv, Or.inr ((replayOrder_iff r a).mpr ⟨p.1, hrem, ha⟩)⟩
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
    have hrc : (D α).toUpdateSig.replayBefore r a := (replayOrder_iff r a).mpr ⟨p.1, hrem, ha⟩
    by_cases hva : C.vis r a
    · exact Or.inl ⟨hva, Or.inl hrc⟩
    · refine Or.inr ⟨hva, ?_, hrc, ?_⟩
      · exact fun hv => hn ⟨r, hre, hv, hrem⟩
      · rintro ⟨c, hce, hvc, hc⟩
        rcases hc with hc | hc
        · obtain ⟨x, ha', _⟩ := (replayOrder_iff a c).mp hc
          rw [ha] at ha'; cases ha'
        · obtain ⟨x, hc, ha'⟩ := (replayOrder_iff c a).mp hc
          rw [ha] at ha'; injection ha' with hx
          subst x
          exact hn ⟨c, hce, hvc, hc⟩

theorem live_iff_fixed_remove {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} (hsub : E ⊆ C.events)
    {p : α × Timestamp} {a : Op (Update α)}
    (hac : a ∈ C.events) (ha : a.2.2 = .remove p.1) (ht : a.1 = p.2) :
    Live C E p ↔ a ∈ E ∧ Survives C E a p.1 := by
  constructor
  · rintro ⟨b, hb, _, hbt, hs⟩
    have heq : b = a := C.ts_unique (hsub hb) hac (hbt.trans ht.symm)
    subst b
    exact ⟨hb, hs⟩
  · rintro ⟨he, hs⟩
    exact ⟨a, he, ha, ht, hs⟩


/-- Initial records survive exactly when no Add for their element occurs. -/
theorem fold_mem (ops : List (Op (Update α))) (s : State α) (p : α × Timestamp) :
    p ∈ (show State α from applySeq (D α).toUpdateSig s ops) ↔
      (p ∈ s ∧ NoAdd ops p.1) ∨ p ∈ BornRun ops := by
  induction ops using List.reverseRecOn with
  | nil => simp [BornRun,applySeq,NoAdd,D]
  | append_singleton ops e ih =>
    rw [applySeq_append_single]
    change p ∈ step (applySeq (D α).toUpdateSig s ops) e ↔ _
    have hn : NoAdd (ops ++ [e]) p.1 ↔ NoAdd ops p.1 ∧ e.op ≠ .add p.1 := by
      unfold NoAdd
      constructor
      · intro h; exact ⟨fun x hx => h x (List.mem_append_left _ hx),h e (by simp)⟩
      · rintro ⟨h,he⟩ x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact h x hx
        · exact List.mem_singleton.mp hx ▸ he
    have runeq : BornRun (ops ++ [e]) = step (BornRun ops) e := applySeq_append_single _ _ _
    rw [hn,runeq]
    rcases e with ⟨t,r,op⟩
    cases op <;> simp only [step,Finset.mem_insert,Finset.mem_filter,Op.op]
    all_goals rw [ih]
    all_goals simp only [Update.add.injEq,ne_eq]
    all_goals grind

def Seed (C : ReplayContext (D α).toUpdateSig) (E : Set (Op (Update α)))
    (p : α × Timestamp) : Prop :=
  p.2 = 0 ∧ ∀ e ∈ E, e.op ≠ .add p.1

def Tags (C : ReplayContext (D α).toUpdateSig) (E : Set (Op (Update α)))
    (p : α × Timestamp) : Prop := Seed C E p ∨ Live C E p

@[simp] theorem mem_initial (p : α × Timestamp) : p ∈ initial α ↔ p.2 = 0 := by
  rcases p with ⟨x,t⟩
  simp [initial,Finset.mem_image,eq_comm]

theorem canonical_mem_iff {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} {s : State α}
    (hs : IsCanonicalState C E s) (p : α × Timestamp) : p ∈ s ↔ Tags C E p := by
  obtain ⟨ops,hp,hr,hf⟩ := hs
  rw [← hf,fold_mem]
  change (p ∈ initial α ∧ NoAdd ops p.1) ∨ p ∈ BornRun ops ↔ _
  rw [mem_initial,born_mem_iff_live hp hr]
  unfold Tags Seed
  have hn : NoAdd ops p.1 ↔ ∀ e ∈ E, e.op ≠ .add p.1 := by
    unfold NoAdd
    exact ⟨fun h e he => h e ((hp.2 e).mpr he),fun h e he => h e ((hp.2 e).mp he)⟩
  rw [hn]

end Sal.MRDTs.Paper1.RemoveWinsSet
