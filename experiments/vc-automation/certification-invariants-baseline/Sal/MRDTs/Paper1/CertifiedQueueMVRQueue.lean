import Sal.MRDTs.Paper1.CertifiedPolicy
import Sal.MRDTs.Paper1.GuardedQueueMVR

/-! A minimal fork/apply/apply certified queue experiment. Two concurrent
same-payload enqueues already force the forbidden payload self-chain. -/
namespace Sal.MRDTs.Paper1.CertifiedQueueMVR.Queue
open Foundation Instances.Queue
open Classical

abbrev a : Op QOp := (1,0,.enq 7)
abbrev b : Op QOp := (2,1,.enq 7)
def rawParents (v : Nat) : List Nat := if v = 1 ∨ v = 2 then [0] else if v = 3 then [1] else []
def parents (k v : Nat) : List Nat := if v ≤ k then rawParents v else []
def version (k v : Nat) : Option (QState × Set (Op QOp)) :=
  if v = 0 then some ([], ∅)
  else if v = 1 ∧ 1 ≤ k then some ([], ∅)
  else if v = 2 ∧ 2 ≤ k then some ([(1,7)], {a})
  else if v = 3 ∧ 3 ≤ k then some ([(2,7)], {b}) else none
def heads (k r : Nat) : Option Nat :=
  if r = 0 then some (if 2 ≤ k then 2 else 0)
  else if r = 1 ∧ 1 ≤ k then some (if 3 ≤ k then 3 else 1) else none

private theorem rawParents_lt : ∀ v p, p ∈ rawParents v → p < v := by
  intro v p h
  simp only [rawParents] at h
  split at h
  · simp only [List.mem_singleton] at h; subst p; omega
  · split at h
    · simp only [List.mem_singleton] at h; subst p; omega
    · simp at h

private theorem reaches_shape {v w : Nat} (h : Reaches rawParents v w) :
    v = w ∨ (v = 0 ∧ (w = 1 ∨ w = 2 ∨ w = 3)) ∨ (v = 1 ∧ w = 3) := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail x y h edge ih =>
    simp only [rawParents] at edge
    split at edge
    · simp only [List.mem_singleton] at edge
      subst x
      have le := reaches_le rawParents_lt h
      have zero : v = 0 := by omega
      exact Or.inr (Or.inl ⟨zero, by tauto⟩)
    · split at edge
      · simp only [List.mem_singleton] at edge
        subst x
        have le := reaches_le rawParents_lt h
        have wy : y = 3 := by assumption
        subst y
        rcases ih with eq | ⟨eq,_⟩ | ⟨eq,_⟩
        · exact Or.inr (Or.inr ⟨eq,rfl⟩)
        · exact Or.inr (Or.inl ⟨eq,Or.inr (Or.inr rfl)⟩)
        · exact Or.inr (Or.inr ⟨eq,rfl⟩)
      · simp at edge

private theorem version_cases {k v : Nat} {s : QState} {E : Set (Op QOp)}
    (h : version k v = some (s,E)) :
    (v = 0 ∧ s = [] ∧ E = ∅) ∨
    (v = 1 ∧ s = [] ∧ E = ∅) ∨
    (v = 2 ∧ s = [(1,7)] ∧ E = {a}) ∨
    (v = 3 ∧ s = [(2,7)] ∧ E = {b}) := by
  simp only [version] at h
  split at h
  · simp_all
  · split at h
    · simp_all
    · split at h
      · simp_all
      · split at h <;> simp_all

private theorem head_events_cases {k r : Nat} {E : Set (Op QOp)}
    (h : @headEventsFrom Q (version k) (heads k) r = some E) :
    E = ∅ ∨ E = {a} ∨ E = {b} := by
  unfold headEventsFrom at h
  cases hr : heads k r with
  | none => simp [hr] at h
  | some v =>
    cases hv : version k v with
    | none => simp [hr,hv] at h
    | some record =>
      obtain ⟨s,F⟩ := record
      have eq : F = E := by simpa [hr,hv] using h
      subst F
      rcases version_cases hv with ⟨_,_,eq⟩ | ⟨_,_,eq⟩ | ⟨_,_,eq⟩ | ⟨_,_,eq⟩
      · exact Or.inl eq
      · exact Or.inl eq
      · exact Or.inr (Or.inl eq)
      · exact Or.inr (Or.inr eq)

def config (k : Nat) : Configuration Q where
  vis _ _ := False
  ver := version k
  head := heads k
  parents := parents k
  parents_lt := by
    intro v p h
    unfold parents at h
    split at h
    · exact rawParents_lt v p h
    · simp at h
  ver_init := by simp [version,Q]
  head_alloc := by
    intro r v h
    unfold heads at h
    split at h
    · split at h
      · have hv : v = 2 := (Option.some.inj h).symm
        subst v
        simp_all [version]
      · have hv : v = 0 := (Option.some.inj h).symm
        subst v
        simp_all [version]
    · split at h
      · split at h
        · have hv : v = 3 := (Option.some.inj h).symm
          subst v
          simp_all [version]
        · have hv : v = 1 := (Option.some.inj h).symm
          subst v
          simp_all [version]
      · simp at h
  vis_src := by simp
  vis_tgt := by simp
  vis_causal := by simp
  timestamps_distinct := by
    intro x y r E r' F hE hx hF hy ne
    change x ∈ E at hx
    change y ∈ F at hy
    rcases head_events_cases hE with rfl | rfl | rfl <;>
      rcases head_events_cases hF with rfl | rfl | rfl <;>
      simp only [Set.mem_empty_iff_false,Set.mem_singleton_iff] at hx hy
    all_goals subst x; subst y; simp_all [a,b]
  causal_mono := by simp
  vis_total_same_replica := by
    intro x y r E r' F hE hx hF hy ne same
    change x ∈ E at hx
    change y ∈ F at hy
    rcases head_events_cases hE with rfl | rfl | rfl <;>
      rcases head_events_cases hF with rfl | rfl | rfl <;>
      simp only [Set.mem_empty_iff_false,Set.mem_singleton_iff] at hx hy
    all_goals subst x; subst y; simp_all [a,b]
  gca_events := by
    intro v₁ v₂ vT s₁ E₁ s₂ E₂ sT ET hg hv₁ hv₂ hvT
    have rawReach : ∀ {x y}, Reaches (parents k) x y → Reaches rawParents x y := by
      intro x y h
      induction h with
      | refl => exact .refl
      | tail _ edge ih =>
        apply ih.tail
        unfold parents at edge
        split at edge
        · exact edge
        · simp at edge
    have first := reaches_shape (rawReach hg.1)
    have second := reaches_shape (rawReach hg.2.1)
    have same : v₁ = v₂ → vT = v₁ := by
      intro eq
      subst v₂
      exact Nat.le_antisymm (reaches_le rawParents_lt (rawReach hg.1))
        (reaches_le rawParents_lt (rawReach (hg.2.2 v₁ .refl .refl)))
    rcases version_cases hv₁ with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;>
      rcases version_cases hv₂ with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;>
      rcases version_cases hvT with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;>
      simp_all [Set.inter_comm,a,b]

private theorem version_member {k v : Nat} {s : QState} {E : Set (Op QOp)}
    (hv : version k v = some (s,E)) {e : Op QOp} (he : e ∈ E) :
    (e = a ∧ 2 ≤ k) ∨ (e = b ∧ 3 ≤ k) := by
  unfold version at hv
  split at hv
  · simp only [Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨_,rfl⟩ := hv
    simp at he
  · split at hv
    · simp only [Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨_,rfl⟩ := hv
      simp at he
    · split at hv
      · simp only [Option.some.injEq, Prod.mk.injEq] at hv
        obtain ⟨_,rfl⟩ := hv
        simp_all
      · split at hv
        · simp only [Option.some.injEq, Prod.mk.injEq] at hv
          obtain ⟨_,rfl⟩ := hv
          simp_all
        · simp at hv

private theorem observed_member {k : Nat} {e : Op QOp} (he : e ∈ (config k).events) :
    (e = a ∧ 2 ≤ k) ∨ (e = b ∧ 3 ≤ k) := by
  obtain ⟨r,E,hE,he⟩ := he
  change headEventsFrom (version k) (heads k) r = some E at hE
  unfold headEventsFrom at hE
  cases hr : heads k r with
  | none => simp [hr] at hE
  | some v =>
    cases hv : version k v with
    | none => simp [hr,hv] at hE
    | some record =>
      obtain ⟨s,F⟩ := record
      have eq : F = E := by simpa [hr,hv] using hE
      subst F
      exact version_member hv he

theorem config_zero : config 0 = initConfig Q := by
  unfold config initConfig
  congr 1 <;> funext x <;> simp [version,heads,parents,rawParents,Q]
  intro h
  subst x
  rfl

theorem fork_step : Step Q (config 0) (.fork 1 0) (config 1) := by
  apply Step.fork (v := 0) (s := []) (ev := ∅) (vnew := 1)
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
  · rfl
  · funext v; simp [config,version]; split_ifs <;> simp_all
  · funext r; simp [config,heads]; split_ifs <;> simp_all
  · funext v; simp [config,parents,rawParents]; split_ifs <;> simp_all

theorem first_step : Step Q (config 1) (.apply 1 0 (.enq 7)) (config 2) := by
  apply Step.apply (v := 0) (s := []) (ev := ∅) (vnew := 2)
  · rfl
  · rfl
  · intro e he
    have h := observed_member he
    omega
  · intro v s E hv e he
    have h := version_member hv he
    omega
  · rfl
  · decide
  · funext x y
    apply propext
    change False ↔ False ∨ (False ∧ _)
    simp
  · funext v; simp [config,version,Q,qUpdate,qTags]; split_ifs <;> simp_all
  · funext r; simp [config,heads]; split_ifs <;> simp_all
  · funext v; simp [config,parents,rawParents]; split_ifs <;> simp_all

theorem second_step : Step Q (config 2) (.apply 2 1 (.enq 7)) (config 3) := by
  apply Step.apply (v := 1) (s := []) (ev := ∅) (vnew := 3)
  · rfl
  · rfl
  · intro e he
    rcases observed_member he with ⟨rfl,_⟩ | ⟨_,bad⟩
    · decide
    · omega
  · intro v s E hv e he
    rcases version_member hv he with ⟨rfl,_⟩ | ⟨_,bad⟩
    · decide
    · omega
  · rfl
  · decide
  · funext x y
    apply propext
    change False ↔ False ∨ (False ∧ _)
    simp
  · funext v; simp [config,version,Q,qUpdate,qTags]; split_ifs <;> simp_all
  · funext r; simp [config,heads]; split_ifs <;> simp_all
  · funext v; simp [config,parents,rawParents]; split_ifs <;> simp_all
    all_goals omega

theorem mint_honest (k : Nat) : MintHonest Q generation.CanIssue (config k) := by
  intro e he
  refine ⟨[],?_,by simp [respects],?_⟩
  · simp [listPermOf,config]
  · rcases observed_member he with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp [generation,qApplicable,qTags,applySeq,Q]

theorem certified : MintCertifiedReach Q generation (config 3) := by
  have initial : MintCertifiedReach Q generation (config 0) := by
    rw [config_zero]
    exact .init
  have forked := MintCertifiedReach.step initial (mint_honest 0)
    (IssuedStep.nonApply fork_step (by intro t r o h; cases h)) (mint_honest 1)
  have first := MintCertifiedReach.step forked (mint_honest 1)
    (IssuedStep.apply (v := 0) (s := []) rfl rfl (by simp [generation,qApplicable,qTags,Q]) first_step)
    (mint_honest 2)
  exact .step first (mint_honest 2)
    (IssuedStep.apply (v := 1) (s := []) rfl rfl (by simp [generation,qApplicable,qTags,Q]) second_step)
    (mint_honest 3)


theorem endpoint_members : a ∈ (config 3).events ∧ b ∈ (config 3).events := by
  constructor
  · exact ⟨0,{a},rfl,rfl⟩
  · exact ⟨1,{b},rfl,rfl⟩

/-- PASS+FAIL: both mint heads and the represented common root are empty;
the actual issuer admits both enqueues, but opposite legal orders have
different FIFO heads. The negative excludes vacuous conflict classification. -/
theorem certified_control :
    MintCertifiedReach Q generation (config 3) ∧
    a ∈ (config 3).events ∧ b ∈ (config 3).events ∧
    ¬ (config 3).vis a b ∧ ¬ (config 3).vis b a ∧
    (config 3).ver 0 = some ([], ∅) ∧
    qApplicable a [] ∧ qApplicable b [] ∧
    qApplicable b (qUpdate [] a) ∧ qApplicable a (qUpdate [] b) ∧
    Q.query (qUpdate (qUpdate [] a) b) () = some (1,7) ∧
    Q.query (qUpdate (qUpdate [] b) a) () = some (2,7) ∧
    Q.query (qUpdate (qUpdate [] a) b) () ≠
      Q.query (qUpdate (qUpdate [] b) a) () := by
  refine ⟨certified,endpoint_members.1,endpoint_members.2,?_,?_,rfl,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [config,qApplicable,qUpdate,qTags,Q]

/-- Even exactness restricted to this certified history's concurrent events
and its represented empty root forces a payload self-edge. Timestamp-guarded
no-chain still forbids that edge: the triple (a,b,a) meets both pair guards.
No raw all-state commutation or independently chosen origin is assumed. -/
theorem no_local_payload_policy :
    ¬ ∃ P : OperationPolicy QOp,
      (∀ x y : Op QOp, x ∈ (config 3).events → y ∈ (config 3).events →
        ¬ (config 3).vis x y → ¬ (config 3).vis y x →
        distinctOps (D := Q.toUpdateSig) x y → x.rep ≠ y.rep →
        (qUpdate (qUpdate [] x) y ≠ qUpdate (qUpdate [] y) x ↔
          P.before x.op y.op ∨ P.before y.op x.op)) ∧
      (∀ x y z : Op QOp,
        x ∈ (config 3).events → y ∈ (config 3).events → z ∈ (config 3).events →
        distinctOps (D := Q.toUpdateSig) x y → distinctOps (D := Q.toUpdateSig) y z →
        ¬ (P.before x.op y.op ∧ P.before y.op z.op)) := by
  rintro ⟨P,exactness,noChain⟩
  have conflict := (exactness a b endpoint_members.1 endpoint_members.2
    (by simp [config]) (by simp [config])
    (by change 1 ≠ 2; decide) (by decide)).mp (by decide)
  have self : P.before (QOp.enq 7) (QOp.enq 7) := by
    simpa only [Op.op,or_self] using conflict
  exact noChain a b a endpoint_members.1 endpoint_members.2 endpoint_members.1
    (by change 1 ≠ 2; decide) (by change 2 ≠ 1; decide) ⟨self,self⟩

/-- The obstruction also targets the actual certified policy interface, not
only its single-prefix specialization. Every scope containing the represented
empty root and this original certified history is excluded. -/
theorem no_scoped_policy (S : CertifiedReplay.Scope Q.toUpdateSig)
    (context : S.context = (config 3).replayContext)
    (events : S.events = (config 3).events)
    (empty : S.represented ∅ []) :
    ¬ ∃ P : OperationPolicy QOp, CertifiedReplay.PolicyLaws S P := by
  rintro ⟨P,laws⟩
  have ha : a ∈ S.events := events ▸ endpoint_members.1
  have hb : b ∈ S.events := events ▸ endpoint_members.2
  have readyA : CertifiedReplay.Ready S ∅ a := by
    refine ⟨ha,by simp,?_⟩
    intro p hp vis
    rw [context] at vis
    exact False.elim vis
  have readyB : CertifiedReplay.Ready S ∅ b := by
    refine ⟨hb,by simp,?_⟩
    intro p hp vis
    rw [context] at vis
    exact False.elim vis
  have noncommute : ¬ CertifiedReplay.Commutes S a b := by
    intro commute
    have neq : qUpdate (qUpdate [] a) b ≠ qUpdate (qUpdate [] b) a := by decide
    exact neq (commute ∅ [] empty readyA readyB)
  have conflict := (laws.concurrent_exact a b ha hb
    (by change 1 ≠ 2; decide) (by decide)
    (by rw [context]; exact fun h => h) (by rw [context]; exact fun h => h)).mp noncommute
  have self : P.before (QOp.enq 7) (QOp.enq 7) := by
    simpa only [Op.op,or_self] using conflict
  exact laws.no_chain a b a ha hb ha
    (by change 1 ≠ 2; decide) (by change 2 ≠ 1; decide) ⟨self,self⟩


#print axioms certified
#print axioms no_local_payload_policy

end Sal.MRDTs.Paper1.CertifiedQueueMVR.Queue
