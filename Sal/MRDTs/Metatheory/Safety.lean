import Sal.MRDTs.Metatheory.CertifiedAdequacy

namespace Sal.MRDTs

open Sal.MRDTs.Foundation
open Classical

/-- **Causal fold**: `σ` is the fold of some enumeration of `E`
that linearizes `vis` (no later element is `vis`-before an earlier one).
Prefixes of such an enumeration are exactly the vis-backward-closed subsets
of `E`. -/
def CausalFold {D' : UpdateSig} (C : Sal.MRDTs.Foundation.ReplayContext D')
    (E : Set (Op D'.AppOp)) (σ : D'.State) : Prop :=
  ∃ ρ : List (Op D'.AppOp),
    listPermOf ρ E ∧ respects ρ C.vis ∧ applySeq D' D'.init ρ = σ

section
variable {D : MRDTSig}
variable [ReplayPolicy D.toUpdateSig]

/-- The ∃-form honesty over an explicit guard `A`: every event satisfies `A`
at some causal fold of its causal past. Existential because the issuer holds
only the one fold its replica materialized (order-sensitive datatypes:
different causal enumerations of the same past can fold differently). Being
an ∃-statement, it carries its own enumeration witness, with no separate
enumerability side condition. -/
def HonestAppOn (D : MRDTSig)
    (A : Op D.AppOp → D.State → Prop) (C : Configuration D) : Prop :=
  ∀ e ∈ C.events, ∃ σ : D.State,
    CausalFold (Configuration.replayContext C) {e' ∈ C.events | C.vis e' e} σ ∧ A e σ

/-- **Causal canonical witness**: every version state is the
fold of an enumeration of its event set that linearizes `vis` and respects
`loOn`, strictly refining `CanonicalConfig.canonical`. -/
def CausalCanonical (C : Configuration D) : Prop :=
  ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) →
    ∃ ρ : List (Op D.AppOp),
      listPermOf ρ E ∧ respects ρ C.vis ∧
      respects ρ (loOn (Configuration.replayContext C) E) ∧
      applySeq D.toUpdateSig D.init ρ = s

/-- **The per-datatype safety obligation**, over an explicit
conditioning pair `(I, A)`: over vis-closed, future-free causal prefixes `S`
with `past(e) ⊆ S ⊆ E` and causal folds `σS` of `S`, `σP` of `past(e)`,
`I σS → A e σP → I (update σS e)`. Fused with `I`-preservation so that
unconditionally-safe ops need no guard at all. -/
def SafetyStepOn (D : MRDTSig) (I : D.State → Prop)
    (A : Op D.AppOp → D.State → Prop) : Prop :=
  ∀ (C : Configuration D) (E S : Set (Op D.AppOp)) (e : Op D.AppOp)
    (σS σP : D.State),
    (∀ a ∈ E, a ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ E → a ∈ E) →
    e ∈ E → S ⊆ E → e ∉ S →
    (∀ a b, C.vis a b → b ∈ S → a ∈ S) →
    (∀ x ∈ S, ¬ C.vis e x) →
    (∀ x, C.vis x e → x ∈ S) →
    CausalFold (Configuration.replayContext C) S σS →
    CausalFold (Configuration.replayContext C) {e' ∈ C.events | C.vis e' e} σP →
    I σS → A e σP → I (D.update σS e)

/-! ## §2  The metatheorem: induction along the causal witness

Snoc-forward along the causal witness ρ of a version `(s, E)`, maintaining
`I` at every prefix fold. The bookkeeping: a
prefix set of a `respects · vis` enumeration of the (fully causally closed,
`CanonicalConfig.version_events_causal`) set `E` is vis-backward-closed, future-free, and
contains the whole causal past of the next element, all read off the
`Pairwise` structure of `π ++ e :: τ`. -/

/-- Every prefix of a causal enumeration of a stored version satisfies the
datatype invariant.  This is the prefix-strengthened form of the generic
safety argument and is used directly by sequential specifications whose
legality is prefix safety. -/
theorem prefix_inv_of_causal_witness
    {I : D.State → Prop} {A : Op D.AppOp → D.State → Prop}
    (hInit : I D.init) (hStep : SafetyStepOn D I A)
    {C : Configuration D} (hG : CanonicalConfig C)
    (hHon : HonestAppOn D A C)
    {v : Version} {s : D.State} {E : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E))
    {ρ : List (Op D.AppOp)} (hperm : listPermOf ρ E)
    (hvisR : respects ρ C.vis) :
    ∀ pre suf, ρ = pre ++ suf →
      I (applySeq D.toUpdateSig D.init pre) := by
  have hE_ev : ∀ a ∈ E, a ∈ C.events :=
    hG.version_events_supported v s E hv
  have hE_cl : ∀ a b, C.vis a b → b ∈ E → a ∈ E :=
    hG.version_events_causal v s E hv
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
      intro _ _
      exact hInit
  | append_singleton pre e ih =>
      intro suf hsplit
      have hsplit' : ρ = pre ++ e :: suf := by
        simpa [List.append_assoc] using hsplit
      have hprev : I (applySeq D.toUpdateSig D.init pre) :=
        ih (e :: suf) hsplit'
      have hnd : (pre ++ e :: suf).Nodup := by
        rw [← hsplit']
        exact hperm.1
      have hpw : (pre ++ e :: suf).Pairwise (fun a b => ¬ C.vis b a) := by
        rw [← hsplit']
        exact hvisR
      obtain ⟨hpwPre, hpwE, hcross⟩ := List.pairwise_append.mp hpw
      have hsuf_no_e : ∀ x ∈ suf, ¬ C.vis x e :=
        (List.pairwise_cons.mp hpwE).1
      have hmemρ : ∀ x, x ∈ pre ++ e :: suf ↔ x ∈ E := by
        intro x
        rw [← hsplit']
        exact hperm.2 x
      have heE : e ∈ E :=
        (hmemρ e).mp (List.mem_append_right _ List.mem_cons_self)
      have hSsub : {x : Op D.AppOp | x ∈ pre} ⊆ E := fun x hx =>
        (hmemρ x).mp (List.mem_append_left _ hx)
      have heS : e ∉ ({x : Op D.AppOp | x ∈ pre} : Set (Op D.AppOp)) := by
        intro hmem
        exact (List.nodup_append.mp hnd).2.2 e hmem e List.mem_cons_self rfl
      have hfut : ∀ x ∈ ({x : Op D.AppOp | x ∈ pre} : Set (Op D.AppOp)),
          ¬ C.vis e x :=
        fun x hx => hcross x hx e List.mem_cons_self
      have hpast : ∀ x, C.vis x e →
          x ∈ ({x : Op D.AppOp | x ∈ pre} : Set (Op D.AppOp)) := by
        intro x hvis
        have hxE : x ∈ E := hE_cl x e hvis heE
        rcases List.mem_append.mp ((hmemρ x).mpr hxE) with hx | hx
        · exact hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact absurd hvis (hG.vis_irrefl x)
          · exact absurd hvis (hsuf_no_e x hx)
      have hScl : ∀ a b, C.vis a b →
          b ∈ ({x : Op D.AppOp | x ∈ pre} : Set (Op D.AppOp)) →
          a ∈ ({x : Op D.AppOp | x ∈ pre} : Set (Op D.AppOp)) := by
        intro a b hvis hb
        have haE : a ∈ E := hE_cl a b hvis (hSsub hb)
        rcases List.mem_append.mp ((hmemρ a).mpr haE) with ha | ha
        · exact ha
        · exfalso
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hfut b hb hvis
          · exact hcross b hb a (List.mem_cons_of_mem _ ha) hvis
      have hσS : CausalFold (Configuration.replayContext C)
          {x : Op D.AppOp | x ∈ pre}
          (applySeq D.toUpdateSig D.init pre) :=
        ⟨pre, ⟨(List.nodup_append.mp hnd).1, fun _ => Iff.rfl⟩, hpwPre, rfl⟩
      obtain ⟨σP, hσP, happ⟩ := hHon e (hE_ev e heE)
      rw [applySeq_append_single]
      exact hStep C E {x : Op D.AppOp | x ∈ pre} e
        (applySeq D.toUpdateSig D.init pre) σP
        hE_ev hE_cl heE hSsub heS hScl hfut hpast hσS hσP hprev happ

/-- **Generic safety, causal-witness form, explicit conditioning pair.** -/
theorem version_inv_on_of_causal_canonical
    {I : D.State → Prop} {A : Op D.AppOp → D.State → Prop}
    (hInit : I D.init) (hStep : SafetyStepOn D I A)
    {C : Configuration D}
    (hG : CanonicalConfig C) (hCC : CausalCanonical C)
    (hHon : HonestAppOn D A C) :
    ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
      C.ver v = some (s, E) → I s := by
  intro v s E hv
  obtain ⟨ρ, hperm, hvisR, _hloR, hfold⟩ := hCC v s E hv
  have hE_ev : ∀ a ∈ E, a ∈ C.events := hG.version_events_supported v s E hv
  have hE_cl : ∀ a b, C.vis a b → b ∈ E → a ∈ E := hG.version_events_causal v s E hv
  suffices h : ∀ (τ π : List (Op D.AppOp)), ρ = π ++ τ →
      I (applySeq D.toUpdateSig D.init π) →
      I (applySeq D.toUpdateSig D.init ρ) by
    rw [← hfold]
    exact h ρ [] rfl hInit
  intro τ
  induction τ with
  | nil =>
    intro π hsplit hI
    rw [List.append_nil] at hsplit
    rw [hsplit]
    exact hI
  | cons e τ' ih =>
    intro π hsplit hI
    -- prefix bookkeeping at the step `e`
    have hnd : (π ++ e :: τ').Nodup := by rw [← hsplit]; exact hperm.1
    have hpw : (π ++ e :: τ').Pairwise (fun a b => ¬ C.vis b a) := by
      rw [← hsplit]; exact hvisR
    obtain ⟨hpwπ, hpwE, hcross⟩ := List.pairwise_append.mp hpw
    have hτ'_no_e : ∀ x ∈ τ', ¬ C.vis x e := (List.pairwise_cons.mp hpwE).1
    have hmemρ : ∀ x, x ∈ π ++ e :: τ' ↔ x ∈ E := by
      intro x; rw [← hsplit]; exact hperm.2 x
    have he_E : e ∈ E :=
      (hmemρ e).mp (List.mem_append_right _ List.mem_cons_self)
    have hS_sub : {x : Op D.AppOp | x ∈ π} ⊆ E := fun x hx =>
      (hmemρ x).mp (List.mem_append_left _ hx)
    have he_not_π : e ∉ ({x : Op D.AppOp | x ∈ π} : Set (Op D.AppOp)) := by
      intro hmem
      exact (List.nodup_append.mp hnd).2.2 e hmem e List.mem_cons_self rfl
    have hfut : ∀ x ∈ ({x : Op D.AppOp | x ∈ π} : Set (Op D.AppOp)),
        ¬ C.vis e x :=
      fun x hx => hcross x hx e List.mem_cons_self
    have hpast : ∀ x, C.vis x e →
        x ∈ ({x : Op D.AppOp | x ∈ π} : Set (Op D.AppOp)) := by
      intro x hvis
      have hxE : x ∈ E := hE_cl x e hvis he_E
      rcases List.mem_append.mp ((hmemρ x).mpr hxE) with hx | hx
      · exact hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hvis (hG.vis_irrefl x)
        · exact absurd hvis (hτ'_no_e x hx)
    have hS_cl : ∀ a b, C.vis a b →
        b ∈ ({x : Op D.AppOp | x ∈ π} : Set (Op D.AppOp)) →
        a ∈ ({x : Op D.AppOp | x ∈ π} : Set (Op D.AppOp)) := by
      intro a b hvis hb
      have haE : a ∈ E := hE_cl a b hvis (hS_sub hb)
      rcases List.mem_append.mp ((hmemρ a).mpr haE) with ha | ha
      · exact ha
      · exfalso
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hfut b hb hvis
        · exact hcross b hb a (List.mem_cons_of_mem _ ha) hvis
    -- the prefix fold IS a causal fold of its own set
    have hσS : CausalFold (Configuration.replayContext C) {x : Op D.AppOp | x ∈ π}
        (applySeq D.toUpdateSig D.init π) :=
      ⟨π, ⟨(List.nodup_append.mp hnd).1, fun _ => Iff.rfl⟩, hpwπ, rfl⟩
    -- honesty supplies the causal-past fold
    obtain ⟨σP, hσP, happ⟩ := hHon e (hE_ev e he_E)
    -- the step, then recurse on the extended prefix
    have hstep := hStep C E {x : Op D.AppOp | x ∈ π} e
      (applySeq D.toUpdateSig D.init π) σP
      hE_ev hE_cl he_E hS_sub he_not_π hS_cl hfut hpast hσS hσP hI happ
    refine ih (π ++ [e]) (by rw [hsplit, List.append_cons]) ?_
    rw [applySeq_append_single]
    exact hstep

/-! ## §3  The pointwise `CausalCanonical` discharge (all-comm + rc-Either)

Any finite enumeration reorders into a vis-linearizing one (peel a
vis-minimal element, exists since `vis` is transitive and irreflexive on a
finite list), and all-comm makes folds permutation-invariant; `rc ≡ Either`
kills the `loOn` rc-arm, so the `loOn`-respect conjunct is free. -/



/-- Folds are permutation-invariant when every pair of ops commutes
(adjacent-swap induction over the `Perm` derivation; `commutes` is exactly
the needed swap equation). -/
theorem applySeq_perm_of_all_comm {D' : UpdateSig}
    (hcomm : ∀ a b : Op D'.AppOp, D'.commutes a b)
    {l₁ l₂ : List (Op D'.AppOp)} (h : l₁.Perm l₂) :
    ∀ s : D'.State, applySeq D' s l₁ = applySeq D' s l₂ := by
  induction h with
  | nil => intro _; rfl
  | cons x _ ih => intro s; exact ih (D'.update s x)
  | swap x y l =>
    intro s
    show applySeq D' (D'.update (D'.update s y) x) l
      = applySeq D' (D'.update (D'.update s x) y) l
    rw [hcomm y x s]
  | trans _ _ ih₁ ih₂ => intro s; exact (ih₁ s).trans (ih₂ s)

/-- **The pointwise `CausalCanonical` discharge** (first species): all-comm +
`rc ≡ Either` upgrade `CanonicalConfig.canonical` to a causal witness. Reorder the
canonical enumeration into a vis-linearization (same fold by all-comm); the
`loOn`-respect conjunct is vacuous (`loOn = ∅`: vis-arm dead by all-comm, rc-arm
dead by `Either`). No reachability induction. -/
theorem causalCanonical_of_all_comm_rc_either
    (hcomm : ∀ a b : Op D.AppOp, D.toUpdateSig.commutes a b)
    (hrc : ∀ a b : Op D.AppOp, D.toUpdateSig.replayOrder a b = RcRes.Either)
    {C : Configuration D} (hG : CanonicalConfig C) :
    CausalCanonical C := by
  intro v s E hv
  obtain ⟨ρ, hperm, _hresp, hfold⟩ := hG.canonical v s E hv
  obtain ⟨ρ', hp, hr⟩ := exists_respecting_perm (R := C.vis)
    (fun hab hbc => hG.vis_trans hab hbc) hG.vis_irrefl ρ
  refine ⟨ρ', ⟨hp.nodup hperm.1,
    fun a => (hp.mem_iff (a := a)).symm.trans (hperm.2 a)⟩, hr, ?_, ?_⟩
  · -- `loOn` has no edges at all under all-comm + rc-Either
    exact hr.imp (fun _ hlo => by
      rcases hlo with ⟨_, hnc⟩ | ⟨_, _, hfs, _⟩
      · rcases hnc with hfs | hfs
        · change D.toUpdateSig.replayOrder _ _ = RcRes.Fst_then_snd at hfs
          rw [hrc] at hfs
          exact RcRes.noConfusion hfs
        · change D.toUpdateSig.replayOrder _ _ = RcRes.Fst_then_snd at hfs
          rw [hrc] at hfs
          exact RcRes.noConfusion hfs
      · change D.toUpdateSig.replayOrder _ _ = RcRes.Fst_then_snd at hfs
        rw [hrc] at hfs
        exact RcRes.noConfusion hfs)
  · exact (applySeq_perm_of_all_comm hcomm hp D.init).symm.trans hfold

/-! ## §4  Sub-enumerations, the registered-store fact, and the honesty
bridge -/

/-- Any subset of an enumerable set is enumerable via `filter` (classical
membership test); the workhorse for restricting a version witness to a
causal past. -/
theorem listPermOf_filter_subset {α : Type} {ρ : List α} {T S : Set α}
    (hperm : listPermOf ρ T) (hsub : S ⊆ T) :
    listPermOf (ρ.filter fun a => decide (a ∈ S)) S := by
  refine ⟨hperm.1.filter _, fun a => ?_⟩
  rw [List.mem_filter]
  constructor
  · rintro ⟨_, hd⟩
    exact of_decide_eq_true hd
  · intro ha
    exact ⟨(hperm.2 a).mpr (hsub ha), decide_eq_true ha⟩

/-- Issuer-local counts are prefix-stable: under `SafetyStepOn`'s prefix
hypotheses, `countP p` agrees between enumerations of `S` and of `past(e)`
for any `p` firing only on events of `e`'s replica. -/
theorem countP_prefix_eq_causal_past {C : Configuration D}
    {E S : Set (Op D.AppOp)} {e : Op D.AppOp}
    (hEev : ∀ a ∈ E, a ∈ C.events)
    (hSsub : S ⊆ E) (heE : e ∈ E) (heS : e ∉ S)
    (hfut : ∀ x ∈ S, ¬ C.vis e x)
    (hpast : ∀ x, C.vis x e → x ∈ S)
    {ρS ρP : List (Op D.AppOp)}
    (hpS : listPermOf ρS S)
    (hpP : listPermOf ρP {e' ∈ C.events | C.vis e' e})
    (p : Op D.AppOp → Bool)
    (hp : ∀ x, p x = true → x.2.1 = e.2.1) :
    ρS.countP p = ρP.countP p := by
  have hperm : (ρS.filter p).Perm (ρP.filter p) := by
    rw [List.perm_ext_iff_of_nodup (hpS.1.filter _) (hpP.1.filter _)]
    intro x
    rw [List.mem_filter, List.mem_filter]
    constructor
    · rintro ⟨hxS, hpx⟩
      refine ⟨?_, hpx⟩
      have hxSset : x ∈ S := (hpS.2 x).mp hxS
      have hx_ev : x ∈ C.events := hEev x (hSsub hxSset)
      have he_ev : e ∈ C.events := hEev e heE
      have hne : x ≠ e := fun h => heS (h ▸ hxSset)
      obtain ⟨r₁, s₁, hL₁, hs₁⟩ := hx_ev
      obtain ⟨r₂, s₂, hL₂, hs₂⟩ := he_ev
      rcases C.vis_total_same_replica hL₁ hs₁ hL₂ hs₂ hne (hp x hpx) with
        hxe | hex
      · exact (hpP.2 x).mpr ⟨⟨r₁, s₁, hL₁, hs₁⟩, hxe⟩
      · exact absurd hex (hfut x hxSset)
    · rintro ⟨hxP, hpx⟩
      obtain ⟨_, hvis⟩ := (hpP.2 x).mp hxP
      exact ⟨(hpS.2 x).mpr (hpast x hvis), hpx⟩
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter,
    hperm.length_eq]

end

end Sal.MRDTs
