import Sal.MRDTs.Instances.AegisSheetMaterialisedUpdate
import Sal.MRDTs.Instances.AegisSheetMaterialisedCertificates

/-!
# From union-model executions to issue-ordered histories

Every version of a certified execution of the union model `D` holds an event
set that some issue-ordered history enumerates: sort the events by timestamp
and pair each with its causal past. The materialised fold of the erased
operations is therefore the canonical state of the version, and on purge-free
versions the materialised observation is the union model's view. This is the
cross-model statement for concurrent executions, made on the union model's own
configurations.
-/

namespace Sal.MRDTs.Instances.AegisSheet.Materialised

open Sal.MRDTs Sal.MRDTs.Foundation
open Classical

/-- Distinct events of a configuration have distinct timestamps. -/
theorem ts_ne_of_events {C : Configuration D} {a b : Event} (ha : a ∈ C.events)
    (hb : b ∈ C.events) (hne : a ≠ b) : a.1 ≠ b.1 := by
  obtain ⟨r, s, hrs, hsa⟩ := ha
  obtain ⟨r', s', hrs', hsb⟩ := hb
  exact C.timestamps_distinct hrs hsa hrs' hsb hne

/-- The causal past of an event of a mint-honest configuration, as a finite
set. -/
noncomputable def pastOf {C : Configuration D} (hmint : MintHonest D applicable C)
    (e : Event) : Finset Event :=
  if he : e ∈ C.events then (Classical.choose (hmint e he)).toFinset else ∅

theorem pastOf_spec {C : Configuration D} (hmint : MintHonest D applicable C) {e : Event}
    (he : e ∈ C.events) :
    (∀ x, x ∈ pastOf hmint e ↔ x ∈ C.events ∧ C.vis x e) ∧ applicable e (pastOf hmint e) := by
  unfold pastOf
  rw [dif_pos he]
  obtain ⟨hperm, _, hg⟩ := Classical.choose_spec (hmint e he)
  refine ⟨fun x => ?_, ?_⟩
  · rw [List.mem_toFinset]
    exact hperm.2 x
  · rw [applySeq_eq_toFinset] at hg
    exact hg

/-- Timestamp order on a causally closed, supported event list of a canonical
mint-honest configuration is an issue order: pair each event with its causal
past. -/
theorem issued_of_sorted {C : Configuration D} (hcan : CanonicalConfig C)
    (hmint : MintHonest D applicable C) {Eset : Set Event}
    (hsupp : ∀ a ∈ Eset, a ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → b ∈ Eset → a ∈ Eset)
    (π : List Event) (hnodup : π.Nodup) (hsorted : π.Pairwise fun a b => a.1 ≤ b.1)
    (hmem : ∀ x, x ∈ π ↔ x ∈ Eset) :
    ∀ τ rest, τ ++ rest = π → Issued (τ.map fun e => (e, pastOf hmint e)) := by
  intro τ
  induction τ using List.reverseRecOn with
  | nil => intro rest _; exact Issued.nil
  | append_singleton τ e ih =>
    intro rest hsplit
    have hsplit' : τ ++ (e :: rest) = π := by rw [← hsplit]; simp
    have ih' := ih (e :: rest) hsplit'
    rw [List.map_append, List.map_singleton]
    have hπτ : ∀ x ∈ τ, x ∈ π := fun x hx => by
      rw [← hsplit']; exact List.mem_append_left _ hx
    have heπ : e ∈ π := by rw [← hsplit']; simp
    have heE : e ∈ C.events := hsupp e ((hmem e).mp heπ)
    have hnd : (τ ++ e :: rest).Nodup := by rw [hsplit']; exact hnodup
    rw [List.nodup_append] at hnd
    have hsort : (τ ++ e :: rest).Pairwise (fun a b => a.1 ≤ b.1) := by
      rw [hsplit']; exact hsorted
    rw [List.pairwise_append] at hsort
    have hτe : ∀ x ∈ τ, x.1 ≤ e.1 := fun x hx => hsort.2.2 x hx e (by simp)
    have hτne : ∀ x ∈ τ, x ≠ e := fun x hx => hnd.2.2 x hx e (by simp)
    have hmapfst : (τ.map fun e => (e, pastOf hmint e)).map Prod.fst = τ := by
      rw [List.map_map]
      exact List.map_id'' (fun _ => rfl) τ
    refine Issued.snoc ih' ?_ ?_ (pastOf_spec hmint heE).2
    · rw [hmapfst]
      intro x hx
      rw [List.mem_toFinset]
      have hx' := ((pastOf_spec hmint heE).1 x).mp hx
      have hxE : x ∈ Eset := hclosed x e hx'.2 ((hmem e).mp heπ)
      have hxπ : x ∈ π := (hmem x).mpr hxE
      rw [← hsplit', List.mem_append, List.mem_cons] at hxπ
      rcases hxπ with hxτ | rfl | hxrest
      · exact hxτ
      · exact absurd hx'.2 (hcan.vis_irrefl _)
      · exfalso
        have hle : e.1 ≤ x.1 := (List.pairwise_cons.mp hsort.2.1).1 x hxrest
        exact absurd (C.causal_mono hx'.2) (not_lt.mpr hle)
    · rw [hmapfst]
      intro ht
      unfold eventTimes at ht
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at ht
      rcases ht with ⟨r, hr, hrt⟩ | ⟨r, hr, hrt⟩
      · rw [List.mem_toFinset] at hr
        exact ts_ne_of_events (hsupp r ((hmem r).mp (hπτ r hr))) heE (hτne r hr) hrt
      · rw [List.mem_toFinset] at hr
        cases hp : purge? r with
        | none => rw [hp] at hrt; simp at hrt
        | some m =>
          rw [hp, Finset.mem_image] at hrt
          obtain ⟨entry, hentry, het⟩ := hrt
          have hrE : r ∈ C.events := hsupp r ((hmem r).mp (hπτ r hr))
          obtain ⟨c, hc, _, _, hct, _⟩ :=
            covered_of_applicable (pastOf_spec hmint hrE).2 (purge?_eq_some.mp hp) hentry
          have hc' := ((pastOf_spec hmint hrE).1 c).mp hc
          have hce : c = e := by
            by_contra hne
            exact ts_ne_of_events hc'.1 heE hne (hct.trans het)
          subst hce
          exact absurd (C.causal_mono hc'.2) (not_lt.mpr (hτe r hr))

theorem exists_sorted (π : List Event) :
    ∃ π' : List Event, π'.Perm π ∧ π'.Pairwise (fun a b => a.1 ≤ b.1) := by
  refine ⟨π.mergeSort (fun a b => decide (a.1 ≤ b.1)), List.mergeSort_perm _ _, ?_⟩
  have := List.pairwise_mergeSort (le := fun a b : Event => decide (a.1 ≤ b.1))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hab hbc)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total a.1 b.1) π
  exact this.imp fun h => by simpa using h

theorem canonicalConfig_of_certified {C : Configuration D}
    (hC : CertifiedExecution D AegisSheet.generation C) : CanonicalConfig C :=
  hC.canonicalConfig (fun C _ => AegisSheet.join C.replayContext)

/-- **Every version of a certified union-model execution is an issue-ordered
history.** -/
theorem issued_of_version {C : Configuration D}
    (hC : CertifiedExecution D AegisSheet.generation C)
    {v : Version} {s : Finset Event} {Eset : Set Event} (hv : C.ver v = some (s, Eset)) :
    ∃ ρ : List (Event × Finset Event), Issued ρ ∧ histEvents ρ = s := by
  have hcan := canonicalConfig_of_certified hC
  have hmint : MintHonest D applicable C := hC.mintHonest
  obtain ⟨π, hperm, _, hfold⟩ := hasReplayWitness_of_canonical hcan v s Eset hv
  rw [applySeq_eq_toFinset] at hfold
  obtain ⟨π', hp, hsorted⟩ := exists_sorted π
  have hnodup : π'.Nodup := hp.nodup_iff.mpr hperm.1
  have hmem : ∀ x, x ∈ π' ↔ x ∈ Eset := fun x => hp.mem_iff.trans (hperm.2 x)
  refine ⟨π'.map fun e => (e, pastOf hmint e),
    issued_of_sorted hcan hmint (hcan.version_events_supported v s Eset hv)
      (hcan.version_events_causal v s Eset hv) π' hnodup hsorted hmem π' [] (by simp), ?_⟩
  rw [← hfold]
  unfold histEvents
  ext x
  simp [hp.mem_iff]

/-- **The cross-model theorem on concurrent executions.** For every version of
a certified execution of the union model, the materialised fold of the erased
operations of an issue-ordered enumeration of its events is the canonical
state of the version; on purge-free versions the materialised observation is
the union model's view. -/
theorem cross_model {C : Configuration D}
    (hC : CertifiedExecution D AegisSheet.generation C)
    {v : Version} {s : Finset Event} {Eset : Set Event} (hv : C.ver v = some (s, Eset)) :
    ∃ ρ : List (Event × Finset Event), Issued ρ ∧ histEvents ρ = s ∧
      applySeq M.toUpdateSig M.init (erase ρ) = canon s ∧
      ((∀ e ∈ s, purge? e = none) →
        M.query (applySeq M.toUpdateSig M.init (erase ρ)) () = D.query s ()) := by
  obtain ⟨ρ, hρ, hs⟩ := issued_of_version hC hv
  refine ⟨ρ, hρ, hs, ?_, ?_⟩
  · rw [hρ.fold, hs]
  · intro hpf
    show mview (applySeq M.toUpdateSig M.init (erase ρ)) = view s
    rw [hρ.fold, hs]
    exact observationEquivalence s hpf

#print axioms issued_of_version
#print axioms cross_model

end Sal.MRDTs.Instances.AegisSheet.Materialised
