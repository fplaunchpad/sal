import LeanProofs_no_spec_non_comm.Soundness.SequentialSpec
import LeanProofs_no_spec_non_comm.Metatheory.Adequacy

/-!
# The overall soundness theorem

The adequacy theorem of Section 5: the obligations and the sequential premise
give RA-linearizability of every certified execution. This is the only file
that uses both clauses of Definition 4, so it is the only one that reads both
`Metatheory/Adequacy.lean` and `Soundness/SequentialSpec.lean`.

```
  Laws + VC1..VC5        per implementation, at every context
      |
      v
  the join lemma         Metatheory.joinLemma
      |
      v
  canonical correctness  every stored version holds can(E(v))        clause 1
      |
      +--  + JointAcyclic + AnyOrderSound        -->  clause 2, order built
      +--  + SpecChosenOrderSound                -->  clause 2, order chosen
```

Convergence comes from the left-hand premise, conformance from the right. As
the paper says, the canonical join laws alone do not establish conformance,
which is why the sequential premise is a separate hypothesis everywhere below.

## No SPEC-NON-COMM

Every theorem here reaches specification visibility, and none of them asks
for SPEC-NON-COMM. That law says every conflict the specification sees is a
conflict the implementation sees, so a history respecting `lo^C_E` respects
specification visibility for free.

There is a second way, and it needs no law at all. Every
specification-visibility arrow runs along `vis`:

```
  specVisibility S C a b  =  C.vis a b ∧ ¬ S.Commutes a.op b.op
```

So a history that respects `vis` respects all of them, whatever the
specification thinks conflicts. The price is that the row must produce a
history respecting `vis` **and** `lo^C_E` at once, which needs the two
relations to have no cycle between them. That is `JointAcyclic`, and it is
what a row pays here in place of the fourth law.

Weaker hypotheses mean the Definition 4 theorems of the main tree have no
counterpart here. A row states the criterion with specification visibility
and takes Definition 4 from `certifiedRA_of_spec`.
-/

namespace LeanProofs.NoSpecNonComm.Soundness

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {type : MRDTType} {D : Impl type}

/-! ## The criterion

Every row reaches Definition 4 through `Obligations` and nothing else. The
contract underneath is the framework's **guarded** one, so `rc` is consulted
only about pairs carrying distinct timestamps and issued by different
replicas, which is exactly the domain the paper's RC-NON-COMM speaks about.

`ObligationsOn` keeps a `Good` parameter although almost every row
instantiates it at `fun _ => True`. The generality is what a row whose
conditions hold only at the contexts an execution produces would use; the
optional register is that row, and
`Implementations/OptionalRegister/Negative.lean` says why it needs one.
-/

/-- Definition 4 strengthened with specification visibility, at every
certified execution. -/
abbrev SpecCertifiedRA (D : Impl type) (S : Spec type) (I : Issuance D.toMRDTSig) :
    Prop :=
  ∀ C : Configuration D.toMRDTSig,
    MintCertifiedReachV D.toMRDTSig (canonicalVirtualMergeBase D.toMRDTSig) I C →
    SpecificationRALinearizable D.toMRDTSig (policy D) S C

/-- Definition 4 itself follows, so a row proving the fourth law need not
prove the criterion twice. -/
theorem certifiedRA_of_spec {S : Spec type} {I : Issuance D.toMRDTSig}
    (h : SpecCertifiedRA D S I) : CertifiedRA D S I :=
  fun C reach => (h C reach).active

/-- **The execution-scoped premise, carrying specification visibility.**
A row is handed a real configuration and picks the history itself. Beyond
enumerating the event set and respecting `lo^C_E`, the history must also
respect the conflicts the specification sees. -/
abbrev SpecChosenOrderSound (D : Impl type) (S : Spec type)
    (I : Issuance D.toMRDTSig) : Prop :=
  ∀ C : Configuration D.toMRDTSig, MintHonest D.toMRDTSig I.CanIssue C →
    VisStrict D C.replayContext →
    ∀ E : Set D.Event, (∀ e ∈ E, e ∈ C.events) →
      (∀ a b, C.vis a b → b ∈ E → a ∈ E) → (∃ π, listPermOf π E) →
      ∀ q, ∃ π : List D.Event,
        listPermOf π E ∧
        respects π (paperOrder (Interface.policy D) C.replayContext E) ∧
        respects π (specVisibility S C.replayContext) ∧
        S.admits (projectedUpdates (D := D.toMRDTSig) π ++
          [.query q (D.query (D.applyList D.sigma0 π) q)])

/-- **The adequacy theorem for that premise.** Clause 1 comes from the join
lemma, clause 2 from the history the row chooses, and canonical uniqueness
identifies the two.

The join lemma is taken as a hypothesis rather than derived, because a row
may reach it by either route: `Metatheory.joinLemma` from the five
conditions of Section 5, or `Metatheory.causalJoinLemma` from the five
conditions at the full causal past. Both produce this same `PaperJoinOn`,
which is why the two routes need only one soundness theorem between them.
The bounded counter is the row that takes the second. -/
theorem certifiedSpecRA_scoped_strict {Good : Ctx D → Prop} {S : Spec type}
    {I : Issuance D.toMRDTSig}
    (hl : Laws D) (hself : EqualOpCommutes D) (hsame : SameReplicaCondComm D)
    (X : ExecutionOrder D) (join : PaperJoinOn D Good)
    (good : ∀ C : Configuration D.toMRDTSig,
      MintHonest D.toMRDTSig I.CanIssue C → Good C.replayContext)
    (history : SpecChosenOrderSound D S I) :
    SpecCertifiedRA D S I := by
  have hlg := guardedLaws hl hself hsame
  have jr := Metatheory.representationJoin_of_paperJoin join
  intro C reach r v s E _ hv q
  letI : EventOrder D.toMRDTSig.toUpdateSig := X.order
  have cfg := Metatheory.paperCanonicalConfig X jr good reach
  have hsup := cfg.version_events_supported v s E hv
  have hcan := Metatheory.paperCanonicalVersions X jr good reach v s E hv
  obtain ⟨ρ, hρ, -, -⟩ := id hcan
  obtain ⟨π, hp, hr, hspec, hadm⟩ := history C reach.mintHonest
    ⟨fun hab hbc => cfg.vis_trans hab hbc, cfg.vis_irrefl⟩ E hsup
    (cfg.version_events_causal v s E hv) ⟨ρ, hρ⟩ q
  have heq : D.applyList D.sigma0 π = s :=
    ConcreteMRDT.canonical_unique hlg C.replayContext E hsup ⟨π, hp, hr, rfl⟩ hcan
  exact ⟨π, hp, hr, hspec, by simpa only [heq] using hadm⟩

/-- **The adequacy theorem at a bundle.** `certifiedSpecRA_scoped_strict`
with the five conditions taken from an `ObligationsOn` record instead of one
at a time, which is how every row but the bounded counter supplies them.
The bounded counter cannot use it, because its join comes from
`Metatheory.causalJoinLemma` at the full causal past rather than from
`joinLemma` at the paper's dependency set. That row calls
`certifiedSpecRA_scoped_strict` directly, which is the whole reason the join
is a hypothesis there. -/
theorem certifiedSpecRA_scoped_on {Good : Ctx D → Prop} (h : ObligationsOn D Good)
    {S : Spec type} {I : Issuance D.toMRDTSig}
    (good : ∀ C : Configuration D.toMRDTSig,
      MintHonest D.toMRDTSig I.CanIssue C → Good C.replayContext)
    (history : SpecChosenOrderSound D S I) :
    SpecCertifiedRA D S I :=
  certifiedSpecRA_scoped_strict h.laws h.equal_op_commutes h.same_rep_cond_comm
    h.executionOrder.some (Metatheory.joinLemma h) good history

/-! ## The route every ported row takes

A row reaches the criterion here by supplying **one relation with no loop**.
`joint` is specification visibility together with `lo^C_E`, so a history
respecting it satisfies both order clauses of Definition 4 at once, and
`JointAcyclic` is the single fact a row has to prove about it. The
sequential premise stays `AnyOrderSound`, the unrestricted one, which is
also what the main tree's `Soundness.certifiedSpecRA` consumes.

What a row does **not** supply is SPEC-NON-COMM. The main tree needs that
law to know the canonical witness respects specification visibility; here
the witness is picked out of `joint` instead, which carries the requirement
in its left disjunct.

Why a loop has to be ruled out at all: `lo^C_E` may carry same-time arrows
between concurrent events, and such an arrow is free to point backwards in
time, so the chronological order together with one of them is already a
loop. A row whose events all commute has no same-time arrows and proves
`JointAcyclic` in three lines; a row with a non-empty `rc` has to look at
what its `rc` relates. -/

/-- **Both kinds of arrow at once.** Specification visibility and `lo^C_E`,
inside `E`. -/
def joint (D : Impl type) (S : Spec type) (C : Ctx D) (E : Set D.Event)
    (a b : D.Event) : Prop :=
  a ∈ E ∧ b ∈ E ∧ (specVisibility S C a b ∨ paperOrder (Interface.policy D) C E a b)

/-- **What a row supplies in place of a chosen-order premise.** -/
abbrev JointAcyclic (D : Impl type) (S : Spec type) : Prop :=
  ∀ (C : Configuration D.toMRDTSig) (E : Set D.Event),
    VisStrict D C.replayContext →
    ∀ a : D.Event, ¬ Relation.TransGen (joint D S C.replayContext E) a a

/-- **The adequacy theorem.** The bundle with SPEC-NON-COMM dropped, the one
fact about `joint`, and the unrestricted sequential premise. This is what
every row on the specification route calls, and it is all they pass. -/
theorem certifiedSpecRA_any (h : Obligations D) {S : Spec type}
    {I : Issuance D.toMRDTSig} (acyclic : JointAcyclic D S)
    (sound : AnyOrderSound D S) : SpecCertifiedRA D S I := by
  classical
  refine certifiedSpecRA_scoped_on h (fun _ _ => trivial) ?_
  intro C _ hvs E hsup hcl hfin q
  obtain ⟨π₀, hp₀⟩ := hfin
  obtain ⟨ρ, hperm, hrt⟩ := exists_respecting_perm
    (R := Relation.TransGen (joint D S C.replayContext E))
    (fun hab hbc => hab.trans hbc) (acyclic C E hvs) π₀
  have hρ : listPermOf ρ E :=
    ⟨hperm.nodup hp₀.1, fun a => (hperm.mem_iff (a := a)).symm.trans (hp₀.2 a)⟩
  have hrj : respects ρ (joint D S C.replayContext E) :=
    hrt.imp (fun {_ _} hno hedge => hno (Relation.TransGen.single hedge))
  exact ⟨ρ, hρ,
    hrj.imp_of_mem (fun {a b} ha hb hno hp =>
      hno ⟨(hρ.2 b).mp hb, (hρ.2 a).mp ha, Or.inr hp⟩),
    hrj.imp_of_mem (fun {a b} ha hb hno hs =>
      hno ⟨(hρ.2 b).mp hb, (hρ.2 a).mp ha, Or.inl hs⟩),
    sound ρ q⟩

/-! ## One lemma the ported rows share

Several rows choose a **chronological** history. For those the new clause is
free: `causal_mono` says visibility increases the timestamp, so a history
sorted by timestamp inverts no `vis` arrow at all, and therefore inverts no
specification-visibility arrow either, whatever the specification thinks
conflicts. -/

/-- **A chronological history respects specification visibility.** The only
fact used is `causal_mono`, which every `Configuration` carries. -/
theorem respects_specVisibility_of_time_sorted {S : Spec type}
    {C : Configuration D.toMRDTSig} {π : List D.Event}
    (h : π.Pairwise (fun a b => a.time ≤ b.time)) :
    respects π (specVisibility S C.replayContext) :=
  h.imp (fun {_ _} hab hvis => absurd (C.causal_mono hvis.1) (Nat.not_lt.mpr hab))

/-- **A two-step run, unpacked.** Specification commutation is a diamond on
two labels, and `commutes_of_diamond` wants it stated that way. -/
theorem runs_pair {State Label : Type} {step : State → Label → State → Prop}
    {s t : State} {l₁ l₂ : Label} :
    Runs step s [l₁, l₂] t ↔ ∃ m, step s l₁ m ∧ step m l₂ t := by
  constructor
  · intro h
    cases h with
    | cons h1 r1 => cases r1 with
      | cons h2 r2 => cases r2; exact ⟨_, h1, h2⟩
  · rintro ⟨m, h1, h2⟩
    exact Runs.cons h1 (Runs.cons h2 (Runs.nil _))

end LeanProofs.NoSpecNonComm.Soundness
