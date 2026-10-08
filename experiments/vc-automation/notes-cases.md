# VC extraction and premise audit

The 15 goals are the five fields of `ConcreteMRDT.Raw.MergeVCs` specialized to the exact OR-set (`ORSet.GuardedRawVC.mergeVCs`), efficient OR-set (`EfficientORSet.GuardedRawVC.mergeVCs`), and embedded RGA (`CertifiedRGAVC.Embedded.mergeVCs Γ`) parameters. `Cases.lean` copies every quantifier and hypothesis, including representation reconstruction and smaller-union evidence. It uses no existing bundle value. Its five ephemeral `#check` casts kernel-check that each generic copied proposition is definitionally identical to the actual field type. The specialization parameters were read directly from the production bundle declarations.

Goal identifiers are `VCAutomation.{Exact,Efficient,Embedded}.{merge_comm,init,causal_delta,local_redistribute,shared}`. Embedded goals additionally take `Γ : Sal.EmbedRGA.OrderedPrefixCode`. Unfold the specialization followed by `VCAutomation.<field>_goal` to expose the original proposition. Keep α abstract; specializing α to a finite singleton would change the benchmark.

`premises.json` gives an explicit, conservative whitelist. Generic tier supplies collection membership/extensionality; helper tier additionally supplies membership, provenance, freshness and sorted-list conversion facts. `merge_toFinset` and `merge_sorted` are substantial datatype helpers: they expose the merge implementation's set meaning and canonical list order. They do not assert a VC equation, but a successful helper-tier RGA result must disclose dependence on these facts. `killed_covered` and `common_record` supply representation-derived coverage, also substantial evidence rather than mere normalization.

Leakage exclusions: exact/efficient `causal_replay_eq`, `local_replay_eq`, `shared_replay_eq`, efficient `merge_update_eq`, `GuardedEqualityVC.causal_add_eq/local_add_eq`, and RGA `finite_causal` package the target equation or its algebraic core. `SetMergeAlgebra.local_redistribute` is polymorphic, but is still essentially the local VC algebra; it is excluded even from the generic tier. No Join/representationJoin fact or bundle projection is an allowed hint. Replay imports necessarily expose other theorem declarations transitively; imported availability is not authorization. A controlled tactic must use only local hypotheses plus the stated explicit whitelist, and audit proof dependencies for forbidden categories. Unrestricted simp/grind/aesop global databases cannot establish a clean tier result.

Validation: `lake env lean experiments/vc-automation/Cases.lean` exits 0. The unused-policy warnings on commutativity/init arise because those genuine field propositions do not use semantic policy.

## Validated solver preprocessing recipes

The following probes retain the complete fixed obligation and abstract α. All three compiled with `lake env lean` and ended in `grind only`; no final VC equation or Join theorem was supplied. The OR-set recipes are retained in `NativeProofs.lean`; the manually structured RGA control is retained in `StructuredRGAControl.lean`. These are normalization-assisted controls, not evidence that an opaque `grind only` call discovers extensionality or the representation abstraction on its own. The runner must record preprocessing alongside the backend result.

### Generic tier: both OR-set shared VCs

After unfolding the named specialization and `shared_goal`, use this recipe (replace `NS` by `Sal.MRDTs.Paper1.ORSet` or `Sal.MRDTs.Instances.EfficientORSet`):

```lean
intros
dsimp only [NS.D]
apply Finset.ext
intro p
simp only [NS.merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
grind only
```

`dsimp only [NS.D]` is essential: changing just the outer equation to the concrete merge leaves inner `(D α).merge` projections opaque to `simp only [merge]`. This recipe does not unfold update or use representation hypotheses: the shared equation is a universal Boolean identity on membership in the five input sets. The same extensional normalization is a useful generic tier adapter for commutativity and init; causal/local equations need actual coverage and freshness reasoning.

### Helper tier: Embedded RGA commutativity

After unfolding the named specialization and `merge_comm_goal`, retain the following datatype facts. Set `A := Sal.MRDTs.Paper1.CertifiedRGAVCAlgebra.Embedded`, open `Sal.MRDTs.Paper1`, `Sal.MRDTs.Instances.EmbedRGA`, and `CertifiedRGAVCReplay.Embedded`, and import `CertifiedRGAVCAlgebra`.

```lean
intro C E₁ E₂ l a b _ _ _ _ hl ha hb
simp only [E] at *
have hsortedab := A.merge_sorted Γ C _ _ l a b ha hb
have hsortedba := A.merge_sorted Γ C _ _ l b a hb ha
have hab := A.merge_toFinset Γ C _ _ _ l a b hl ha hb
have hba := A.merge_toFinset Γ C _ _ _ l b a hl hb ha
have heq := @A.eq_of_toFinset α _ _
have : (eMerge l a b).toFinset = (eMerge l b a).toFinset := by
  rw [hab, hba]
  apply Finset.ext
  intro p
  simp only [SetMergeAlgebra.merge, Finset.mem_union,
    Finset.mem_inter, Finset.mem_sdiff]
  grind only
grind only
```

Lean accepts the generic `heq` function as a local quantified premise: the final `grind only` instantiates it using sortedness and the automatically solved set equality. No direct `apply eq_of_toFinset` is needed. However, the intermediate toFinset equality and selection/instantiation of the four abstraction facts are explicit structural preprocessing, so report this as a helper-assisted solver result. The original represented-state premises remain intact. `merge_toFinset` and `merge_sorted` account for the datatype-specific mathematics; the backend handles generic set commutativity and sorted-list injectivity.

### Monomorphic helper injection

Bare `@helper` quantifies over types and `DecidableEq`/`Inhabited` structures. In these trials, some such hints triggered Lean-auto reification errors. Specialization removes this confound but does not guarantee successful translation. Fix the current datatype and instances while leaving state/event/context arguments quantified:

- Exact OR-set (both listed helpers): `have h := @name α inferInstance`.
- Efficient OR-set (both listed helpers): `have h := @name α inferInstance`.
- Embedded RGA: `have h := @name α inferInstance inferInstance Γ` for all listed helpers except `merge_membership` and `eq_of_toFinset`.
- Embedded `merge_membership` and `eq_of_toFinset`: `have h := @name α inferInstance inferInstance`; these facts have no Γ parameter.

All family-specific complete lists compiled successfully in `/private/tmp/vc-param-hints-{Exact,Efficient,Embedded}.lean`. A plain `name (α := α)` is insufficient for helpers with implicit non-instance arguments: exact `mem_run_iff_live` tries to synthesize unknown C/E/ops, while embedded `merge_membership` and `eq_of_toFinset` try to synthesize unknown states. The partially applied `@` syntax retains those arguments as quantifiers without retaining typeclass quantifiers. Embedded helpers that mention a prefix code are fixed to the current Γ, rather than universally quantifying over unrelated codes.

The manifest now stores exact validated partial applications under `tiers.helpers.helper_application`, keyed by full helper name. This replaces universal type/class injection with specialization to the current α, its instances, and current Γ where present; the initial opaque/helper campaign should remain separately recorded. All 19 application expressions were validated together by family.

## Residual reasoning map

Generic membership normalization solves the Boolean algebra but does not establish the connections between represented histories and live records. The remaining research question is whether automation can derive a small, sufficient set of pointwise freshness/coverage facts from the supplied representations, then discharge the normalized algebra without receiving the equation itself.

| Obligation | Facts beyond collection logic | Production route |
|---|---|---|
| Exact causal delta | A newly added `(x,t)` is absent from causal-past B; every live x-record removed from remainder s occurs in B. | `ConcreteORSetAlgebra.lean` converts replay representation to live-membership witnesses. Add freshness uses supported events and `C.ts_unique`; remove coverage uses semantic maximality to put the birth before the removal, then metadata-past inclusion and preservation of liveness. The remaining equation is propositional membership logic. |
| Efficient causal delta | Every record born at e is absent from B; every live remainder record killed by e is in B. Unlike exact OR-set, an add may kill an older same-replica/same-value record too. | `GuardedRawORSetVC.lean` uses represented membership directly. `live_killed_before_raw` obtains visibility using same-replica totality for add and semantic-order maximality for remove; noncommutation gives a metadata dependency. Closure places the birth in Past; dead-predicate monotonicity preserves liveness. `merge_update_eq` packages the final Boolean algebra, so is excluded as a benchmark hint. |
| Exact local redistribution | A record in past B and other branch b must occur in represented intersection l; a genuinely new update record cannot already occur in l. | Closure gives Past(e) ⊆ E₁. Fixed-birth live-membership plus timestamp uniqueness identifies the same add across histories. Other-branch liveness implies intersection liveness. For new adds, uniqueness identifies the birth as e, contradicting e ∉ E₂; remove creates no new record. Production calls the excluded polymorphic `SetMergeAlgebra.local_redistribute` after deriving these pointwise facts. |
| Efficient local redistribution | The same common-record coverage and new-record/base exclusion. | Direct birth/dead representation avoids replay extraction. Past inclusion and monotonicity of dead establish coverage. Add freshness and absence from E₂ establish exclusion; remove only filters. The production raw bundle splits add/remove, using `GuardedEqualityVC.local_add_eq` or generic redistribution; both final-equation hints are excluded. |

For Embedded RGA all five equations first require a bridge from list semantics to finite sets and back: represented states have sorted keys; honest immutable records imply compatibility; `merge_toFinset` identifies the list merge with the finite-set merge; `merge_sorted` preserves canonical order; `eq_of_toFinset` turns finite-set equality into actual list equality. The per-field additional inputs are:

- **Commutativity:** sortedness of both merge orders and the two merge-toFinset identities; Boolean commutativity remains.
- **Init:** the represented empty state and sortedness of the input/empty merge; empty-set identity remains.
- **Causal delta:** sortedness of merge and updated remainder; `update_toFinset`, `recordStep_mem`, `fresh_born`, and `killed_covered`; production then uses excluded `finite_causal` for the Boolean core.
- **Local redistribution:** sortedness of the two nested merge results and four merge-toFinset identities; `common_record`, update membership, and fresh birth outside the intersection; production then uses excluded generic redistribution.
- **Shared:** sortedness of both nested merge results and conversion of each inner/outer merge; a universal finite-set Boolean identity remains.

These premises are already supplied representation invariants: the RGA representation explicitly includes honest issuance, visibility transitivity/irreflexivity, event support, and an ordered replay witness; efficient OR-set representation includes live/dead membership evidence and replay validity. This benchmark asks solvers to exploit that evidence. It does **not** test discovery of an adequate representation invariant, honesty contract, or sortedness abstraction. Helper-assisted success must say which representation-to-membership facts were supplied, rather than crediting the solver with discovering them.

### Relation to Neem's induction VCs

The local reference `_references/Neem/appendix.tex` describes nested induction over the ancestor/local event partitions for BottomUp-0/1/2-OP: separate base/induction rules extend one event partition at a time, and induction hypotheses become preconditions of these smaller VCs (notably the discussion around lines 471–523 and 569–707). Its local implementation reference is `_references/neem_fstar_repo`. Our five direct represented VCs instead quantify over complete indexed state/history evidence, including reconstructed sides and a represented smaller union. `ConcreteJoin.lean` performs the finite-history induction once to derive Join from these equations.

Consequently the current 15-goal experiment is not a like-for-like replication of Neem's generated small induction-VC automation. A raw solver failure may reflect the cost of extracting consequences from whole representations or transporting list invariants, whereas Neem moves part of this structure into generation and IH-shaped premises. A meaningful next experiment would generate pointwise freshness/coverage/provenance subgoals from each fixed represented VC, verify those subgoals independently, and let every backend solve the same normalized Boolean residual. Report whole-goal and residual-stage results separately, and retain the cost of the generator/representation lemmas; otherwise the apparent automation gain simply relocates the proof burden.
