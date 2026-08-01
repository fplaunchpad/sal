# Legacy `sorry` audit

The source tree contains six proof placeholders in two declarations. None
is in the production `VerifiedMRDT` certificates or their cited theorem chains.

| Declaration | Placeholders | Status |
|---|---:|---|
| `Merge_Linearization.distinct_last_case` | 4 | Part of the original global-`lo` induction. Its missing commuting-tail cases require a false forward-closure/convergence route. |
| `Merge_Linearization.merge_linearization_exists` | 2 | Attempts to manufacture forward closure for replica event sets; the file itself documents that step as unavailable. |

## Corrected routes

`Merge_Linearization_Set.lean` replaces the unstable global order with
set-relative `loOn`. Its `merge_linearization_of_join` reduces merge correctness
to an explicit `JoinLemma`; concrete conditioned instances discharge their own
join kits. Although this module imports the legacy file for shared definitions,
the corrected results' `#print axioms` audits do not contain `sorryAx`.

For Shesha, `shesha_rows_residue`, `shesha_join_at_effC`, and
`shesha_ra_linearizable3` have been retired. `Shesha_Cond.lean` now exports the
checked negative results instead, and the source tree contains no Shesha
`sorry`.

## Reproduce

```sh
grep -R -n -E '^[[:space:]]*sorry([[:space:]]|$)' Sal --include='*.lean'
lake build Sal.ConditionedMRDTs.Metatheory.ProductionCertificateLedger
```

The build should report `sorryAx` only for declarations that consume the two
legacy global-`lo` items above; `embedVerifiedRuntime`, its multi-epoch theorem,
`embedQueueVerified`, and the other production certificates remain kernel-clean
apart from the standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
