# Translation mitigation probe

The common `Exact.merge_comm` definitions-level trial failed with `incorrect number of universe levels DecidableEq`. These probes preserve its full theorem statement and existing premises; no VC theorem is supplied.

| Probe | Outcome |
| --- | --- |
| `ProbeMono.lean` | `+mono` bypasses universe error; normal unable-to-prove failure |
| `ProbeDropInstance.lean` | Instance cannot be cleared: context types depend on it |
| `ProbeGeneric.lean` | Finset membership normalization still hits universe error |
| `ProbeGenericNoHints.lean` | Omitting `[ * ]` does not remove universe error |
| `ProbeGenericMono.lean` | `+mono` fails on dependent `Representation` context |
| `ProbeGenericClear.lean` | Removing irrelevant context still hits universe error without `+mono` |
| `ProbeGenericClearMono.lean` | Checked success; axioms only `propext`, `Quot.sound`, `Classical.choice` |

The successful source unfolds the concrete merge definition, applies `Finset.ext`, introduces an arbitrary element `x`, normalizes membership using `Finset.mem_union`, `Finset.mem_inter`, and `Finset.mem_sdiff`, runs `clear * - x`, then `smt +mono (timeout := some 10) [*]`. These are generic extensionality and propositional normalization steps. `clear` discards irrelevant premises without weakening the theorem. The audit reports no existing VC/algebra helper theorem dependency. Logs sit beside each source.

This is one diagnostic probe, not a campaign measurement. Keep the original failure. If using the mitigation in a common campaign, give every tool the same generic normalization/clearing tier and label the SMT adapter `+mono`; do not silently combine rows from different invocations. The solver's raw tier remains an ordinary failed proof attempt under the monomorphizing adapter.
