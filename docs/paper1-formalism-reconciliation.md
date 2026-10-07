# Changes needed in the Sal paper

Compared the freshly pulled paper **`2095552`** with Lean **`paper1` at
`07fe525`** on 7 October 2026. The Lean metatheory is complete for its stated
assumptions, including issuance-certified executions and recursive virtual
merges. The manuscript needs the following changes to match it.

1. **State the event guards (`ralin.tex`, replay laws).** Keep user-supplied
   `rc` on operation payloads and lift it to events. State noncommutation
   exactness for distinct timestamps and different replicas; state conditional
   commutation with its timestamp-distinctness guards and actual noncommuting
   absorber. **Why:** the current unguarded operation-level laws exclude valid
   implementations, including efficient OR-set.

2. **Include the certified, invariant-scoped theorem (`ralin.tex`,
   `proof_strategy.tex`).** Quantify over eligible issued events and represented
   states. Define implementation commutation on an independently justified
   invariant, using that same domain in both clauses of the linearization order;
   prove preservation. **Why:** arbitrary raw states produce spurious conflicts
   for Embedded RGA. Original issuance must not be rechecked on reordered replay
   states.

3. **Add specification-conflict visibility (`ralin.tex`, RA definition;
   `seq_spec.tex`, broken set).** Require the same witness to preserve visibility
   between updates that do not commute in the independent history language,
   including future contexts. **Why:** the current definition admits the broken
   no-op-remove set through `[remove, add]`. The example currently refutes the
   sequential-simulation premise, not RA-linearizability as written.

4. **Allow datatype-specific event labels (`ralin.tex`, operation projection).**
   Replace mandatory timestamp/replica erasure with an explicit label mapping.
   OR-set can discard these inputs; identified RGA and anchored Queue retain
   their original IDs. **Why:** allocating fresh replacement IDs in the
   specification can change ordering and which element an operation names.

5. **Extend the specification bridge (`seq_spec.tex`, lifting theorem).** Keep
   total sequential simulation as one sufficient method. Add the certified
   method: construct one independently legal history that respects both orders
   and explains the stored query. **Why:** Queue/RGA use issuance evidence and
   cannot establish the current premise over every arbitrary event list. The
   strengthened RA definition also needs specification visibility proved here.

6. **Expose metadata premises in the merge proof (`proof_strategy.tex`,
   VC1–VC5 and induction).** State history-indexed representation, metadata
   dependency closure, and the reconstruction premises used when removing a
   maximal event. **Why:** commuting predecessors can still supply tags or
   anchors needed by merge. Noncommutation closure and canonicality alone do
   not capture these premises. A dependency-past replay is not necessarily the
   full state seen by the original issuer.

7. **Align the execution model (`opsem.tex`).** State fresh-version snapshot
   forks, timestamps increasing along visibility, and the issuance discipline.
   Use a greatest common ancestor for the ordinary merge rule; describe
   recursive virtual bases for multiple incomparable bases. **Why:** these are
   the semantics and hypotheses covered by the Lean execution theorems; an
   arbitrary chosen common ancestor does not guarantee event-set intersection.

**Equality decision:** keep concrete state equality; semantic `abs` is unnecessary
for the proved positive results. Keep the specification-refinement function
`α` in `seq_spec.tex`: it serves a different purpose. There is no need to add
an alternative direct-Join proof route to the paper.
