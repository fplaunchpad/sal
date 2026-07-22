# Verification distance: from the Lean proofs to the deployed editor

An honest accounting of how far the DEPLOYED rich-text editor
(https://sal-p2p.kc-7c7.workers.dev, `deploy/cloudflare/`) is from the PROVED
artifacts (`Sal/`). Short version: the deployment is a TESTED MIRROR of the
proofs, not a compiled or extracted product of them. The distance differs per
layer; this note records each link, what keeps it honest, and what would
shrink it.

Related: `collab-design-note.md` (architecture + roadmap),
`runtime/README.md` (what each runtime piece mirrors),
`p2p-demo/README.md` (the demo-vs-verified table).

## The chain, layer by layer

| Layer | What runs there | Connection to the proofs |
| --- | --- | --- |
| Lean (`Sal/`) | nothing runs; theorems | The source of truth: the Peritext MRDT (`Sal/MRDTs/Peritext_with_tombstones/`, 0 sorries), the document-order mark read model (`Sal/ConditionedMRDTs/MRDT_Instances/Peritext_Embed/PeritextEmbed_MarkIntent.lean`: the Ex1-8 renderings, `doc_no_backward_leak`, `doc_delete_can_respan`), the tombstone-free RGA embed, convergence up to `≈`, the certified GC cut (`settledAt_of_allHeard`), the order-preserving Elias-delta code |
| Python references (`whiteboard/litmus/`) | test oracles only | Hand-written mirrors of the Lean specs (`peritext_read_model.py`, `marks_gc_check.py`); validated against the Lean statements, unproven themselves |
| JS runtime (`runtime/src/`) | the datatype + merge + GC the editor executes | NO MECHANICAL LINK. The bridge is: fixtures extracted from the Python reference (never from the JS itself), the Ex1-8 pins, twin PBTs against never-compacted controls, mark-permutation convergence, PASS+FAIL SPOT discipline (110 tests) |
| Replica machinery (`runtime/src/replica.js`, `hash.js`, `lca.js`) | DAG, SHA content addressing, delta/ingest, LCA, epochs, `commitBatch` | NO LEAN COUNTERPART AT ALL. Never formalized; tested (content-address gate, batch==fold, wire round-trips) but the theorems say nothing about it |
| Demo glue (`p2p-demo/src/`) | transport, reconnect, manual merge, debounce, op-diffing, codecs | Unverified engineering, 33 headless tests; the debounce's `specRead`/flush equality holds by construction and is pinned by a test |
| Browser + edge (`web/richtext.js`, ProseMirror, Chrome, workerd, the DO relay) | the UI and the wire's host | Entirely outside the verification story; ProseMirror is a large unverified dependency |

The deployed editor is roughly TWO TESTING BRIDGES and ONE UNFORMALIZED LAYER
away from the proofs.

## What keeps that distance honest

- The proved read model is AUTHORITATIVE ON SCREEN. The editor reconciles the
  ProseMirror doc against `read()` after every transaction, so whatever the
  theorems say about mark boundaries and rehoming is what users see, even
  where PM's own mark heuristics disagree. The unverified DOM layer cannot
  silently change document semantics, only fail loudly.
- The relay is OUTSIDE THE TCB by design. It never inspects payloads, and
  `ingest` recomputes every SHA, so a relay (node or Durable Object) can
  drop, delay, or duplicate, but cannot corrupt a commit undetected.
- Fixtures flow ONE WAY. Expected test values come from the reference model
  (or are hand-derived from the documented rules), never from the
  implementation under test, so the JS cannot grade its own homework.

## The genuine gaps, largest first

1. NO EXTRACTION OR REFINEMENT PROOF connects Lean to JS. A transcription bug
   in `runtime/src/datatypes/peritext.js` that the fixture suite happens not
   to exercise would ship. (The comment-encoding tests are hand-derived, not
   reference-extracted: one notch weaker than the Ex1-8 pins.)
2. THE REPLICA/WIRE LAYER IS PARTLY FORMALIZED, ALL OF IT TRANSLITERATED:
   virtual-LCA resolution (#90) and the GC keep set now mirror mechanized
   constructions (`Step3V`/`mca_events_cover`, `keepSetV`), and the
   stability certificate mirrors `settledAt_of_allHeard`; but the
   JS implementations are tested transliterations, not extractions, and
   epoch handling plus content addressing have no Lean counterpart at all.
   The convergence theorem assumes the three-way merges it models are the
   ones actually performed.
3. NO IDENTITY OR AUTHENTICATION: the proofs assume well-formed ops from
   honest replicas; today any connection can author ops under any name
   (design-note sharp edge D). This matters more now that a URL is public.
4. NUMERIC/ENCODING SEAMS: JS numbers and `stableStringify` canonicalization
   vs Lean's mathematical types; tested at the seams, not proved.

## Shrinking the distance (highest value first)

1. Extraction, or a differential-testing harness that replays the Lean SPOT
   suites directly against the JS datatype (mechanize the fixture bridge).
2. Formalize the replica layer's merge selection, at least the LCA-uniqueness
   assumption the deployed merges rely on.
3. Signatures on commits, so the deployed trust model matches the proofs'
   honest-replica assumption.
