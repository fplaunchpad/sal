import LeanProofs_no_spec_non_comm.Implementations.EmbeddedRGA.Coordinates

/-!
# Embedded RGA: the implementation tuple

The Embedded RGA row of Table 1, following Appendix `app:dt-embed-rga`. An
insertion stores its ancestry as a **coordinate** rather than as tree edges.
Descending coordinate order gives depth-first, newest-sibling-first RGA
order; merge combines surviving records and deletion removes the named
identity.

```
  Sigma = List (id, value, coordinate)      coordinate : List Bool
  o = Ins v p a    insert v, anchored at a, carrying the anchor's coordinate
  o = Del x        remove the record with identity x
  c_e = p ++ enc (t - a)      K(c) = b_{1,2}(c) ++ [3]
```

The row **is** the embedded-coordinate core of `Scheme.lean` at the unary
scheme of `Coordinates.lean`, with payload `Nat`. Sided Embedded RGA,
Embedded Peritext and Sided Peritext are the same core at other schemes and
payloads, so none of them repeats a proof.

An insertion takes the event's **timestamp** as its identity, and `rc` is
empty, with the appendix's qualification that the laws hold "for the states
and event prefixes arising in guarded executions". `Negative.lean` shows
what that qualification costs and `Certificate.lean` discharges it.

No proof appears in this file.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- The row's own tuple: the core at the unary scheme, payload `Nat`, with
the appendix's empty `rc`. -/
abbrev De : Impl (type unaryScheme Nat (payloadQuery unaryScheme Nat)) :=
  Dα unaryScheme Nat (payloadQuery unaryScheme Nat)

end LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA
