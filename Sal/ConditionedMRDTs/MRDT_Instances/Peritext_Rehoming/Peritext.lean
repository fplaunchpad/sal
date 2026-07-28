import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RA_Lin

/-!
# Peritext (FUSED, tombstone-free) — the instance

Rich text as **one** tombstone-free RGA over a payload that carries both characters
and formatting boundaries, instead of a *product* of an RGA (characters) and a
separate mark store (`Peritext_Composed/`).  This is the tombstone-free/live corner of the
mark-positioning trilemma: formatting marks are **id-paired boundary nodes IN the
sequence**, live-rehomed exactly like character nodes, so a mark endpoint tracks the
current document position rather than a frozen snapshot of tree-ancestry.

## The payload

`PeritextElt` is opaque to the RGA (which only needs `DecidableEq` + `Inhabited`):

* `char c`   — a character, codepoint `c`;
* `bound markId mark isStart` — a formatting boundary.  A mark instance is a
  *pair* of boundary nodes sharing a fresh `markId`: `isStart := true` opens the
  span, `isStart := false` closes it.

The MRDT operations are **exactly** RGACore's `Ins`/`Del` at `α := PeritextElt`:

* typing a character `c` after anchor `a` is `Ins (char c) pre a`;
* "bold this range" is two `Ins` of `bound markId .bold true/false` with a fresh
  `markId` — the start anchored where the span begins, the end where it ends;
* removing a mark is `Del` of its two boundary nodes.

Add-wins for marks is *inherited*: it is the RGA's OR-set node survival, not a
bespoke rule.  Gravity / expansion (Litt et al. Ex 7–8) is a **read-layer** policy
`Mark → Gravity` (see `Peritext_Read.lean`), never stored.

## What is inherited (this file)

Because the element is opaque, **nothing** about convergence is re-proved here.
`peritext_ra_linearizable_up_to_eq` is a one-line instantiation of the RGA
capstone `rga_ra_linearizable3_eq` at `α := PeritextElt`.  Per-version
RA-linearizability up to the observational equivalence `≈`, and hence convergence,
transport verbatim.

## The ONE honesty contract (the trilemma payoff)

The whole datatype — characters *and* mark boundaries — runs under the SINGLE RGA
contract `HonestDelivery (α := PeritextElt)` (born accuracy + born-applicable
delivery).  The product design `Peritext_Composed/` needed **two** contracts: the RGA's
honest delivery for characters *and* a separate `MarkAccurate` discipline for the
mark store's frozen recorded paths.  Here a boundary insert is just an RGA `Ins`, so
it is covered by the same clause as a character insert — one contract, uniformly.
-/

namespace Sal.ConditionedMRDTs.Peritext

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
open Sal.ConditionedMRDTs.RGASkeleton3 (HonestDelivery)

/-! ## §1  The payload types -/

/-- Formatting marks.  Opaque to the RGA; only `DecidableEq` is required (the
`String`/`ℕ` payloads all have it). -/
inductive Mark
  | bold
  | italic
  | underline
  | strike
  | link (url : String)
  | comment (author : ℕ) (text : String)
  | color (rgb : ℕ)
  | heading (level : ℕ)
  deriving DecidableEq

/-- A rich-text element: a character codepoint, or a formatting boundary node
carrying its mark-instance id, the mark, and whether it opens (`true`) or closes
(`false`) the span.  `deriving Inhabited` picks `char 0` as the empty-slot default
the RGA's `init_st` needs. -/
inductive PeritextElt
  | char (codepoint : ℕ)
  | bound (markId : ℕ) (mark : Mark) (isStart : Bool)
  deriving DecidableEq, Inhabited

/-! ## §2  The instantiated signature

`PeritextElt` is a legal RGA payload, so the entire conditioned RGA signature
instantiates at it with no new proof obligations.  `PFSig` is the `≈`-quotient
ternary signature the capstone is stated over. -/

/-- The Peritext-fused conditioned signature: the RGA's hosting `ConditionedMRDTSig`
at `α := PeritextElt` (`Inv := wf ∧ root-free ∧ id_mono`,
`applicable := accurate ∧ fresh_ts`). -/
noncomputable abbrev PeritextSig : ConditionedMRDTSig := RGACondSig' PeritextElt

/-- The `≈`-quotient ternary signature the RA-linearizability capstone lives over. -/
noncomputable abbrev PFSig :=
  QSig (rgaEqEquiv' PeritextElt) (WfOpA (α := PeritextElt)) (rgaInvPresA (α := PeritextElt))
    (rgaCongVC' PeritextElt) (rgaInvInvVCA (α := PeritextElt))

/-! ## §3  The capstone — pure instantiation, nothing re-proved -/

/-- **The fused tombstone-free Peritext is RA-linearizable up to `≈`** at every
reachable configuration of the ternary execution model, under the single honest
delivery contract `HonestDelivery (α := PeritextElt)`.

This is `rga_ra_linearizable3_eq` at `α := PeritextElt`, verbatim.
Convergence and per-version RA-linearizability-up-to-`≈` are therefore *inherited* —
the payload is opaque to the RGA, so specialising the element type from `ℕ`
(characters only) to `char ⊕ boundary` (characters + marks) costs no new
convergence proof.  The observable reading guarantee is the separate read layer
(`Peritext_Read.lean`). -/
theorem peritext_ra_linearizable_up_to_eq
    (hHD : HonestDelivery (α := PeritextElt))
    (C : Configuration PFSig)
    (hReach : (labeledTS3 PFSig).ReachableFrom (initConfig PFSig trivial) C) :
    IsRALinearizable3Eq (rgaEqEquiv' PeritextElt) (WfOpA (α := PeritextElt))
      (rgaInvPresA (α := PeritextElt)) (rgaCongVC' PeritextElt) (rgaInvInvVCA (α := PeritextElt)) C :=
  rga_ra_linearizable3_eq (α := PeritextElt) hHD C hReach

/-! ## §4  Axiom audit -/

#print axioms peritext_ra_linearizable_up_to_eq

end Sal.ConditionedMRDTs.Peritext
