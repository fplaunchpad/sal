import Sal.ConditionedMRDTs.MRDT_Instances.PeritextTF.Supplies
import Sal.ConditionedMRDTs.MRDT_Instances.PeritextTF.Render

/-!
# Tombstone-free Peritext, BY COMPOSITION — `PeritextTF := RGA_TF ⊗ MarkStore`

The payoff instantiation of the composition arc (memo
`Development/COMPOSITION_PENPAPER.md` §4): rich text as the binary product of

* **the genuine tombstone-free, path-carrying RGA** (`RGA_TombstoneFree/` —
  conditioned, quotiented by observational `≈`; its 40-file chain is REUSED
  as a certificate bundle, not re-proved), and
* **a mark store** (`MarkStore.lean` — an `ORSetCore` payload instantiation:
  mark records with recorded endpoint ids+paths, rem-by-markId, add-wins),

through the product `≈`-lift kit at the pragmatic cut
(`Metatheory/ProductEq.lean`, `≈₂ = Eq`). Distinguish this from the flat
production mirror `MRDT_Instances/Peritext/` (grow-only + tombstones,
all-comm): here the character component genuinely deletes, so its commutation
holds only conditioned on accurate states and only up to `≈` — the composite
inherits the full conditioned treatment.

**The capstone** (`peritextTF_ra_linearizable_up_to_eq`): every version of
every reachable configuration of the composite's quotient ternary LTS is
RA-linearizable up to `≈₁ × Eq` — its class is `qmk` of a representative that
is the RAW product fold of a `lo`-respecting linearization of its events,
with the character component correct up to the RGA's observational
equivalence and the mark component literally. The single behavioural premise
is `PeritextHonestDelivery` (`Supplies.lean`): the RGA's honest-delivery
residual read through `proj₁` — born accuracy + born-applicable delivery for
CHARACTER ops only; mark ops are entirely unguarded. This is the honest
composite analogue of `rga_tombstone_free_ra_linearizable3_eq`, and NOT a
gate: the RGA-only capstone carries the same per-step assumption.

What the assembly consumes, premise by premise
(`prod_ra_linearizable_up_to_eq_H`):

| premise | supplied by | provenance |
|---|---|---|
| `hInvCong₁` | `rga_invCong` | RGA chain, reused |
| `hJ₁` (`EqJoinLemma3C_H`) | `rgaJoinH_of_canon` + discharged leaves | RGA chain, reused (config-free) |
| `hJoin₂` (`JoinLemma3C` full) | `markStore_joinLemma3C_full` | `ORSetCore` instantiation |
| `hHon₁` | `peritext_hHon_discharged` | **the §2.5.6 supply rerun** |
| `hHnil` | `rgaH_nil` | RGA chain, reused |
| `hHext` | `peritext_hHext_discharged` | rerun (config-free core + product freshness) |
| `hBA` | `peritext_hBA_discharged` | `PeritextHonestDelivery` (`inl`) / discharged outright (`inr`) |

The read layer (`Render.lean`) resolves marks against the character component
at read time; `peritextRender_congr` shows the render is well-defined on
exactly the quotient this capstone speaks about.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.PeritextTF

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.ProductEq
open Sal.ConditionedMRDTs (Configuration initConfig labeledTS3 prodSig)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA
  rgaCongVC' rgaInvInvVCA)
open Sal.ConditionedMRDTs.RGAInstanceNF (rga_invCong)
open Sal.ConditionedMRDTs.RGASkeleton3 (rgaJoinH_of_canon hCanon_of_leaves3
  rgaH rgaH_nil)
open Sal.ConditionedMRDTs.RGAK1Delta (rgaHonJ rga_hEnum_discharged
  rga_hMergeInputs_discharged)

local notation "PQD" => Sal.ConditionedMRDTs.ProductEq.prodQSig
  rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA markInvT

/-- **THE COMPOSITE CAPSTONE — tombstone-free Peritext is RA-linearizable up
to `≈₁ × Eq`** at every reachable configuration of the product quotient
ternary system, under `PeritextHonestDelivery` (honest delivery of character
ops; mark ops unguarded). Characters up to the RGA's observational `≈`,
marks literally. -/
theorem peritextTF_ra_linearizable_up_to_eq
    (hHD : PeritextHonestDelivery)
    (C : Configuration PQD)
    (hReach : (labeledTS3 PQD).ReachableFrom (initConfig PQD trivial) C) :
    IsRALinearizable3Eq (prodEqEquiv (D₂ := MarkStore) rgaEqEquiv')
      (prodW (D₂ := MarkStore) WfOpA)
      (prodInvPres (D₁ := RGACondSig') (D₂ := MarkStore) WfOpA rgaInvPresA markInvT)
      (prodCongVC (D₂ := MarkStore) rgaEqEquiv' rgaCongVC')
      (prodInvInvVC (D₂ := MarkStore) rgaEqEquiv' WfOpA rgaInvInvVCA) C :=
  Sal.ConditionedMRDTs.ProductEq.prod_ra_linearizable_up_to_eq_H
    rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA markInvT
    (fun heqv hInv => rga_invCong heqv hInv)
    (rgaJoinH_of_canon rgaHonJ rga_hEnum_discharged
      (hCanon_of_leaves3 rgaHonJ rga_hMergeInputs_discharged))
    markStore_joinLemma3C_full
    (fun hreach => peritext_hHon_discharged hHD hreach)
    rgaH_nil
    (fun hreach hstep hhead hver ρ hρp hH happ =>
      peritext_hHext_discharged hreach hstep hhead hver ρ hρp hH happ)
    (fun hreach hstep hhead hver =>
      peritext_hBA_discharged hHD hreach hstep hhead hver)
    C hReach

/-! ## Axiom audit -/

#print axioms peritextTF_ra_linearizable_up_to_eq

end Sal.ConditionedMRDTs.PeritextTF
