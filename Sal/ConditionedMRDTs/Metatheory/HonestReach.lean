import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Framework.ContractReach

/-!
# The conditioned metatheorem, honest-delivery form

Per-version RA-linearizability at every honestly reachable configuration,
from a single per-datatype obligation: **configurations satisfying the
honesty contract admit the ternary Join**.

`HonestReach D H hInit` is LTS reachability through `Step3` where every step
is taken from a configuration satisfying the per-configuration contract `H`,
a client/delivery discipline such as "every dequeue names an enqueue its
issuer had observed" (the mergeable queue) or the trivial `⊤` (any instance
whose join is unconditional). The metatheorem
(`ra_linearizable3_of_honest_reach`) says: if every `H`-configuration admits
the Join Lemma at its core (`JoinLemma3At`), then every `H`-honestly
reachable configuration is per-version RA-linearizable. Plain reachability is
the degenerate instance `H := fun _ => True` (`honestReach_of_reachable`),
recovering the unconditional bridge `ra_linearizable3_of_join`.

The join discharge is the per-datatype residue. Three species:

* **conditioned commutation**: the CD-route VC bundles
  (`join_lemma3_of_cd` and friends, `Adequacy.lean`); contract `⊤`;
* **flat**: the flat-engine bridge (`FlatGeneric_Bridge.lean`); `⊤` again;
* **direct witness**: the merge itself is the linearization witness, valid
  only under an honest-history contract (`MergeableQueue.lean`'s
  `q_join_at`).
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-- **Honest reachability**: LTS reachability where every step is taken from a
configuration satisfying the per-configuration contract `H`. -/
abbrev HonestReach (D : ConditionedMRDTSig) (H : Configuration D → Prop)
    (hInit : D.Inv D.init) : Configuration D → Prop :=
  ContractReach (initConfig D hInit) (Step3 D) H

variable {D : ConditionedMRDTSig} {H : Configuration D → Prop}
    {hInit : D.Inv D.init}

/-- **The honest-reachability induction**: if every `H`-configuration admits
the Join at its core, `GoodConfig3` holds at every `H`-honestly reachable
configuration. The contract feeds `goodConfig3_merge_at` exactly at the merge
steps; the other transitions preserve the invariant unconditionally. -/
theorem goodConfig3_of_honest_reach
    (hJoinAt : ∀ C', H C' → JoinLemma3At D (Configuration.core C'))
    {C : Configuration D} (hReach : HonestReach D H hInit C) :
    GoodConfig3 C := by
  apply ContractReach.invariant (goodConfig3_init hInit) (hReach := hReach)
  intro C₀ C₁ ℓ ih hHon hstep
  cases hstep with
  | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
    exact goodConfig3_createReplica h_fresh hL hvis hver ih
  | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
      hN hL hvis hver hhead hparents =>
    exact goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver ih
  | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
      h_rank₂ C' hN hL hvis hver hhead hparents =>
    exact goodConfig3_merge_at (hJoinAt _ hHon)
      h_head₁ h_ver₁ h_ver₂ h_lca h_verT hL hvis hver ih
  | query h_s h_val => exact ih

/-- **The conditioned metatheorem, honest-delivery form**: per-version
RA-linearizability at every `H`-honestly reachable configuration, given the
Join at every `H`-configuration. -/
theorem ra_linearizable3_of_honest_reach
    (hJoinAt : ∀ C', H C' → JoinLemma3At D (Configuration.core C'))
    {C : Configuration D} (hReach : HonestReach D H hInit C) :
    IsRALinearizable3 C :=
  isRALinearizable3_of_good (goodConfig3_of_honest_reach hJoinAt hReach)

open LabeledTS in
/-- Plain LTS reachability is honest reachability under the trivial
contract. -/
theorem honestReach_of_reachable {C : Configuration D}
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    HonestReach D (fun _ => True) hInit C := by
  induction hReach with
  | refl => exact .init
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    exact ih.step trivial hstep

/-! ## The widened form: honest reachability with virtual merges

`HonestReachV` is `HonestReach` over `Step3V` (the criss-cross gate lifted,
`LCA_Lemma.lean` §9). The merge induction gains the sibling `mergeVirtual` case,
discharged by `goodConfig3_mergeVirtual_at` with `StoreInv` carried alongside; the
per-datatype residue is the *same* `JoinLemma3At` obligation: nothing new is owed by
join-lemma datatypes. -/

/-- **Honest reachability over the widened LTS**: every step from an `H`-configuration,
merges resolved through virtual LCAs when no registered one exists. -/
abbrev HonestReachV (D : ConditionedMRDTSig) (H : Configuration D → Prop)
    (hInit : D.Inv D.init) : Configuration D → Prop :=
  ContractReach (initConfig D hInit) (Step3V D) H

/-- Gated honest reachability is widened honest reachability. -/
theorem honestReachV_of_honestReach {C : Configuration D}
    (hReach : HonestReach D H hInit C) : HonestReachV D H hInit C := by
  induction hReach with
  | init => exact .init
  | step _ hHon hstep ih => exact ih.step hHon (Step3V.base hstep)

/-- The widened induction maintains semantic canonicity and the store invariant
in one generic `ContractReach` fold.  The virtual-merge case consumes the
pre-step store component; all cases advance it with `storeInv_stepV`. -/
theorem goodConfig3_storeInv_of_honest_reachV
    (hJoinAt : ∀ C', H C' → JoinLemma3At D (Configuration.core C'))
    {C : Configuration D} (hReach : HonestReachV D H hInit C) :
    GoodConfig3 C ∧ StoreInv C.ver C.parents := by
  apply ContractReach.invariant
    ⟨goodConfig3_init hInit, storeInv_init hInit⟩ (hReach := hReach)
  intro C₀ C₁ ℓ ih hHon hstep
  have hStore' : StoreInv C₁.ver C₁.parents := storeInv_stepV hstep ih.2
  refine ⟨?_, hStore'⟩
  cases hstep with
    | base hstep' =>
      cases hstep' with
      | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
        exact goodConfig3_createReplica h_fresh hL hvis hver ih.1
      | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
          hN hL hvis hver hhead hparents =>
        exact goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver ih.1
      | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
          h_rank₂ C' hN hL hvis hver hhead hparents =>
        exact goodConfig3_merge_at (hJoinAt _ hHon)
          h_head₁ h_ver₁ h_ver₂ h_lca h_verT hL hvis hver ih.1
      | query h_s h_val => exact ih.1
    | mergeVirtual h_head₁ h_head₂ h_ver₁ h_ver₂ h_vm h_rank₁ h_rank₂ C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3_mergeVirtual_at (hJoinAt _ hHon)
        ih.2 h_head₁ h_ver₁ h_ver₂ hL hvis hver ih.1

/-- `StoreInv` at every widened honestly reachable configuration. -/
theorem storeInv_of_honest_reachV {C : Configuration D}
    (hReach : HonestReachV D H hInit C) : StoreInv C.ver C.parents := by
  apply ContractReach.invariant
    (I := fun C : Configuration D => StoreInv C.ver C.parents)
    (storeInv_init hInit) (hReach := hReach)
  intro C₀ C₁ ℓ ih _ hstep
  exact storeInv_stepV hstep ih

/-- **The widened honest-reachability induction** (ordinary and virtual merge
cases) as the first projection of the paired generic invariant. -/
theorem goodConfig3_of_honest_reachV
    (hJoinAt : ∀ C', H C' → JoinLemma3At D (Configuration.core C'))
    {C : Configuration D} (hReach : HonestReachV D H hInit C) :
    GoodConfig3 C :=
  (goodConfig3_storeInv_of_honest_reachV hJoinAt hReach).1

/-- **The conditioned metatheorem, honest-delivery form, gate lifted**: per-version
RA-linearizability at every `H`-honestly reachable configuration of the widened LTS,
from the same join obligation. -/
theorem ra_linearizable3_of_honest_reachV
    (hJoinAt : ∀ C', H C' → JoinLemma3At D (Configuration.core C'))
    {C : Configuration D} (hReach : HonestReachV D H hInit C) :
    IsRALinearizable3 C :=
  isRALinearizable3_of_good (goodConfig3_of_honest_reachV hJoinAt hReach)

open LabeledTS in
/-- Plain widened reachability is widened honest reachability under the trivial
contract. -/
theorem honestReachV_of_reachableV {C : Configuration D}
    (hReach : (labeledTS3V D).ReachableFrom (initConfig D hInit) C) :
    HonestReachV D (fun _ => True) hInit C := by
  induction hReach with
  | refl => exact .init
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    exact ih.step trivial hstep

#print axioms ra_linearizable3_of_honest_reach
#print axioms ra_linearizable3_of_honest_reachV

end Sal.ConditionedMRDTs
