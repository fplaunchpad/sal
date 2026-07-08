import Sal.ConditionedMRDTs.Metatheory.Adequacy

/-!
# The conditioned metatheorem, honest-delivery form

Per-version RA-linearizability at every honestly reachable configuration,
from a single per-datatype obligation: **configurations satisfying the
honesty contract admit the ternary Join**.

`HonestReach D H hInit` is LTS reachability through `Step3` where every step
is taken from a configuration satisfying the per-configuration contract `H` —
a client/delivery discipline such as "every dequeue names an enqueue its
issuer had observed" (the mergeable queue) or the trivial `⊤` (any instance
whose join is unconditional). The metatheorem
(`ra_linearizable3_of_honest_reach`) says: if every `H`-configuration admits
the Join Lemma at its core (`JoinLemma3At`), then every `H`-honestly
reachable configuration is per-version RA-linearizable. Plain reachability is
the degenerate instance `H := fun _ => True` (`honestReach_of_reachable`),
recovering the unconditional bridge `ra_linearizable3_of_join`.

The join discharge is the per-datatype residue. Three species so far:

* **conditioned commutation** — the CD-route VC bundles
  (`join_lemma3_of_cd` and friends, `Adequacy.lean`); contract `⊤`;
* **flat** — the flat-engine bridge (`FlatGeneric_Bridge.lean`); `⊤` again;
* **direct witness** — the merge itself is the linearization witness, valid
  only under an honest-history contract (`MergeableQueue.lean`'s
  `q_join_at`).
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

open LabeledTS in
/-- **Honest reachability**: LTS reachability where every step is taken from a
configuration satisfying the per-configuration contract `H`. -/
inductive HonestReach (D : ConditionedMRDTSig) (H : Configuration D → Prop)
    (hInit : D.Inv D.init) : Configuration D → Prop where
  | init : HonestReach D H hInit (initConfig D hInit)
  | step {C : Configuration D} {ℓ : Label3 D} {C' : Configuration D} :
      HonestReach D H hInit C → H C → Step3 D C ℓ C' → HonestReach D H hInit C'

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
  induction hReach with
  | init => exact goodConfig3_init hInit
  | step _ hHon hstep ih =>
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

#print axioms ra_linearizable3_of_honest_reach

end Sal.ConditionedMRDTs
