import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.ArbAdequacyReach
import Sal.ConditionedMRDTs.MRDT_Instances.GSet.GSet

/-!
# Counter (`a+b−l`) — the counter-group demo kernel (unconditional delta route)

Split out of the original monolithic `MRDT_Instances.lean`; declarations
verbatim, names unchanged.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## Counter -/

/-- The counter MRDT: `mergeL l a b = a + b - l`. The LCA argument prevents
double-counting — the mathematically canonical example of an MRDT whose merge
*needs* the LCA. Its binary slice `merge a b = mergeL 0 a b = a + b` is the
paper's CRDT collapse — and it is exactly this slice that breaks `lem_0op`. -/
def Counter : ConditionedMRDTSig where
  State := Int
  dec_state := inferInstance
  init := 0
  AppOp := Unit
  dec_op := inferInstance
  Query := Unit
  Value := Int
  update := fun s _ => s + 1
  merge := fun a b => a + b
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => a + b - l
  merge_init_slice := fun a b => by show a + b - 0 = a + b; omega
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem Counter_update_eq (s : Int) (e : Op Counter.AppOp) :
    Counter.update s e = s + 1 := rfl

theorem Counter_merge_eq (a b : Int) :
    Counter.toCRDTSig.merge a b = a + b := rfl

theorem Counter_mergeL_eq (l a b : Int) :
    Counter.mergeL l a b = a + b - l := rfl

theorem Counter_init_eq : Counter.init = (0 : Int) := rfl

/-- Every pair of counter events commutes. -/
theorem Counter_all_comm : ∀ a b : Op Counter.AppOp,
    Counter.toCRDTSig.commutes a b :=
  fun _ _ _ => rfl

theorem Counter_rc_either : ∀ o₁ o₂ : Op Counter.AppOp,
    Counter.toCRDTSig.rc o₁ o₂ = RcRes.Either :=
  fun _ _ => rfl

theorem Counter_updateVCs : UpdateVCs Counter.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (Counter_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [Counter_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [Counter_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [Counter_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

/-- The ternary core bundle for the counter — note `lem_0op3` holds exactly
because the LCA argument absorbs the double count:
`(a+1) + (b+1) - (l+1) = (a + b - l) + 1`. -/
theorem Counter_coreVCs3 : CoreVCs3 Counter := by
  refine ⟨Counter_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    simp only [Counter_mergeL_eq]
    have go : ∀ l' a' b' : Int, a' + b' - l' = b' + a' - l' := by omega
    exact go l a b
  · intro s
    simp only [Counter_mergeL_eq, Counter_init_eq]
    have go : ∀ s' : Int, (0 : Int) + s' - 0 = s' := by omega
    exact go s
  · intro l a b e
    simp only [Counter_update_eq, Counter_mergeL_eq]
    have go : ∀ l' a' b' : Int,
        a' + 1 + (b' + 1) - (l' + 1) = a' + b' - l' + 1 := by omega
    exact go l a b
  · intro a e π₀ π₂ _ _
    simp only [Counter_update_eq, Counter_mergeL_eq]
    have go : ∀ x y z : Int, y + 1 + z - x = y + z - x + 1 := by omega
    exact go _ _ _

/-- The Counter satisfies the delta contract — the **group instance**
(`mergeL l a b = a + (b − l)`; deltas are translation-invariant). Note it
satisfies neither `merge_idem` nor any lattice law: the binary CD route is
closed to it, the ternary one is not. -/
theorem Counter_deltaVCs3 : DeltaVCs3 Counter := by
  constructor
  · intro m x₀ x₁ x₂ c
    simp only [Counter_mergeL_eq]
    have go : ∀ m' x₀' x₁' x₂' c' : Int,
        x₁' + c' - m' + (x₂' + c' - m') - (x₀' + c' - m')
          = x₁' + x₂' - x₀' + c' - m' := by omega
    exact go m x₀ x₁ x₂ c
  · intro l m x c y
    simp only [Counter_mergeL_eq]
    have go : ∀ l' m' x' c' y' : Int,
        x' + c' - m' + y' - l' = x' + y' - l' + c' - m' := by omega
    exact go l m x c y

/-- G-Set satisfies the delta contract — the **lattice instance** (LCA-blind
`mergeL` over an ACI join; the laws collapse to ACI consequences). -/
theorem GSet_deltaVCs3 : DeltaVCs3 GSetCond := by
  constructor
  · intro m x₀ x₁ x₂ c
    simp only [GSet_mergeL_eq]
    apply Set.ext
    intro y
    simp only [Set.mem_union]
    tauto
  · intro l m x c y
    simp only [GSet_mergeL_eq]
    apply Set.ext
    intro z
    simp only [Set.mem_union]
    tauto

/-- The ternary Join Lemma for the Counter, via the CD route. -/
theorem Counter_joinLemma3_cd : JoinLemma3 Counter :=
  join_lemma3_of_cd Counter_coreVCs3 Counter_deltaVCs3
    (cdVC3_of_all_comm Counter_coreVCs3 Counter_all_comm)

/-- The ternary Join Lemma for G-Set, via the CD route. -/
theorem GSet_joinLemma3_cd : JoinLemma3 GSetCond :=
  join_lemma3_of_cd GSet_coreVCs3 GSet_deltaVCs3
    (cdVC3_of_all_comm GSet_coreVCs3 GSet_all_comm)

open LabeledTS in
/-- End-to-end RA-linearizability for the Counter via the delta/CD route. -/
theorem counter_ra_linearizable3_cd
    (C : Configuration Counter)
    (hReach : (labeledTS3 Counter).ReachableFrom
      (initConfig Counter trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_via_capstone Counter_coreVCs3.toCD Counter_coreVCs3.update_core
    (feasibleDeltaVCs3_of_delta Counter_coreVCs3 Counter_deltaVCs3)
    (cdVC3_of_all_comm Counter_coreVCs3 Counter_all_comm) C hReach

open LabeledTS in
/-- End-to-end RA-linearizability for G-Set via the delta/CD route. -/
theorem gset_ra_linearizable3_cd
    (C : Configuration GSetCond)
    (hReach : (labeledTS3 GSetCond).ReachableFrom
      (initConfig GSetCond trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_via_capstone GSet_coreVCs3.toCD GSet_coreVCs3.update_core
    (feasibleDeltaVCs3_of_delta GSet_coreVCs3 GSet_deltaVCs3)
    (cdVC3_of_all_comm GSet_coreVCs3 GSet_all_comm) C hReach


end Sal.ConditionedMRDTs
