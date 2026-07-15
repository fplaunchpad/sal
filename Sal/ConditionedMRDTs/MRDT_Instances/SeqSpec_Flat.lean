import Sal.ConditionedMRDTs.MRDT_Instances.Counter.Counter
import Sal.ConditionedMRDTs.MRDT_Instances.IOC.IOC
import Sal.ConditionedMRDTs.MRDT_Instances.PN.PN
import Sal.ConditionedMRDTs.MRDT_Instances.ORSet.ORSet
import Sal.ConditionedMRDTs.MRDT_Instances.EWFlag.EWFlag

/-!
# Sequential-spec soundness — tier 1: the flat RDTs (task #78 / #65)

The campaign: for every RDT, prove its `do` matches a straightforward
sequential implementation — the intent complement to RA-linearizability,
which certifies convergence to the datatype's OWN fold and is blind to a
wrong `do_` (the spec-limit lesson). Template: Shesha's
`sequential_soundness`.

Shape per RDT: a *view* (the observable a user reads), an independent
*naive sequential program* over plain values, and the theorem that on any
single-replica history the view of the fold IS the naive program's
result. For this tier no inductive invariant is needed — each view is a
fold homomorphism (the interesting invariants start at MVR and the
sequence datatypes, tiers 2–4).
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-- Single-replica sequential fold of an RDT. -/
def seqFold (D : ConditionedMRDTSig) (ρ : List (Op D.AppOp)) : D.State :=
  applySeq D.toCRDTSig D.init ρ

theorem seqFold_snoc (D : ConditionedMRDTSig) (ρ : List (Op D.AppOp))
    (e : Op D.AppOp) :
    seqFold D (ρ ++ [e]) = D.update (seqFold D ρ) e := by
  unfold seqFold applySeq
  rw [List.foldl_append]
  rfl

/-! ## Counter and Increment-Only Counter: the spec is the op count -/

/-- **Counter, sequentially = counting.** The naive spec of an
increment-only counter is the number of operations issued. -/
theorem counter_seq_sound (ρ : List (Op Counter.AppOp)) :
    seqFold Counter ρ = (ρ.length : Int) := by
  induction ρ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ρ o ih =>
      rw [seqFold_snoc, ih]
      show (ρ.length : Int) + 1 = ((ρ ++ [o]).length : Int)
      simp

/-- **IOC, sequentially = counting.** -/
theorem ioc_seq_sound (ρ : List (Op IOC.AppOp)) :
    seqFold IOC ρ = (ρ.length : Int) := by
  induction ρ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ρ o ih =>
      rw [seqFold_snoc, ih]
      show (ρ.length : Int) + 1 = ((ρ ++ [o]).length : Int)
      simp

/-! ## PN-Counter: the spec is increments minus decrements -/

/-- The naive sequential PN spec: `#inc − #dec`. -/
def pnSpec (ρ : List (Op PN.AppOp)) : Int :=
  ((ρ.countP fun o => decide (o.2.2 = PNOp.inc)) : Int) -
  ((ρ.countP fun o => decide (o.2.2 = PNOp.dec)) : Int)

/-- **PN, sequentially = signed counting.** -/
theorem pn_seq_sound (ρ : List (Op PN.AppOp)) :
    seqFold PN ρ = pnSpec ρ := by
  induction ρ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ρ o ih =>
      rw [seqFold_snoc, ih]
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | inc =>
          show pnSpec ρ + 1 = _
          simp [pnSpec, List.countP_append]
          omega
      | dec =>
          show pnSpec ρ - 1 = _
          simp [pnSpec, List.countP_append]
          omega

/-! ## OR-Set: the spec is a plain set with last-action-wins membership -/

/-- The element view: some tag of `e` is live. What a user reads. -/
def orView (s : (ℕ × ℕ) → Bool) (e : ℕ) : Prop := ∃ t, s (t, e) = true

/-- The naive sequential set program: add inserts, remove deletes. -/
def orSpecStep (S : ℕ → Bool) (o : Op ORSetOp) : ℕ → Bool :=
  match o.2.2 with
  | .add e => fun x => S x || decide (x = e)
  | .rem e => fun x => S x && !decide (x = e)

def orSpecFold (ρ : List (Op ORSetOp)) : ℕ → Bool :=
  ρ.foldl orSpecStep (fun _ => false)

theorem orSpecFold_snoc (ρ : List (Op ORSetOp)) (o : Op ORSetOp) :
    orSpecFold (ρ ++ [o]) = orSpecStep (orSpecFold ρ) o := by
  unfold orSpecFold
  rw [List.foldl_append]
  rfl

/-- **OR-Set, sequentially = a plain set.** The tag machinery is invisible
to a single replica: the element view of the fold is exactly the naive
add/remove set program. (No invariant needed — the view is a fold
homomorphism: `add` stakes a tag of `e`, `rem` filters every tag of
`e`.) -/
theorem orset_seq_sound (ρ : List (Op ORSet.AppOp)) (e : ℕ) :
    orView (seqFold ORSet ρ) e ↔ orSpecFold ρ e = true := by
  induction ρ using List.reverseRecOn with
  | nil =>
      show orView (fun _ => false) e ↔ _
      simp [orView, orSpecFold]
  | append_singleton ρ o ih =>
      rw [seqFold_snoc, orSpecFold_snoc]
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | add e' =>
          rw [ORSet_update_eq]
          simp only [orView, orUpdate, orSpecStep, Bool.or_eq_true,
            decide_eq_true_eq, Prod.mk.injEq]
          constructor
          · rintro ⟨t, ht | ⟨rfl, rfl⟩⟩
            · exact Or.inl (ih.mp ⟨t, ht⟩)
            · exact Or.inr rfl
          · rintro (h | rfl)
            · obtain ⟨t, ht⟩ := ih.mpr h
              exact ⟨t, Or.inl ht⟩
            · exact ⟨ts, Or.inr ⟨rfl, rfl⟩⟩
      | rem e' =>
          rw [ORSet_update_eq]
          simp only [orView, orUpdate, orSpecStep, Bool.and_eq_true,
            Bool.not_eq_true', decide_eq_false_iff_not]
          constructor
          · rintro ⟨t, ht, hne⟩
            exact ⟨ih.mp ⟨t, ht⟩, hne⟩
          · rintro ⟨h, hne⟩
            obtain ⟨t, ht⟩ := ih.mpr h
            exact ⟨t, ht, hne⟩

/-! ## Enable-wins flag: the spec is a plain boolean -/

/-- The flag view: some replica's flag is set. -/
def ewView (s : ℕ → ℕ × Bool) : Prop := ∃ k, (s k).2 = true

/-- The naive sequential flag program. -/
def ewSpecStep (_ : Bool) (o : Op EWOp) : Bool :=
  match o.2.2 with
  | .enable => true
  | .disable => false

def ewSpecFold (ρ : List (Op EWOp)) : Bool :=
  ρ.foldl ewSpecStep false

theorem ewSpecFold_snoc (ρ : List (Op EWOp)) (o : Op EWOp) :
    ewSpecFold (ρ ++ [o]) = ewSpecStep (ewSpecFold ρ) o := by
  unfold ewSpecFold
  rw [List.foldl_append]
  rfl

/-- **Enable-wins flag, sequentially = a plain boolean.** Enable sets,
disable clears; the per-replica counters are invisible to one replica. -/
theorem ewflag_seq_sound (ρ : List (Op EWFlag.AppOp)) :
    ewView (seqFold EWFlag ρ) ↔ ewSpecFold ρ = true := by
  induction ρ using List.reverseRecOn with
  | nil =>
      show ewView (fun _ => (0, false)) ↔ _
      simp [ewView, ewSpecFold]
  | append_singleton ρ o ih =>
      rw [seqFold_snoc, ewSpecFold_snoc]
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | enable =>
          show ewView (ewUpdate _ _) ↔ _
          simp only [ewSpecStep]
          constructor
          · intro _
            trivial
          · intro _
            exact ⟨r, by simp [ewUpdate]⟩
      | disable =>
          show ewView (ewUpdate _ _) ↔ _
          simp only [ewSpecStep]
          constructor
          · rintro ⟨k, hk⟩
            simp [ewUpdate] at hk
          · intro h
            exact Bool.noConfusion h

end Sal.ConditionedMRDTs
