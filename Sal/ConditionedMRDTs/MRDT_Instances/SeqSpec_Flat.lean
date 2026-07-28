import Sal.ConditionedMRDTs.MRDT_Instances.Counter.Counter
import Sal.ConditionedMRDTs.MRDT_Instances.IOC.IOC
import Sal.ConditionedMRDTs.MRDT_Instances.PN.PN
import Sal.ConditionedMRDTs.MRDT_Instances.ORSet.ORSet
import Sal.ConditionedMRDTs.MRDT_Instances.ORSetE.ORSetE
import Sal.ConditionedMRDTs.MRDT_Instances.EWFlag.EWFlag
import Sal.ConditionedMRDTs.MRDT_Instances.GOSet.GOSet
import Sal.ConditionedMRDTs.MRDT_Instances.GOMap.GOMap
import Sal.ConditionedMRDTs.MRDT_Instances.MVR.MVR
import Sal.ConditionedMRDTs.MRDT_Instances.AWPQ.AWPQ
import Sal.ConditionedMRDTs.MRDT_Instances.FWWRegister.FWWRegister
import Sal.ConditionedMRDTs.MRDT_Instances.LWWRegister.LWWRegister

/-!
# Sequential-spec soundness: the flat RDTs

The campaign: for every RDT, prove its `do` matches a straightforward
sequential implementation, the intent complement to RA-linearizability,
which certifies convergence to the datatype's OWN fold and is blind to a
wrong `do_` (the spec-limit lesson).

Shape per RDT: a *view* (the observable a user reads), an independent
*naive sequential program* over plain values, and the theorem that on any
single-replica history the view of the fold IS the naive program's
result. No inductive invariant is needed here: each view is a fold
homomorphism (the interesting invariants start at MVR and the sequence
datatypes).
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

/-! ## Grow-only set and map: the spec is the union of payloads -/

theorem GOSet_update_eq' (s : GOSet.State) (o : Op GOSet.AppOp) :
    GOSet.update s o = goUpdate s o := rfl

theorem GOMap_update_eq' (s : GOMap.State) (o : Op GOMap.AppOp) :
    GOMap.update s o = gomUpdate s o := rfl

/-- **Grow-only set, sequentially = accumulation.** Membership is exactly
"some op added it". -/
theorem goset_seq_sound (ρ : List (Op GOSet.AppOp)) (x : ℕ) :
    seqFold GOSet ρ x = true ↔ ∃ o ∈ ρ, o.2.2 = x := by
  induction ρ using List.reverseRecOn with
  | nil =>
      show (false = true) ↔ _
      simp
  | append_singleton ρ o ih =>
      rw [seqFold_snoc, GOSet_update_eq']
      simp only [goUpdate, Bool.or_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro (⟨o', ho', rfl⟩ | rfl)
        · exact ⟨o', List.mem_append_left _ ho', rfl⟩
        · exact ⟨o, List.mem_append_right _ (by simp), rfl⟩
      · rintro ⟨o', ho', rfl⟩
        rcases List.mem_append.mp ho' with h | h
        · exact Or.inl ⟨o', h, rfl⟩
        · simp at h
          subst h
          exact Or.inr rfl

/-- **Grow-only map, sequentially = accumulation** of `(key, value)`
pairs. -/
theorem gomap_seq_sound (ρ : List (Op GOMap.AppOp)) (p : ℕ × ℕ) :
    seqFold GOMap ρ p = true ↔ ∃ o ∈ ρ, o.2.2 = p := by
  induction ρ using List.reverseRecOn with
  | nil =>
      show (false = true) ↔ _
      simp
  | append_singleton ρ o ih =>
      rw [seqFold_snoc, GOMap_update_eq']
      simp only [gomUpdate, Bool.or_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro (⟨o', ho', rfl⟩ | rfl)
        · exact ⟨o', List.mem_append_left _ ho', rfl⟩
        · exact ⟨o, List.mem_append_right _ (by simp), rfl⟩
      · rintro ⟨o', ho', rfl⟩
        rcases List.mem_append.mp ho' with h | h
        · exact Or.inl ⟨o', h, rfl⟩
        · simp at h
          subst h
          exact Or.inr rfl

/-! ## OR-Set-efficient: same spec program as the OR-Set -/

/-- The element view over `(rid, ts, elem)` triples. -/
def orEView (s : (ℕ × ℕ × ℕ) → Bool) (e : ℕ) : Prop :=
  ∃ r t, s (r, t, e) = true

/-- **OR-Set-efficient, sequentially = the same plain set.** The
per-replica tag compaction (add filters the issuer's prior tag before
staking) is invisible at the element view: the two OR-Sets satisfy the
one sequential spec. -/
theorem orsete_seq_sound (ρ : List (Op ORSetE.AppOp)) (e : ℕ) :
    orEView (seqFold ORSetE ρ) e ↔ orSpecFold ρ e = true := by
  induction ρ using List.reverseRecOn with
  | nil =>
      show orEView (fun _ => false) e ↔ _
      simp [orEView, orSpecFold]
  | append_singleton ρ o ih =>
      rw [seqFold_snoc, orSpecFold_snoc, ORSetE_update_eq]
      obtain ⟨ts, rid, op⟩ := o
      cases op with
      | add e' =>
          simp only [orEView, orEUpdate, orSpecStep, Bool.or_eq_true,
            Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨r, t, ⟨hs, -⟩ | heq⟩
            · exact Or.inl (ih.mp ⟨r, t, hs⟩)
            · simp only [Prod.mk.injEq] at heq
              exact Or.inr heq.2.2
          · intro h
            by_cases hee : e = e'
            · subst hee
              exact ⟨rid, ts, Or.inr rfl⟩
            · rcases h with h | h
              · obtain ⟨r, t, hs⟩ := ih.mpr h
                refine ⟨r, t, Or.inl ⟨hs, ?_⟩⟩
                simp only [Bool.not_eq_true', decide_eq_false_iff_not]
                exact fun h => hee h.2.symm
              · exact absurd h hee
      | rem e' =>
          simp only [orEView, orEUpdate, orSpecStep, Bool.and_eq_true,
            Bool.not_eq_true', decide_eq_false_iff_not]
          constructor
          · rintro ⟨r, t, hs, hne⟩
            exact ⟨ih.mp ⟨r, t, hs⟩, fun h => hne h.symm⟩
          · rintro ⟨h, hne⟩
            obtain ⟨r, t, hs⟩ := ih.mpr h
            exact ⟨r, t, hs, fun h => hne h.symm⟩

/-! ## Multi-Valued Register: a genuine inductive invariant

Sequentially the MVR must read as a plain last-write-wins register. The
op payload `O` (the overwritten tags) is honest exactly when it lists the
issuer's currently-visible tags, and stamps are fresh (`mvrOK`). Under
it, the theorem needs a real auxiliary invariant: **every overwritten
stamp is a staked tag** (`mvr_over_tags`), which is what makes a fresh
stamp provably not-yet-overwritten. -/

/-- `n` is a staked write stamp. -/
def mvrTag (s : MVR.State) (n : ℕ) : Prop := ∃ v, s.1 (n, v) = true

/-- `n` is a visible (staked, not overwritten) stamp. -/
def mvrVis (s : MVR.State) (n : ℕ) : Prop := mvrTag s n ∧ s.2 n = false

/-- The register view: values of visible stamps. -/
def mvrView (s : MVR.State) (v : ℕ) : Prop :=
  ∃ n, s.1 (n, v) = true ∧ s.2 n = false

/-- Sequential honesty for MVR histories: every op's stamp is fresh, and
its overwrite payload lists exactly the issuer's visible stamps. -/
def mvrOK (ρ : List (Op MVROp)) : Prop :=
  ∀ (σ : List (Op MVROp)) (o : Op MVROp) (τ : List (Op MVROp)),
    ρ = σ ++ o :: τ →
    (∀ v', (seqFold MVR σ).1 (o.1, v') = false) ∧
    (∀ w O, o.2.2 = MVROp.write w O →
      ∀ n, n ∈ O ↔ mvrVis (seqFold MVR σ) n)

theorem mvrOK_prefix {ρ : List (Op MVROp)} {o : Op MVROp}
    (h : mvrOK (ρ ++ [o])) : mvrOK ρ := by
  intro σ o' τ heq
  exact h σ o' (τ ++ [o]) (by rw [heq]; simp)

/-- The naive sequential register program: the last write's value. -/
def mvrSpecFold (ρ : List (Op MVROp)) : Option ℕ :=
  ρ.foldl (fun _ o => match o.2.2 with | .write v _ => some v) none

theorem mvrSpecFold_snoc (ρ : List (Op MVROp)) (ts r w : ℕ) (O : List ℕ) :
    mvrSpecFold (ρ ++ [(ts, r, MVROp.write w O)]) = some w := by
  unfold mvrSpecFold
  rw [List.foldl_append]
  rfl

/-- **The invariant**: every overwritten stamp is staked. -/
theorem mvr_over_tags {ρ : List (Op MVROp)} (hOK : mvrOK ρ) :
    ∀ n, (seqFold MVR ρ).2 n = true → mvrTag (seqFold MVR ρ) n := by
  induction ρ using List.reverseRecOn with
  | nil =>
      intro n h
      have : (seqFold MVR ([] : List (Op MVROp))).2 n = false := rfl
      rw [this] at h
      exact Bool.noConfusion h
  | append_singleton ρ o ih =>
      intro n h
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | write w O =>
          rw [seqFold_snoc, MVR_update_eq] at h ⊢
          simp only [mvrUpdate, Bool.or_eq_true, decide_eq_true_eq] at h
          simp only [mvrTag, mvrUpdate, Bool.or_eq_true, decide_eq_true_eq]
          rcases h with h' | h'
          · obtain ⟨v', hv'⟩ := ih (mvrOK_prefix hOK) n h'
            exact ⟨v', Or.inl hv'⟩
          · have hO := (hOK ρ (ts, r, .write w O) [] (by simp)).2 w O rfl n
            obtain ⟨⟨v', hv'⟩, -⟩ := hO.mp h'
            exact ⟨v', Or.inl hv'⟩

/-- **MVR, sequentially = a last-write-wins register.** -/
theorem mvr_seq_sound {ρ : List (Op MVROp)} (hOK : mvrOK ρ) (v : ℕ) :
    mvrView (seqFold MVR ρ) v ↔ mvrSpecFold ρ = some v := by
  induction ρ using List.reverseRecOn with
  | nil =>
      constructor
      · rintro ⟨n, hn, -⟩
        exact Bool.noConfusion hn
      · intro h
        simp [mvrSpecFold] at h
  | append_singleton ρ o ih =>
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | write w O =>
          have hcond := hOK ρ (ts, r, .write w O) [] (by simp)
          have hfresh := hcond.1
          have hO := hcond.2 w O rfl
          rw [seqFold_snoc, MVR_update_eq, mvrSpecFold_snoc]
          simp only [mvrView, mvrUpdate, Bool.or_eq_true,
            decide_eq_true_eq, Bool.or_eq_false_iff,
            decide_eq_false_iff_not, Prod.mk.injEq]
          constructor
          · rintro ⟨n, hstake, hov, hnO⟩
            rcases hstake with hs | ⟨rfl, rfl⟩
            · exact absurd ((hO n).mpr ⟨⟨v, hs⟩, hov⟩) hnO
            · rfl
          · intro hspec
            have hvw : w = v := by
              simpa using hspec
            subst hvw
            have hnotag : ¬ mvrTag (seqFold MVR ρ) ts := by
              rintro ⟨v', hv'⟩
              rw [hfresh v'] at hv'
              exact Bool.noConfusion hv'
            have h1 : (seqFold MVR ρ).2 ts = false := by
              cases hh : (seqFold MVR ρ).2 ts with
              | false => rfl
              | true =>
                  exact absurd (mvr_over_tags (mvrOK_prefix hOK) ts hh)
                    hnotag
            have h2 : ts ∉ O := fun hin => hnotag ((hO ts).mp hin).1
            exact ⟨ts, Or.inr ⟨rfl, rfl⟩, h1, h2⟩

/-! ## Conditioned G-Set: the spec is accumulation, over `Set` -/

/-- The set view (the state, at its underlying type). -/
def gsetView (s : GSetCond.State) : Set ℕ := s

/-- **Conditioned G-Set, sequentially = accumulation.** -/
theorem gsetcond_seq_sound (ρ : List (Op GSetCond.AppOp)) (x : ℕ) :
    x ∈ gsetView (seqFold GSetCond ρ) ↔ ∃ o ∈ ρ, o.2.2 = x := by
  induction ρ using List.reverseRecOn with
  | nil =>
      show x ∈ (∅ : Set ℕ) ↔ _
      simp
  | append_singleton ρ o ih =>
      rw [seqFold_snoc]
      show x ∈ insert o.2.2 (gsetView (seqFold GSetCond ρ)) ↔ _
      rw [Set.mem_insert_iff, ih]
      constructor
      · rintro (rfl | ⟨o', ho', rfl⟩)
        · exact ⟨o, List.mem_append_right _ (by simp), rfl⟩
        · exact ⟨o', List.mem_append_left _ ho', rfl⟩
      · rintro ⟨o', ho', rfl⟩
        rcases List.mem_append.mp ho' with h | h
        · exact Or.inr ⟨o', h, rfl⟩
        · simp at h
          subst h
          exact Or.inl rfl

/-! ## Add-Wins Priority Queue: membership + the increment log

Sequentially the AWPQ state is pinned by two theorems: membership behaves
as the plain add/remove set (increments are membership-inert), and the
increment component is a grow-only log of exactly the issued increments.
Together they determine both components pointwise. (A priority-sum view
needs finite aggregation over the log, meaningful only against the
read-side companion; the state-level spec is complete without it.) -/

/-- Membership view: `e` has a live add record. -/
def awpqMemView (s : AWPQ.State) (e : ℕ) : Prop :=
  ∃ t v, s.1 (t, e, v) = true

/-- The naive sequential membership program: add inserts, rmv deletes,
inc is inert. -/
def awpqSpecStep (S : ℕ → Bool) (o : Op AWPQOp) : ℕ → Bool :=
  match o.2.2 with
  | .add e _ => fun x => S x || decide (x = e)
  | .inc _ _ => S
  | .rmv e   => fun x => S x && !decide (x = e)

def awpqSpecFold (ρ : List (Op AWPQOp)) : ℕ → Bool :=
  ρ.foldl awpqSpecStep (fun _ => false)

theorem awpqSpecFold_snoc (ρ : List (Op AWPQOp)) (o : Op AWPQOp) :
    awpqSpecFold (ρ ++ [o]) = awpqSpecStep (awpqSpecFold ρ) o := by
  unfold awpqSpecFold
  rw [List.foldl_append]
  rfl

/-- **AWPQ membership, sequentially = a plain set.** -/
theorem awpq_mem_seq_sound (ρ : List (Op AWPQ.AppOp)) (e : ℕ) :
    awpqMemView (seqFold AWPQ ρ) e ↔ awpqSpecFold ρ e = true := by
  induction ρ using List.reverseRecOn with
  | nil =>
      show awpqMemView (fun _ => false, fun _ => false) e ↔ _
      simp [awpqMemView, awpqSpecFold]
  | append_singleton ρ o ih =>
      rw [seqFold_snoc, awpqSpecFold_snoc, AWPQ_update_eq]
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | add e' v' =>
          simp only [awpqMemView, awpqUpdate, awpqSpecStep,
            Bool.or_eq_true, decide_eq_true_eq, Prod.mk.injEq]
          constructor
          · rintro ⟨t, v, ht | ⟨rfl, rfl, rfl⟩⟩
            · exact Or.inl (ih.mp ⟨t, v, ht⟩)
            · exact Or.inr rfl
          · rintro (h | rfl)
            · obtain ⟨t, v, ht⟩ := ih.mpr h
              exact ⟨t, v, Or.inl ht⟩
            · exact ⟨ts, v', Or.inr ⟨rfl, rfl, rfl⟩⟩
      | inc e' a' =>
          simp only [awpqMemView, awpqUpdate, awpqSpecStep]
          exact ih
      | rmv e' =>
          simp only [awpqMemView, awpqUpdate, awpqSpecStep,
            Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
          constructor
          · rintro ⟨t, v, ht, hne⟩
            exact ⟨ih.mp ⟨t, v, ht⟩, hne⟩
          · rintro ⟨h, hne⟩
            obtain ⟨t, v, ht⟩ := ih.mpr h
            exact ⟨t, v, ht, hne⟩

/-- **The AWPQ increment log, sequentially = exactly the issued
increments** (grow-only accumulation; add/rmv are inert on it). -/
theorem awpq_inc_log_sound (ρ : List (Op AWPQ.AppOp)) (t e : ℕ) (a : ℤ) :
    (seqFold AWPQ ρ).2 (t, e, a) = true ↔
      ∃ o ∈ ρ, o.2.2 = AWPQOp.inc e a ∧ o.1 = t := by
  induction ρ using List.reverseRecOn with
  | nil =>
      show (false = true) ↔ _
      simp
  | append_singleton ρ o ih =>
      rw [seqFold_snoc, AWPQ_update_eq]
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | add e' v' =>
          show (seqFold AWPQ ρ).2 (t, e, a) = true ↔ _
          rw [ih]
          constructor
          · rintro ⟨o', ho', h1, h2⟩
            exact ⟨o', List.mem_append_left _ ho', h1, h2⟩
          · rintro ⟨o', ho', h1, h2⟩
            rcases List.mem_append.mp ho' with h | h
            · exact ⟨o', h, h1, h2⟩
            · simp at h
              subst h
              exact absurd h1 (by simp)
      | rmv e' =>
          show (seqFold AWPQ ρ).2 (t, e, a) = true ↔ _
          rw [ih]
          constructor
          · rintro ⟨o', ho', h1, h2⟩
            exact ⟨o', List.mem_append_left _ ho', h1, h2⟩
          · rintro ⟨o', ho', h1, h2⟩
            rcases List.mem_append.mp ho' with h | h
            · exact ⟨o', h, h1, h2⟩
            · simp at h
              subst h
              exact absurd h1 (by simp)
      | inc e' a' =>
          simp only [awpqUpdate, Bool.or_eq_true, decide_eq_true_eq,
            Prod.mk.injEq, ih]
          constructor
          · rintro (⟨o', ho', h1, h2⟩ | ⟨rfl, rfl, rfl⟩)
            · exact ⟨o', List.mem_append_left _ ho', h1, h2⟩
            · exact ⟨(t, r, AWPQOp.inc e a),
                List.mem_append_right _ (by simp), rfl, rfl⟩
          · rintro ⟨o', ho', h1, h2⟩
            rcases List.mem_append.mp ho' with h | h
            · exact Or.inl ⟨o', h, h1, h2⟩
            · simp at h
              subst h
              simp only at h1 h2
              injection h1 with h3 h4
              subst h3
              subst h4
              exact Or.inr ⟨h2.symm, rfl, rfl⟩

/-! ## LWW and FWW registers: last/first write, under monotone stamps

The registers arbitrate by TIMESTAMP, not program order; the two coincide
exactly when stamps increase along the history — the sequential Lamport
condition. Under it LWW reads the LAST write and FWW the FIRST:
program-order register semantics recovered from payload arbitration. -/

/-- Stamps strictly increase along the history (sequential Lamport). -/
def stampsMono {A : Type} (ρ : List (Op A)) : Prop :=
  ρ.Pairwise (fun a b => a.1 < b.1)

/-- `Lex` on write/claim triples compares stamps first. -/
theorem lex_lt_of_ts {w₁ w₂ : Lex (ℕ × Lex (ℕ × ℕ))}
    (h : (ofLex w₁).1 < (ofLex w₂).1) : w₁ < w₂ := by
  show toLex (ofLex w₁) < toLex (ofLex w₂)
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-- The LWW state, at its underlying semilattice type. -/
def lwwSt (s : LWW.State) : LWWState := s

/-- The value view of the LWW state. -/
def lwwView (s : LWWState) : Option ℕ :=
  s.map fun w => (ofLex (ofLex w).2).2

/-- The naive last-write register program. -/
def lwwSpecFold (ρ : List (Op LWWOp)) : Option ℕ :=
  ρ.foldl (fun _ o => some (lwwVal o)) none

theorem lwwSpecFold_snoc (ρ : List (Op LWWOp)) (o : Op LWWOp) :
    lwwSpecFold (ρ ++ [o]) = some (lwwVal o) := by
  unfold lwwSpecFold
  rw [List.foldl_append]
  rfl

/-- The LWW fold sits strictly below any write whose stamp exceeds the
whole history's. -/
theorem lww_fold_lt (ρ : List (Op LWWOp)) (w : LWWWrite)
    (h : ∀ o' ∈ ρ, o'.1 < (ofLex w).1) :
    lwwSt (seqFold LWW ρ) < (w : LWWState) := by
  induction ρ using List.reverseRecOn with
  | nil => exact WithBot.bot_lt_coe w
  | append_singleton ρ o ih =>
      rw [seqFold_snoc]
      show max (lwwSt (seqFold LWW ρ)) ↑(lwwWrite o) < (w : LWWState)
      refine max_lt (ih fun o' ho' => h o' (List.mem_append_left _ ho')) ?_
      rw [WithBot.coe_lt_coe]
      exact lex_lt_of_ts (h o (List.mem_append_right _ (by simp)))

/-- **LWW, sequentially = a last-write register** (under monotone
stamps: the arbitration key agrees with program order). -/
theorem lww_seq_sound (ρ : List (Op LWWOp)) (hmono : stampsMono ρ) :
    lwwView (lwwSt (seqFold LWW ρ)) = lwwSpecFold ρ := by
  induction ρ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ρ o ih =>
      rw [seqFold_snoc, lwwSpecFold_snoc]
      have hcross := (List.pairwise_append.mp hmono).2.2
      have hlt : lwwSt (seqFold LWW ρ) < (lwwWrite o : LWWState) :=
        lww_fold_lt ρ (lwwWrite o)
          (fun o' ho' => hcross o' ho' o (by simp))
      show lwwView (max (lwwSt (seqFold LWW ρ)) ↑(lwwWrite o)) = _
      rw [max_eq_right (le_of_lt hlt)]
      rfl

/-- The FWW state, at its underlying semilattice type. -/
def fwwSt (s : FWW.State) : FWWState := s

/-- The (stamp, value) view of the FWW state. -/
def fwwView : FWWState → Option (ℕ × ℕ)
  | none => none
  | some w => some ((ofLex w).1, (ofLex (ofLex w).2).2)

/-- The naive first-write register program. -/
def fwwSpecFold (ρ : List (Op FWWOp)) : Option (ℕ × ℕ) :=
  ρ.foldl
    (fun a o => match a with
      | none => some (o.1, fwwVal o)
      | some p => some p) none

theorem fwwSpecFold_snoc (ρ : List (Op FWWOp)) (o : Op FWWOp) :
    fwwSpecFold (ρ ++ [o]) =
      match fwwSpecFold ρ with
      | none => some (o.1, fwwVal o)
      | some p => some p := by
  unfold fwwSpecFold
  rw [List.foldl_append]
  rfl

/-- The first-write program only reports stamps of history members. -/
theorem fwwSpec_stamp_mem (ρ : List (Op FWWOp)) (t v : ℕ)
    (h : fwwSpecFold ρ = some (t, v)) : ∃ o' ∈ ρ, o'.1 = t := by
  induction ρ using List.reverseRecOn with
  | nil => simp [fwwSpecFold] at h
  | append_singleton ρ o ih =>
      rw [fwwSpecFold_snoc] at h
      cases hsp : fwwSpecFold ρ with
      | none =>
          rw [hsp] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨o, List.mem_append_right _ (by simp), h.1⟩
      | some p =>
          rw [hsp] at h
          simp only [Option.some.injEq] at h
          obtain ⟨o', ho', h1⟩ := ih (by rw [hsp, h])
          exact ⟨o', List.mem_append_left _ ho', h1⟩

theorem fwwView_eq_none {s : FWWState} (h : fwwView s = none) : s = ⊤ := by
  cases s with
  | none => rfl
  | some w => simp [fwwView] at h

theorem fwwView_eq_some {s : FWWState} {p : ℕ × ℕ}
    (h : fwwView s = some p) :
    ∃ w : FWWClaim, s = ↑w ∧ ((ofLex w).1, (ofLex (ofLex w).2).2) = p := by
  cases s with
  | none => simp [fwwView] at h
  | some w => exact ⟨w, rfl, by simpa [fwwView] using h⟩

/-- **FWW, sequentially = a first-write register** (under monotone
stamps: every later claim loses the `min`). -/
theorem fww_seq_sound (ρ : List (Op FWWOp)) (hmono : stampsMono ρ) :
    fwwView (fwwSt (seqFold FWW ρ)) = fwwSpecFold ρ := by
  induction ρ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ρ o ih =>
      have hmono' := (List.pairwise_append.mp hmono).1
      have hcross := (List.pairwise_append.mp hmono).2.2
      rw [seqFold_snoc, fwwSpecFold_snoc]
      show fwwView (min (fwwSt (seqFold FWW ρ)) ↑(fwwClaim o)) = _
      cases hsp : fwwSpecFold ρ with
      | none =>
          have hfold := fwwView_eq_none ((ih hmono').trans hsp)
          rw [hfold, min_eq_right (le_top (α := FWWState))]
          rfl
      | some p =>
          obtain ⟨w, hf, hpair⟩ := fwwView_eq_some ((ih hmono').trans hsp)
          obtain ⟨o', ho', ho't⟩ := fwwSpec_stamp_mem ρ p.1 p.2 hsp
          have hlt : w < fwwClaim o := by
            apply lex_lt_of_ts
            show (ofLex w).1 < o.1
            rw [congrArg Prod.fst hpair, ← ho't]
            exact hcross o' ho' o (by simp)
          rw [hf, min_eq_left (le_of_lt (WithTop.coe_lt_coe.mpr hlt))]
          rw [show fwwView ((w : FWWClaim) : FWWState) =
              some ((ofLex w).1, (ofLex (ofLex w).2).2) from rfl, hpair]

end Sal.ConditionedMRDTs
