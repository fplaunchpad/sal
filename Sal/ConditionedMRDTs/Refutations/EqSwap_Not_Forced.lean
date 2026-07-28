import Sal.ConditionedMRDTs.Metatheory.ConverseEq

/-!
# Refutations: vc:comm+vc:inv are NOT forced, vc:disc is EXTRA

The load-bearing results of the conditioned converse.

## `eqswap_not_forced` (datatype RESET): vc:comm+vc:inv are not forced

RESET is a write/reset log: `write v` appends `v`, `reset` erases the log to a
sentinel `Z`, `read` is the last element, `eqObs` compares reads, `Inv = app = ⊤`.
Events `oa = write A`, `ob = write B` are concurrent; `oc = reset` sees both.
`oc` is the add-remove absorber: it does not `eqObs`-commute with `oa` or `ob` (a
write before a reset is erased, one after survives), so it is a legitimate
`loOnEq` absorber of the `oa → ob` rc-edge and carries the vis-arm edges
`oa → oc`, `ob → oc`.

In `ev = {oa, ob, oc}` the pair `(oa, ob)` is therefore `loOnEq`-incomparable and
non-maximal (both order before `oc`). RESET is convergent up to `eqObs` on `ev`
(both extensions `[oa,ob,oc]`, `[ob,oa,oc]` reset to `Z`), so it satisfies the
conditioned-RA-lin hypothesis (`ConvergesEq`); yet the swap oracle
`EqSwap(oa, ob, init)` is owed (incomparable, both enabled at the empty prefix)
and FAILS: `read [oa,ob] = B ≠ A = read [ob,oa]`. So vc:comm and vc:inv are not
forced by conditioned RA-lin: they are a sufficient device strictly stronger than
the convergence RA-lin actually forces.

## `vc_disc_extra` (datatype GSET, two invariants)

The grow-only set with `eqObs = =` converges regardless of `Inv` (folds are
order-independent). Under `Inv₁ = ⊤` the vc:disc preservation clause is green;
under `Inv₂ = (2 ∉ s)` it reddens at `add 2` (applicable, `Inv₂` holds,
`Inv₂(s ∪ {2})` false). Same datatype, same RA-lin verdict, different vc:disc
verdict: vc:disc's universal preservation is EXTRA, a property of the chosen `Inv`.

Every expected value is hand-derived (see the block comments); the RESET
convergence + EqSwap-failure and the two-Inv green/red are the SPOT pins.
-/

namespace Sal.ConditionedMRDTs.Refutations.EqSwapNotForced

open Sal.Emulation
open Sal.ConditionedMRDTs
open Sal.ConditionedMRDTs.GenericEqQuotient

/-! ## §1. The RESET datatype -/

/-- The value alphabet: `A`, `B`, and the reset sentinel `Z`. -/
inductive RVal | A | B | Z
  deriving DecidableEq, Repr

/-- The op alphabet: `write v` (append `v`) and `reset` (erase to `[Z]`). -/
inductive RAppOp | wr (v : RVal) | rst
  deriving DecidableEq, Repr

/-- `read`: the last element of the log (append-order sensitive). -/
def reset_read : List RVal → Option RVal
  | [] => none
  | [v] => some v
  | _ :: rest => reset_read rest

/-- `do`: `write v` appends, `reset` overwrites the log with the sentinel. -/
def reset_do (s : List RVal) (o : Op RAppOp) : List RVal :=
  match o.2.2 with
  | RAppOp.wr v => s ++ [v]
  | RAppOp.rst => [RVal.Z]

/-- `eqObs`: two logs are observationally equal iff they read the same. -/
def reset_eqv (s t : List RVal) : Prop := reset_read s = reset_read t

theorem reset_eqv_refl : ∀ s, reset_eqv s s := fun _ => rfl
theorem reset_eqv_symm : ∀ {s t}, reset_eqv s t → reset_eqv t s := fun h => h.symm
theorem reset_eqv_trans : ∀ {s t u}, reset_eqv s t → reset_eqv t u → reset_eqv s u :=
  fun h₁ h₂ => h₁.trans h₂

/-- `rc`: concurrent ops resolve deterministically by timestamp (smaller = `Fst`). -/
def reset_rc (o₁ o₂ : Op RAppOp) : RcRes :=
  if o₁.1 < o₂.1 then RcRes.Fst_then_snd else RcRes.Snd_then_fst

/-- The RESET conditioned signature. `Inv = applicable = ⊤`; `mergeL` unused by the
refutation (pinned to a total function). -/
def RESET : ConditionedMRDTSig where
  toMRDTSig :=
    { State := List RVal
      dec_state := inferInstance
      init := []
      AppOp := RAppOp
      dec_op := inferInstance
      Query := Unit
      Value := Option RVal
      update := reset_do
      merge := fun a _ => a
      query := fun s _ => reset_read s
      rc := reset_rc
      mergeL := fun _ a _ => a
      merge_init_slice := fun _ _ => rfl }
  Inv := fun _ => True
  applicable := fun _ _ => True

@[simp] theorem RESET_update (s : List RVal) (o : Op RAppOp) :
    RESET.update s o = reset_do s o := rfl
@[simp] theorem RESET_init : RESET.init = [] := rfl
@[simp] theorem RESET_rc (o₁ o₂ : Op RAppOp) : RESET.rc o₁ o₂ = reset_rc o₁ o₂ := rfl
@[simp] theorem RESET_Inv (s : List RVal) : RESET.Inv s ↔ True := Iff.rfl

/-- The observational equivalence supplied by RESET. -/
def RE : EqEquiv RESET := ⟨reset_eqv, ⟨reset_eqv_refl, reset_eqv_symm, reset_eqv_trans⟩⟩

@[simp] theorem RE_eqv (s t : List RVal) : RE.eqv s t ↔ reset_eqv s t := Iff.rfl

/-- The trivial wellformedness guard (RESET applies every op). -/
def RW : Op RAppOp → List RVal → Prop := fun _ _ => True

/-- `doW` at the trivial guard is the raw update. -/
@[simp] theorem reset_doW (o : Op RAppOp) (s : List RVal) :
    doW RESET RW o s = reset_do s o := if_pos trivial

/-! ### The witness events and visibility

`oa = write A` (ts 1), `ob = write B` (ts 2), `oc = reset` (ts 3); `oa → oc`,
`ob → oc`, `oa ∥ ob`. -/

def oa : Op RAppOp := (1, 0, RAppOp.wr RVal.A)
def ob : Op RAppOp := (2, 1, RAppOp.wr RVal.B)
def oc : Op RAppOp := (3, 2, RAppOp.rst)

/-- Visibility: `oa → oc` and `ob → oc` only. -/
def reset_vis (x y : Op RAppOp) : Prop := (x = oa ∧ y = oc) ∨ (x = ob ∧ y = oc)

/-- The witness event set. -/
def evABC : Set (Op RAppOp) := {oa, ob, oc}

/-! ### Vis facts (hand-derived from the DAG) -/

theorem vis_oa_oc : reset_vis oa oc := Or.inl ⟨rfl, rfl⟩
theorem vis_ob_oc : reset_vis ob oc := Or.inr ⟨rfl, rfl⟩

theorem not_vis_oa_ob : ¬ reset_vis oa ob := by
  rintro (⟨_, h⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)
theorem not_vis_ob_oa : ¬ reset_vis ob oa := by
  rintro (⟨h, _⟩ | ⟨_, h⟩) <;> exact absurd h (by decide)
theorem not_vis_oc_oa : ¬ reset_vis oc oa := by
  rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)
theorem not_vis_oc_ob : ¬ reset_vis oc ob := by
  rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)
theorem not_vis_ob_ob : ¬ reset_vis ob ob := by
  rintro (⟨h, _⟩ | ⟨_, h⟩) <;> exact absurd h (by decide)
theorem not_vis_oa_oa : ¬ reset_vis oa oa := by
  rintro (⟨_, h⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)

/-! ### The `¬ eqCommutesOn` facts: the absorber does not `eqObs`-commute

Each is refuted at `s = init = []` by a single hand-derived read mismatch. -/

/-- `oa, ob` do NOT `eqObs`-commute: `read [A,B] = B ≠ A = read [B,A]`. -/
theorem not_eqComm_oa_ob : ¬ eqCommutesOn RE RW oa ob := by
  intro h
  have h0 := h [] trivial
  simp only [reset_doW, oa, ob, reset_do, reset_read, RE_eqv, reset_eqv] at h0
  exact absurd h0 (by decide)

/-- `oa, oc` do NOT `eqObs`-commute: `read (reset [A]) = Z ≠ A = read ([Z] ++ [A])`. -/
theorem not_eqComm_oa_oc : ¬ eqCommutesOn RE RW oa oc := by
  intro h
  have h0 := h [] trivial
  simp only [reset_doW, oa, oc, reset_do, reset_read, RE_eqv, reset_eqv] at h0
  exact absurd h0 (by decide)

/-- `ob, oc` do NOT `eqObs`-commute: `read (reset [B]) = Z ≠ B = read ([Z] ++ [B])`. -/
theorem not_eqComm_ob_oc : ¬ eqCommutesOn RE RW ob oc := by
  intro h
  have h0 := h [] trivial
  simp only [reset_doW, ob, oc, reset_do, reset_read, RE_eqv, reset_eqv] at h0
  exact absurd h0 (by decide)

/-! ### The `loOnEq` edges and non-edges in `ev = {oa, ob, oc}` -/

/-- `oa → oc` (vis arm): visible and non-commuting. -/
theorem loOnEq_oa_oc : loOnEq RE RW reset_vis evABC oa oc :=
  Or.inl ⟨vis_oa_oc, not_eqComm_oa_oc⟩

/-- `ob → oc` (vis arm): visible and non-commuting. -/
theorem loOnEq_ob_oc : loOnEq RE RW reset_vis evABC ob oc :=
  Or.inl ⟨vis_ob_oc, not_eqComm_ob_oc⟩

/-- `oa ∥ ob`: NO `oa → ob` edge, the rc-edge is absorbed by `oc`
(a vis-noncommuting successor of `ob`). This is the crux: the absorber cancels the
rc-edge in the larger set. -/
theorem not_loOnEq_oa_ob : ¬ loOnEq RE RW reset_vis evABC oa ob := by
  rintro (⟨hv, _⟩ | ⟨_, _, _, hnabs⟩)
  · exact not_vis_oa_ob hv
  · exact hnabs ⟨oc, by right; right; rfl, vis_ob_oc, not_eqComm_ob_oc⟩

/-- No `ob → oa` edge: `rc ob oa = Snd_then_fst ≠ Fst_then_snd`. -/
theorem not_loOnEq_ob_oa : ¬ loOnEq RE RW reset_vis evABC ob oa := by
  rintro (⟨hv, _⟩ | ⟨_, _, hrc, _⟩)
  · exact not_vis_ob_oa hv
  · simp only [RESET_rc] at hrc; exact absurd hrc (by decide)

/-- No `oc → oa` edge: `oa → oc` blocks the rc arm's `¬ vis oa oc` conjunct. -/
theorem not_loOnEq_oc_oa : ¬ loOnEq RE RW reset_vis evABC oc oa := by
  rintro (⟨hv, _⟩ | ⟨_, hnv2, _, _⟩)
  · exact not_vis_oc_oa hv
  · exact hnv2 vis_oa_oc

/-- No `oc → ob` edge: `ob → oc` blocks the rc arm's `¬ vis ob oc` conjunct. -/
theorem not_loOnEq_oc_ob : ¬ loOnEq RE RW reset_vis evABC oc ob := by
  rintro (⟨hv, _⟩ | ⟨_, hnv2, _, _⟩)
  · exact not_vis_oc_ob hv
  · exact hnv2 vis_ob_oc

/-! ### Membership helpers -/

theorem mem_oa : oa ∈ evABC := by left; rfl
theorem mem_ob : ob ∈ evABC := by right; left; rfl
theorem mem_oc : oc ∈ evABC := by right; right; rfl

theorem evABC_cases {x : Op RAppOp} (hx : x ∈ evABC) : x = oa ∨ x = ob ∨ x = oc := by
  simpa [evABC, Set.mem_insert_iff, Set.mem_singleton_iff] using hx

/-! ## §2. Convergence up to `eqObs` on `ev = {oa, ob, oc}` (the RA-lin content)

Any `loOnEq(ev)`-respecting enumeration of `{oa, ob, oc}` ends in `oc` (both `oa`
and `ob` `loOnEq`-precede it), so its raw fold is `reset [·] = [Z]`; hence all
folds read `Z` and the canonical class is single-valued up to `eqObs`. -/

/-- Any respecting enumeration of `ev` folds to `[Z]` (it ends in `oc = reset`). -/
theorem fold_reset {ρ : List (Op RAppOp)}
    (hp : listPermOf ρ evABC)
    (hr : respects ρ (loOnEq RE RW reset_vis evABC)) :
    applySeq RESET.toCRDTSig RESET.init ρ = [RVal.Z] := by
  have hCmem : oc ∈ ρ := (hp.2 oc).mpr mem_oc
  rcases List.eq_nil_or_concat ρ with rfl | ⟨ρ', e, rfl⟩
  · exact absurd hCmem List.not_mem_nil
  · rw [List.concat_eq_append] at hCmem hr ⊢
    have hmax := last_is_maximal hr
    have he_cases : e = oa ∨ e = ob ∨ e = oc :=
      evABC_cases ((hp.2 e).mp (by rw [List.concat_eq_append]; simp))
    have hmem_oc' : oc ∈ ρ' ∨ oc ∈ [e] := List.mem_append.mp hCmem
    have he_eq : e = oc := by
      rcases he_cases with rfl | rfl | rfl
      · rcases hmem_oc' with h | h
        · exact absurd loOnEq_oa_oc (hmax oc h)
        · exact absurd (List.mem_singleton.mp h) (by decide)
      · rcases hmem_oc' with h | h
        · exact absurd loOnEq_ob_oc (hmax oc h)
        · exact absurd (List.mem_singleton.mp h) (by decide)
      · rfl
    rw [he_eq, applySeq_append_single]
    rfl

/-- **RESET converges up to `eqObs` on `{oa, ob, oc}`**: the canonical class is
single-valued (every respecting fold reads `Z`). This is the conditioned-RA-lin
hypothesis `ConvergesEq` satisfied at the witness set. -/
theorem reset_converges : ConvergesEq RE RW reset_vis evABC := by
  rintro s s' ⟨ρ, hp, hr, hf⟩ ⟨ρ', hp', hr', hf'⟩
  have e1 : applySeq RESET.toCRDTSig RESET.init ρ = [RVal.Z] := fold_reset hp hr
  have e2 : applySeq RESET.toCRDTSig RESET.init ρ' = [RVal.Z] := fold_reset hp' hr'
  have hf2 : reset_eqv [RVal.Z] s := by rw [← e1]; exact hf
  have hf2' : reset_eqv [RVal.Z] s' := by rw [← e2]; exact hf'
  exact reset_eqv_trans (reset_eqv_symm hf2) hf2'

/-! ## §3. The swap oracle FAILS (vc:comm + vc:inv not forced) -/

/-- `EqSwap(oa, ob, init)` FAILS: `read [A,B] = B ≠ A = read [B,A]`. -/
theorem reset_eqSwap_fails : ¬ EqSwap RE oa ob RESET.init := by
  intro h
  simp only [EqSwap, RESET_update, RESET_init, oa, ob, reset_do, reset_read,
    RE_eqv, reset_eqv] at h
  exact absurd h (by decide)

/-- No event of `ev` `loOnEq`-precedes `oa`: `oa` is enabled at every prefix. -/
theorem no_pred_oa {z : Op RAppOp} (hz : z ∈ evABC) (hzne : z ≠ oa) :
    ¬ loOnEq RE RW reset_vis evABC z oa := by
  rcases evABC_cases hz with rfl | rfl | rfl
  · exact absurd rfl hzne
  · exact not_loOnEq_ob_oa
  · exact not_loOnEq_oc_oa

/-- No event of `ev` `loOnEq`-precedes `ob`: `ob` is enabled at every prefix. -/
theorem no_pred_ob {z : Op RAppOp} (hz : z ∈ evABC) (hzne : z ≠ ob) :
    ¬ loOnEq RE RW reset_vis evABC z ob := by
  rcases evABC_cases hz with rfl | rfl | rfl
  · exact not_loOnEq_oa_ob
  · exact absurd rfl hzne
  · exact not_loOnEq_oc_ob

/-- **The swap oracle is not satisfied.** At the incomparable pair `(oa, ob)`,
both enabled at the empty prefix, the oracle would supply `EqSwap(oa, ob, init)`,
which fails. -/
theorem reset_not_eqSwapOracle : ¬ EqSwapOracle RE RW reset_vis evABC := by
  intro hO
  have hswap := hO oa ob [] mem_oa mem_ob (by decide)
    not_loOnEq_oa_ob not_loOnEq_ob_oa
    List.nodup_nil (fun x hx => absurd hx List.not_mem_nil) List.Pairwise.nil
    (fun z hz hzne hlo => absurd hlo (no_pred_oa hz hzne))
    (fun z hz hzne hlo => absurd hlo (no_pred_ob hz hzne))
  rw [show applySeq RESET.toCRDTSig RESET.init [] = RESET.init from rfl] at hswap
  exact reset_eqSwap_fails hswap

/-! ## §4. The vc:comm+vc:inv refutation -/

/-- **`eqswap_not_forced`.** There is a conditioned datatype (RESET) and an event
set on which the convergence-up-to-`eqObs` content of conditioned RA-lin holds
(`ConvergesEq`) yet the swap oracle vc:comm+vc:inv fails (`¬ EqSwapOracle`). So
vc:comm and vc:inv are NOT forced by conditioned RA-lin; they are a sufficient
device strictly stronger than the convergence it forces. -/
theorem eqswap_not_forced :
    ∃ (D : ConditionedMRDTSig) (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
      (vis : Op D.AppOp → Op D.AppOp → Prop) (ev : Set (Op D.AppOp)),
      ConvergesEq E W vis ev ∧ ¬ EqSwapOracle E W vis ev :=
  ⟨RESET, RE, RW, reset_vis, evABC, reset_converges, reset_not_eqSwapOracle⟩

/-! ### SPOT pins (PASS + FAIL, hand-derived) -/

/-- PASS pin: the τ-burdened equality convergence gives
`fold [oa,ob,oc] ≈ fold [ob,oa,oc]` (append `oc` reconciles), both reading `Z`. -/
theorem reset_tau_reconciles :
    reset_eqv (applySeq RESET.toCRDTSig RESET.init [oa, ob, oc])
      (applySeq RESET.toCRDTSig RESET.init [ob, oa, oc]) := by
  unfold reset_eqv; decide
/-- PASS pin: both witness linearizations fold to `[Z]` (read `Z`). -/
theorem reset_fold_abc : applySeq RESET.toCRDTSig RESET.init [oa, ob, oc] = [RVal.Z] := by decide
theorem reset_fold_bac : applySeq RESET.toCRDTSig RESET.init [ob, oa, oc] = [RVal.Z] := by decide
/-- FAIL pin: the LOCAL swap does not reconcile, `[oa,ob]` reads `B`,
`[ob,oa]` reads `A`, so `EqSwap(oa,ob,init)` fails. -/
theorem reset_fold_ab : applySeq RESET.toCRDTSig RESET.init [oa, ob] = [RVal.A, RVal.B] := by decide
theorem reset_fold_ba : applySeq RESET.toCRDTSig RESET.init [ob, oa] = [RVal.B, RVal.A] := by decide
theorem reset_read_ab_ne_ba :
    reset_read [RVal.A, RVal.B] ≠ reset_read [RVal.B, RVal.A] := by decide

/-- PASS pin: the antitone contrast, in `ev' = {oa, ob}` (no absorber) the edge
`oa → ob` IS present via the rc arm. The pair is incomparable only once `oc`
enlarges the set. -/
theorem loOnEq_oa_ob_small : loOnEq RE RW reset_vis ({oa, ob} : Set (Op RAppOp)) oa ob := by
  refine Or.inr ⟨not_vis_oa_ob, not_vis_ob_oa, ?_, ?_⟩
  · simp only [RESET_rc]; decide
  · rintro ⟨e₃, he₃, hv, _⟩
    rcases (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using he₃ :
        e₃ = oa ∨ e₃ = ob) with rfl | rfl
    · exact not_vis_ob_oa hv
    · exact not_vis_ob_ob hv

/-! ## §5. The GSET datatype (grow-only set) -/

/-- The grow-only set base signature: state `Set ℕ`, `update` inserts the op's
element, `mergeL` is union, `rc = Either`. `noncomputable` (classical `Set ℕ`
equality). -/
noncomputable def gsetMR : MRDTSig where
  State := Set Nat
  dec_state := fun a b => Classical.propDecidable (a = b)
  init := (∅ : Set Nat)
  AppOp := Nat
  dec_op := inferInstance
  Query := Unit
  Value := Set Nat
  update := fun s o => insert o.2.2 s
  merge := fun a b => a ∪ b
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun _ a b => a ∪ b
  merge_init_slice := fun _ _ => rfl

/-- GSET under the trivial invariant `Inv₁ = ⊤`. -/
noncomputable def GS1 : ConditionedMRDTSig where
  toMRDTSig := gsetMR
  Inv := fun _ => True
  applicable := fun _ _ => True

/-- The poison-free invariant `Inv₂ = (2 ∉ s)`. -/
def gs2Inv (s : Set Nat) : Prop := (2 : Nat) ∉ s

/-- GSET under `Inv₂ = (2 ∉ s)` (the "poison-free" invariant). -/
noncomputable def GS2 : ConditionedMRDTSig where
  toMRDTSig := gsetMR
  Inv := gs2Inv
  applicable := fun _ _ => True

/-- Both invariants sit over the SAME underlying datatype. -/
theorem gs_same : GS1.toMRDTSig = GS2.toMRDTSig := rfl

/-- The identity observational equivalence for the two GSET conditionings. -/
def EG1 : EqEquiv GS1 := ⟨Eq, eq_equivalence⟩
def EG2 : EqEquiv GS2 := ⟨Eq, eq_equivalence⟩

def WG1 : Op GS1.AppOp → GS1.State → Prop := fun _ _ => True
def WG2 : Op GS2.AppOp → GS2.State → Prop := fun _ _ => True

/-! ### Order-independence of the G-set fold -/

/-- Membership in the insert-fold: `y` is in the fold iff it was in the seed or is
some op's element. -/
theorem mem_foldl_insert (ρ : List (Op Nat)) (s0 : Set Nat) (y : Nat) :
    y ∈ ρ.foldl (fun s o => insert o.2.2 s) s0 ↔ y ∈ s0 ∨ ∃ o ∈ ρ, o.2.2 = y := by
  induction ρ generalizing s0 with
  | nil => simp
  | cons o ρ ih =>
    rw [List.foldl_cons, ih]
    constructor
    · rintro (h | ⟨o', ho', hy⟩)
      · rcases Set.mem_insert_iff.mp h with rfl | h
        · exact Or.inr ⟨o, List.mem_cons_self, rfl⟩
        · exact Or.inl h
      · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', hy⟩
    · rintro (h | ⟨o', ho', hy⟩)
      · exact Or.inl (Set.mem_insert_of_mem _ h)
      · rcases List.mem_cons.mp ho' with rfl | ho'
        · exact Or.inl (hy ▸ Set.mem_insert _ _)
        · exact Or.inr ⟨o', ho', hy⟩

/-- **The G-set fold is order-independent**: two enumerations of the same event
set fold to the same set. -/
theorem gset_fold_perm_eq {ρ ρ' : List (Op Nat)} {ev : Set (Op Nat)}
    (hp : listPermOf ρ ev) (hp' : listPermOf ρ' ev) :
    applySeq gsetMR.toCRDTSig gsetMR.init ρ = applySeq gsetMR.toCRDTSig gsetMR.init ρ' := by
  apply Set.ext
  intro y
  show y ∈ ρ.foldl (fun s o => insert o.2.2 s) ∅
      ↔ y ∈ ρ'.foldl (fun s o => insert o.2.2 s) ∅
  rw [mem_foldl_insert, mem_foldl_insert]
  simp only [Set.mem_empty_iff_false, false_or]
  constructor
  · rintro ⟨o, ho, hy⟩; exact ⟨o, (hp'.2 o).mpr ((hp.2 o).mp ho), hy⟩
  · rintro ⟨o, ho, hy⟩; exact ⟨o, (hp.2 o).mpr ((hp'.2 o).mp ho), hy⟩

/-- **GSET converges up to `=` under `Inv₁`, for any config.** Since folds are
order-independent, the canonical class is single-valued regardless of `Inv`. -/
theorem gs1_converges (vis : Op GS1.AppOp → Op GS1.AppOp → Prop)
    (ev : Set (Op GS1.AppOp)) : ConvergesEq EG1 WG1 vis ev := by
  rintro s s' ⟨ρ, hp, _, hf⟩ ⟨ρ', hp', _, hf'⟩
  have hf2 : applySeq GS1.toCRDTSig GS1.init ρ = s := hf
  have hf2' : applySeq GS1.toCRDTSig GS1.init ρ' = s' := hf'
  show s = s'
  rw [← hf2, ← hf2']
  exact gset_fold_perm_eq hp hp'

/-- **GSET converges up to `=` under `Inv₂`, for any config**: the SAME verdict
as under `Inv₁` (order-independence does not read `Inv`). -/
theorem gs2_converges (vis : Op GS2.AppOp → Op GS2.AppOp → Prop)
    (ev : Set (Op GS2.AppOp)) : ConvergesEq EG2 WG2 vis ev := by
  rintro s s' ⟨ρ, hp, _, hf⟩ ⟨ρ', hp', _, hf'⟩
  have hf2 : applySeq GS2.toCRDTSig GS2.init ρ = s := hf
  have hf2' : applySeq GS2.toCRDTSig GS2.init ρ' = s' := hf'
  show s = s'
  rw [← hf2, ← hf2']
  exact gset_fold_perm_eq hp hp'

/-! ### The vc:disc separation -/

/-- **vc:disc is GREEN under `Inv₁ = ⊤`**: preservation is vacuous. -/
theorem gs1_discipline : Discipline GS1 := ⟨trivial, fun _ _ _ _ => trivial⟩

/-- The poison op `add 2`. -/
def op_poison : Op Nat := (9, 0, 2)

/-- **vc:disc is RED under `Inv₂ = (2 ∉ s)`**: preservation FAILS at `add 2`
(applicable, `Inv₂ ∅` holds, `Inv₂ (∅ ∪ {2})` false). Hand-derived: `2 ∈ {2}`. -/
theorem gs2_not_discipline : ¬ Discipline GS2 := by
  rintro ⟨_, hpres⟩
  have hbad : GS2.Inv (GS2.update (∅ : Set Nat) op_poison) :=
    hpres (∅ : Set Nat) op_poison (Set.notMem_empty 2) trivial
  exact hbad (Set.mem_insert 2 ∅)

/-! ## §6. The vc:disc refutation -/

/-- **`vc_disc_extra`.** One datatype (GSET), one RA-lin verdict (`ConvergesEq`
under both invariants), two `Inv` choices: vc:disc is green under `Inv₁` and red
under `Inv₂`. So vc:disc's universal `Inv`-preservation clause is EXTRA, a property
of the datatype's chosen `Inv`, not forced by RA-lin (the failure is off the
reachable-canonical domain). -/
theorem vc_disc_extra :
    ∃ (D₁ D₂ : ConditionedMRDTSig) (E₁ : EqEquiv D₁) (E₂ : EqEquiv D₂)
      (W₁ : Op D₁.AppOp → D₁.State → Prop) (W₂ : Op D₂.AppOp → D₂.State → Prop),
      D₁.toMRDTSig = D₂.toMRDTSig ∧
      (∀ vis ev, ConvergesEq E₁ W₁ vis ev) ∧
      (∀ vis ev, ConvergesEq E₂ W₂ vis ev) ∧
      Discipline D₁ ∧ ¬ Discipline D₂ :=
  ⟨GS1, GS2, EG1, EG2, WG1, WG2, gs_same, gs1_converges, gs2_converges,
    gs1_discipline, gs2_not_discipline⟩

/-! ## §7. Axiom audit -/

#print axioms eqswap_not_forced
#print axioms vc_disc_extra
#print axioms reset_not_eqSwapOracle
#print axioms reset_converges

end Sal.ConditionedMRDTs.Refutations.EqSwapNotForced
