import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_CanonFoldOK

/-!
# K1 — the delta discipline: `CanonFoldOK ρ₀ (fold ρ₀) π₀` from the generation discipline

*Additive; modifies no existing file; 0 `sorry`.*

The corrected skeleton's K1 leaf (`RGA_Skeleton2.hEnum`, conjunct 4): the delta enumeration `π₀`
satisfies the per-event canonical discipline CONTINUED FROM the LCA fold.  The engine's own
`canonStepOK_of_gen` cannot be applied verbatim: its `GoodEnum (F ++ [o])` interface threads the
application prefix's `loOnA`-respect, and the LCA enum `ρ₀` (an NF canonical-state witness) is only
`loOnEq`-respecting — its internal order is adversarial.

**The fix (this file): the prefix's ORDER is irrelevant; only its set and its fold matter.**
* Every order-sensitive ingredient is re-based on a FREELY CHOSEN `loOnA`-respecting enumeration
  `U'` of the whole event set: dependency prefixes are carved from `U'` (`depList Cfg E U' w`), so
  `isDepPreC_depList`, `chain_entries_mem` and the engine `canonFoldOK_of_gen` apply to them
  verbatim.
* The application prefix `F = ρ₀ ++ π₀-consumed` enters only through `CanonInv F (fold F)`
  (maintained incrementally, order-free) and SET-inclusions — exactly what the §5 transports
  (`anc_transport`, `chainOK_transport`) consume.
* `loOnA ⊆ vis` for the RGA (`rc = Either` kills `loOnC`'s concurrent arm), so `DepC` is
  irreflexive and dependency chains from delta ops never cross back out of the delta
  (used by the closure bookkeeping).

Main results:
* `canonStepOK_delta` — `CanonStepOK F (fold F) o` for any dep-closed, `CanonInv`-carrying prefix
  set `F` (no order hypothesis on `F`).
* `canonFoldOK_delta` — **K1**: `CanonFoldOK ρ₀ (fold ρ₀) π₀`, given the LCA's own discipline
  (`CanonFoldOK [] init ρ₀` — from the noopFeasible engine route), dependency closure of the LCA
  set, and per-position dependency closure of `π₀` (`hδdeps`; its discharge from
  `respects π₀ (loOnA …)` + branch closures is the follow-up step).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open Classical

namespace Sal.ConditionedMRDTs.RGAK1Delta

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.RGASig (RGACondSig rc_is_Either)
open Sal.ConditionedMRDTs (loOnC)
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA appliesDependsOn)
open RGAMergeLinearization (applySeqR applySeqR_cons)
open RGACanonConvergence
open Sal.ConditionedMRDTs.RGACanonFoldOK

/-! ## §1  `loOnA ⊆ vis` for the RGA, and `DepC` facts -/

/-- `loOnC ⊆ vis` for the RGA: the concurrent arm requires `rc = Fst_then_snd`, but
`(RGACondSig α).rc ≡ Either`. -/
theorem loOnC_imp_vis (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (ev : Set (op_t α)) (e₁ e₂ : op_t α) (h : loOnC (RGACondSig α) Cfg ev e₁ e₂) : Cfg.vis e₁ e₂ := by
  rcases h with ⟨hv, _⟩ | ⟨_, _, hrc, _⟩
  · exact hv
  · rw [rc_is_Either] at hrc
    exact absurd hrc (fun h => Sal.Emulation.RcRes.noConfusion h)

/-- `loOnA ⊆ vis` for the RGA. -/
theorem loOnA_imp_vis (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (ev : Set (op_t α)) (e₁ e₂ : op_t α) (h : loOnA (RGACondSig α) Cfg ev e₁ e₂) : Cfg.vis e₁ e₂ := by
  rcases h with h | ⟨hv, _⟩
  · exact loOnC_imp_vis Cfg ev e₁ e₂ h
  · exact hv

/-- A dependency edge is a `vis` edge. -/
theorem depE_imp_vis (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (z x : op_t α) (h : DepE Cfg E z x) : Cfg.vis z x :=
  loOnA_imp_vis Cfg E z x h.2

/-- Transitive dependency stays inside the causal order. -/
theorem depC_imp_vis (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (z x : op_t α) (h : DepC Cfg E z x) : Cfg.vis z x := by
  induction h with
  | single hzx => exact depE_imp_vis Cfg E _ _ hzx
  | tail _ hbc ih => exact htr ih (depE_imp_vis Cfg E _ _ hbc)

/-- `DepC` is irreflexive (via `vis` strictness). -/
theorem depC_irrefl (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a) (o : op_t α) : ¬ DepC Cfg E o o :=
  fun h => hirr o (depC_imp_vis Cfg E htr o o h)

/-! ## §2  The freely-chosen ambient enumeration and its dep-lists -/

/-- A full `loOnA`-respecting enumeration of `E` is a `GoodEnum` (closure is vacuous). -/
theorem goodEnum_of_perm (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (U : List (op_t α)) (hUp : listPermOf U E)
    (hUr : respects U (loOnA (RGACondSig α) Cfg E)) : GoodEnum Cfg E U :=
  ⟨fun x hx => (hUp.2 x).mp hx, hUp.1, hUr, fun _x _hx z hz _ _ => (hUp.2 z).mpr hz⟩

/-- The dep-list of ANY event `o ∈ E`, carved from a full enumeration `U`, is a `GoodEnum`:
the `loOnA`-predecessor closure follows from `DepC`-transitivity, with the `z = o` degenerate
case killed by `DepC`-irreflexivity. -/
theorem goodEnum_depList_of_perm (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α))
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (U : List (op_t α)) (hUp : listPermOf U E)
    (hUr : respects U (loOnA (RGACondSig α) Cfg E)) (o : op_t α) :
    GoodEnum Cfg E (depList Cfg E U o) := by
  have hgU := goodEnum_of_perm Cfg E U hUp hUr
  refine ⟨fun x hx => hgU.1 x (mem_depList.mp hx).1,
          hgU.2.1.filter _,
          List.Pairwise.sublist (List.filter_sublist) hgU.2.2.1,
          ?_⟩
  intro x hx z hz hzx hlo
  obtain ⟨_hxU, hxo, hxdep⟩ := mem_depList.mp hx
  have hdep : DepC Cfg E z o := Relation.TransGen.head ⟨hz, hlo⟩ hxdep
  have hzo : z ≠ o := by
    rintro rfl
    exact depC_irrefl Cfg E htr hirr z hdep
  exact mem_depList.mpr ⟨(hUp.2 z).mpr hz, hzo, hdep⟩

/-- `IsDepPreC` for the dep-list of any `o`, carved from a full enumeration. -/
theorem isDepPreC_depList_of_perm (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (U : List (op_t α)) (hUp : listPermOf U E)
    (hUr : respects U (loOnA (RGACondSig α) Cfg E)) (o : op_t α) :
    IsDepPreC Cfg E o (depList Cfg E U o) :=
  isDepPreC_depList Cfg E U o (fun x hx => (hUp.2 x).mp hx) hUp.1 hUr
    (fun z hz _ _ => (hUp.2 z).mpr hz)

/-- `CanonInv` at the dep-list's fold: the engine (`canonFoldOK_of_gen`) runs on the carved
`GoodEnum` and `canon_fold` folds it up. -/
theorem canonInv_depList_of_perm (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α))
    (hdts : ∀ a b : op_t α, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2C Cfg E)
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (U : List (op_t α)) (hUp : listPermOf U E)
    (hUr : respects U (loOnA (RGACondSig α) Cfg E)) (o : op_t α) :
    CanonInv (depList Cfg E U o) (applySeqR (init_st (α := α)) (depList Cfg E U o)) := by
  have hOK : CanonFoldOK [] (init_st (α := α)) (depList Cfg E U o) :=
    canonFoldOK_of_gen Cfg E hdts hids0 hGen (depList Cfg E U o).length _ le_rfl
      (goodEnum_depList_of_perm Cfg E htr hirr U hUp hUr o)
  have h := canon_fold (depList Cfg E U o) [] (init_st (α := α)) canonInv_init hOK
  rwa [List.nil_append] at h

/-- Recorded-chain closure of the dep-list: chain entries of a `d`-member are root-or-inserted
in `d` itself (via `chain_entries_mem` at the full enumeration + `DepC`-transitivity). -/
theorem chains_closed_depList_of_perm (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (hGen : GenDisc2C Cfg E)
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (U : List (op_t α)) (hUp : listPermOf U E)
    (hUr : respects U (loOnA (RGACondSig α) Cfg E)) (o : op_t α) :
    ∀ z rz ez az (pz : List ℕ), (z, rz, .Ins ez pz az) ∈ depList Cfg E U o →
      ∀ c ∈ az :: pz, c = 0 ∨ insertedIn (depList Cfg E U o) c := by
  intro z rz ez az pz hm c hc
  obtain ⟨hzU, hzo, hzdep⟩ := mem_depList.mp hm
  rcases chain_entries_mem Cfg E hGen U (goodEnum_of_perm Cfg E U hUp hUr)
      z rz ez az pz hzU c hc with h | h
  · exact Or.inl h
  · refine Or.inr (insertedIn_mono ?_ h)
    intro x hx
    obtain ⟨hxU, _hxz, hxdep⟩ := mem_depList.mp hx
    have hdep : DepC Cfg E x o := Relation.TransGen.trans hxdep hzdep
    have hxo : x ≠ o := by
      rintro rfl
      exact depC_irrefl Cfg E htr hirr _ (Relation.TransGen.trans hxdep hzdep)
    exact mem_depList.mpr ⟨hxU, hxo, hdep⟩

/-! ## §3  The per-step delta discipline — no order hypothesis on the prefix -/

/-- **`canonStepOK_delta`** — the application discipline for `o` at a prefix `F` that carries
`CanonInv` and the dependency closures, with NO order hypothesis on `F`.  Mirror of
`canonStepOK_of_gen` with every dep-list carved from the freely-chosen full enumeration `U`. -/
theorem canonStepOK_delta (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α))
    (hdts : ∀ a b : op_t α, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2C Cfg E)
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (U : List (op_t α)) (hUp : listPermOf U E)
    (hUr : respects U (loOnA (RGACondSig α) Cfg E))
    (F : List (op_t α)) (o : op_t α)
    (hFsub : ∀ x ∈ F, x ∈ E) (hoE : o ∈ E) (honF : o ∉ F)
    (hinvF : CanonInv F (applySeqR (init_st (α := α)) F))
    (hdepF : ∀ z ∈ E, z ≠ o → DepC Cfg E z o → z ∈ F)
    (hFclosed : ∀ w ∈ F, ∀ z ∈ E, z ≠ w → DepC Cfg E z w → z ∈ F) :
    CanonStepOK F (applySeqR (init_st (α := α)) F) o := by
  -- o's id was never allocated by any insert seen from F (id uniqueness)
  have hfresh : ∀ L : List (op_t α), (∀ x ∈ L, x ∈ F) → ¬ insertedIn L o.1 := by
    rintro L hL ⟨r', e', p', a', hm⟩
    have hmF : (o.1, r', .Ins e' p' a') ∈ F := hL _ hm
    have hne : (o.1, r', .Ins e' p' a') ≠ o := fun hEq => honF (hEq ▸ hmF)
    exact hdts _ o (hFsub _ hmF) hoE hne rfl
  -- o's dependency package, carved from U
  set d := depList Cfg E U o with hd
  have hdsubF : ∀ x ∈ d, x ∈ F := by
    intro x hx
    obtain ⟨_hxU, hxo, hxdep⟩ := mem_depList.mp hx
    exact hdepF x ((hUp.2 x).mp (mem_depList.mp hx).1) hxo hxdep
  have hinvD : CanonInv d (applySeqR (init_st (α := α)) d) :=
    canonInv_depList_of_perm Cfg E hdts hids0 hGen htr hirr U hUp hUr o
  have hacc : accurate o (applySeqR (init_st (α := α)) d) :=
    hGen o hoE d (isDepPreC_depList_of_perm Cfg E U hUp hUr o)
  have hchains : ∀ z rz ez az (pz : List ℕ), (z, rz, .Ins ez pz az) ∈ d →
      ∀ c ∈ az :: pz, c = 0 ∨ insertedIn d c :=
    chains_closed_depList_of_perm Cfg E hGen htr hirr U hUp hUr o
  -- member dep-lists land inside F
  have hmemdep : ∀ w ∈ F, ∀ x ∈ depList Cfg E U w, x ∈ F := by
    intro w hw x hx
    obtain ⟨hxU, hxw, hxdep⟩ := mem_depList.mp hx
    exact hFclosed w hw x ((hUp.2 x).mp hxU) hxw hxdep
  obtain ⟨t, r, op⟩ := o
  have ht0 : t ≠ 0 := hids0 (t, r, op) hoE
  cases op with
  | Ins e p a =>
    refine ⟨ht0, ?_, ?_, ?_, ?_, ?_⟩
    · -- t is absent from the application fold
      cases hb : contains (applySeqR (init_st (α := α)) F) t with
      | false => rfl
      | true =>
        exact absurd (insertedIn_of_contains_fold F t hb)
          (hfresh F (fun _ hx => hx))
    · -- t was never deleted in F
      rintro ⟨t', r', p', hm⟩
      have haccδ := hGen _ (hFsub _ hm) _
        (isDepPreC_depList_of_perm Cfg E U hUp hUr (t', r', .Del p' t))
      simp only [accurate, opLeaf, opPath] at haccδ
      rcases haccδ with ⟨hx0, _⟩ | ⟨hxl, _⟩
      · exact ht0 hx0
      · exact hfresh (depList Cfg E U (t', r', .Del p' t))
          (hmemdep _ hm)
          (insertedIn_of_contains_fold _ t hxl)
    · -- t is not on its own recorded chain
      intro hmem
      rcases accurate_ins_entries t r e a p _ hacc t hmem with h | h
      · exact ht0 h
      · exact hfresh d hdsubF (insertedIn_of_contains_fold d t h)
    · -- t is not on any recorded chain in F
      intro t' r' e' p' a' hm hmem
      rcases chain_entries_mem Cfg E hGen U (goodEnum_of_perm Cfg E U hUp hUr)
          t' r' e' a' p' ((hUp.2 _).mpr (hFsub _ hm)) t hmem with h | h
      · exact ht0 h
      · exact hfresh (depList Cfg E U (t', r', .Ins e' p' a')) (hmemdep _ hm) h
    · -- ChainOK at the application fold, via the §4 transport
      simp only [accurate, opLeaf, opPath] at hacc
      rcases hacc with ⟨ha0, hp0⟩ | ⟨hal, hpath⟩
      · subst ha0; subst hp0
        intro c cs heq
        have hnil : liveSub (applySeqR (init_st (α := α)) F) [0] = [] := by
          unfold liveSub
          rw [List.filter_cons, List.filter_nil, hinvF.1]
          simp
        rw [hnil] at heq
        exact absurd heq (by simp)
      · exact fun c cs heq =>
          chainOK_transport F d hdsubF hinvF hinvD hchains p a hal hpath c cs heq
  | Del p x =>
    simp only [accurate, opLeaf, opPath] at hacc
    rcases hacc with ⟨hx0, hp0⟩ | ⟨hxl, hpath⟩
    · subst hx0; subst hp0
      refine ⟨fun _ => rfl, fun hcx => ?_⟩
      rw [hinvF.1] at hcx
      exact Bool.noConfusion hcx
    · refine ⟨fun hx0 => ?_, fun hcx => ?_⟩
      · rw [hx0, hinvD.1] at hxl
        exact Bool.noConfusion hxl
      · exact (anc_transport F d hdsubF hinvF hinvD hchains x hxl hcx p hpath).symm

/-! ## §4  K1 — the induction along the delta -/

/-- The workhorse induction: extend a dep-closed, `CanonInv`-carrying prefix `F` along a delta
list `π`, maintaining the invariants. -/
theorem canonFoldOK_delta_aux (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α))
    (hdts : ∀ a b : op_t α, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2C Cfg E)
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (U : List (op_t α)) (hUp : listPermOf U E)
    (hUr : respects U (loOnA (RGACondSig α) Cfg E)) :
    ∀ (π F : List (op_t α)),
      (∀ x ∈ F, x ∈ E) → (∀ x ∈ π, x ∈ E) →
      (F ++ π).Nodup →
      CanonInv F (applySeqR (init_st (α := α)) F) →
      (∀ w ∈ F, ∀ z ∈ E, z ≠ w → DepC Cfg E z w → z ∈ F) →
      (∀ pre o post, π = pre ++ o :: post →
        ∀ z ∈ E, z ≠ o → DepC Cfg E z o → z ∈ F ++ pre) →
      CanonFoldOK F (applySeqR (init_st (α := α)) F) π := by
  intro π
  induction π with
  | nil => intro F _ _ _ _ _ _; trivial
  | cons o rest ih =>
    intro F hFsub hπsub hnd hinvF hFclosed hδdeps
    have hoE : o ∈ E := hπsub o (by simp)
    have honF : o ∉ F := by
      intro hoF
      have hcross := (List.pairwise_append.mp hnd).2.2
      exact hcross o hoF o (by simp) rfl
    have hdepF : ∀ z ∈ E, z ≠ o → DepC Cfg E z o → z ∈ F := by
      intro z hz hzo hdep
      have := hδdeps [] o rest rfl z hz hzo hdep
      rwa [List.append_nil] at this
    have hstep : CanonStepOK F (applySeqR (init_st (α := α)) F) o :=
      canonStepOK_delta Cfg E hdts hids0 hGen htr hirr U hUp hUr F o
        hFsub hoE honF hinvF hdepF hFclosed
    refine ⟨hstep, ?_⟩
    -- extend the invariants to F ++ [o] and recurse
    have hfold' : applySeqR (init_st (α := α)) (F ++ [o]) = do_ (applySeqR (init_st (α := α)) F) o := by
      simp only [applySeqR, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hinvF' : CanonInv (F ++ [o]) (applySeqR (init_st (α := α)) (F ++ [o])) := by
      have h := canon_fold [o] F (applySeqR (init_st (α := α)) F) hinvF ⟨hstep, trivial⟩
      rwa [show applySeqR (applySeqR (init_st (α := α)) F) [o] = applySeqR (init_st (α := α)) (F ++ [o]) from by
        simp only [applySeqR, List.foldl_append]] at h
    have hFsub' : ∀ x ∈ F ++ [o], x ∈ E := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hFsub x h
      · rw [List.mem_singleton.mp h]; exact hoE
    have hnd' : ((F ++ [o]) ++ rest).Nodup := by
      rwa [show (F ++ [o]) ++ rest = F ++ o :: rest from by simp]
    have hFclosed' : ∀ w ∈ F ++ [o], ∀ z ∈ E, z ≠ w → DepC Cfg E z w → z ∈ F ++ [o] := by
      intro w hw z hz hzw hdep
      rcases List.mem_append.mp hw with h | h
      · exact List.mem_append_left _ (hFclosed w h z hz hzw hdep)
      · rw [List.mem_singleton.mp h] at hdep hzw
        exact List.mem_append_left _ (hdepF z hz hzw hdep)
    have hδdeps' : ∀ pre o' post, rest = pre ++ o' :: post →
        ∀ z ∈ E, z ≠ o' → DepC Cfg E z o' → z ∈ (F ++ [o]) ++ pre := by
      intro pre o' post hsplit z hz hzo hdep
      have := hδdeps (o :: pre) o' post (by rw [hsplit]; rfl) z hz hzo hdep
      rwa [show F ++ o :: pre = (F ++ [o]) ++ pre from by simp] at this
    have := ih (F ++ [o]) hFsub' (fun x hx => hπsub x (by simp [hx])) hnd' hinvF'
      hFclosed' hδdeps'
    rwa [hfold'] at this

/-- **K1 — the delta discipline.**  `CanonFoldOK ρ₀ (applySeqR (init_st (α := α)) ρ₀) π₀` from:
the generation discipline (`GenDisc2C` — each event accurate at its own dependency fold, the
condition that survives concurrent anchor-kills), the LCA's own discipline (`CanonFoldOK [] init ρ₀`
— from the noopFeasible engine route on the given born-applicable `ρ₀`), dependency closure of the
LCA set, and per-position dependency closure of the delta (`hδdeps`).  NO order hypothesis on `ρ₀`. -/
theorem canonFoldOK_delta (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α))
    (hdts : ∀ a b : op_t α, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2C Cfg E)
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (U : List (op_t α)) (hUp : listPermOf U E)
    (hUr : respects U (loOnA (RGACondSig α) Cfg E))
    (ρ₀ π₀ : List (op_t α))
    (hρsub : ∀ x ∈ ρ₀, x ∈ E) (hπsub : ∀ x ∈ π₀, x ∈ E)
    (hnd : (ρ₀ ++ π₀).Nodup)
    (hρOK : CanonFoldOK [] (init_st (α := α)) ρ₀)
    (hρclosed : ∀ w ∈ ρ₀, ∀ z ∈ E, z ≠ w → DepC Cfg E z w → z ∈ ρ₀)
    (hδdeps : ∀ pre o post, π₀ = pre ++ o :: post →
        ∀ z ∈ E, z ≠ o → DepC Cfg E z o → z ∈ ρ₀ ++ pre) :
    CanonFoldOK ρ₀ (applySeqR (init_st (α := α)) ρ₀) π₀ := by
  have hinvρ : CanonInv ρ₀ (applySeqR (init_st (α := α)) ρ₀) := by
    have h := canon_fold ρ₀ [] (init_st (α := α)) canonInv_init hρOK
    rwa [List.nil_append] at h
  exact canonFoldOK_delta_aux Cfg E hdts hids0 hGen htr hirr U hUp hUr π₀ ρ₀
    hρsub hπsub hnd hinvρ hρclosed hδdeps

/-! ## Axiom audit -/

#print axioms loOnA_imp_vis
#print axioms depC_irrefl
#print axioms canonStepOK_delta
#print axioms canonFoldOK_delta

end Sal.ConditionedMRDTs.RGAK1Delta
