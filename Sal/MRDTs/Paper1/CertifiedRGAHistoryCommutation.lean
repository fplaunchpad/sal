import Sal.MRDTs.Paper1.CertifiedRGAHistory
import Sal.MRDTs.Paper1.CertifiedHistoryCommutation

namespace Sal.MRDTs.Paper1.CertifiedRGAHistory
open Foundation Instances.ProductionRGA
open Sal.EmbedRGA (OrderedPrefixCode Side)
variable {α : Type} [DecidableEq α] [Inhabited α]

private theorem embed_filter_splice (anchor target : Nat) (p : Nat × α)
    (anchor_ne : anchor ≠ target) (id_ne : p.1 ≠ target)
    (xs : List (Nat × α)) :
    (Instances.EmbedRGA.eInsAfter anchor p xs).filter (fun q => decide (q.1 ≠ target)) =
    Instances.EmbedRGA.eInsAfter anchor p (xs.filter (fun q => decide (q.1 ≠ target))) := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    by_cases ha : q.1 = anchor
    · have hn : q.1 ≠ target := ha ▸ anchor_ne
      simp_all [List.filter_cons, Instances.EmbedRGA.eInsAfter]
    · by_cases ht : q.1 = target
      · simp_all [List.filter_cons, Instances.EmbedRGA.eInsAfter]
      · simp_all [List.filter_cons, Instances.EmbedRGA.eInsAfter]

private theorem sided_filter_splice_after (anchor target : Nat) (p : Nat × Nat)
    (anchor_ne : anchor ≠ target) (id_ne : p.1 ≠ target)
    (xs : List (Nat × Nat)) :
    (Instances.SidedEmbedRGA.sInsAfter anchor p xs).filter (fun q => decide (q.1 ≠ target)) =
    Instances.SidedEmbedRGA.sInsAfter anchor p (xs.filter (fun q => decide (q.1 ≠ target))) := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    by_cases ha : q.1 = anchor
    · have hn : q.1 ≠ target := ha ▸ anchor_ne
      simp_all [List.filter_cons, Instances.SidedEmbedRGA.sInsAfter]
    · by_cases ht : q.1 = target
      · simp_all [List.filter_cons, Instances.SidedEmbedRGA.sInsAfter]
      · simp_all [List.filter_cons, Instances.SidedEmbedRGA.sInsAfter]

private theorem sided_filter_splice_before (anchor target : Nat) (p : Nat × Nat)
    (anchor_ne : anchor ≠ target) (id_ne : p.1 ≠ target)
    (xs : List (Nat × Nat)) :
    (Instances.SidedEmbedRGA.sInsBefore anchor p xs).filter (fun q => decide (q.1 ≠ target)) =
    Instances.SidedEmbedRGA.sInsBefore anchor p (xs.filter (fun q => decide (q.1 ≠ target))) := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    by_cases ha : q.1 = anchor
    · have hn : q.1 ≠ target := ha ▸ anchor_ne
      simp_all [List.filter_cons, Instances.SidedEmbedRGA.sInsBefore]
    · by_cases ht : q.1 = target
      · simp_all [List.filter_cons, Instances.SidedEmbedRGA.sInsBefore]
      · simp_all [List.filter_cons, Instances.SidedEmbedRGA.sInsBefore]

theorem embed_delete_insert_steps (Γ : OrderedPrefixCode)
    (dts dr its ir target anchor : Nat) (el : α) (pref : List Bool)
    (anchor_ne : anchor ≠ target) (id_ne : its ≠ target)
    (s : List (Nat × α)) :
    (embedClientSpec Γ).step ((embedClientSpec Γ).step s (dts,dr,.del target))
      (its,ir,.ins el pref anchor) =
    (embedClientSpec Γ).step ((embedClientSpec Γ).step s (its,ir,.ins el pref anchor))
      (dts,dr,.del target) := by
  simp only [embedClientSpec, embedSpec]
  change Instances.EmbedRGA.eSpecStep (Instances.EmbedRGA.eSpecStep s (dts,dr,.del target)) (its,ir,.ins el pref anchor) =
    Instances.EmbedRGA.eSpecStep (Instances.EmbedRGA.eSpecStep s (its,ir,.ins el pref anchor)) (dts,dr,.del target)
  simp only [Instances.EmbedRGA.eSpecStep]
  by_cases root : anchor = 0
  · simp [root,id_ne]
  · simp only [root, ↓reduceIte]
    exact (embed_filter_splice anchor target (its,el) anchor_ne id_ne s).symm

theorem sided_delete_insert_steps (Γ : OrderedPrefixCode)
    (dts dr its ir target anchor el : Nat) (pref : List Nat) (side : Side)
    (anchor_ne : anchor ≠ target) (id_ne : its ≠ target)
    (s : List (Nat × Nat)) :
    (sidedClientSpec Γ).step ((sidedClientSpec Γ).step s (dts,dr,.del target))
      (its,ir,.ins el pref anchor side) =
    (sidedClientSpec Γ).step ((sidedClientSpec Γ).step s (its,ir,.ins el pref anchor side))
      (dts,dr,.del target) := by
  simp only [sidedClientSpec, sidedSpec]
  change Instances.SidedEmbedRGA.sSpecStep (Instances.SidedEmbedRGA.sSpecStep s (dts,dr,.del target)) (its,ir,.ins el pref anchor side) =
    Instances.SidedEmbedRGA.sSpecStep (Instances.SidedEmbedRGA.sSpecStep s (its,ir,.ins el pref anchor side)) (dts,dr,.del target)
  cases side with
  | R => exact (sided_filter_splice_after anchor target (its,el) anchor_ne id_ne s).symm
  | L => exact (sided_filter_splice_before anchor target (its,el) anchor_ne id_ne s).symm

/-- A causal deletion preceding an eligible insertion cannot delete either
its fresh identifier or its live mint-time anchor. -/
theorem embed_causal_delete_insert (Γ : OrderedPrefixCode)
    (C : Configuration (Instances.EmbedRGA.E Γ α))
    (good : CanonicalConfig C)
    (mint : MintHonest (Instances.EmbedRGA.E Γ α) Instances.EmbedRGA.eApplicable C)
    (dts dr its ir target anchor : Nat) (el : α) (pref : List Bool)
    (hd : (dts,dr,Instances.EmbedRGA.EOp.del target) ∈ C.events)
    (hi : (its,ir,Instances.EmbedRGA.EOp.ins el pref anchor) ∈ C.events)
    (vis : C.vis (dts,dr,.del target) (its,ir,.ins el pref anchor)) :
    its ≠ target ∧ anchor ≠ target := by
  open Instances.EmbedRGA in
    have honest := eHonest_core (eHonest_of_mint mint)
    obtain ⟨creator,hc,hcv,hct,hins⟩ := honest.del_has_ins _ hd target rfl
    have earlier : target < dts := by simpa only [hct] using C.causal_mono hcv
    have id_ne : its ≠ target := by
      have ht : dts < its := C.causal_mono vis
      omega
    obtain ⟨origin,perm,ordered,guard⟩ := mint _ hi
    change eApplicable (its,ir,.ins el pref anchor) (eFold Γ origin) at guard
    have wf : EWf Γ origin := CertifiedRGAScope.Embedded.wellformed Γ
      C.replayContext honest {e ∈ C.events | C.vis e (its,ir,.ins el pref anchor)} origin
      (fun _ h => h.1) (fun a b ab hb => ⟨by
        obtain ⟨r,H,hr,ha⟩ := C.vis_src ab
        exact ⟨r,H,hr,ha⟩, good.vis_trans ab hb.2⟩) perm ordered
    have target_pos : 0 < target := by
      obtain ⟨co,cp,cr,cg⟩ := mint creator hc
      obtain ⟨ct,rep,op⟩ := creator
      cases op with
      | del x => simp [eIsIns] at hins
      | ins ce pr an =>
        change eApplicable (ct,rep,.ins ce pr an) (eFold Γ co) at cg
        simp only [eApplicable] at cg
        change ct = target at hct
        have positive : 0 < ct := Nat.lt_of_le_of_lt (Nat.zero_le an) cg.1
        exact hct ▸ positive
    refine ⟨id_ne,?_⟩
    intro equal
    simp only [eApplicable] at guard
    rcases guard.2 with root | ⟨ae,mem⟩
    · omega
    · have absent := ((e_fold_mem Γ wf (anchor,ae,pref)).mp mem).2
      apply absent
      unfold eDels
      apply List.mem_filterMap.mpr
      refine ⟨(dts,dr,.del target), (perm.2 _).mpr ⟨hd,vis⟩,?_⟩
      simp [equal]

/-- A causal deletion preceding an eligible insertion cannot delete either
its fresh identifier or its live mint-time anchor. -/
theorem sided_causal_delete_insert (Γ : OrderedPrefixCode)
    (C : Configuration (Instances.SidedEmbedRGA.S Γ))
    (good : CanonicalConfig C)
    (mint : MintHonest (Instances.SidedEmbedRGA.S Γ) Instances.SidedEmbedRGA.sApplicable C)
    (dts dr its ir target anchor : Nat) (el : Nat) (pref : List Nat) (side : Side)
    (hd : (dts,dr,Instances.SidedEmbedRGA.SOp.del target) ∈ C.events)
    (hi : (its,ir,Instances.SidedEmbedRGA.SOp.ins el pref anchor side) ∈ C.events)
    (vis : C.vis (dts,dr,.del target) (its,ir,.ins el pref anchor side)) :
    its ≠ target ∧ anchor ≠ target := by
  open Instances.SidedEmbedRGA in
    have honest := sHonest_core (sHonest_of_mint mint)
    obtain ⟨creator,hc,hcv,hct,hins⟩ := honest.del_has_ins _ hd target rfl
    have earlier : target < dts := by simpa only [hct] using C.causal_mono hcv
    have id_ne : its ≠ target := by
      have ht : dts < its := C.causal_mono vis
      omega
    obtain ⟨origin,perm,ordered,guard⟩ := mint _ hi
    change sApplicable (its,ir,.ins el pref anchor side) (sFold Γ origin) at guard
    have wf : SWf Γ origin := CertifiedRGAScope.Sided.wellformed Γ
      C.replayContext honest {e ∈ C.events | C.vis e (its,ir,.ins el pref anchor side)} origin
      (fun _ h => h.1) (fun a b ab hb => ⟨by
        obtain ⟨r,H,hr,ha⟩ := C.vis_src ab
        exact ⟨r,H,hr,ha⟩, good.vis_trans ab hb.2⟩) perm ordered
    have target_pos : 0 < target := by
      obtain ⟨co,cp,cr,cg⟩ := mint creator hc
      obtain ⟨ct,rep,op⟩ := creator
      cases op with
      | del x => simp [sIsIns] at hins
      | ins ce pr an sd =>
        change sApplicable (ct,rep,.ins ce pr an sd) (sFold Γ co) at cg
        simp only [sApplicable] at cg
        change ct = target at hct
        have positive : 0 < ct := Nat.lt_of_le_of_lt (Nat.zero_le an) cg.1
        exact hct ▸ positive
    refine ⟨id_ne,?_⟩
    intro equal
    simp only [sApplicable] at guard
    rcases guard.2 with root | ⟨ae,mem⟩
    · omega
    · have absent := ((s_fold_mem Γ wf (anchor,ae,pref)).mp mem).2
      apply absent
      unfold sDels
      apply List.mem_filterMap.mpr
      refine ⟨(dts,dr,.del target), (perm.2 _).mpr ⟨hd,vis⟩,?_⟩
      simp [equal]

private def PrefixChecks {E : Type} (check : List E → E → Prop) : List E → List E → Prop
  | _, [] => True
  | pre, e :: rest => check pre e ∧ PrefixChecks check (pre ++ [e]) rest

private theorem checks_splits {E : Type} (check : List E → E → Prop)
    (pre xs : List E) :
    PrefixChecks check pre xs ↔
      ∀ before e after, xs = before ++ e :: after → check (pre ++ before) e := by
  induction xs generalizing pre with
  | nil => simp [PrefixChecks]
  | cons x xs ih =>
    constructor
    · intro h before e after eq
      cases before with
      | nil => simp only [List.nil_append,List.cons.injEq] at eq; obtain ⟨rfl,rfl⟩ := eq; simpa using h.1
      | cons b bs =>
        simp only [List.cons_append,List.cons.injEq] at eq
        obtain ⟨rfl,eq⟩ := eq
        simpa [List.append_assoc] using (ih (pre ++ [x])).mp h.2 bs e after eq
    · intro h
      refine ⟨by simpa using h [] x xs rfl, (ih _).mpr ?_⟩
      intro before e after eq
      simpa [List.append_assoc] using h (x :: before) e after (by simp [eq])

private theorem checks_append {E : Type} (check : List E → E → Prop)
    (pre xs ys : List E) :
    PrefixChecks check pre (xs ++ ys) ↔
      PrefixChecks check pre xs ∧ PrefixChecks check (pre ++ xs) ys := by
  induction xs generalizing pre with
  | nil => simp [PrefixChecks]
  | cons x xs ih => simp [PrefixChecks,ih,List.append_assoc,and_assoc]

private theorem checks_congr {E : Type} (check : List E → E → Prop)
    (p q xs : List E)
    (equal : ∀ tail e, check (p ++ tail) e ↔ check (q ++ tail) e) :
    PrefixChecks check p xs ↔ PrefixChecks check q xs := by
  rw [checks_splits,checks_splits]
  exact forall_congr' fun before => forall_congr' fun e => forall_congr' fun after =>
    imp_congr_right fun _ => equal before e

private theorem checks_swap {E : Type} (check : List E → E → Prop)
    (pre suf : List E) (a b : E)
    (firstA : check (pre ++ [b]) a ↔ check pre a)
    (firstB : check (pre ++ [a]) b ↔ check pre b)
    (suffix : ∀ tail e, check ((pre ++ [a,b]) ++ tail) e ↔
      check ((pre ++ [b,a]) ++ tail) e) :
    PrefixChecks check [] (pre ++ [a,b] ++ suf) ↔
      PrefixChecks check [] (pre ++ [b,a] ++ suf) := by
  rw [checks_append,checks_append]
  simp only [List.nil_append]
  rw [checks_append,checks_append]
  simp only [PrefixChecks,List.append_nil,true_and,and_true]
  have last := checks_congr check (pre ++ [a,b]) (pre ++ [b,a]) suf suffix
  simp only [List.append_assoc] at last ⊢
  tauto

private def embedCheck (Γ : OrderedPrefixCode)
    (pre : List (Op (Instances.EmbedRGA.EOp α)))
    (current : Op (Instances.EmbedRGA.EOp α)) : Prop :=
  match current.2.2 with
  | .ins _ pref anchor =>
      (∀ x ∈ Instances.EmbedRGA.eInsIds pre, x < current.1) ∧
      ((anchor = 0 ∧ pref = []) ∨ ∃ parent ∈ pre,
        Instances.EmbedRGA.eIsIns parent = true ∧ parent.1 = anchor ∧
        Instances.EmbedRGA.eCoord Γ parent = pref)
  | .del target => ∃ parent ∈ pre,
      Instances.EmbedRGA.eIsIns parent = true ∧ parent.1 = target

private theorem embed_checks_legal (Γ : OrderedPrefixCode)
    (xs : List (Op (Instances.EmbedRGA.EOp α))) :
    PrefixChecks (embedCheck Γ) [] xs ↔ (embedClientSpec Γ).Legal xs := by
  simpa [embedCheck,embedClientSpec,embedLegal] using checks_splits (embedCheck Γ) [] xs

theorem embed_delete_insert_legal_swap (Γ : OrderedPrefixCode)
    (dts dr its ir target anchor : Nat) (el : α) (pref : List Bool)
    (id_ne : its ≠ target)
    (pre suf : List (Op (Instances.EmbedRGA.EOp α))) :
    (embedClientSpec Γ).Legal (pre ++ [(dts,dr,.del target),(its,ir,.ins el pref anchor)] ++ suf) ↔
    (embedClientSpec Γ).Legal (pre ++ [(its,ir,.ins el pref anchor),(dts,dr,.del target)] ++ suf) := by
  rw [← embed_checks_legal,← embed_checks_legal]
  apply checks_swap
  · simp [embedCheck,List.mem_append,id_ne,Ne.symm id_ne,Instances.EmbedRGA.eIsIns]
  · simp [embedCheck,Instances.EmbedRGA.eInsIds,Instances.EmbedRGA.eIsIns,
      or_and_right,exists_or]
  · intro tail e
    obtain ⟨ts,rep,op⟩ := e
    cases op <;>
      simp [embedCheck,Instances.EmbedRGA.eInsIds,Instances.EmbedRGA.eIsIns,
        List.mem_append,or_assoc,or_comm,or_left_comm]

private def sidedCheck (Γ : OrderedPrefixCode)
    (pre : List (Op (Instances.SidedEmbedRGA.SOp)))
    (current : Op (Instances.SidedEmbedRGA.SOp)) : Prop :=
  match current.2.2 with
  | .ins _ pref anchor _ =>
      (∀ x ∈ Instances.SidedEmbedRGA.sInsIds pre, x < current.1) ∧
      ((anchor = 0 ∧ pref = []) ∨ ∃ parent ∈ pre,
        Instances.SidedEmbedRGA.sIsIns parent = true ∧ parent.1 = anchor ∧
        Instances.SidedEmbedRGA.sCoord Γ parent = pref)
  | .del target => ∃ parent ∈ pre,
      Instances.SidedEmbedRGA.sIsIns parent = true ∧ parent.1 = target

private theorem sided_checks_legal (Γ : OrderedPrefixCode)
    (xs : List (Op (Instances.SidedEmbedRGA.SOp))) :
    PrefixChecks (sidedCheck Γ) [] xs ↔ (sidedClientSpec Γ).Legal xs := by
  simpa [sidedCheck,sidedClientSpec,sidedLegal] using checks_splits (sidedCheck Γ) [] xs

theorem sided_delete_insert_legal_swap (Γ : OrderedPrefixCode)
    (dts dr its ir target anchor : Nat) (el : Nat) (pref : List Nat) (side : Side)
    (id_ne : its ≠ target)
    (pre suf : List (Op (Instances.SidedEmbedRGA.SOp))) :
    (sidedClientSpec Γ).Legal (pre ++ [(dts,dr,.del target),(its,ir,.ins el pref anchor side)] ++ suf) ↔
    (sidedClientSpec Γ).Legal (pre ++ [(its,ir,.ins el pref anchor side),(dts,dr,.del target)] ++ suf) := by
  rw [← sided_checks_legal,← sided_checks_legal]
  apply checks_swap
  · simp [sidedCheck,List.mem_append,id_ne,Ne.symm id_ne,Instances.SidedEmbedRGA.sIsIns]
  · simp [sidedCheck,Instances.SidedEmbedRGA.sInsIds,Instances.SidedEmbedRGA.sIsIns,
      or_and_right,exists_or]
  · intro tail e
    obtain ⟨ts,rep,op⟩ := e
    cases op <;>
      simp [sidedCheck,Instances.SidedEmbedRGA.sInsIds,Instances.SidedEmbedRGA.sIsIns,
        List.mem_append,or_assoc,or_comm,or_left_comm]

theorem embed_delete_insert_language (Γ : OrderedPrefixCode)
    (dts dr its ir target anchor : Nat) (el : α)
    (pref : List Bool)
    (anchor_ne : anchor ≠ target) (id_ne : its ≠ target) :
    (GuardedHistory.language (embedClientSpec Γ)).Commutes
      (dts,dr,.del target) (its,ir,.ins el pref anchor) := by
  apply GuardedHistory.language_commutes_of_legal_swap (embedClientSpec Γ)
    (embed_legal_prefix Γ)
  · exact embed_delete_insert_steps Γ dts dr its ir target anchor el pref anchor_ne id_ne
  · exact embed_delete_insert_legal_swap Γ dts dr its ir target anchor el pref id_ne

theorem embed_deletes_language (Γ : OrderedPrefixCode)
    (ats ar ax bts br bx : Nat) :
    (GuardedHistory.language (embedClientSpec (α := α) Γ)).Commutes
      (ats,ar,.del ax) (bts,br,.del bx) := by
  apply GuardedHistory.language_commutes_of_legal_swap (embedClientSpec (α := α) Γ)
    (embed_legal_prefix (α := α) Γ)
  · intro s
    simp [embedClientSpec,embedSpec,Instances.EmbedRGA.eSpecStep,
      List.filter_filter,Bool.and_comm]
  · intro before after
    rw [← embed_checks_legal (α := α),← embed_checks_legal (α := α)]
    apply checks_swap
    · simp [embedCheck,List.mem_append,Instances.EmbedRGA.eIsIns,or_and_right,exists_or]
    · simp [embedCheck,List.mem_append,Instances.EmbedRGA.eIsIns,or_and_right,exists_or]
    · intro tail e
      obtain ⟨ts,r,op⟩ := e
      cases op <;> simp [embedCheck,Instances.EmbedRGA.eInsIds,
        Instances.EmbedRGA.eIsIns,List.mem_append,or_and_right,exists_or]

theorem sided_delete_insert_language (Γ : OrderedPrefixCode)
    (dts dr its ir target anchor : Nat) (el : Nat)
    (pref : List Nat) (side : Side)
    (anchor_ne : anchor ≠ target) (id_ne : its ≠ target) :
    (GuardedHistory.language (sidedClientSpec Γ)).Commutes
      (dts,dr,.del target) (its,ir,.ins el pref anchor side) := by
  apply GuardedHistory.language_commutes_of_legal_swap (sidedClientSpec Γ)
    (sided_legal_prefix Γ)
  · exact sided_delete_insert_steps Γ dts dr its ir target anchor el pref side anchor_ne id_ne
  · exact sided_delete_insert_legal_swap Γ dts dr its ir target anchor el pref side id_ne

theorem sided_deletes_language (Γ : OrderedPrefixCode)
    (ats ar ax bts br bx : Nat) :
    (GuardedHistory.language (sidedClientSpec Γ)).Commutes
      (ats,ar,.del ax) (bts,br,.del bx) := by
  apply GuardedHistory.language_commutes_of_legal_swap (sidedClientSpec Γ)
    (sided_legal_prefix Γ)
  · intro s
    simp [sidedClientSpec,sidedSpec,Instances.SidedEmbedRGA.sSpecStep,
      List.filter_filter,Bool.and_comm]
  · intro before after
    rw [← sided_checks_legal,← sided_checks_legal]
    apply checks_swap
    · simp [sidedCheck,List.mem_append,Instances.SidedEmbedRGA.sIsIns,or_and_right,exists_or]
    · simp [sidedCheck,List.mem_append,Instances.SidedEmbedRGA.sIsIns,or_and_right,exists_or]
    · intro tail e
      obtain ⟨ts,r,op⟩ := e
      cases op <;> simp [sidedCheck,Instances.SidedEmbedRGA.sInsIds,
        Instances.SidedEmbedRGA.sIsIns,List.mem_append,or_and_right,exists_or]

/-- The insertion-first public history preserves specification-conflict
visibility. Moved causal deletes commute contextually, including later queries. -/
theorem embed_canonical_specVisibility (Γ : OrderedPrefixCode)
    (C : Configuration (Instances.EmbedRGA.E Γ α))
    (good : CanonicalConfig C)
    (mint : MintHonest (Instances.EmbedRGA.E Γ α) Instances.EmbedRGA.eApplicable C)
    (E : Set (Op (Instances.EmbedRGA.EOp α))) (supported : E ⊆ C.events)
    (ops : List (Op (Instances.EmbedRGA.EOp α))) (perm : listPermOf ops E) :
    respects (EmbedWitness.canonical ops)
      (projectedSpecVisibility id (GuardedHistory.language (embedClientSpec Γ)) C.replayContext) := by
  have can := EmbedWitness.canonical_listPermOf perm
  apply (EmbedWitness.canonical_ordered ops).imp_of_mem
  intro a b ha hb le conflict
  have haC := supported ((can.2 a).mp ha)
  have hbC := supported ((can.2 b).mp hb)
  obtain ⟨ats,ar,aop⟩ := a
  obtain ⟨bts,br,bop⟩ := b
  obtain ⟨vis,ncomm⟩ := conflict
  cases aop with
  | ins ael apref aanchor =>
    cases bop with
    | ins bel bpref banchor =>
      have lt : bts < ats := C.causal_mono vis
      have ge : ats ≤ bts := by simpa [EmbedWitness.LE,EmbedWitness.leBool] using le
      exact (Nat.not_lt_of_ge ge) lt
    | del target =>
      obtain ⟨id_ne,anchor_ne⟩ := embed_causal_delete_insert Γ C good mint
        bts br ats ar target aanchor ael apref hbC haC vis
      exact ncomm (embed_delete_insert_language Γ bts br ats ar target aanchor
        ael apref anchor_ne id_ne)
  | del target =>
    cases bop with
    | ins bel bpref banchor => simp [EmbedWitness.LE,EmbedWitness.leBool] at le
    | del other => exact ncomm (embed_deletes_language Γ bts br other ats ar target)

/-- The insertion-first public history preserves specification-conflict
visibility. Moved causal deletes commute contextually, including later queries. -/
theorem sided_canonical_specVisibility (Γ : OrderedPrefixCode)
    (C : Configuration (Instances.SidedEmbedRGA.S Γ))
    (good : CanonicalConfig C)
    (mint : MintHonest (Instances.SidedEmbedRGA.S Γ) Instances.SidedEmbedRGA.sApplicable C)
    (E : Set (Op (Instances.SidedEmbedRGA.SOp))) (supported : E ⊆ C.events)
    (ops : List (Op (Instances.SidedEmbedRGA.SOp))) (perm : listPermOf ops E) :
    respects (SidedWitness.canonical ops)
      (projectedSpecVisibility id (GuardedHistory.language (sidedClientSpec Γ)) C.replayContext) := by
  have can := SidedWitness.canonical_listPermOf perm
  apply (SidedWitness.canonical_ordered ops).imp_of_mem
  intro a b ha hb le conflict
  have haC := supported ((can.2 a).mp ha)
  have hbC := supported ((can.2 b).mp hb)
  obtain ⟨ats,ar,aop⟩ := a
  obtain ⟨bts,br,bop⟩ := b
  obtain ⟨vis,ncomm⟩ := conflict
  cases aop with
  | ins ael apref aanchor asd =>
    cases bop with
    | ins bel bpref banchor bsd =>
      have lt : bts < ats := C.causal_mono vis
      have ge : ats ≤ bts := by simpa [SidedWitness.LE,SidedWitness.leBool] using le
      exact (Nat.not_lt_of_ge ge) lt
    | del target =>
      obtain ⟨id_ne,anchor_ne⟩ := sided_causal_delete_insert Γ C good mint
        bts br ats ar target aanchor ael apref asd hbC haC vis
      exact ncomm (sided_delete_insert_language Γ bts br ats ar target aanchor
        ael apref asd anchor_ne id_ne)
  | del target =>
    cases bop with
    | ins bel bpref banchor bsd => simp [SidedWitness.LE,SidedWitness.leBool] at le
    | del other => exact ncomm (sided_deletes_language Γ bts br other ats ar target)

theorem embed_full_history_of_replay {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.EmbedRGA.E Γ α)}
    (exec : CertifiedExecution (Sal.MRDTs.Instances.EmbedRGA.E Γ α) (Sal.MRDTs.Instances.EmbedRGA.generation Γ) C)
    (hgood : CanonicalConfig C)
    {v : Version} {s : (Sal.MRDTs.Instances.EmbedRGA.E Γ α).State} {E : Set (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hver : C.ver v = some (s,E)) {ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hperm : listPermOf ops E) (hresp : respects ops C.vis)
    (hfold : Sal.MRDTs.Instances.EmbedRGA.eFold Γ ops = s)
    (q : (Sal.MRDTs.Instances.EmbedRGA.E Γ α).Query) :
    ∃ π, listPermOf π E ∧
      Sal.MRDTs.Instances.EmbedRGA.eFold Γ π = s ∧
      respects π (projectedSpecVisibility id
        (GuardedHistory.language (embedClientSpec Γ)) C.replayContext) ∧
      (GuardedHistory.language (embedClientSpec Γ)).admits
        (projectedLabels id π ++ [.query q ((Sal.MRDTs.Instances.EmbedRGA.E Γ α).query s q)]) := by
  open Sal.MRDTs.Instances.EmbedRGA in
    have hseq := embedCanonical_seqOK_of hgood exec.mintHonest hver hperm
    have hlegal := embedLegal_of_seqOK hseq
    have hcan := EmbedWitness.canonical_listPermOf hperm
    have hsub := hgood.version_events_supported v s E hver
    have hclosed := hgood.version_events_causal v s E hver
    have hhon : EHonestCore Γ C.replayContext :=
      eHonest_core (eHonest_of_mint exec.mintHonest)
    have hwfReplay : EWf Γ ops :=
      CertifiedRGAScope.Embedded.wellformed Γ C.replayContext hhon E ops
        hsub hclosed hperm hresp
    have hwfCanonical : EWf Γ (EmbedWitness.canonical ops) :=
      eWf_of_seqOK hseq
    have hcanonFold :
        eFold Γ (EmbedWitness.canonical ops) = eFold Γ ops :=
      e_fold_canon Γ hwfCanonical hwfReplay
        (fun e => (hcan.2 e).trans (hperm.2 e).symm)
    have hstate : eFold Γ (EmbedWitness.canonical ops) = s := by
      rw [hcanonFold]
      exact hfold
    have hsound := embed_seq_sound hseq
    have hrel : embedRel s ((embedClientSpec Γ).run
        (EmbedWitness.canonical ops)) := by
      unfold embedRel
      change s.map eProj = eSpecFold (EmbedWitness.canonical ops)
      rw [← hstate]
      exact hsound
    have observes : ∀ query, (Sal.MRDTs.Instances.EmbedRGA.E Γ α).query s query =
        (embedClientSpec Γ).query ((embedClientSpec Γ).run (EmbedWitness.canonical ops)) query := by
      intro query
      cases query
      change s.map (fun r => r.2.1) =
        ((embedClientSpec Γ).run (EmbedWitness.canonical ops)).map Prod.snd
      simpa [eProj, List.map_map, Function.comp_def] using
        congrArg (List.map Prod.snd) hrel
    refine ⟨EmbedWitness.canonical ops,hcan,hstate,?_,?_⟩
    · exact embed_canonical_specVisibility Γ C hgood exec.mintHonest E hsub ops hperm
    · rw [observes q]
      exact GuardedHistory.admits_updates_query (embedClientSpec Γ)
        (embed_legal_prefix Γ) (EmbedWitness.canonical ops) hlegal q

theorem sided_full_history_of_replay {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)}
    (exec : CertifiedExecution (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ) (Sal.MRDTs.Instances.SidedEmbedRGA.generation Γ) C)
    (hgood : CanonicalConfig C)
    {v : Version} {s : (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).State} {E : Set (Op (Sal.MRDTs.Instances.SidedEmbedRGA.SOp))}
    (hver : C.ver v = some (s,E)) {ops : List (Op (Sal.MRDTs.Instances.SidedEmbedRGA.SOp))}
    (hperm : listPermOf ops E) (hresp : respects ops C.vis)
    (hfold : Sal.MRDTs.Instances.SidedEmbedRGA.sFold Γ ops = s)
    (q : (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).Query) :
    ∃ π, listPermOf π E ∧
      Sal.MRDTs.Instances.SidedEmbedRGA.sFold Γ π = s ∧
      respects π (projectedSpecVisibility id
        (GuardedHistory.language (sidedClientSpec Γ)) C.replayContext) ∧
      (GuardedHistory.language (sidedClientSpec Γ)).admits
        (projectedLabels id π ++ [.query q ((Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).query s q)]) := by
  open Sal.MRDTs.Instances.SidedEmbedRGA in
    have hseq := sidedCanonical_seqOK_of hgood exec.mintHonest hver hperm
    have hlegal := sidedLegal_of_seqOK hseq
    have hcan := SidedWitness.canonical_listPermOf hperm
    have hsub := hgood.version_events_supported v s E hver
    have hclosed := hgood.version_events_causal v s E hver
    have hhon : SHonestCore Γ C.replayContext :=
      sHonest_core (sHonest_of_mint exec.mintHonest)
    have hwfReplay : SWf Γ ops :=
      CertifiedRGAScope.Sided.wellformed Γ C.replayContext hhon E ops
        hsub hclosed hperm hresp
    have hwfCanonical : SWf Γ (SidedWitness.canonical ops) :=
      sWf_of_seqOK hseq
    have hcanonFold :
        sFold Γ (SidedWitness.canonical ops) = sFold Γ ops :=
      s_fold_canon Γ hwfCanonical hwfReplay
        (fun e => (hcan.2 e).trans (hperm.2 e).symm)
    have hstate : sFold Γ (SidedWitness.canonical ops) = s := by
      rw [hcanonFold]
      exact hfold
    have hsound := sided_seq_read hseq
    have hrel : sidedRel s ((sidedClientSpec Γ).run
        (SidedWitness.canonical ops)) := by
      unfold sidedRel
      change s.map sProj = (sSpecFold (SidedWitness.canonical ops)).filter
        (fun p => decide (p.1 ≠ 0))
      rw [← hstate]
      exact hsound
    have observes : ∀ query, (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).query s query =
        (sidedClientSpec Γ).query ((sidedClientSpec Γ).run (SidedWitness.canonical ops)) query := by
      intro query
      cases query
      change s.map (fun r => r.2.1) =
        (((sidedClientSpec Γ).run (SidedWitness.canonical ops)).filter
          (fun p => decide (p.1 ≠ 0))).map Prod.snd
      simpa [sProj, List.map_map, Function.comp_def] using
        congrArg (List.map Prod.snd) hrel
    refine ⟨SidedWitness.canonical ops,hcan,hstate,?_,?_⟩
    · exact sided_canonical_specVisibility Γ C hgood exec.mintHonest E hsub ops hperm
    · rw [observes q]
      exact GuardedHistory.admits_updates_query (sidedClientSpec Γ)
        (sided_legal_prefix Γ) (SidedWitness.canonical ops) hlegal q

private def checksDecidable {E : Type} (check : List E → E → Prop)
    (dec : ∀ pre e, Decidable (check pre e)) (pre xs : List E) :
    Decidable (PrefixChecks check pre xs) :=
  match xs with
  | [] => isTrue True.intro
  | e :: rest => @instDecidableAnd (check pre e) (PrefixChecks check (pre ++ [e]) rest)
      (dec pre e) (checksDecidable check dec (pre ++ [e]) rest)

instance embed_legal_decidable (Γ : OrderedPrefixCode)
    (xs : List (Op (Instances.EmbedRGA.EOp α))) : Decidable ((embedClientSpec Γ).Legal xs) := by
  letI := checksDecidable (embedCheck Γ) (fun pre e => by
    unfold embedCheck
    split <;> infer_instance) [] xs
  exact decidable_of_iff (PrefixChecks (embedCheck Γ) [] xs) (embed_checks_legal Γ xs)

end Sal.MRDTs.Paper1.CertifiedRGAHistory
