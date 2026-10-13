import Sal.MRDTs.Instances.FugueMaxHonesty

namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode fmCoordOf fmCoordOf_append fmCoordOf_inj
  fmδ PosFMChain TagsOK sKey)

attribute [local instance] rc

def project (Γ : OrderedPrefixCode) (e : Op Payload) : Op FOp :=
  fOpOfM Γ (recordOf e)

@[simp] theorem project_time (Γ : OrderedPrefixCode) (e : Op Payload) :
    (project Γ e).1 = e.1 := by
  unfold project fOpOfM
  cases (recordOf e).op <;> cases (recordOf e).chain.getLast? <;> rfl

@[simp] theorem project_ins (Γ : OrderedPrefixCode) (e : Op Payload) :
    fIsIns (project Γ e) = mIsIns (recordOf e) := by
  unfold project fOpOfM mIsIns
  cases (recordOf e).op <;> cases (recordOf e).chain.getLast? <;> rfl

@[simp] theorem project_del (Γ : OrderedPrefixCode) (e : Op Payload) (x : ℕ) :
    (project Γ e).2.2 = .del x ↔ e.2.2.op = .del x := by
  unfold project fOpOfM recordOf
  cases e.2.2.op <;> cases e.2.2.chain.getLast? <;> simp

theorem project_coord (Γ : OrderedPrefixCode) (e : Op Payload)
    (hi : mIsIns (recordOf e) = true) (hne : e.2.2.chain ≠ []) :
    fCoord Γ (project Γ e) = fmCoordOf Γ e.2.2.chain := by
  obtain ⟨p, sd, hop⟩ := mIsIns_shape hi
  cases hl : e.2.2.chain.getLast? with
  | none => exact False.elim (hne (List.getLast?_eq_none_iff.mp hl))
  | some ent =>
      obtain ⟨pre, heq⟩ := List.getLast?_eq_some_iff.mp hl
      change fCoord Γ (fOpOfM Γ (recordOf e)) = _
      unfold fOpOfM
      rw [hop]
      rw [show (recordOf e).chain.getLast? = some ent from hl]
      simp [fCoord, recordOf, heq, fmCoordOf_append, fmCoordOf]

theorem rc_before (Γ : OrderedPrefixCode) (a b : Op Payload) :
    (datatype Γ).toUpdateSig.rc a b ↔
      mIsIns (recordOf a) = true ∧ b.2.2.op = .del a.1 := by
  rcases a with ⟨ta, ra, ⟨oa, la, roa, ca⟩⟩
  rcases b with ⟨tb, rb, ⟨ob, lb, rob, cb⟩⟩
  cases oa <;> cases ob <;> cases ha : ca.getLast? <;> cases hb : cb.getLast? <;>
    simp [UpdateSig.rc, ReplayPolicy.Before, rc, fRcOrder, fOpOfM, recordOf,
      mIsIns, ha, hb, eq_comm] <;> split <;> simp_all

theorem insert_delete_noncommuting (Γ : OrderedPrefixCode) (a b : Op Payload)
    (ha : mIsIns (recordOf a) = true) (hb : b.2.2.op = .del a.1) :
    ¬ (datatype Γ).toUpdateSig.commutes a b := by
  intro h
  have h0 := congrArg State.live (h ⟨[], ∅⟩)
  obtain ⟨p, sd, hop⟩ := mIsIns_shape ha
  change (mStep Γ (mStep Γ [] (recordOf a)) (recordOf b)) =
    mStep Γ (mStep Γ [] (recordOf b)) (recordOf a) at h0
  change a.2.2.op = .ins p sd at hop
  simp [mStep, recordOf, hop, hb, sIds, sInsert] at h0

theorem rc_visible {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    {a b : Op Payload} (ha : a ∈ C.events) (hb : b ∈ C.events)
    (hrc : (datatype Γ).toUpdateSig.rc a b) : C.vis a b := by
  obtain ⟨hi, hd⟩ := (rc_before Γ a b).mp hrc
  rcases delete_birth_of_mint C hmint htrans b hb a.1 hd with hz | ⟨c, hc, hv, _, ht⟩
  · have hp := (event_chain_of_mint C hmint htrans a ha).1
    exact False.elim ((Nat.ne_of_gt hp) hz)
  · have heq : c = a := C.replayContext.ts_unique hc ha ht
    simpa [heq] using hv

theorem lo_iff_rc {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    (E : Set (Op Payload)) {a b : Op Payload} (ha : a ∈ C.events) (hb : b ∈ C.events) :
    loOn C.replayContext E a b ↔ (datatype Γ).toUpdateSig.rc a b := by
  constructor
  · rintro (⟨hv, h | h⟩ | ⟨hn, _, h, _⟩)
    · exact h
    · have hr := rc_visible C hmint htrans hb ha h
      exact False.elim (Nat.lt_irrefl a.1 (Nat.lt_trans (C.causal_mono hv) (C.causal_mono hr)))
    · exact h
  · intro h
    exact Or.inl ⟨rc_visible C hmint htrans ha hb h, Or.inl h⟩

private theorem chain_nonempty {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    (e : Op Payload) (he : e ∈ C.events) (hi : mIsIns (recordOf e) = true) :
    e.2.2.chain ≠ [] := by
  obtain ⟨hp, hw⟩ := event_chain_of_mint C hmint htrans e he
  have hs := (hw hi).2.2
  intro hn
  simp [hn] at hs
  exact (Nat.ne_of_gt hp) hs.symm

theorem liveFold_project {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    (ops : List (Op Payload)) (hsub : ∀ e ∈ ops, e ∈ C.events) :
    mFold Γ (ops.map recordOf) = fFold Γ (ops.map (project Γ)) := by
  have h := mFold_eq_fFold Γ (ops.map recordOf) (by
    intro g hg hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
    exact chain_nonempty C hmint htrans e (hsub e he) hi)
  simpa only [List.map_map, project, Function.comp_def] using h

theorem projected_ids (Γ : OrderedPrefixCode) (ops : List (Op Payload)) :
    fInsIds (ops.map (project Γ)) =
      (ops.filter (fun e => mIsIns (recordOf e))).map Prod.fst := by
  induction ops with
  | nil => rfl
  | cons e ops ih =>
      cases hi : mIsIns (recordOf e) <;>
        simp [fInsIds, hi, project_ins, project_time, fInsIds] at ih ⊢ <;> exact ih

theorem projected_wf {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (hp : listPermOf ops E) (hsub : ∀ e ∈ E, e ∈ C.events)
    (hr : respects ops (loOn C.replayContext E)) : FWf Γ (ops.map (project Γ)) := by
  have hev : ∀ e ∈ ops, e ∈ C.events := fun e he => hsub e ((hp.2 e).mp he)
  constructor
  · rw [projected_ids]
    apply List.Nodup.map_on ?_ (hp.1.filter _)
    intro a ha b hb ht
    exact C.replayContext.ts_unique (hev a (List.mem_of_mem_filter ha))
      (hev b (List.mem_of_mem_filter hb)) ht
  · have hpair : (ops.map (project Γ)).Pairwise
        (fun a b => fIsIns b = true → a.2.2 ≠ .del b.1) := by
      rw [List.pairwise_map]
      apply hr.imp_of_mem
      intro a b ha hb hn hi hd
      apply hn
      apply (lo_iff_rc C hmint htrans E (hev b hb) (hev a ha)).mpr
      apply (rc_before Γ b a).mpr
      exact ⟨(project_ins Γ b) ▸ hi,
        (project_del Γ a b.1).mp (by simpa only [project_time] using hd)⟩
    intro pre e post heq hi hd
    obtain ⟨d, hd, hdel⟩ := mem_fDels.mp hd
    rw [heq] at hpair
    exact (List.pairwise_append.mp hpair).2.2 d hd e List.mem_cons_self hi hdel
  · intro a ha b hb hi hj hne hkey
    obtain ⟨ea, hea, rfl⟩ := List.mem_map.mp ha
    obtain ⟨eb, heb, rfl⟩ := List.mem_map.mp hb
    have hia : mIsIns (recordOf ea) = true := (project_ins Γ ea) ▸ hi
    have hib : mIsIns (recordOf eb) = true := (project_ins Γ eb) ▸ hj
    obtain ⟨pa, ta, sa⟩ := (event_chain_of_mint C hmint htrans ea (hev ea hea)).2 hia
    obtain ⟨pb, tb, sb⟩ := (event_chain_of_mint C hmint htrans eb (hev eb heb)).2 hib
    rw [project_coord Γ ea hia (chain_nonempty C hmint htrans ea (hev ea hea) hia),
      project_coord Γ eb hib (chain_nonempty C hmint htrans eb (hev eb heb) hib)] at hkey
    have heq := fmCoordOf_inj Γ pa pb ta tb (sKey_inj hkey)
    apply hne
    simp only [project_time]
    rw [← sa, ← sb, heq]

#print axioms projected_wf

def written (Γ : OrderedPrefixCode) (e : Op Payload) : SRec :=
  (e.1, e.1, fmCoordOf Γ e.2.2.chain)

theorem project_written (Γ : OrderedPrefixCode) (e : Op Payload)
    (hi : mIsIns (recordOf e) = true) (hne : e.2.2.chain ≠ []) :
    fRecOf Γ (project Γ e) = written Γ e := by
  have hc := project_coord Γ e hi hne
  obtain ⟨p, sd, hop⟩ := mIsIns_shape hi
  unfold fRecOf
  rw [project_time, hc]
  unfold project fOpOfM
  rw [hop]
  cases (recordOf e).chain.getLast? <;> rfl

theorem live_membership {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (hp : listPermOf ops E) (hsub : ∀ e ∈ E, e ∈ C.events)
    (hr : respects ops (loOn C.replayContext E)) (r : SRec) :
    r ∈ mFold Γ (ops.map recordOf) ↔
      (∃ e ∈ E, mIsIns (recordOf e) = true ∧ r = written Γ e) ∧
      ∀ d ∈ E, d.2.2.op ≠ .del r.1 := by
  rw [liveFold_project C hmint htrans ops (fun e he => hsub e ((hp.2 e).mp he)),
    f_fold_mem Γ (projected_wf C hmint htrans hp hsub hr)]
  constructor
  · rintro ⟨⟨p, hpm, hi, heq⟩, hd⟩
    obtain ⟨e, hem, rfl⟩ := List.mem_map.mp hpm
    have hi' := (project_ins Γ e) ▸ hi
    have he := (hp.2 e).mp hem
    refine ⟨⟨e, he, hi', ?_⟩, ?_⟩
    · rw [heq, project_written Γ e hi' (chain_nonempty C hmint htrans e (hsub e he) hi')]
    · intro d hdm hdel
      apply hd
      exact mem_fDels.mpr ⟨project Γ d, List.mem_map.mpr ⟨d, (hp.2 d).mpr hdm, rfl⟩,
        (project_del Γ d r.1).mpr hdel⟩
  · rintro ⟨⟨e, he, hi, heq⟩, hd⟩
    refine ⟨⟨project Γ e, List.mem_map.mpr ⟨e, (hp.2 e).mpr he, rfl⟩,
      by simpa using hi, ?_⟩, ?_⟩
    · rw [project_written Γ e hi (chain_nonempty C hmint htrans e (hsub e he) hi)]
      exact heq
    · intro hdel
      obtain ⟨d, hdm, hdel⟩ := mem_fDels.mp hdel
      obtain ⟨e, hem, rfl⟩ := List.mem_map.mp hdm
      exact hd e ((hp.2 e).mp hem) ((project_del Γ e r.1).mp hdel)

theorem live_ids {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (hp : listPermOf ops E) (hsub : ∀ e ∈ E, e ∈ C.events)
    (hr : respects ops (loOn C.replayContext E)) (x : ℕ) :
    x ∈ sIds (mFold Γ (ops.map recordOf)) ↔
      (∃ e ∈ E, mIsIns (recordOf e) = true ∧ e.1 = x) ∧
      ∀ d ∈ E, d.2.2.op ≠ .del x := by
  constructor
  · intro hx
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨⟨e, he, hi, rfl⟩, hd⟩ := (live_membership C hmint htrans hp hsub hr r).mp hm
    exact ⟨⟨e, he, hi, rfl⟩, hd⟩
  · rintro ⟨⟨e, he, hi, ht⟩, hd⟩
    apply List.mem_map.mpr
    refine ⟨written Γ e, (live_membership C hmint htrans hp hsub hr _).mpr
      ⟨⟨e, he, hi, rfl⟩, ?_⟩, ht⟩
    simpa only [written, ht] using hd

theorem live_sorted {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (hp : listPermOf ops E) (hsub : ∀ e ∈ E, e ∈ C.events)
    (hr : respects ops (loOn C.replayContext E)) :
    SSorted (mFold Γ (ops.map recordOf)) := by
  rw [liveFold_project C hmint htrans ops (fun e he => hsub e ((hp.2 e).mp he))]
  exact f_fold_sorted Γ (projected_wf C hmint htrans hp hsub hr)

def birthsFirst (ops : List (Op Payload)) : List (Op Payload) :=
  ops.mergeSort (fun a b => mIsIns (recordOf a) || !mIsIns (recordOf b))

theorem birthsFirst_perm (ops : List (Op Payload)) : ops.Perm (birthsFirst ops) :=
  (List.mergeSort_perm _ _).symm

theorem birthsFirst_respects {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    {ops : List (Op Payload)} (hsub : ∀ e ∈ ops, e ∈ C.events) (E : Set (Op Payload)) :
    respects (birthsFirst ops) (loOn C.replayContext E) := by
  have hpair : (birthsFirst ops).Pairwise (fun a b =>
      (mIsIns (recordOf a) || !mIsIns (recordOf b)) = true) := by
    apply List.pairwise_mergeSort
    · intro a b c
      cases mIsIns (recordOf a) <;> cases mIsIns (recordOf b) <;>
        cases mIsIns (recordOf c) <;> simp
    · intro a b
      cases mIsIns (recordOf a) <;> cases mIsIns (recordOf b) <;> simp
  apply hpair.imp_of_mem
  intro a b ha hb hab hlo
  have haC := hsub a ((birthsFirst_perm ops).mem_iff.mpr ha)
  have hbC := hsub b ((birthsFirst_perm ops).mem_iff.mpr hb)
  obtain ⟨hi, hd⟩ := (rc_before Γ b a).mp ((lo_iff_rc C hmint htrans E hbC haC).mp hlo)
  have hia : mIsIns (recordOf a) = false := by simp [mIsIns, recordOf, hd]
  simp [hi, hia] at hab

theorem same_written_of_key {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    {a b : Op Payload} (ha : a ∈ C.events) (hb : b ∈ C.events)
    (hi : mIsIns (recordOf a) = true) (hj : mIsIns (recordOf b) = true)
    (hk : sKey (written Γ a).2.2 = sKey (written Γ b).2.2) : a = b := by
  obtain ⟨pa, ta, sa⟩ := (event_chain_of_mint C hmint htrans a ha).2 hi
  obtain ⟨pb, tb, sb⟩ := (event_chain_of_mint C hmint htrans b hb).2 hj
  have hc := fmCoordOf_inj Γ pa pb ta tb (sKey_inj hk)
  apply C.replayContext.ts_unique ha hb
  rw [← sa, ← sb, hc]

theorem birth_closed {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    {E : Set (Op Payload)} (hsub : ∀ e ∈ E, e ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → ¬ (datatype Γ).toUpdateSig.commutes a b → b ∈ E → a ∈ E)
    {d : Op Payload} (hd : d ∈ E) {x : ℕ} (hx : x ≠ 0) (hdel : d.2.2.op = .del x) :
    ∃ a ∈ E, mIsIns (recordOf a) = true ∧ a.1 = x := by
  rcases delete_birth_of_mint C hmint htrans d (hsub d hd) x hdel with hz | ⟨a, ha, hv, hi, ht⟩
  · exact False.elim (hx hz)
  · exact ⟨a, hclosed a d hv (insert_delete_noncommuting Γ a d hi (ht ▸ hdel)) hd, hi, ht⟩

theorem merge_live_membership {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    {E₁ E₂ : Set (Op Payload)} {ops₀ ops₁ ops₂ : List (Op Payload)}
    (sub₁ : ∀ e ∈ E₁, e ∈ C.events) (sub₂ : ∀ e ∈ E₂, e ∈ C.events)
    (cl₁ : ∀ a b, C.vis a b → ¬ (datatype Γ).toUpdateSig.commutes a b → b ∈ E₁ → a ∈ E₁)
    (cl₂ : ∀ a b, C.vis a b → ¬ (datatype Γ).toUpdateSig.commutes a b → b ∈ E₂ → a ∈ E₂)
    (hp₀ : listPermOf ops₀ (E₁ ∩ E₂)) (hp₁ : listPermOf ops₁ E₁) (hp₂ : listPermOf ops₂ E₂)
    (hr₀ : respects ops₀ (loOn C.replayContext (E₁ ∩ E₂)))
    (hr₁ : respects ops₁ (loOn C.replayContext E₁))
    (hr₂ : respects ops₂ (loOn C.replayContext E₂)) (r : SRec) :
    r ∈ sMerge (mFold Γ (ops₀.map recordOf))
      (mFold Γ (ops₁.map recordOf)) (mFold Γ (ops₂.map recordOf)) ↔
      (∃ e ∈ E₁ ∪ E₂, mIsIns (recordOf e) = true ∧ r = written Γ e) ∧
      ∀ d ∈ E₁ ∪ E₂, d.2.2.op ≠ .del r.1 := by
  classical
  have sub₀ : ∀ e ∈ E₁ ∩ E₂, e ∈ C.events := fun e he => sub₁ e he.1
  have mem₁ := live_membership C hmint htrans hp₁ sub₁ hr₁
  have mem₂ := live_membership C hmint htrans hp₂ sub₂ hr₂
  have ids₀ := live_ids C hmint htrans hp₀ sub₀ hr₀
  have ids₁ := live_ids C hmint htrans hp₁ sub₁ hr₁
  have ids₂ := live_ids C hmint htrans hp₂ sub₂ hr₂
  rw [sMerge, mem_sMerge2]
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (⟨hr, cond⟩ | ⟨hr, cond⟩)
    · obtain ⟨⟨e, he, hi, heq⟩, nd⟩ := (mem₁ r).mp hr
      have ht : e.1 = r.1 := (congrArg Prod.fst heq).symm
      have hpos : r.1 ≠ 0 := ht ▸ Nat.ne_of_gt (event_chain_of_mint C hmint htrans e (sub₁ e he)).1
      refine ⟨⟨e, Or.inl he, hi, heq⟩, ?_⟩
      intro d hd hdel
      rcases hd with hd | hd
      · exact nd d hd hdel
      · rcases cond with h₂ | hn₀
        · exact ((ids₂ r.1).mp h₂).2 d hd hdel
        · obtain ⟨a, ha, _, hat⟩ := birth_closed C hmint htrans sub₂ cl₂ hd hpos hdel
          have hae : a = e := C.replayContext.ts_unique (sub₂ a ha) (sub₁ e he) (hat.trans ht.symm)
          subst a
          apply hn₀
          exact (ids₀ r.1).mpr ⟨⟨e, ⟨he, ha⟩, hi, ht⟩, fun d hd => nd d hd.1⟩
    · obtain ⟨⟨e, he, hi, heq⟩, nd⟩ := (mem₂ r).mp hr
      have ht : e.1 = r.1 := (congrArg Prod.fst heq).symm
      have hpos : r.1 ≠ 0 := ht ▸ Nat.ne_of_gt (event_chain_of_mint C hmint htrans e (sub₂ e he)).1
      refine ⟨⟨e, Or.inr he, hi, heq⟩, ?_⟩
      intro d hd hdel
      rcases hd with hd | hd
      · obtain ⟨a, ha, _, hat⟩ := birth_closed C hmint htrans sub₁ cl₁ hd hpos hdel
        have hae : a = e := C.replayContext.ts_unique (sub₁ a ha) (sub₂ e he) (hat.trans ht.symm)
        subst a
        apply cond.1
        exact (ids₀ r.1).mpr ⟨⟨e, ⟨ha, he⟩, hi, ht⟩, fun d hd => nd d hd.2⟩
      · exact nd d hd hdel
  · rintro ⟨⟨e, he, hi, heq⟩, nd⟩
    have ht : e.1 = r.1 := (congrArg Prod.fst heq).symm
    by_cases h₁ : e ∈ E₁
    · left
      refine ⟨(mem₁ r).mpr ⟨⟨e, h₁, hi, heq⟩, fun d hd => nd d (Or.inl hd)⟩, ?_⟩
      by_cases h₀ : r.1 ∈ sIds (mFold Γ (ops₀.map recordOf))
      · left
        obtain ⟨⟨a, ha, hai, hat⟩, _⟩ := (ids₀ r.1).mp h₀
        exact (ids₂ r.1).mpr ⟨⟨a, ha.2, hai, hat⟩, fun d hd => nd d (Or.inr hd)⟩
      · exact Or.inr h₀
    · right
      have h₂ : e ∈ E₂ := he.resolve_left h₁
      refine ⟨(mem₂ r).mpr ⟨⟨e, h₂, hi, heq⟩, fun d hd => nd d (Or.inr hd)⟩, ?_, ?_⟩
      · intro h₀
        obtain ⟨⟨a, ha, _, hat⟩, _⟩ := (ids₀ r.1).mp h₀
        have hae : a = e := C.replayContext.ts_unique (sub₁ a ha.1) (sub₂ e h₂) (hat.trans ht.symm)
        exact h₁ (hae ▸ ha.1)
      · intro h₁'
        obtain ⟨⟨a, ha, _, hat⟩, _⟩ := (ids₁ r.1).mp h₁'
        have hae : a = e := C.replayContext.ts_unique (sub₁ a ha) (sub₂ e h₂) (hat.trans ht.symm)
        exact h₁ (hae ▸ ha)

theorem join_of_mint {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) :
    JoinAt (datatype Γ) C.replayContext := by
  intro E₁ E₂ s₀ s₁ s₂ htrans hirr sub₁ sub₂ cl₁ cl₂ h₀ h₁ h₂
  classical
  obtain ⟨ops₀, hp₀, hr₀, hf₀⟩ := h₀
  obtain ⟨ops₁, hp₁, hr₁, hf₁⟩ := h₁
  obtain ⟨ops₂, hp₂, hr₂, hf₂⟩ := h₂
  have subU : ∀ e ∈ E₁ ∪ E₂, e ∈ C.events := by
    intro e he
    exact he.elim (sub₁ e) (sub₂ e)
  let ops := (ops₁ ++ ops₂).dedup
  have hp : listPermOf ops (E₁ ∪ E₂) := by
    refine ⟨List.nodup_dedup _, ?_⟩
    intro e
    simp only [ops, List.mem_dedup, List.mem_append, hp₁.2 e, hp₂.2 e, Set.mem_union]
  have hperm := birthsFirst_perm ops
  have hpU : listPermOf (birthsFirst ops) (E₁ ∪ E₂) :=
    ⟨hperm.nodup hp.1, fun e => hperm.mem_iff.symm.trans (hp.2 e)⟩
  have hrU := birthsFirst_respects C hmint (fun _ _ _ => htrans)
    (fun e he => subU e ((hp.2 e).mp he)) (E₁ ∪ E₂)
  refine ⟨birthsFirst ops, hpU, hrU, ?_⟩
  rw [rawFold_records] at hf₀ hf₁ hf₂ ⊢
  rw [← hf₀, ← hf₁, ← hf₂]
  change stateOf Γ ((birthsFirst ops).map recordOf) =
    rawMerge (stateOf Γ (ops₀.map recordOf))
      (stateOf Γ (ops₁.map recordOf)) (stateOf Γ (ops₂.map recordOf))
  have htr : Transitive C.vis := fun _ _ _ => htrans
  have liveEq : mFold Γ ((birthsFirst ops).map recordOf) =
      sMerge (mFold Γ (ops₀.map recordOf))
        (mFold Γ (ops₁.map recordOf)) (mFold Γ (ops₂.map recordOf)) := by
    apply ssorted_ext (live_sorted C hmint htr hpU subU hrU)
      (sMerge_sorted (live_sorted C hmint htr hp₁ sub₁ hr₁)
        (live_sorted C hmint htr hp₂ sub₂ hr₂) ?_)
    · intro r
      rw [live_membership C hmint htr hpU subU hrU,
        merge_live_membership C hmint htr sub₁ sub₂ cl₁ cl₂ hp₀ hp₁ hp₂ hr₀ hr₁ hr₂]
    · intro r₁ hr₁' r₂ hr₂' hk
      obtain ⟨⟨a, ha, hi, rfl⟩, _⟩ := (live_membership C hmint htr hp₁ sub₁ hr₁ r₁).mp hr₁'
      obtain ⟨⟨b, hb, hj, rfl⟩, _⟩ := (live_membership C hmint htr hp₂ sub₂ hr₂ r₂).mp hr₂'
      rw [same_written_of_key C hmint htr (sub₁ a ha) (sub₂ b hb) hi hj hk]
  unfold stateOf rawMerge
  rw [liveEq]
  congr 1
  ext g
  simp only [Finset.mem_union, List.mem_toFinset, mMinted, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨e, he, rfl⟩, hi⟩
    rcases (hpU.2 e).mp he with h | h
    · exact Or.inl ⟨⟨e, (hp₁.2 e).mpr h, rfl⟩, hi⟩
    · exact Or.inr ⟨⟨e, (hp₂.2 e).mpr h, rfl⟩, hi⟩
  · rintro (⟨⟨e, he, rfl⟩, hi⟩ | ⟨⟨e, he, rfl⟩, hi⟩)
    · exact ⟨⟨e, (hpU.2 e).mpr (Or.inl ((hp₁.2 e).mp he)), rfl⟩, hi⟩
    · exact ⟨⟨e, (hpU.2 e).mpr (Or.inr ((hp₂.2 e).mp he)), rfl⟩, hi⟩

#print axioms join_of_mint

def replayAdequacy (Γ : OrderedPrefixCode) :
    ReplayAdequacyCertificate (datatype Γ) (generation Γ) where
  soundV h := replayWitness_of_mintCertifiedV (fun C hm => join_of_mint C hm) h

/-- The actual enriched implementation has one replay witness that also
satisfies all three maximal-non-interleaving clauses. Both execution modes
are covered, and the caller supplies no generation-model reachability proof. -/
theorem replay_noninterleaving {Γ : OrderedPrefixCode}
    {C : Configuration (datatype Γ)}
    (h : CertifiedExecution (datatype Γ) (generation Γ) C)
    (v : Version) (s : State) (E : Set (Op Payload)) (hv : C.ver v = some (s, E)) :
    ∃ ops : List (Op Payload), listPermOf ops E ∧
      respects ops (loOn C.replayContext E) ∧
      applySeq (datatype Γ).toUpdateSig (datatype Γ).init ops = s ∧
      MaxNonInterleavingM Γ (ops.map recordOf) := by
  have hc := h.canonicalConfig (fun C hm => join_of_mint C hm)
  obtain ⟨ops, hp, hr, hf⟩ := hc.canonical v s E hv
  refine ⟨ops, hp, hr, hf, noninterleaving_of_mint C h.mintHonest
    (fun _ _ _ => hc.vis_trans) ops hp.1 ?_ ?_⟩
  · intro e he
    exact hc.version_events_supported v s E hv e ((hp.2 e).mp he)
  · intro a b hab hb
    exact (hp.2 a).mpr (hc.version_events_causal v s E hv a b hab ((hp.2 b).mp hb))

#print axioms replay_noninterleaving

end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
