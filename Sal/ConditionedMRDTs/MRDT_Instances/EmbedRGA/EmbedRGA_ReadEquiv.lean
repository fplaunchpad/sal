import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA
import Sal.MRDTs.RGA_Embed.RGA_Embed_ReadEquiv

/-!
# The compaction theorem: the embed read IS the published RGA's read

This file supplies everything but the order core, which is
`Sal/MRDTs/RGA_Embed/RGA_Embed_ReadEquiv.lean`. One event set, two folds:

* the **embed fold** `eFold Γ ρ`, live records sorted by coordinate; its
  id sequence *is* the read;
* the **RGA† fold** `rgaFold ρ`, the published tombstoned RGA
  (`Sal/MRDTs/RGA_with_tombstones`) folded over the same enumeration with
  the ghost prefix `π` dropped (`toRgaOp`, the wire format of
  `sal-mrdts.tex` §3); its read is relational: the `visible` ids in
  `visible_lt` order.

The capstone (`rga_read_eq_embed_read`): **any** `visible_lt`-sorted
enumeration of the RGA† fold's visible ids equals the embed fold's id
sequence. The published RGA's read, whatever executable form it takes,
is the embed read; the embedded-chain RGA is the tombstoned RGA with the
tombstone set compressed into the coordinates. The Python lockstep
(120/120) is this theorem's tested form.

Hypotheses: the §8 generation discipline (`EAppDiscipline`, the same
hypothesis that discharges honesty for the RA-linearizability capstone)
plus a well-formed enumeration of the event set (`EWf`, dischargeable by
`e_wf_of_enum` for any `loOn`-respecting enumeration).
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode keyLt key PosChain coordOf coordOf_inj
  coordOf_append keyLt_asymm keyLt_irrefl RealId TreeId BirthEnv
  chainBefore chainBefore_display display_iff_chainBefore
  posChain_of_treeId visible_lt_iff_chainBefore visible_lt_chainBefore
  chainBefore_visible_lt)

/-! ## §1  The wire translation and the RGA† fold -/

/-- Translate an embed op to the published RGA's op type. The ghost prefix
`π` is DROPPED, this is `sal-mrdts.tex`'s claim that `π` may be omitted
from the wire, made syntactic. -/
def toRgaOp : Op EOp → _root_.op_t
  | (t, r, .ins e _ a) => (t, r, _root_.app_op_t.Add_after a e)
  | (t, r, .del x)     => (t, r, _root_.app_op_t.Remove x)

/-- The published RGA's fold of (the translation of) an enumeration. -/
def rgaFold (ρ : List (Op EOp)) : _root_.concrete_st :=
  ρ.foldl (fun s o => _root_.do_ s (toRgaOp o)) _root_.init_st

theorem rgaFold_snoc (ρ : List (Op EOp)) (e : Op EOp) :
    rgaFold (ρ ++ [e]) = _root_.do_ (rgaFold ρ) (toRgaOp e) := by
  unfold rgaFold
  rw [List.foldl_append]
  rfl

theorem mem_add_iff {a : Type} [DecidableEq a] (v x : a) (s : _root_.set a) :
    mem v (add x s) = true ↔ mem v s = true ∨ v = x := by
  simp [mem, add, union, _root_.singleton]

/-- Insert-record membership in the RGA† fold, order-free: a record is
present iff its insert op is in the enumeration (any replica id, any
dropped prefix). -/
theorem rgaFold_fst_mem : ∀ (ρ : List (Op EOp)) (c p e : ℕ),
    mem (c, p, e) (rgaFold ρ).1 = true ↔
      ∃ r π, (c, r, EOp.ins e π p) ∈ ρ := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
      intro c p e
      simp [rgaFold, _root_.init_st]
  | append_singleton ρ o ih =>
      intro c p e
      rw [rgaFold_snoc]
      obtain ⟨ts, rr, op⟩ := o
      cases op with
      | ins el π a =>
          rw [show _root_.do_ (rgaFold ρ)
                (toRgaOp (ts, rr, EOp.ins el π a)) =
              (add (ts, (a, el)) (rgaFold ρ).1, (rgaFold ρ).2) from rfl]
          rw [show ((add (ts, (a, el)) (rgaFold ρ).1, (rgaFold ρ).2) :
                _root_.concrete_st).1 =
              add (ts, (a, el)) (rgaFold ρ).1 from rfl]
          rw [mem_add_iff, ih]
          constructor
          · rintro (⟨r, π', hm⟩ | heq)
            · exact ⟨r, π', List.mem_append_left _ hm⟩
            · simp only [Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl, rfl⟩ := heq
              exact ⟨rr, π, List.mem_append_right _ (by simp)⟩
          · rintro ⟨r, π', hm⟩
            rcases List.mem_append.mp hm with h | h
            · exact Or.inl ⟨r, π', h⟩
            · simp only [List.mem_singleton, Prod.mk.injEq,
                EOp.ins.injEq] at h
              obtain ⟨rfl, -, rfl, -, rfl⟩ := h
              exact Or.inr rfl
      | del x =>
          rw [show _root_.do_ (rgaFold ρ) (toRgaOp (ts, rr, EOp.del x)) =
              ((rgaFold ρ).1, add x (rgaFold ρ).2) from rfl]
          rw [show (((rgaFold ρ).1, add x (rgaFold ρ).2) :
                _root_.concrete_st).1 = (rgaFold ρ).1 from rfl]
          rw [ih]
          constructor
          · rintro ⟨r, π', hm⟩
            exact ⟨r, π', List.mem_append_left _ hm⟩
          · rintro ⟨r, π', hm⟩
            rcases List.mem_append.mp hm with h | h
            · exact ⟨r, π', h⟩
            · simp at h

/-- Tombstone membership in the RGA† fold = the delete targets of the
enumeration. -/
theorem rgaFold_snd_mem : ∀ (ρ : List (Op EOp)) (x : ℕ),
    mem x (rgaFold ρ).2 = true ↔ x ∈ eDels ρ := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
      intro x
      simp [rgaFold, _root_.init_st, eDels]
  | append_singleton ρ o ih =>
      intro x
      rw [rgaFold_snoc, eDels_append]
      obtain ⟨ts, rr, op⟩ := o
      cases op with
      | ins el π a =>
          rw [show _root_.do_ (rgaFold ρ)
                (toRgaOp (ts, rr, EOp.ins el π a)) =
              (add (ts, (a, el)) (rgaFold ρ).1, (rgaFold ρ).2) from rfl]
          rw [show ((add (ts, (a, el)) (rgaFold ρ).1, (rgaFold ρ).2) :
                _root_.concrete_st).2 = (rgaFold ρ).2 from rfl]
          rw [ih]
          simp [eDels]
      | del y =>
          rw [show _root_.do_ (rgaFold ρ) (toRgaOp (ts, rr, EOp.del y)) =
              ((rgaFold ρ).1, add y (rgaFold ρ).2) from rfl]
          rw [show (((rgaFold ρ).1, add y (rgaFold ρ).2) :
                _root_.concrete_st).2 = add y (rgaFold ρ).2 from rfl]
          rw [mem_add_iff, ih]
          simp [eDels]

/-! ## §2  The edge and visibility bridges -/

/-- The RGA† fold's `after_of` edge = an insert of the enumeration with
that anchor. Both models' birth trees are THE birth tree of `ρ`. -/
theorem after_of_rgaFold {ρ : List (Op EOp)} {c p : ℕ} :
    _root_.after_of (rgaFold ρ) c p ↔
      ∃ r π e, (c, r, EOp.ins e π p) ∈ ρ := by
  unfold _root_.after_of
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨r, π, hm⟩ := (rgaFold_fst_mem ρ c p e).mp he
    exact ⟨r, π, e, hm⟩
  · rintro ⟨r, π, e, hm⟩
    exact ⟨e, (rgaFold_fst_mem ρ c p e).mpr ⟨r, π, hm⟩⟩

/-- Visibility in the RGA† fold = inserted somewhere, never deleted, the
same order-free description `e_fold_id_mem` gives for the embed fold. -/
theorem visible_rgaFold {ρ : List (Op EOp)} {t : ℕ} :
    _root_.visible (rgaFold ρ) t ↔
      (∃ o ∈ ρ, eIsIns o = true ∧ o.1 = t) ∧ t ∉ eDels ρ := by
  unfold _root_.visible
  constructor
  · rintro ⟨⟨r, e, he⟩, htomb⟩
    obtain ⟨rr, π, hm⟩ := (rgaFold_fst_mem ρ t r e).mp he
    refine ⟨⟨(t, rr, EOp.ins e π r), hm, by simp [eIsIns], rfl⟩, ?_⟩
    intro hdel
    rw [(rgaFold_snd_mem ρ t).mpr hdel] at htomb
    exact Bool.noConfusion htomb
  · rintro ⟨⟨o, hm, hins, hot⟩, hdel⟩
    obtain ⟨ts, rr, op⟩ := o
    cases op with
    | del y => simp [eIsIns] at hins
    | ins el π a =>
        simp only at hot
        subst hot
        refine ⟨⟨a, el, (rgaFold_fst_mem ρ ts a el).mpr ⟨rr, π, hm⟩⟩, ?_⟩
        cases htomb : mem ts (rgaFold ρ).2 with
        | false => rfl
        | true => exact absurd ((rgaFold_snd_mem ρ ts).mp htomb) hdel

/-- **The visibility bridge** (step 3): the RGA† fold's visible ids are
exactly the embed fold's live ids. -/
theorem visible_iff_eIds {Γ : OrderedPrefixCode} {ρ : List (Op EOp)}
    (hwf : EWf Γ ρ) (t : ℕ) :
    _root_.visible (rgaFold ρ) t ↔ t ∈ eIds (eFold Γ ρ) := by
  rw [visible_rgaFold, e_fold_id_mem Γ hwf]

/-! ## §3  The birth environment at the folds -/

/-- The §8 generation discipline, named: every op was applicable at some
fold of its issuer's causal past. The same hypothesis that discharges
honesty for the RA-linearizability capstone (`eHonest_of_applicable`). -/
abbrev EAppDiscipline (Γ : OrderedPrefixCode) (C : Configuration (E Γ)) :
    Prop :=
  ∀ e ∈ C.events, ∃ π : List (Op EOp),
    listPermOf π {e' ∈ C.events | C.vis e' e} ∧
    eApplicable e (eFold Γ π)

/-- The global chain assignment of an honest configuration (choice over
`e_chain_exists`). -/
noncomputable def eChainOf {Γ : OrderedPrefixCode}
    (C : Configuration (E Γ)) (hApp : EAppDiscipline Γ C) : ℕ → List ℕ :=
  fun t => Classical.choose (e_chain_exists C hApp t)

theorem eChainOf_spec {Γ : OrderedPrefixCode} (C : Configuration (E Γ))
    (hApp : EAppDiscipline Γ C) (t : ℕ) :
    PosChain (eChainOf C hApp t) ∧ (eChainOf C hApp t).sum = t ∧
    ∀ o ∈ C.events, eIsIns o = true → o.1 = t →
      eCoord Γ o = coordOf Γ (eChainOf C hApp t) :=
  Classical.choose_spec (e_chain_exists C hApp t)

theorem eChainOf_zero {Γ : OrderedPrefixCode} (C : Configuration (E Γ))
    (hApp : EAppDiscipline Γ C) : eChainOf C hApp 0 = [] := by
  obtain ⟨hpos, hsum, -⟩ := eChainOf_spec C hApp 0
  cases hch : eChainOf C hApp 0 with
  | nil => rfl
  | cons d ds =>
      rw [hch] at hpos hsum
      have := hpos d List.mem_cons_self
      have hge : ds.sum ≥ 0 := Nat.zero_le _
      simp [List.sum_cons] at hsum
      omega

/-- **The birth environment at the RGA† fold** (steps 1–2): under the
generation discipline, the RGA† fold of any enumeration of the event set,
together with the honest chain assignment, satisfies every fact the order
core consumes. -/
theorem birthEnv_rgaFold {Γ : OrderedPrefixCode} {C : Configuration (E Γ)}
    (hApp : EAppDiscipline Γ C) {ρ : List (Op EOp)}
    (hperm : listPermOf ρ C.events) :
    BirthEnv (rgaFold ρ) (eChainOf C hApp) := by
  constructor
  case anchor_lt =>
    intro c p h
    obtain ⟨r, π, e, hm⟩ := after_of_rgaFold.mp h
    obtain ⟨πe, hπe, happ⟩ := hApp _ ((hperm.2 _).mp hm)
    simp only [eApplicable] at happ
    exact happ.1
  case anchor_real =>
    intro c p h hp0
    obtain ⟨r, π, e, hm⟩ := after_of_rgaFold.mp h
    obtain ⟨πe, hπe, happ⟩ := hApp _ ((hperm.2 _).mp hm)
    simp only [eApplicable] at happ
    rcases happ.2 with ⟨ha0, -⟩ | ⟨el', hmem⟩
    · exact absurd ha0 hp0
    · obtain ⟨aop, haπ, hai, hae⟩ := e_fold_rec_sub Γ πe (p, el', π) hmem
      have haev : aop ∈ C.events := ((hπe.2 aop).mp haπ).1
      have hap : aop.1 = p := by
        have := congrArg Prod.fst hae
        exact this.symm
      obtain ⟨ap, ar, aop2⟩ := aop
      cases aop2 with
      | del y => simp [eIsIns] at hai
      | ins ae aπ aa =>
          simp only at hap
          subst hap
          exact ⟨aa, after_of_rgaFold.mpr
            ⟨ar, aπ, ae, (hperm.2 _).mpr haev⟩⟩
  case chain_zero => exact eChainOf_zero C hApp
  case chain_step =>
    intro c p h
    obtain ⟨r, π, e, hm⟩ := after_of_rgaFold.mp h
    have hev := (hperm.2 _).mp hm
    obtain ⟨πe, hπe, happ⟩ := hApp _ hev
    simp only [eApplicable] at happ
    obtain ⟨hpc, hcase⟩ := happ
    obtain ⟨hpos_c, -, hpin_c⟩ := eChainOf_spec C hApp c
    have hcoord : π ++ Γ.enc (c - p) = coordOf Γ (eChainOf C hApp c) := by
      have := hpin_c _ hev (by simp [eIsIns]) rfl
      simpa [eCoord] using this
    rcases hcase with ⟨hp0, hπ0⟩ | ⟨el', hmem⟩
    · -- front insert: the chain is the singleton delta
      subst hp0
      subst hπ0
      have h1 : coordOf Γ (eChainOf C hApp c) = coordOf Γ [c] := by
        rw [← hcoord]
        simp [coordOf]
      have hpos1 : PosChain [c] := by
        intro d hd
        simp at hd
        omega
      rw [coordOf_inj Γ hpos_c hpos1 h1, eChainOf_zero C hApp]
      simp
    · -- anchored insert: the carried prefix is the anchor's chain coord
      obtain ⟨aop, haπ, hai, hae⟩ := e_fold_rec_sub Γ πe (p, el', π) hmem
      have haev : aop ∈ C.events := ((hπe.2 aop).mp haπ).1
      have hap : aop.1 = p := (congrArg Prod.fst hae).symm
      have hπval : π = eCoord Γ aop :=
        congrArg (fun q : ERec => q.2.2) hae
      obtain ⟨hpos_p, -, hpin_p⟩ := eChainOf_spec C hApp p
      have hπchain : π = coordOf Γ (eChainOf C hApp p) := by
        rw [hπval]
        exact hpin_p aop haev hai hap
      have hkey : coordOf Γ (eChainOf C hApp c) =
          coordOf Γ (eChainOf C hApp p ++ [c - p]) := by
        rw [← hcoord, hπchain, coordOf_append]
        simp [coordOf]
      have hpos2 : PosChain (eChainOf C hApp p ++ [c - p]) := by
        intro d hd
        rcases List.mem_append.mp hd with h' | h'
        · exact hpos_p d h'
        · simp at h'
          omega
      exact coordOf_inj Γ hpos_c hpos2 hkey

/-! ## §4  The order equivalence at the folds -/

/-- Every live id of the embed fold has an insert record in the RGA†
fold. -/
theorem realId_of_fold {Γ : OrderedPrefixCode} {ρ : List (Op EOp)}
    {r : ERec} (hr : r ∈ eFold Γ ρ) : RealId (rgaFold ρ) r.1 := by
  obtain ⟨o, ho, hoi, hrec⟩ := e_fold_rec_sub Γ ρ r hr
  obtain ⟨ts, rr, op⟩ := o
  cases op with
  | del y => simp [eIsIns] at hoi
  | ins el π a =>
      refine ⟨a, after_of_rgaFold.mpr ⟨rr, π, el, ?_⟩⟩
      have : r.1 = ts := by rw [hrec]; rfl
      rw [this]
      exact ho

/-- Every record's coordinate in the embed fold is its id's chain
coordinate. -/
theorem fold_coord_pinned {Γ : OrderedPrefixCode} {C : Configuration (E Γ)}
    (hApp : EAppDiscipline Γ C) {ρ : List (Op EOp)}
    (hperm : listPermOf ρ C.events) {r : ERec} (hr : r ∈ eFold Γ ρ) :
    r.2.2 = coordOf Γ (eChainOf C hApp r.1) := by
  obtain ⟨o, ho, hoi, hrec⟩ := e_fold_rec_sub Γ ρ r hr
  obtain ⟨-, -, hpin⟩ := eChainOf_spec C hApp r.1
  have h1 : r.2.2 = eCoord Γ o := by rw [hrec]; rfl
  have h2 : o.1 = r.1 := by rw [hrec]; rfl
  rw [h1]
  exact hpin o ((hperm.2 o).mp ho) hoi h2

/-- **The embed read is `visible_lt`-sorted** (step 5, sortedness half):
the embed fold's id sequence is pairwise-increasing in the published
RGA's visible order. -/
theorem embed_read_pairwise {Γ : OrderedPrefixCode} {C : Configuration (E Γ)}
    (hApp : EAppDiscipline Γ C) {ρ : List (Op EOp)}
    (hperm : listPermOf ρ C.events) (hwf : EWf Γ ρ) :
    (eIds (eFold Γ ρ)).Pairwise (_root_.visible_lt (rgaFold ρ)) := by
  have B := birthEnv_rgaFold hApp hperm
  have hsorted := e_fold_sorted Γ hwf
  unfold eIds
  rw [List.pairwise_map]
  refine hsorted.imp_of_mem ?_
  intro r r' hr hr' hkey
  have hpin := fold_coord_pinned hApp hperm hr
  have hpin' := fold_coord_pinned hApp hperm hr'
  rw [hpin, hpin'] at hkey
  obtain ⟨hpos, -, -⟩ := eChainOf_spec C hApp r.1
  obtain ⟨hpos', -, -⟩ := eChainOf_spec C hApp r'.1
  have hchne : eChainOf C hApp r.1 ≠ eChainOf C hApp r'.1 := by
    intro heq
    rw [heq, keyLt_irrefl] at hkey
    exact Bool.noConfusion hkey
  exact chainBefore_visible_lt B (realId_of_fold hr) (realId_of_fold hr')
    ((display_iff_chainBefore Γ hpos hpos' hchne).mp hkey)

/-! ## §5  The capstone: any RGA† read equals the embed read

The published RGA's read is relational, "the `visible` ids, enumerated
in `visible_lt` order." Any list meeting that specification is unique
(sortedness by an asymmetric relation pins the enumeration), and the
embed fold's id sequence meets it. -/

/-- Two lists sorted by an asymmetric relation with the same members are
equal. -/
theorem sorted_unique {R : ℕ → ℕ → Prop}
    (hasym : ∀ a b, R a b → ¬ R b a) :
    ∀ (l1 l2 : List ℕ), l1.Pairwise R → l2.Pairwise R →
      (∀ t, t ∈ l1 ↔ t ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: t2, _, _, hmem =>
      absurd ((hmem b).mpr List.mem_cons_self) (by simp)
  | a :: t1, [], _, _, hmem =>
      absurd ((hmem a).mp List.mem_cons_self) (by simp)
  | a :: t1, b :: t2, h1, h2, hmem => by
      have hirr : ∀ x, ¬ R x x := fun x hx => hasym _ _ hx hx
      obtain ⟨hRa, h1'⟩ := List.pairwise_cons.mp h1
      obtain ⟨hRb, h2'⟩ := List.pairwise_cons.mp h2
      have hab : a = b := by
        by_contra hne
        have ha2 : a ∈ t2 := by
          rcases List.mem_cons.mp ((hmem a).mp List.mem_cons_self) with
            h | h
          · exact absurd h hne
          · exact h
        have hb1 : b ∈ t1 := by
          rcases List.mem_cons.mp ((hmem b).mpr List.mem_cons_self) with
            h | h
          · exact absurd h.symm hne
          · exact h
        exact hasym _ _ (hRa b hb1) (hRb a ha2)
      subst hab
      have ha1 : a ∉ t1 := fun h => hirr a (hRa a h)
      have ha2 : a ∉ t2 := fun h => hirr a (hRb a h)
      have hmem' : ∀ t, t ∈ t1 ↔ t ∈ t2 := by
        intro t
        constructor
        · intro h
          rcases List.mem_cons.mp
            ((hmem t).mp (List.mem_cons_of_mem _ h)) with rfl | h'
          · exact absurd h ha1
          · exact h'
        · intro h
          rcases List.mem_cons.mp
            ((hmem t).mpr (List.mem_cons_of_mem _ h)) with rfl | h'
          · exact absurd h ha2
          · exact h'
      rw [sorted_unique hasym t1 t2 h1' h2' hmem']

/-- **The compaction theorem**: any `visible_lt`-sorted
enumeration of the RGA† fold's visible ids IS the embed fold's id
sequence. The published tombstoned RGA's read, whatever executable form
realizes its relational specification, equals the embedded-chain RGA's
read on every honest event set: the embedded-chain RGA is the published
RGA with the tombstone set compressed into the coordinates. -/
theorem rga_read_eq_embed_read {Γ : OrderedPrefixCode}
    {C : Configuration (E Γ)} (hApp : EAppDiscipline Γ C)
    {ρ : List (Op EOp)} (hperm : listPermOf ρ C.events) (hwf : EWf Γ ρ)
    (L : List ℕ)
    (hLsort : L.Pairwise (_root_.visible_lt (rgaFold ρ)))
    (hLmem : ∀ t, t ∈ L ↔ _root_.visible (rgaFold ρ) t) :
    L = eIds (eFold Γ ρ) :=
  sorted_unique
    (fun _ _ => Sal.EmbedRGA.visible_lt_asymm (birthEnv_rgaFold hApp hperm))
    L (eIds (eFold Γ ρ)) hLsort (embed_read_pairwise hApp hperm hwf)
    (fun t => (hLmem t).trans (visible_iff_eIds hwf t))

/-- Element agreement: every record the embed fold displays is read by
the published RGA with the same element at the same id. -/
theorem embed_rec_readSeq {Γ : OrderedPrefixCode} {ρ : List (Op EOp)}
    (hwf : EWf Γ ρ) {t el : ℕ} {co : List Bool}
    (hr : (t, el, co) ∈ eFold Γ ρ) :
    _root_.readSeq_visible (rgaFold ρ) t el := by
  obtain ⟨⟨o, ho, hoi, hrec⟩, hnd⟩ := (e_fold_mem Γ hwf _).mp hr
  obtain ⟨ts, rr, op⟩ := o
  cases op with
  | del y => simp [eIsIns] at hoi
  | ins el' π a =>
      have hts : ts = t := by
        have := congrArg Prod.fst hrec
        exact this.symm
      have hel : el' = el := by
        have := congrArg (fun q : ERec => q.2.1) hrec
        simpa [eRecOf] using this.symm
      subst hts
      subst hel
      constructor
      · rw [show ((ts, el', co) : ERec).1 = ts from rfl] at hnd
        exact (visible_rgaFold).mpr
          ⟨⟨(ts, rr, EOp.ins el' π a), ho, by simp [eIsIns], rfl⟩, hnd⟩
      · exact ⟨a, (rgaFold_fst_mem ρ ts a el').mpr ⟨rr, π, ho⟩⟩

end Sal.ConditionedMRDTs
