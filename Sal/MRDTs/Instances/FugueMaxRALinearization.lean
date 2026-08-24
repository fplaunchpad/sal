import Sal.MRDTs.Instances.FugueMaxBackward

/-!
# The FugueMax variant alphabet as a plain MRDT instance

`SidedRGA.lean`'s capstone `sided_embed_ra_linearizable3` covers plain sided
coordinates (`sBlock`); the FugueMax realization (`SidedRGA_FugueMax.lean`)
writes records over the variant alphabet of
`RGAKernel/FugueMaxChainLex.lean`; R entries carry an immutable
right-origin tag (`fwTag`) before the delta code, which is a different block
format, so RA-linearizability for the FM datatype needs a separate proof,
which this file gives.

The route is the sided instance's, verbatim in structure: the state is the
same canonical sorted list (`SState`, strictly descending by `sKey`), so the
whole §2/§2½ list algebra of `SidedRGA.lean` (`ssorted_ext`, `sInsert`,
`sMerge2`, `sMergeL`) is REUSED; what changes is the op alphabet (`FOp`
carries a coordinate prefix and one `FMEntry`) and the key-injectivity
discharge, which runs through the variant's unique decodability
`fmCoordOf_inj`, this is where the FM format differs materially: the
variant needs `TagsOK` (wellformed right-origin tags) alongside chain
positivity, so the honesty contract `FMHonest` carries both. Convergence is
otherwise insensitive to what the coordinates contain, exactly as expected:
coordinates are injectively minted, immutable, and consumed only through
`sKey` comparisons.

Sections: §1 the datatype (`FMSig`) · §3 well-formed enumerations and
fold-canonicity (`f_fold_canon`, the FM analogue of `s_fold_canon`) · §5
honest histories (`FMHonestCore`) · §6 the Join (`f_join_at`: the merge is
its own linearization witness) · §7 the capstone
`fuguemax_ra_linearizable3` · §7½ the bridge to the generation layer
(`mFold_eq_fFold`: the display fold of `SidedRGA_FugueMax.lean` IS this
signature's fold of the mapped enumeration, so fold-canonicity covers
`mFold`-generated states) · §8 SPOTs (PASS+FAIL, hand-derived).
-/

namespace Sal.MRDTs.Instances.SidedEmbedRGA

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode keyLt sKey unaryCode
  keyLt_irrefl keyLt_asymm keyLt_trans keyLt_total
  FMEntry FMChain fmδ PosFMChain TagOK fmTagOK TagsOK
  fmBlock fmCoordOf fmCoordOf_append fmCoordOf_inj)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## §1  The datatype -/

/-- FM ops: an insert names an element, a coordinate prefix (the parent
chain's coordinate), and ONE FugueMax entry (`.R tag δ` or `.L δ`); a
delete names an id. The tag is payload to the datatype: it is minted by
the generation policy (`mGenInsAfter`) and stored blindly. -/
inductive FOp : Type where
  | ins (e : ℕ) (π : List ℕ) (ent : FMEntry)
  | del (x : ℕ)
deriving DecidableEq

/-- The coordinate an insert writes, a function of the op alone: the
carried prefix + the entry's variant block (`fmBlock` composes the
reversed right-origin tag and the complemented delta code on R, the sided
L band on L). -/
def fCoord (Γ : OrderedPrefixCode) (o : Op FOp) : List ℕ :=
  match o.2.2 with
  | .ins _ π ent => π ++ fmBlock Γ ent
  | .del _       => []

/-- Insert places the record at its sorted position (idempotent on a
present id); delete removes the record wherever it sits. Same shape as the
sided `sUpdate`, over the variant block. -/
def fUpdate (Γ : OrderedPrefixCode) (s : SState) (o : Op FOp) : SState :=
  match o.2.2 with
  | .ins e π ent =>
      if o.1 ∈ sIds s then s
      else sInsert (o.1, e, π ++ fmBlock Γ ent) s
  | .del x => s.filter (fun r => decide (r.1 ≠ x))

/-- The FugueMax embedded-chain RGA, parametric in the delta code. State,
merge, query, and `rc` are the sided instance's verbatim (the state IS the
same canonical sorted list); only the op alphabet and the block format
differ. -/
def FMSig (Γ : OrderedPrefixCode) : MRDTSig where
  State := SState
  dec_state := inferInstance
  init := []
  AppOp := FOp
  dec_op := inferInstance
  Query := Unit
  Value := List ℕ
  update := fUpdate Γ
  merge := fun a b => sMergeL [] a b
  query := fun s _ => s.map (fun r => r.2.1)
  mergeL := sMergeL
  merge_init_slice := fun _ _ => rfl

theorem FMSig_core_update (Γ : OrderedPrefixCode) (s : SState) (o : Op FOp) :
    (FMSig Γ).toCRDTSig.update s o = fUpdate Γ s o := rfl

theorem FMSig_rc_either (Γ : OrderedPrefixCode) (o₁ o₂ : Op FOp) :
    (FMSig Γ).toCRDTSig.replayOrder o₁ o₂ = RcRes.Either := rfl

/-! ## §3  Well-formed enumerations and fold-canonicity

`f_fold_canon`: any two well-formed enumerations of one event set fold to
the SAME state, the FM analogue of `s_fold_canon`, by `ssorted_ext` + the
fold membership characterization. The tag rides along inertly: it is
consumed by `fCoord` at record-creation time and never consulted again,
which is why every proof below is the sided proof with `fCoord`
substituted. -/

def fFold (Γ : OrderedPrefixCode) (ρ : List (Op FOp)) : SState :=
  applySeq (FMSig Γ).toCRDTSig (FMSig Γ).init ρ

theorem fFold_snoc (Γ : OrderedPrefixCode) (ρ : List (Op FOp)) (e : Op FOp) :
    fFold Γ (ρ ++ [e]) = fUpdate Γ (fFold Γ ρ) e := by
  unfold fFold applySeq
  rw [List.foldl_append]
  rfl

def fIsIns (o : Op FOp) : Bool :=
  match o.2.2 with
  | .ins _ _ _ => true
  | .del _ => false

/-- The record an insert writes. -/
def fRecOf (Γ : OrderedPrefixCode) (o : Op FOp) : SRec :=
  (o.1, (match o.2.2 with | .ins e _ _ => e | .del _ => 0), fCoord Γ o)

def fInsIds (ρ : List (Op FOp)) : List ℕ :=
  (ρ.filter (fun o => fIsIns o)).map Prod.fst

def fDels (ρ : List (Op FOp)) : List ℕ :=
  ρ.filterMap (fun o => match o.2.2 with
    | .del x => some x | .ins _ _ _ => none)

theorem mem_fInsIds {ρ : List (Op FOp)} {t : ℕ} :
    t ∈ fInsIds ρ ↔ ∃ o ∈ ρ, fIsIns o = true ∧ o.1 = t := by
  simp only [fInsIds, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨o, ⟨hm, hi⟩, rfl⟩
    exact ⟨o, hm, hi, rfl⟩
  · rintro ⟨o, hm, hi, rfl⟩
    exact ⟨o, ⟨hm, hi⟩, rfl⟩

theorem mem_fDels {ρ : List (Op FOp)} {x : ℕ} :
    x ∈ fDels ρ ↔ ∃ o ∈ ρ, o.2.2 = FOp.del x := by
  simp only [fDels, List.mem_filterMap]
  constructor
  · rintro ⟨o, hm, hsome⟩
    refine ⟨o, hm, ?_⟩
    cases hop : o.2.2 with
    | ins e π ent => rw [hop] at hsome; simp at hsome
    | del y => rw [hop] at hsome; simp at hsome; rw [hsome]
  · rintro ⟨o, hm, hdel⟩
    exact ⟨o, hm, by rw [hdel]⟩

theorem fInsIds_append (ρ σ : List (Op FOp)) :
    fInsIds (ρ ++ σ) = fInsIds ρ ++ fInsIds σ := by
  simp [fInsIds, List.filter_append]

theorem fDels_append (ρ σ : List (Op FOp)) :
    fDels (ρ ++ σ) = fDels ρ ++ fDels σ := by
  simp [fDels, List.filterMap_append]

/-- Well-formed enumerations: insert ids are unique, nothing is deleted
before its insert, and distinct inserts mint distinct keys (supplied on
honest histories by FM chain-generation + variant unique decodability,
`fmCoordOf_inj`). -/
structure FWf (Γ : OrderedPrefixCode) (ρ : List (Op FOp)) : Prop where
  ins_nodup : (fInsIds ρ).Nodup
  del_late : ∀ σ o τ, ρ = σ ++ o :: τ → fIsIns o = true → o.1 ∉ fDels σ
  keys_inj : ∀ o₁ ∈ ρ, ∀ o₂ ∈ ρ, fIsIns o₁ = true → fIsIns o₂ = true →
      o₁.1 ≠ o₂.1 → sKey (fCoord Γ o₁) ≠ sKey (fCoord Γ o₂)

theorem FWf.prefix {Γ : OrderedPrefixCode} {ρ : List (Op FOp)} {e : Op FOp}
    (h : FWf Γ (ρ ++ [e])) : FWf Γ ρ where
  ins_nodup := by
    have := h.ins_nodup
    rw [fInsIds_append] at this
    exact this.of_append_left
  del_late := fun σ o τ heq hins => by
    refine h.del_late σ o (τ ++ [e]) ?_ hins
    rw [heq]
    simp
  keys_inj := fun o₁ h₁ o₂ h₂ => h.keys_inj o₁ (List.mem_append_left _ h₁)
    o₂ (List.mem_append_left _ h₂)

/-- Record provenance, unconditioned: everything in a fold was written by
some insert of the enumeration. -/
theorem f_fold_rec_sub (Γ : OrderedPrefixCode) : ∀ (ρ : List (Op FOp))
    (r : SRec), r ∈ fFold Γ ρ → ∃ o ∈ ρ, fIsIns o = true ∧ r = fRecOf Γ o := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
      intro r hr
      exact absurd hr (by simp [fFold, applySeq, FMSig])
  | append_singleton ρ e ih =>
      intro r hr
      rw [fFold_snoc] at hr
      obtain ⟨ts, rr, op⟩ := e
      cases op with
      | ins el π ent =>
          simp only [fUpdate] at hr
          by_cases hmem : ts ∈ sIds (fFold Γ ρ)
          · rw [if_pos hmem] at hr
            obtain ⟨o, hm, hi, hrec⟩ := ih r hr
            exact ⟨o, List.mem_append_left _ hm, hi, hrec⟩
          · rw [if_neg hmem] at hr
            rcases mem_sInsert.mp hr with hr' | rfl
            · obtain ⟨o, hm, hi, hrec⟩ := ih r hr'
              exact ⟨o, List.mem_append_left _ hm, hi, hrec⟩
            · exact ⟨(ts, rr, .ins el π ent),
                List.mem_append_right _ (by simp),
                by simp [fIsIns], by simp [fRecOf, fCoord]⟩
      | del x =>
          simp only [fUpdate] at hr
          obtain ⟨o, hm, hi, hrec⟩ := ih r (List.mem_of_mem_filter hr)
          exact ⟨o, List.mem_append_left _ hm, hi, hrec⟩

/-- Under well-formedness the insert guard never fires: a fresh insert's id
is not in the fold of its past. -/
theorem f_fold_guard_free {Γ : OrderedPrefixCode} {ρ : List (Op FOp)}
    {e : Op FOp} (hwf : FWf Γ (ρ ++ [e])) (hins : fIsIns e = true) :
    e.1 ∉ sIds (fFold Γ ρ) := by
  intro hmem
  obtain ⟨r, hr, hr1⟩ := List.mem_map.mp hmem
  obtain ⟨o, hm, hi, hrec⟩ := f_fold_rec_sub Γ ρ r hr
  have ho1 : o.1 = e.1 := by rw [hrec] at hr1; exact hr1
  have h1 : e.1 ∈ fInsIds ρ := mem_fInsIds.mpr ⟨o, hm, hi, ho1⟩
  have := hwf.ins_nodup
  rw [fInsIds_append] at this
  rcases List.nodup_append.mp this with ⟨-, -, hdisj⟩
  have h2 : e.1 ∈ fInsIds [e] := by
    simp [fInsIds, hins]
  exact (hdisj e.1 h1 e.1 h2) rfl

/-- Folds of well-formed enumerations are canonical (sorted). -/
theorem f_fold_sorted (Γ : OrderedPrefixCode) : ∀ {ρ : List (Op FOp)},
    FWf Γ ρ → SSorted (fFold Γ ρ) := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
      intro _
      rw [show fFold Γ [] = [] from rfl]
      exact List.Pairwise.nil
  | append_singleton ρ e ih =>
      intro hwf
      have hsorted := ih hwf.prefix
      rw [fFold_snoc]
      obtain ⟨ts, rr, op⟩ := e
      cases op with
      | del x => exact List.Pairwise.filter _ hsorted
      | ins el π ent =>
          simp only [fUpdate]
          by_cases hmem : ts ∈ sIds (fFold Γ ρ)
          · rw [if_pos hmem]; exact hsorted
          · rw [if_neg hmem]
            apply sInsert_sorted hsorted
            intro x hx
            obtain ⟨o, hm, hi, hrec⟩ := f_fold_rec_sub Γ ρ x hx
            have hx1 : x.1 = o.1 := by rw [hrec]; rfl
            have hne : o.1 ≠ ts := by
              intro heq
              exact hmem (List.mem_map.mpr ⟨x, hx, by rw [hx1, heq]⟩)
            have hkey := hwf.keys_inj o (List.mem_append_left _ hm)
              (ts, rr, .ins el π ent) (List.mem_append_right _ (by simp))
              hi (by simp [fIsIns]) hne
            rw [hrec]
            show sKey (fCoord Γ o) ≠ sKey (π ++ fmBlock Γ ent)
            simpa [fCoord] using hkey

/-- **The fold membership characterization**: under well-formedness a record
is in the fold iff its insert is in the enumeration and its id is never
deleted, an ORDER-FREE description. -/
theorem f_fold_mem (Γ : OrderedPrefixCode) : ∀ {ρ : List (Op FOp)},
    FWf Γ ρ → ∀ (r : SRec),
    (r ∈ fFold Γ ρ ↔
      (∃ o ∈ ρ, fIsIns o = true ∧ r = fRecOf Γ o) ∧ r.1 ∉ fDels ρ) := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
      intro _ r
      simp [show fFold Γ [] = [] from rfl]
  | append_singleton ρ e ih =>
      intro hwf r
      have IH := ih hwf.prefix
      rw [fFold_snoc]
      obtain ⟨ts, rr, op⟩ := e
      cases op with
      | ins el π ent =>
          simp only [fUpdate]
          rw [if_neg (f_fold_guard_free hwf (by simp [fIsIns]))]
          have hdels : fDels (ρ ++ [(ts, rr, FOp.ins el π ent)]) = fDels ρ := by
            rw [fDels_append]
            simp [fDels]
          rw [hdels, mem_sInsert]
          constructor
          · rintro (hr | rfl)
            · obtain ⟨⟨o, hm, hi, hrec⟩, hnd⟩ := (IH r).mp hr
              exact ⟨⟨o, List.mem_append_left _ hm, hi, hrec⟩, hnd⟩
            · refine ⟨⟨(ts, rr, .ins el π ent),
                List.mem_append_right _ (by simp),
                by simp [fIsIns], by simp [fRecOf, fCoord]⟩, ?_⟩
              show ts ∉ fDels ρ
              exact hwf.del_late ρ (ts, rr, .ins el π ent) [] rfl
                (by simp [fIsIns])
          · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
            rcases List.mem_append.mp hm with hm' | hm'
            · exact Or.inl ((IH r).mpr ⟨⟨o, hm', hi, hrec⟩, hnd⟩)
            · right
              have : o = (ts, rr, .ins el π ent) := List.mem_singleton.mp hm'
              rw [hrec, this]
              simp [fRecOf, fCoord]
      | del x =>
          simp only [fUpdate]
          have hdels : fDels (ρ ++ [(ts, rr, FOp.del x)])
              = fDels ρ ++ [x] := by
            rw [fDels_append]
            simp [fDels]
          rw [hdels]
          constructor
          · intro hr
            have hm := List.mem_of_mem_filter hr
            have hx := List.of_mem_filter hr
            simp only [decide_eq_true_eq] at hx
            obtain ⟨⟨o, hmo, hi, hrec⟩, hnd⟩ := (IH r).mp hm
            refine ⟨⟨o, List.mem_append_left _ hmo, hi, hrec⟩, ?_⟩
            simp only [List.mem_append, List.mem_singleton]
            rintro (h | h)
            · exact hnd h
            · exact hx h
          · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
            simp only [List.mem_append, List.mem_singleton] at hnd
            push_neg at hnd
            have hm' : o ∈ ρ := by
              rcases List.mem_append.mp hm with h | h
              · exact h
              · have : o = (ts, rr, .del x) := List.mem_singleton.mp h
                rw [this] at hi
                simp [fIsIns] at hi
            refine List.mem_filter.mpr
              ⟨(IH r).mpr ⟨⟨o, hm', hi, hrec⟩, hnd.1⟩, by
                simpa using hnd.2⟩

/-- **Fold-canonicity**, FM variant: well-formed enumerations of one event
set fold to the SAME state. The state is a function of the event set, the
property the queue-route Join hook cannot live without, and the reason the
right-origin tag can be policy-minted: the datatype's canonical state never
depends on enumeration order, whatever tags the ops carry. -/
theorem f_fold_canon (Γ : OrderedPrefixCode) {ρ ρ' : List (Op FOp)}
    (hwf : FWf Γ ρ) (hwf' : FWf Γ ρ')
    (hmem : ∀ o, o ∈ ρ ↔ o ∈ ρ') :
    fFold Γ ρ = fFold Γ ρ' := by
  apply ssorted_ext (f_fold_sorted Γ hwf) (f_fold_sorted Γ hwf')
  intro r
  rw [f_fold_mem Γ hwf r, f_fold_mem Γ hwf' r]
  constructor
  · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
    refine ⟨⟨o, (hmem o).mp hm, hi, hrec⟩, fun hx => hnd ?_⟩
    obtain ⟨o', hm', hdel⟩ := mem_fDels.mp hx
    exact mem_fDels.mpr ⟨o', (hmem o').mpr hm', hdel⟩
  · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
    refine ⟨⟨o, (hmem o).mpr hm, hi, hrec⟩, fun hx => hnd ?_⟩
    obtain ⟨o', hm', hdel⟩ := mem_fDels.mp hx
    exact mem_fDels.mpr ⟨o', (hmem o').mp hm', hdel⟩

/-! ## §5  Honest histories, well-formedness of enumerations

`FMHonestCore` is the FM analogue of the sided instance's honesty: every
delete names an id its issuer had observed (a `vis`-prior insert), and
inserts are chain-generated over the VARIANT alphabet, the mint is a
positive, TAG-WELLFORMED FugueMax birth chain's coordinate whose deltas
telescope to the id. `TagsOK` is the one clause the sided contract did not
need: the variant's unique decodability (`fmCoordOf_inj`) consumes it,
because tag decoding (`fwTag_cancel`) is only unambiguous on wellformed
tags. The FugueMax generation layer supplies it for free
(`SidedRGA_FugueMax.lean`'s `KInv.wf`). -/

/-- The one non-commuting shape: an insert and the delete of its id.
Witnessed at the empty state. -/
theorem f_ins_del_not_comm (Γ : OrderedPrefixCode) (ts r el : ℕ)
    (π : List ℕ) (ent : FMEntry) (ts' r' : ℕ) :
    ¬ (FMSig Γ).toCRDTSig.commutes (ts, r, FOp.ins el π ent) (ts', r', FOp.del ts) := by
  intro h
  have h0 := h []
  rw [FMSig_core_update, FMSig_core_update, FMSig_core_update,
    FMSig_core_update] at h0
  simp only [fUpdate, sIds, sInsert, List.map_nil, List.not_mem_nil,
    if_false, List.filter_nil] at h0
  simp at h0

/-- Honest histories. -/
structure FMHonestCore (Γ : OrderedPrefixCode)
    (C : Sal.MRDTs.Foundation.Configuration (FMSig Γ).toCRDTSig) : Prop where
  /-- Every delete's target was inserted `vis`-before it. -/
  del_has_ins : ∀ e ∈ C.events, ∀ x : ℕ, e.2.2 = FOp.del x →
    ∃ a ∈ C.events, C.vis a e ∧ a.1 = x ∧ fIsIns a = true
  /-- Inserts are chain-generated: each mint is the coordinate of a
  positive tag-wellformed FugueMax birth chain whose deltas telescope to
  the id (so chains are injective on ids for free). -/
  chain_gen : ∃ chainOf : ℕ → FMChain,
    ∀ o ∈ C.events, fIsIns o = true →
      PosFMChain (chainOf o.1) ∧ TagsOK (chainOf o.1) ∧
      fCoord Γ o = fmCoordOf Γ (chainOf o.1) ∧
      ((chainOf o.1).map fmδ).sum = o.1

/-- Honesty + backward closure: a delete's insert lies in the same closed
event set, `vis`-before it. -/
theorem f_del_ins_mem {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration (FMSig Γ).toCRDTSig}
    (hHon : FMHonestCore Γ C) {ev : Set (Op FOp)}
    (hin : ∀ a ∈ ev, a ∈ C.events)
    (hcl : ∀ a b, C.vis a b → ¬ (FMSig Γ).toCRDTSig.commutes a b → b ∈ ev → a ∈ ev) :
    ∀ d ∈ ev, ∀ x : ℕ, d.2.2 = FOp.del x →
      ∃ a ∈ ev, fIsIns a = true ∧ a.1 = x ∧ C.vis a d := by
  intro d hd x hdel
  obtain ⟨a, haev, hvis, hax, hains⟩ := hHon.del_has_ins d (hin d hd) x hdel
  have hncomm : ¬ (FMSig Γ).toCRDTSig.commutes a d := by
    obtain ⟨a1, a2, aop⟩ := a
    obtain ⟨d1, d2, dop⟩ := d
    simp only at hdel hax
    subst hdel
    cases aop with
    | del y => simp [fIsIns] at hains
    | ins el π ent =>
        subst hax
        exact f_ins_del_not_comm Γ a1 a2 el π ent d1 d2
  exact ⟨a, hcl a d hvis hncomm hd, hains, hax, hvis⟩

/-- **A `loOn`-respecting enumeration of a closed honest set is
well-formed**, the bridge from the configuration layer to `FWf`, one
honesty ingredient per field: timestamp uniqueness gives `ins_nodup`,
delete-after-insert visibility gives `del_late`, chain generation +
variant unique decodability give `keys_inj`. -/
theorem f_wf_of_enum {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration (FMSig Γ).toCRDTSig}
    (hHon : FMHonestCore Γ C) {ev : Set (Op FOp)} {ρ : List (Op FOp)}
    (hin : ∀ a ∈ ev, a ∈ C.events)
    (hcl : ∀ a b, C.vis a b → ¬ (FMSig Γ).toCRDTSig.commutes a b → b ∈ ev → a ∈ ev)
    (hperm : listPermOf ρ ev)
    (hresp : respects ρ (loOn C ev)) : FWf Γ ρ where
  ins_nodup := by
    apply List.Nodup.map_on ?_ (hperm.1.filter _)
    intro o₁ h₁ o₂ h₂ hfst
    exact C.ts_unique
      (hin _ ((hperm.2 _).mp (List.mem_of_mem_filter h₁)))
      (hin _ ((hperm.2 _).mp (List.mem_of_mem_filter h₂))) hfst
  del_late := by
    intro σ o τ heq hins hdel
    obtain ⟨d, hdσ, hddel⟩ := mem_fDels.mp hdel
    have hdρ : d ∈ ρ := by
      rw [heq]; exact List.mem_append_left _ hdσ
    have hoρ : o ∈ ρ := by
      rw [heq]; exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨a, haev, hains, hax, hvis⟩ :=
      f_del_ins_mem hHon hin hcl d ((hperm.2 d).mp hdρ) o.1 hddel
    have hao : a = o :=
      C.ts_unique (hin a haev) (hin o ((hperm.2 o).mp hoρ)) hax
    subst hao
    unfold respects at hresp
    rw [heq] at hresp
    have hcross := (List.pairwise_append.mp hresp).2.2 d hdσ a
      List.mem_cons_self
    apply hcross
    rw [loOn_iff_of_rc_either (FMSig_rc_either Γ)]
    refine ⟨hvis, ?_⟩
    obtain ⟨a1, a2, aop⟩ := a
    obtain ⟨d1, d2, dop⟩ := d
    simp only at hddel
    subst hddel
    cases aop with
    | del y => simp [fIsIns] at hins
    | ins el π ent =>
        exact f_ins_del_not_comm Γ a1 a2 el π ent d1 d2
  keys_inj := by
    obtain ⟨chainOf, hch⟩ := hHon.chain_gen
    intro o₁ h₁ o₂ h₂ hi₁ hi₂ hne hkey
    obtain ⟨hp₁, ht₁, hc₁, hs₁⟩ := hch o₁ (hin _ ((hperm.2 _).mp h₁)) hi₁
    obtain ⟨hp₂, ht₂, hc₂, hs₂⟩ := hch o₂ (hin _ ((hperm.2 _).mp h₂)) hi₂
    apply hne
    have hc : fmCoordOf Γ (chainOf o₁.1) = fmCoordOf Γ (chainOf o₂.1) := by
      rw [← hc₁, ← hc₂]
      exact sKey_inj hkey
    have hchain := fmCoordOf_inj Γ hp₁ hp₂ ht₁ ht₂ hc
    calc o₁.1 = ((chainOf o₁.1).map fmδ).sum := hs₁.symm
      _ = ((chainOf o₂.1).map fmδ).sum := by rw [hchain]
      _ = o₂.1 := hs₂

/-! ## §6a  The survival algebra

The record-level membership of the ternary merge, characterized order-free
against the union event set, the mathematical core of the Join. §6b turns
it into `JoinLemma3At` by exhibiting the witness enumeration. All verbatim
sided proofs: the merge never looks inside a coordinate. -/

theorem f_fold_id_mem (Γ : OrderedPrefixCode) {ρ : List (Op FOp)}
    (hwf : FWf Γ ρ) (t : ℕ) :
    t ∈ sIds (fFold Γ ρ) ↔
      (∃ o ∈ ρ, fIsIns o = true ∧ o.1 = t) ∧ t ∉ fDels ρ := by
  constructor
  · intro h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    obtain ⟨⟨o, hm, hi, hrec⟩, hnd⟩ := (f_fold_mem Γ hwf r).mp hr
    exact ⟨⟨o, hm, hi, by rw [hrec]; rfl⟩, hnd⟩
  · rintro ⟨⟨o, hm, hi, rfl⟩, hnd⟩
    have hr : fRecOf Γ o ∈ fFold Γ ρ :=
      (f_fold_mem Γ hwf _).mpr ⟨⟨o, hm, hi, rfl⟩, hnd⟩
    exact List.mem_map.mpr ⟨fRecOf Γ o, hr, rfl⟩

/-- Distinct honest inserts mint distinct keys (the standalone form of
`f_wf_of_enum`'s third discharge, for use at the merge site). -/
theorem f_keys_inj_events {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration (FMSig Γ).toCRDTSig}
    (hHon : FMHonestCore Γ C) :
    ∀ o₁ ∈ C.events, ∀ o₂ ∈ C.events, fIsIns o₁ = true → fIsIns o₂ = true →
      o₁.1 ≠ o₂.1 → sKey (fCoord Γ o₁) ≠ sKey (fCoord Γ o₂) := by
  obtain ⟨chainOf, hch⟩ := hHon.chain_gen
  intro o₁ h₁ o₂ h₂ hi₁ hi₂ hne hkey
  obtain ⟨hp₁, ht₁, hc₁, hs₁⟩ := hch o₁ h₁ hi₁
  obtain ⟨hp₂, ht₂, hc₂, hs₂⟩ := hch o₂ h₂ hi₂
  apply hne
  have hc : fmCoordOf Γ (chainOf o₁.1) = fmCoordOf Γ (chainOf o₂.1) := by
    rw [← hc₁, ← hc₂]
    exact sKey_inj hkey
  have hchain := fmCoordOf_inj Γ hp₁ hp₂ ht₁ ht₂ hc
  calc o₁.1 = ((chainOf o₁.1).map fmδ).sum := hs₁.symm
    _ = ((chainOf o₂.1).map fmδ).sum := by rw [hchain]
    _ = o₂.1 := hs₂

/-- **The merge membership characterization.** At a join site (three
canonical enumerations over an honest configuration), a record is in the
ternary merge iff its insert is somewhere in the union and its id is deleted
nowhere in the union, the union's order-free membership. OR-set survival,
with honesty closing the one subtle corner (a branch-2 delete of a
branch-1 survivor forces the insert into the LCA). -/
theorem f_mergeL_mem {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration (FMSig Γ).toCRDTSig}
    (hHon : FMHonestCore Γ C) {ev₁ ev₂ : Set (Op FOp)}
    {ρ₀ ρ₁ ρ₂ : List (Op FOp)}
    (hin₁ : ∀ a ∈ ev₁, a ∈ C.events) (hin₂ : ∀ a ∈ ev₂, a ∈ C.events)
    (hcl₁ : ∀ a b, C.vis a b → ¬ (FMSig Γ).toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁)
    (hcl₂ : ∀ a b, C.vis a b → ¬ (FMSig Γ).toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂)
    (hp₀ : listPermOf ρ₀ (ev₁ ∩ ev₂)) (hp₁ : listPermOf ρ₁ ev₁)
    (hp₂ : listPermOf ρ₂ ev₂)
    (hwf₀ : FWf Γ ρ₀) (hwf₁ : FWf Γ ρ₁) (hwf₂ : FWf Γ ρ₂) (r : SRec) :
    r ∈ sMergeL (fFold Γ ρ₀) (fFold Γ ρ₁) (fFold Γ ρ₂) ↔
      (∃ o, (o ∈ ev₁ ∨ o ∈ ev₂) ∧ fIsIns o = true ∧ r = fRecOf Γ o) ∧
      (∀ d, (d ∈ ev₁ ∨ d ∈ ev₂) → d.2.2 ≠ FOp.del r.1) := by
  classical
  set s₀ := fFold Γ ρ₀
  set s₁ := fFold Γ ρ₁
  set s₂ := fFold Γ ρ₂
  have hdels : ∀ {ρ : List (Op FOp)} {ev : Set (Op FOp)}, listPermOf ρ ev →
      ∀ {t : ℕ}, t ∈ fDels ρ ↔ ∃ d ∈ ev, d.2.2 = FOp.del t := by
    intro ρ ev hp t
    rw [mem_fDels]
    constructor
    · rintro ⟨d, hm, hdel⟩
      exact ⟨d, (hp.2 d).mp hm, hdel⟩
    · rintro ⟨d, hm, hdel⟩
      exact ⟨d, (hp.2 d).mpr hm, hdel⟩
  rw [show sMergeL s₀ s₁ s₂ = sMerge2
    (s₁.filter (fun x => decide (x.1 ∈ sIds s₂ ∨ x.1 ∉ sIds s₀)))
    (s₂.filter (fun x => decide (x.1 ∉ sIds s₀ ∧ x.1 ∉ sIds s₁))) from rfl,
    mem_sMerge2]
  constructor
  · rintro (hr | hr)
    · -- branch-1 survivor
      have hm := List.mem_of_mem_filter hr
      have hcond := List.of_mem_filter hr
      simp only [decide_eq_true_eq] at hcond
      obtain ⟨⟨o, hoρ, hi, hrec⟩, hnd₁⟩ := (f_fold_mem Γ hwf₁ r).mp hm
      refine ⟨⟨o, Or.inl ((hp₁.2 o).mp hoρ), hi, hrec⟩, ?_⟩
      rintro d (hd | hd) hdel
      · exact hnd₁ ((hdels hp₁).mpr ⟨d, hd, hdel⟩)
      · rcases hcond with hin2 | hout0
        · have := ((f_fold_id_mem Γ hwf₂ r.1).mp hin2).2
          exact this ((hdels hp₂).mpr ⟨d, hd, hdel⟩)
        · -- honest corner: the deleter's insert lands in the LCA
          obtain ⟨a, haev₂, hains, hax, -⟩ :=
            f_del_ins_mem hHon hin₂ hcl₂ d hd r.1 hdel
          have hao : a = o := by
            apply C.ts_unique (hin₂ a haev₂)
              (hin₁ o ((hp₁.2 o).mp hoρ))
            rw [hax, hrec]; rfl
          have ho₀ : o ∈ ev₁ ∩ ev₂ :=
            ⟨(hp₁.2 o).mp hoρ, hao ▸ haev₂⟩
          apply hout0
          rw [f_fold_id_mem Γ hwf₀]
          refine ⟨⟨o, (hp₀.2 o).mpr ho₀, hi, by rw [hrec]; rfl⟩, ?_⟩
          intro hdel0
          obtain ⟨d', hd', hdel'⟩ := (hdels hp₀).mp hdel0
          exact hnd₁ ((hdels hp₁).mpr ⟨d', hd'.1, hdel'⟩)
    · -- branch-2 news
      have hm := List.mem_of_mem_filter hr
      have hcond := List.of_mem_filter hr
      simp only [decide_eq_true_eq] at hcond
      obtain ⟨⟨o, hoρ, hi, hrec⟩, hnd₂⟩ := (f_fold_mem Γ hwf₂ r).mp hm
      refine ⟨⟨o, Or.inr ((hp₂.2 o).mp hoρ), hi, hrec⟩, ?_⟩
      rintro d (hd | hd) hdel
      · -- a branch-1 delete would force the insert into the LCA,
        -- contradicting r.1 ∉ ids s₀
        obtain ⟨a, haev₁, hains, hax, -⟩ :=
          f_del_ins_mem hHon hin₁ hcl₁ d hd r.1 hdel
        have hao : a = o := by
          apply C.ts_unique (hin₁ a haev₁)
            (hin₂ o ((hp₂.2 o).mp hoρ))
          rw [hax, hrec]; rfl
        have ho₀ : o ∈ ev₁ ∩ ev₂ :=
          ⟨hao ▸ haev₁, (hp₂.2 o).mp hoρ⟩
        apply hcond.1
        rw [f_fold_id_mem Γ hwf₀]
        refine ⟨⟨o, (hp₀.2 o).mpr ho₀, hi, by rw [hrec]; rfl⟩, ?_⟩
        intro hdel0
        obtain ⟨d', hd', hdel'⟩ := (hdels hp₀).mp hdel0
        exact hnd₂ ((hdels hp₂).mpr ⟨d', hd'.2, hdel'⟩)
      · exact hnd₂ ((hdels hp₂).mpr ⟨d, hd, hdel⟩)
  · rintro ⟨⟨o, hor, hi, hrec⟩, hnd⟩
    by_cases ho₁ : o ∈ ev₁
    · -- route through branch 1
      left
      refine List.mem_filter.mpr ⟨?_, ?_⟩
      · rw [f_fold_mem Γ hwf₁]
        refine ⟨⟨o, (hp₁.2 o).mpr ho₁, hi, hrec⟩, ?_⟩
        intro hdel1
        obtain ⟨d, hd, hdel⟩ := (hdels hp₁).mp hdel1
        exact hnd d (Or.inl hd) hdel
      · simp only [decide_eq_true_eq]
        by_cases h0 : r.1 ∈ sIds s₀
        · left
          obtain ⟨⟨o', ho'ρ, hi', ho'1⟩, -⟩ := (f_fold_id_mem Γ hwf₀ r.1).mp h0
          have ho'₀ := (hp₀.2 o').mp ho'ρ
          rw [f_fold_id_mem Γ hwf₂]
          refine ⟨⟨o', (hp₂.2 o').mpr ho'₀.2, hi', ho'1⟩, ?_⟩
          intro hdel2
          obtain ⟨d, hd, hdel⟩ := (hdels hp₂).mp hdel2
          exact hnd d (Or.inr hd) hdel
        · exact Or.inr h0
    · -- o ∈ ev₂ only: route through branch 2
      have ho₂ : o ∈ ev₂ := by
        rcases hor with h | h
        · exact absurd h ho₁
        · exact h
      right
      refine List.mem_filter.mpr ⟨?_, ?_⟩
      · rw [f_fold_mem Γ hwf₂]
        refine ⟨⟨o, (hp₂.2 o).mpr ho₂, hi, hrec⟩, ?_⟩
        intro hdel2
        obtain ⟨d, hd, hdel⟩ := (hdels hp₂).mp hdel2
        exact hnd d (Or.inr hd) hdel
      · simp only [decide_eq_true_eq]
        have hnot : ∀ {ρ : List (Op FOp)} {ev : Set (Op FOp)},
            listPermOf ρ ev → FWf Γ ρ → (∀ a ∈ ev, a ∈ C.events) →
            (∀ a ∈ ev, a ∈ ev₁) → r.1 ∉ sIds (fFold Γ ρ) := by
          intro ρ ev hp hwf hin hsub hmem
          obtain ⟨⟨o', ho'ρ, hi', ho'1⟩, -⟩ := (f_fold_id_mem Γ hwf r.1).mp hmem
          have ho'ev := (hp.2 o').mp ho'ρ
          have : o' = o := by
            apply C.ts_unique (hin o' ho'ev) (hin₂ o ho₂)
            rw [ho'1, hrec]; rfl
          exact ho₁ (this ▸ hsub o' ho'ev)
        exact ⟨hnot hp₀ hwf₀ (fun a ha => hin₁ a ha.1) (fun a ha => ha.1),
               hnot hp₁ hwf₁ hin₁ (fun a ha => ha)⟩

/-! ## §6b  The Join: the merge is its own linearization witness

Witness enumeration for the union: the LCA's enumeration, then branch one's
delta (in branch order), then branch two's news. Its `respects` obligation
falls to CLOSURE, and `loOn` is event-set independent under `rc = Either`,
so within-block orders transfer verbatim. Sided proof, `f`-substituted. -/

open LabeledTS in
theorem f_join_at {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration (FMSig Γ).toCRDTSig}
    (hHon : FMHonestCore Γ C) : JoinLemma3At (FMSig Γ) C := by
  intro ev₁ ev₂ s₀ s₁ s₂ _htr _hir hin₁ hin₂ hcl₁ hcl₂ h₀ h₁ h₂
  classical
  obtain ⟨ρ₀, hp₀, hr₀, hf₀⟩ := h₀
  obtain ⟨ρ₁, hp₁, hr₁, hf₁⟩ := h₁
  obtain ⟨ρ₂, hp₂, hr₂, hf₂⟩ := h₂
  set ev₀ := ev₁ ∩ ev₂ with hev₀
  have hin₀ : ∀ a ∈ ev₀, a ∈ C.events := fun a ha => hin₁ a ha.1
  have hcl₀ : ∀ a b, C.vis a b → ¬ (FMSig Γ).toCRDTSig.commutes a b →
      b ∈ ev₀ → a ∈ ev₀ :=
    fun a b hv hc hb => ⟨hcl₁ a b hv hc hb.1, hcl₂ a b hv hc hb.2⟩
  have hinU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events := by
    rintro a (ha | ha)
    · exact hin₁ a ha
    · exact hin₂ a ha
  have hclU : ∀ a b, C.vis a b → ¬ (FMSig Γ).toCRDTSig.commutes a b →
      b ∈ ev₁ ∪ ev₂ → a ∈ ev₁ ∪ ev₂ := by
    rintro a b hv hc (hb | hb)
    · exact Or.inl (hcl₁ a b hv hc hb)
    · exact Or.inr (hcl₂ a b hv hc hb)
  have hwf₀ := f_wf_of_enum hHon hin₀ hcl₀ hp₀ hr₀
  have hwf₁ := f_wf_of_enum hHon hin₁ hcl₁ hp₁ hr₁
  have hwf₂ := f_wf_of_enum hHon hin₂ hcl₂ hp₂ hr₂
  -- loOn is event-set independent under rc = Either
  have hloOn : ∀ (ev ev' : Set (Op FOp)) (x y : Op FOp),
      loOn C ev x y → loOn C ev' x y := by
    intro ev ev' x y h
    rw [loOn_iff_of_rc_either (FMSig_rc_either Γ)] at h ⊢
    exact h
  -- the witness enumeration
  set δ₁ := ρ₁.filter (fun o => decide (o ∉ ev₀)) with hδ₁
  set δ₂ := ρ₂.filter (fun o => decide (o ∉ ev₁)) with hδ₂
  set ρᵤ := ρ₀ ++ (δ₁ ++ δ₂) with hρᵤ
  have hmemδ₁ : ∀ {o}, o ∈ δ₁ ↔ o ∈ ρ₁ ∧ o ∉ ev₀ := by
    intro o
    rw [hδ₁]
    simp [List.mem_filter]
  have hmemδ₂ : ∀ {o}, o ∈ δ₂ ↔ o ∈ ρ₂ ∧ o ∉ ev₁ := by
    intro o
    rw [hδ₂]
    simp [List.mem_filter]
  -- membership: ρᵤ enumerates the union
  have hmemU : ∀ o, o ∈ ρᵤ ↔ o ∈ ev₁ ∪ ev₂ := by
    intro o
    rw [hρᵤ]
    simp only [List.mem_append]
    constructor
    · rintro (h | h | h)
      · exact Or.inl ((hp₀.2 o).mp h).1
      · exact Or.inl ((hp₁.2 o).mp (hmemδ₁.mp h).1)
      · exact Or.inr ((hp₂.2 o).mp (hmemδ₂.mp h).1)
    · rintro (h | h)
      · by_cases h0 : o ∈ ev₀
        · exact Or.inl ((hp₀.2 o).mpr h0)
        · exact Or.inr (Or.inl (hmemδ₁.mpr ⟨(hp₁.2 o).mpr h, h0⟩))
      · by_cases h1 : o ∈ ev₁
        · by_cases h0 : o ∈ ev₀
          · exact Or.inl ((hp₀.2 o).mpr h0)
          · exact Or.inr (Or.inl (hmemδ₁.mpr ⟨(hp₁.2 o).mpr h1, h0⟩))
        · exact Or.inr (Or.inr (hmemδ₂.mpr ⟨(hp₂.2 o).mpr h, h1⟩))
  -- nodup: blocks are nodup and pairwise set-separated
  have hndU : ρᵤ.Nodup := by
    rw [hρᵤ]
    rw [List.nodup_append]
    refine ⟨hp₀.1, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hp₁.1.filter _, hp₂.1.filter _, ?_⟩
      intro a ha b hb hab
      subst hab
      exact (hmemδ₂.mp hb).2 ((hp₁.2 a).mp (hmemδ₁.mp ha).1)
    · intro a ha b hb hab
      subst hab
      have ha0 : a ∈ ev₀ := (hp₀.2 a).mp ha
      rcases List.mem_append.mp hb with h | h
      · exact (hmemδ₁.mp h).2 ha0
      · exact (hmemδ₂.mp h).2 ha0.1
  have hpU : listPermOf ρᵤ (ev₁ ∪ ev₂) := ⟨hndU, hmemU⟩
  -- respects: within-blocks by transfer, cross-blocks by closure
  have hrU : respects ρᵤ (loOn C (ev₁ ∪ ev₂)) := by
    rw [hρᵤ]
    unfold respects at hr₀ hr₁ hr₂ ⊢
    rw [List.pairwise_append]
    refine ⟨hr₀.imp (fun h hl => h (hloOn _ _ _ _ hl)), ?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨(hr₁.sublist List.filter_sublist).imp
          (fun h hl => h (hloOn _ _ _ _ hl)),
        (hr₂.sublist List.filter_sublist).imp
          (fun h hl => h (hloOn _ _ _ _ hl)), ?_⟩
      -- cross δ₁ × δ₂: a loOn-later δ₂ event before a δ₁ event would be in ev₁
      intro a ha b hb hl
      rw [loOn_iff_of_rc_either (FMSig_rc_either Γ)] at hl
      have hb1 : b ∈ ev₁ := hcl₁ b a hl.1 hl.2 ((hp₁.2 a).mp (hmemδ₁.mp ha).1)
      exact (hmemδ₂.mp hb).2 hb1
    · -- cross ρ₀ × deltas: a loOn-later delta event before an LCA event
      -- would be in ev₀
      intro a ha b hb hl
      rw [loOn_iff_of_rc_either (FMSig_rc_either Γ)] at hl
      have ha0 : a ∈ ev₀ := (hp₀.2 a).mp ha
      have hb0 : b ∈ ev₀ := hcl₀ b a hl.1 hl.2 ha0
      rcases List.mem_append.mp hb with h | h
      · exact (hmemδ₁.mp h).2 hb0
      · exact (hmemδ₂.mp h).2 hb0.1
  have hwfU : FWf Γ ρᵤ := f_wf_of_enum hHon hinU hclU hpU hrU
  -- the fold of the witness IS the merge, by canonical-form extensionality
  refine ⟨ρᵤ, hpU, hrU, ?_⟩
  show fFold Γ ρᵤ = (FMSig Γ).mergeL s₀ s₁ s₂
  rw [← hf₀, ← hf₁, ← hf₂]
  show fFold Γ ρᵤ = sMergeL (fFold Γ ρ₀) (fFold Γ ρ₁) (fFold Γ ρ₂)
  -- cross-key-injectivity feeding the merge's sortedness
  have hdisj : ∀ x ∈ fFold Γ ρ₁, ∀ y ∈ fFold Γ ρ₂,
      sKey x.2.2 = sKey y.2.2 → x = y := by
    intro x hx y hy hkey
    obtain ⟨o₁, hm₁, hi₁, hrec₁⟩ := f_fold_rec_sub Γ ρ₁ x hx
    obtain ⟨o₂, hm₂, hi₂, hrec₂⟩ := f_fold_rec_sub Γ ρ₂ y hy
    have he₁ : o₁ ∈ C.events := hin₁ o₁ ((hp₁.2 o₁).mp hm₁)
    have he₂ : o₂ ∈ C.events := hin₂ o₂ ((hp₂.2 o₂).mp hm₂)
    have hkey' : sKey (fCoord Γ o₁) = sKey (fCoord Γ o₂) := by
      rw [hrec₁, hrec₂] at hkey
      exact hkey
    have hids : o₁.1 = o₂.1 := by
      by_contra hne
      exact f_keys_inj_events hHon o₁ he₁ o₂ he₂ hi₁ hi₂ hne hkey'
    have : o₁ = o₂ := C.ts_unique he₁ he₂ hids
    rw [hrec₁, hrec₂, this]
  apply ssorted_ext (f_fold_sorted Γ hwfU)
    (sMergeL_sorted (f_fold_sorted Γ hwf₁) (f_fold_sorted Γ hwf₂) hdisj)
  intro r
  rw [f_fold_mem Γ hwfU r,
      f_mergeL_mem hHon hin₁ hin₂ hcl₁ hcl₂ hp₀ hp₁ hp₂ hwf₀ hwf₁ hwf₂ r]
  constructor
  · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
    have hor : o ∈ ev₁ ∨ o ∈ ev₂ := by
      rcases (hmemU o).mp hm with h | h
      · exact Or.inl h
      · exact Or.inr h
    refine ⟨⟨o, hor, hi, hrec⟩, ?_⟩
    intro d hd hdel
    apply hnd
    apply mem_fDels.mpr
    refine ⟨d, (hmemU d).mpr ?_, hdel⟩
    rcases hd with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro ⟨⟨o, hor, hi, hrec⟩, hnd⟩
    have hmU : o ∈ ev₁ ∪ ev₂ := by
      rcases hor with h | h
      · exact Or.inl h
      · exact Or.inr h
    refine ⟨⟨o, (hmemU o).mpr hmU, hi, hrec⟩, ?_⟩
    intro hdel
    obtain ⟨d, hd, hdel'⟩ := mem_fDels.mp hdel
    rcases (hmemU d).mp hd with h | h
    · exact hnd d (Or.inl h) hdel'
    · exact hnd d (Or.inr h) hdel'

/-! ## §7  Honest reachability and the capstone -/

/-- Honest histories at the ternary configuration: every delete names an id
its issuer had observed (a `vis`-prior insert), and inserts are
chain-generated over the variant alphabet (positive, tag-wellformed,
telescoping). The FM datatype's `HonestDelivery`. -/
def FMHonest (Γ : OrderedPrefixCode) (C : Configuration (FMSig Γ)) : Prop :=
  (∀ e ∈ C.events, ∀ x : ℕ, e.2.2 = FOp.del x →
    ∃ a ∈ C.events, C.vis a e ∧ a.1 = x ∧ fIsIns a = true) ∧
  (∃ chainOf : ℕ → FMChain, ∀ o ∈ C.events, fIsIns o = true →
    PosFMChain (chainOf o.1) ∧ TagsOK (chainOf o.1) ∧
    fCoord Γ o = fmCoordOf Γ (chainOf o.1) ∧
    ((chainOf o.1).map fmδ).sum = o.1)

theorem fmHonest_core {Γ : OrderedPrefixCode} {C : Configuration (FMSig Γ)}
    (h : FMHonest Γ C) : FMHonestCore Γ (Configuration.core C) where
  del_has_ins := by
    intro e he x hx
    obtain ⟨a, ha, hv, hax, hai⟩ := h.1 e he x hx
    exact ⟨a, ha, hv, hax, hai⟩
  chain_gen := by
    obtain ⟨chainOf, hch⟩ := h.2
    exact ⟨chainOf, hch⟩

/-! ## §7.1  Public generation and convergence certificates -/

/-- The public FugueMax minting discipline.  An insert carries the positive,
tag-wellformed birth chain that justifies its coordinate and timestamp; a
delete may name only an element present in the issuer's materialized state.
Timestamp freshness is supplied separately by `LinearMintHistory`, as for the
other production instances. -/
def fApplicable (Γ : OrderedPrefixCode) (o : Op FOp) (s : SState) : Prop :=
  match o.2.2 with
  | .ins _ _ _ =>
      o.1 ∉ sIds s ∧ ∃ ch : FMChain,
        PosFMChain ch ∧ TagsOK ch ∧ fCoord Γ o = fmCoordOf Γ ch ∧
          (ch.map fmδ).sum = o.1
  | .del x => x ∈ sIds s

private theorem f_chain_witness {Γ : OrderedPrefixCode}
    (C : Configuration (FMSig Γ))
    (hApp : ∀ e ∈ C.events, ∃ π : List (Op FOp),
      listPermOf π {e' ∈ C.events | C.vis e' e} ∧
      fApplicable Γ e (fFold Γ π)) :
    ∀ t : ℕ, ∃ ch : FMChain, ∀ o ∈ C.events,
      fIsIns o = true → o.1 = t →
        PosFMChain ch ∧ TagsOK ch ∧ fCoord Γ o = fmCoordOf Γ ch ∧
          (ch.map fmδ).sum = o.1 := by
  intro t
  classical
  by_cases hex : ∃ o ∈ C.events, fIsIns o = true ∧ o.1 = t
  · obtain ⟨o, ho, hoi, hot⟩ := hex
    obtain ⟨π, _hπ, happ⟩ := hApp o ho
    obtain ⟨ts, r, op⟩ := o
    cases op with
    | del x => simp [fIsIns] at hoi
    | ins el pref ent =>
        obtain ⟨_fresh, ch, hpos, htags, hcoord, hsum⟩ := happ
        refine ⟨ch, ?_⟩
        intro o' ho' hoi' hot'
        have hoeq : o' = (ts, r, FOp.ins el pref ent) :=
          (Configuration.core C).ts_unique ho' ho (hot'.trans hot.symm)
        subst o'
        exact ⟨hpos, htags, hcoord, hsum⟩
  · refine ⟨[], ?_⟩
    intro o ho hi hot
    exact False.elim (hex ⟨o, ho, hi, hot⟩)

theorem fmHonest_of_applicable {Γ : OrderedPrefixCode}
    (C : Configuration (FMSig Γ))
    (hApp : ∀ e ∈ C.events, ∃ π : List (Op FOp),
      listPermOf π {e' ∈ C.events | C.vis e' e} ∧
      fApplicable Γ e (fFold Γ π)) : FMHonest Γ C := by
  constructor
  · intro e he x hx
    obtain ⟨π, hπ, happ⟩ := hApp e he
    obtain ⟨ts, r, op⟩ := e
    cases op with
    | ins el pref ent => simp at hx
    | del target =>
        injection hx with htarget
        subst x
        simp only [fApplicable] at happ
        unfold sIds at happ
        obtain ⟨rec, hrec, hrecId⟩ := List.mem_map.mp happ
        obtain ⟨a, ha, hai, harec⟩ := f_fold_rec_sub Γ π rec hrec
        have haev := (hπ.2 a).mp ha
        have hax : a.1 = target := by
          rw [harec] at hrecId
          exact hrecId
        exact ⟨a, haev.1, haev.2, hax, hai⟩
  · classical
    refine ⟨fun t => Classical.choose (f_chain_witness C hApp t), ?_⟩
    intro o ho hi
    exact Classical.choose_spec (f_chain_witness C hApp o.1) o ho hi rfl

def fmGeneration (Γ : OrderedPrefixCode) : Issuance (FMSig Γ) where
  CanIssue := fApplicable Γ

theorem fmHonest_of_mint {Γ : OrderedPrefixCode}
    {C : Configuration (FMSig Γ)}
    (h : MintHonest (FMSig Γ) (fApplicable Γ) C) : FMHonest Γ C :=
  fmHonest_of_applicable C (fun e he => by
    obtain ⟨π, hp, _hr, hg⟩ := h e he
    exact ⟨π, hp, hg⟩)

def fmConvergence (Γ : OrderedPrefixCode) :
    ConvergenceCertificate (FMSig Γ) (fmGeneration Γ) where
  soundV := fun h => isRALinearizable_of_join
    (ra_of_mintCertifiedV
      (fun _ hH => f_join_at (fmHonest_core (fmHonest_of_mint hH))) h)

theorem fuguemax_ra_linearizable {Γ : OrderedPrefixCode}
    {C : Configuration (FMSig Γ)}
    (h : MintCertifiedReach (FMSig Γ) (fmGeneration Γ) C) :
    IsRALinearizable (FMSig Γ) C :=
  (fmConvergence Γ).sound h

#print axioms fuguemax_ra_linearizable

/-! ## §7½  The bridge to the generation layer

`SidedRGA_FugueMax.lean`'s display fold `mFold` (over generation records
`MRec`) IS this signature's fold of the mapped enumeration: an insert
record denotes the `FOp.ins` carrying its chain's coordinate split as
(prefix of all but the last entry, minted entry). So `f_fold_canon` covers
the generation layer's states, and `MaxReach` configurations are runs of
the verified datatype. -/

/-- The op a generation record denotes. The `.ins` arm splits the chain as
(everything but the last entry, the minted entry); the empty-chain arm is
degenerate (unreachable on honest knowledge: deltas telescope to a
positive id). -/
def fOpOfM (Γ : OrderedPrefixCode) (g : MRec) : Op FOp :=
  match g.op, g.chain.getLast? with
  | .ins _ _, some ent =>
      (g.ts, g.rep, .ins g.ts (fmCoordOf Γ g.chain.dropLast) ent)
  | .ins _ _, none => (g.ts, g.rep, .ins g.ts [] (.L 0))
  | .del x, _ => (g.ts, g.rep, .del x)

/-- One step of the generation-layer fold is one step of the datatype. -/
theorem fUpdate_fOpOfM (Γ : OrderedPrefixCode) (s : SState) {g : MRec}
    (hch : mIsIns g = true → g.chain ≠ []) :
    fUpdate Γ s (fOpOfM Γ g) = mStep Γ s g := by
  cases hop : g.op with
  | del x =>
      unfold fOpOfM mStep
      rw [hop]
      cases g.chain.getLast? <;> rfl
  | ins p sd =>
      have hins : mIsIns g = true := by simp [mIsIns, hop]
      have hne := hch hins
      cases hlast : g.chain.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hlast) hne
      | some ent =>
          obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hlast
          have hcoord : fmCoordOf Γ g.chain.dropLast ++ fmBlock Γ ent
              = fmCoordOf Γ g.chain := by
            rw [hpre, List.dropLast_concat, fmCoordOf_append]
            simp [fmCoordOf]
          unfold fOpOfM mStep
          rw [hop, hlast]
          show (if g.ts ∈ sIds s then s
              else sInsert (g.ts, g.ts,
                fmCoordOf Γ g.chain.dropLast ++ fmBlock Γ ent) s)
            = (if g.ts ∈ sIds s then s
              else sInsert (g.ts, g.ts, fmCoordOf Γ g.chain) s)
          rw [hcoord]

/-- **The generation-layer fold is the datatype fold**: on knowledges whose
insert records carry nonempty chains (all honest ones), `mFold` is `fFold`
of the mapped enumeration. -/
theorem mFold_eq_fFold (Γ : OrderedPrefixCode) : ∀ (K : KnowM),
    (∀ g ∈ K, mIsIns g = true → g.chain ≠ []) →
    mFold Γ K = fFold Γ (K.map (fOpOfM Γ)) := by
  intro K
  induction K using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton K g ih =>
      intro hch
      rw [List.map_append, List.map_singleton, mFold_snoc, fFold_snoc,
        ih (fun g' hg' => hch g' (List.mem_append_left _ hg')),
        fUpdate_fOpOfM Γ _ (hch g (List.mem_append_right _ (by simp)))]

/-- Insert records of a `KInv`-satisfying knowledge carry nonempty chains
(their deltas telescope to a positive id). -/
theorem kinv_chain_ne_nil {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) : ∀ g ∈ K, mIsIns g = true → g.chain ≠ [] := by
  intro g hg hi hnil
  have hsum := (inv.wf g hg hi).2.2
  rw [hnil] at hsum
  have hpos := inv.pos g hg
  simp at hsum
  omega

/-- **Fold-canonicity for `mFold`**: two knowledges whose mapped
enumerations are well-formed and enumerate the same events display the
same state, the generation-layer face of `f_fold_canon`. -/
theorem m_fold_canon (Γ : OrderedPrefixCode) {K K' : KnowM}
    (hch : ∀ g ∈ K, mIsIns g = true → g.chain ≠ [])
    (hch' : ∀ g ∈ K', mIsIns g = true → g.chain ≠ [])
    (hwf : FWf Γ (K.map (fOpOfM Γ))) (hwf' : FWf Γ (K'.map (fOpOfM Γ)))
    (hmem : ∀ o, o ∈ K.map (fOpOfM Γ) ↔ o ∈ K'.map (fOpOfM Γ)) :
    mFold Γ K = mFold Γ K' := by
  rw [mFold_eq_fFold Γ K hch, mFold_eq_fFold Γ K' hch',
    f_fold_canon Γ hwf hwf' hmem]

#print axioms f_fold_canon
#print axioms mFold_eq_fFold
#print axioms m_fold_canon

/-! ## §8  SPOTs (PASS+FAIL, hand-derived)

Unary code: `enc d = replicate d true ++ [false]`; `compl` negates;
`symR : false ↦ 1, true ↦ 2`; `fw k = [(8-k)/3, (8-k)%3]` so
`fw 0 = [2,2]`, `fw 1 = [2,1]`, `fw 2 = [2,0]`, `fw 3 = [1,2]`;
`fmBlock (.R t d) = fwTag t ++ map symR (compl (enc d))`;
`sKey c = c ++ [3]`; the state is sorted strictly DESCENDING by key. -/

namespace FugueMaxRALinSPOT

/-! ### Same-tag R siblings: ascending delta, order-insensitive fold -/

def opA : Op FOp := (1, 0, FOp.ins 11 [] (.R [0] 1))
def opB : Op FOp := (2, 1, FOp.ins 22 [] (.R [0] 2))
def ρTie : List (Op FOp) := [opA, opB]

/-- PASS, record-level: hand-derived coordinates.
`coord opA = fwTag [0] ++ map symR (compl [t,f]) = [2,2] ++ [1,2]`;
`coord opB = [2,2] ++ map symR [f,f,t] = [2,2,1,1,2]`. First key
difference at index 3 (`2` vs `1`), so id 1 displays first. -/
theorem tie_fold :
    fFold unaryCode ρTie
      = [(1, 11, [2, 2, 1, 2]), (2, 22, [2, 2, 1, 1, 2])] := by
  native_decide

/-- PASS: same-tag siblings ascend by delta, the display twin of the
generation layer's `tie_display`. -/
theorem tie_ids : sIds (fFold unaryCode ρTie) = [1, 2] := by native_decide

/-- FAIL pin: the descending order is NOT displayed. -/
theorem tie_ids_not_desc : sIds (fFold unaryCode ρTie) ≠ [2, 1] := by
  native_decide

/-- FAIL pin: the fold is not constantly empty. -/
theorem tie_fold_ne_empty : fFold unaryCode ρTie ≠ [] := by native_decide

/-- PASS: fold-canonicity made concrete, the reversed enumeration folds
to the SAME state (the enumeration order is erased). -/
theorem tie_fold_order_erased :
    fFold unaryCode [opB, opA] = fFold unaryCode ρTie := by native_decide

/-! ### The tag is decisive: it overrides ascending-id order -/

def opA2 : Op FOp := (2, 0, FOp.ins 22 [] (.R [0] 2))
/-- Right origin = `opA2` (tag = its key `[2,2,1,1,2,3]`), the
FugueMax-critical shape: an R sibling anchored at a LIVE right origin. -/
def opB2 : Op FOp := (1, 1, FOp.ins 11 [] (.R [2, 2, 1, 1, 2, 3] 1))

/-- PASS: the end-tagged sibling (right origin `end`, display-later)
precedes the live-origin sibling despite its LARGER id:
`coord opA2 = [2,2,1,1,2]`; `coord opB2 = fwTag [2,2,1,1,2,3] ++ [1,2]
= [2,0,2,0,2,1,2,1,2,0,1,2,1,2]`; first key difference at index 1
(`2` vs `0`). The tag overrides the id order. -/
theorem tag_decisive_ids :
    sIds (fFold unaryCode [opA2, opB2]) = [2, 1] := by native_decide

/-- FAIL pin: the ascending-id (plain-Fugue tiebreak) order is NOT
displayed, the pin that kills every re-banding without tags. -/
theorem tag_decisive_not_id_order :
    sIds (fFold unaryCode [opA2, opB2]) ≠ [1, 2] := by native_decide

/-! ### Delete and merge -/

def ρDel : List (Op FOp) := ρTie ++ [(3, 0, FOp.del 1)]

/-- PASS: delete removes exactly its target. -/
theorem del_ids : sIds (fFold unaryCode ρDel) = [2] := by native_decide

/-- FAIL pin: the delete is not a no-op. -/
theorem del_not_noop : sIds (fFold unaryCode ρDel) ≠ [1, 2] := by
  native_decide

/-- FAIL pin: the delete did not clobber the survivor. -/
theorem del_not_clobber : sIds (fFold unaryCode ρDel) ≠ [] := by
  native_decide

/-- PASS: the ternary merge of the two singleton branches (empty LCA) is
the canonical two-record state, hand-derived, same keys as `tie_fold`. -/
theorem merge_ids :
    sIds (sMergeL [] (fFold unaryCode [opA]) (fFold unaryCode [opB]))
      = [1, 2] := by native_decide

/-- FAIL pin: the merge is not a projection of either input. -/
theorem merge_not_projection :
    sMergeL [] (fFold unaryCode [opA]) (fFold unaryCode [opB])
        ≠ fFold unaryCode [opA] ∧
    sMergeL [] (fFold unaryCode [opA]) (fFold unaryCode [opB])
        ≠ fFold unaryCode [opB] := by native_decide

end FugueMaxRALinSPOT

#print axioms FugueMaxRALinSPOT.tie_fold
#print axioms FugueMaxRALinSPOT.tag_decisive_ids

end Sal.MRDTs.Instances.SidedEmbedRGA
