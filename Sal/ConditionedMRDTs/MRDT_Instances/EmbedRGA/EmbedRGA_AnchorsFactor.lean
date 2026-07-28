import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_Stability_Bridge

/-!
# AnchorsFactorBeyond discharged: the stable-prefix geometry of honest mints

`EmbedRGA_Stability_Bridge.lean` left one named residue: `AnchorsFactorBeyond`,
the claim that every op minted with a settled cut in its causal past carries an
anchor prefix that factors at the stable-prefix map. This file discharges it.

**The geometry.** Under the §8 generation discipline (`GenHonest eApplicable` +
`CausalPastEnumerable`, the same hypotheses `eHonest_of_genHonest` already
consumes), every insert's carried prefix is the *stored coordinate of an actual
anchor record* in the fold of its causal past. That pins the factorization at a
codeword boundary: there is a global chain assignment (`EAnchored`) under which
every insert's coordinate is a positive birth-chain telescope, the carried
prefix is exactly the anchor's chain coordinate, and the mint appends one
positive delta (`chainOf o.1 = chainOf d ++ [o.1 - d]`). The residue then
reduces to a containment: any bundle whose `MintAt` contains the canonical
chain-aligned mints (`ChainMintBeyond`) satisfies `AnchorsFactorBeyond`
(`anchorsFactorBeyond_of_anchored`), and the bridge is restated without the
residue (`eRecode_settled_bridge_honest`).

**Remarks (hypotheses and scope).**
* The residue is *not* dischargeable from bare honest reachability
  (`EReach`/`EHonest` alone): `chain_gen` constrains the minted coordinate,
  not the carried split. Countermodel: unary code, `ins e 1^{t-1} (t-1)` at
  id `t` has `eCoord = coordOf [t]` (so `chain_gen` holds with chain `[t]`)
  while the carried prefix `1^{t-1}` is not a chain coordinate. The correct
  source is the generation discipline, which this file takes as hypotheses.
* The `d = 0` corner: under the discipline no insert event can carry id `0`
  (`eApplicable` would demand `anchor < 0`), so the second `eApplicable`
  disjunct never fires at anchor `0` and root mints factor at `coordOf [] = []`.
  The `MintAt` guard needs no special case.
* Per the runtime twin's erratum (id-addressed cuts break after epoch one:
  renumbered coordinates no longer telescope to event ids), the cut-side data
  in the concrete compaction construction are addressed by
  *coordinates/chains*, never by ids resolved through prefix sums; the
  id-arithmetic in this file (`sum` fields, `causal_mono` freshness) is used
  only *inside* the honest epoch-zero configuration. **Scope: the
  single-epoch statement**, one compaction applied at a settled cut of an
  honest configuration; re-basing honesty for later epochs remains open,
  addressed by the protocol construction in `EmbedRGA_Recoding.lean` §6.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode PosChain coordOf coordOf_append coordOf_inj)

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §1 Chain scraps -/

theorem posChain_eq_nil_of_sum_eq_zero {ch : List ℕ} (hpos : PosChain ch)
    (hsum : ch.sum = 0) : ch = [] := by
  cases ch with
  | nil => rfl
  | cons d ds =>
      have hd := hpos d List.mem_cons_self
      rw [List.sum_cons] at hsum
      omega

theorem eIsIns_of_ins {o : Op (EOp α)} {e : α} {π : List Bool} {d : ℕ}
    (h : o.2.2 = EOp.ins e π d) : eIsIns o = true := by
  simp [eIsIns, h]

/-! ## §2 What the `applicable` discipline pins about every insert's anchor

The carried prefix is the stored coordinate of a real, `vis`-prior anchor
record; the anchor id is smaller (Lamport); and the anchor is **live in the
whole causal past**, no delete of it is visible to the mint. The liveness
clause is where the ∀-enumeration form of `GenHonest` earns its keep: were a
delete visible, the enumeration ending with that delete would refute the
`eApplicable` membership check. -/

/-- Under the discipline, no insert event carries timestamp `0` (its anchor
would need `anchor < 0`). This closes the `d = 0` corner: anchor `0` always
means the root, never a record. -/
theorem eGen_no_zero_ins {Γ : OrderedPrefixCode} {C : Configuration (E Γ α)}
    (hGen : GenHonest (E Γ α) eApplicable C)
    (hEnum : CausalPastEnumerable (E Γ α) C) :
    ∀ a ∈ C.events, eIsIns a = true → a.1 ≠ 0 := by
  intro a ha hai h0
  obtain ⟨π₀, hπ₀⟩ := hEnum a ha
  have happ := hGen a ha π₀ hπ₀
  obtain ⟨ta, ra, opa⟩ := a
  cases opa with
  | del x => simp [eIsIns] at hai
  | ins e' π' d' =>
      simp only [eApplicable] at happ
      have hta : ta = 0 := h0
      rw [hta] at happ
      exact absurd happ.1 (Nat.not_lt_zero d')

/-- **The anchor extraction.** Every insert of a disciplined configuration
carries: a Lamport-smaller anchor id; and either the root anchor with the
empty prefix, or a `vis`-prior anchor *insert event* whose stored coordinate
IS the carried prefix, with **no delete of that anchor anywhere in the mint's
causal past**. -/
theorem eGen_ins_anchor {Γ : OrderedPrefixCode} {C : Configuration (E Γ α)}
    (hGen : GenHonest (E Γ α) eApplicable C)
    (hEnum : CausalPastEnumerable (E Γ α) C) :
    ∀ o ∈ C.events, ∀ (e : α) (π : List Bool) (d : ℕ), o.2.2 = EOp.ins e π d →
      d < o.1 ∧
      ((d = 0 ∧ π = []) ∨
        (d ≠ 0 ∧
          (∃ a, a ∈ C.events ∧ C.vis a o ∧ eIsIns a = true ∧ a.1 = d ∧
            π = eCoord Γ a) ∧
          (∀ dl, dl ∈ C.events → C.vis dl o → dl.2.2 ≠ EOp.del d))) := by
  intro o ho e π d hop
  obtain ⟨π₀, hπ₀⟩ := hEnum o ho
  have happ := hGen o ho π₀ hπ₀
  obtain ⟨t, r, op⟩ := o
  simp only at hop
  subst hop
  simp only [eApplicable] at happ
  obtain ⟨hdt, hcase⟩ := happ
  refine ⟨hdt, ?_⟩
  rcases hcase with ⟨h0, hπ⟩ | ⟨el, hmem⟩
  · exact Or.inl ⟨h0, hπ⟩
  · obtain ⟨a, haπ, hai, hae⟩ := e_fold_rec_sub Γ π₀ (d, el, π) hmem
    have haev := (hπ₀.2 a).mp haπ
    have ha1 : a.1 = d := (congrArg Prod.fst hae).symm
    have hπcoord : π = eCoord Γ a :=
      congrArg (fun p : ERec α => p.2.2) hae
    have hd0 : d ≠ 0 := fun h0 =>
      eGen_no_zero_ins hGen hEnum a haev.1 hai (ha1.trans h0)
    refine Or.inr ⟨hd0, ⟨a, haev.1, haev.2, hai, ha1, hπcoord⟩, ?_⟩
    -- anchor liveness: re-enumerate the causal past with the delete last
    intro dl hdl hvisdl hdel
    have hdlπ : dl ∈ π₀ := (hπ₀.2 dl).mpr ⟨hdl, hvisdl⟩
    have hperm₁ : listPermOf (π₀.erase dl ++ [dl])
        {e' ∈ C.events | C.vis e' (t, r, EOp.ins e π d)} := by
      constructor
      · refine List.nodup_append.mpr
          ⟨hπ₀.1.erase dl, List.nodup_singleton dl, ?_⟩
        intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        rw [hy] at hxy
        rw [hxy] at hx
        exact ((hπ₀.1.mem_erase_iff).mp hx).1 rfl
      · intro x
        rw [List.mem_append, List.mem_singleton]
        constructor
        · rintro (hx | rfl)
          · exact (hπ₀.2 x).mp (List.mem_of_mem_erase hx)
          · exact ⟨hdl, hvisdl⟩
        · intro hx
          by_cases hxdl : x = dl
          · exact Or.inr hxdl
          · exact Or.inl ((List.mem_erase_of_ne hxdl).mpr ((hπ₀.2 x).mpr hx))
    have happ₁ := hGen _ ho _ hperm₁
    simp only [eApplicable] at happ₁
    rcases happ₁.2 with ⟨h0, -⟩ | ⟨el', hmem'⟩
    · exact hd0 h0
    · have hfold : eFold Γ (π₀.erase dl ++ [dl])
          = eUpdate Γ (eFold Γ (π₀.erase dl)) dl := eFold_snoc Γ _ dl
      have hupd : eUpdate Γ (eFold Γ (π₀.erase dl)) dl
          = (eFold Γ (π₀.erase dl)).filter (fun rec => decide (rec.1 ≠ d)) := by
        obtain ⟨t', r', op'⟩ := dl
        simp only at hdel
        rw [hdel]
        rfl
      have hmem'' : (d, el', π) ∈
          (eFold Γ (π₀.erase dl)).filter (fun rec => decide (rec.1 ≠ d)) := by
        rw [← hupd, ← hfold]
        exact hmem'
      have := List.of_mem_filter hmem''
      simp at this

/-! ## §3 The anchored chain certificate

`EHonest.chain_gen` upgraded: one global chain assignment under which the
carried prefix of every insert is its anchor's chain coordinate, the
stable/unstable split of a coordinate is a chain split, at a codeword
boundary. -/

/-- The anchored chain certificate for a configuration. -/
structure EAnchored (Γ : OrderedPrefixCode) (C : Configuration (E Γ α))
    (chainOf : ℕ → List ℕ) : Prop where
  root : chainOf 0 = []
  pos : ∀ o, o ∈ C.events → eIsIns o = true → PosChain (chainOf o.1)
  coord : ∀ o, o ∈ C.events → eIsIns o = true →
    eCoord Γ o = coordOf Γ (chainOf o.1)
  sum : ∀ o, o ∈ C.events → eIsIns o = true → (chainOf o.1).sum = o.1
  /-- The factorization: the carried prefix IS the anchor's chain coordinate,
  and the mint appends exactly one positive delta. -/
  anchored : ∀ o, o ∈ C.events → ∀ (e : α) (π : List Bool) (d : ℕ),
    o.2.2 = EOp.ins e π d →
    d < o.1 ∧ π = coordOf Γ (chainOf d) ∧ chainOf o.1 = chainOf d ++ [o.1 - d]
  /-- Non-root anchors are real `vis`-prior insert events, live in the whole
  causal past of the mint. -/
  anchor_event : ∀ o, o ∈ C.events → ∀ (e : α) (π : List Bool) (d : ℕ),
    o.2.2 = EOp.ins e π d → d ≠ 0 →
    (∃ a, a ∈ C.events ∧ eIsIns a = true ∧ a.1 = d ∧ C.vis a o) ∧
    (∀ dl, dl ∈ C.events → C.vis dl o → dl.2.2 ≠ EOp.del d)

/-- **The certificate exists** at every disciplined configuration: the chain
assignment of `e_chain_exists`, with the carried-prefix factorization pinned
by unique decodability against the anchor extraction. -/
theorem eAnchored_exists {Γ : OrderedPrefixCode} {C : Configuration (E Γ α)}
    (hGen : GenHonest (E Γ α) eApplicable C)
    (hEnum : CausalPastEnumerable (E Γ α) C) :
    ∃ chainOf : ℕ → List ℕ, EAnchored Γ C chainOf := by
  classical
  have hApp : ∀ e ∈ C.events, ∃ π : List (Op (EOp α)),
      listPermOf π {e' ∈ C.events | C.vis e' e} ∧ eApplicable e (eFold Γ π) :=
    fun e he => (hEnum e he).imp (fun π hπ => ⟨hπ, hGen e he π hπ⟩)
  set chainOf : ℕ → List ℕ :=
    fun t => Classical.choose (e_chain_exists C hApp t) with hchdef
  have hspec : ∀ t : ℕ, PosChain (chainOf t) ∧ (chainOf t).sum = t ∧
      ∀ o ∈ C.events, eIsIns o = true → o.1 = t →
        eCoord Γ o = coordOf Γ (chainOf t) :=
    fun t => Classical.choose_spec (e_chain_exists C hApp t)
  have hroot : chainOf 0 = [] :=
    posChain_eq_nil_of_sum_eq_zero (hspec 0).1 (hspec 0).2.1
  have hcoord : ∀ o, o ∈ C.events → eIsIns o = true →
      eCoord Γ o = coordOf Γ (chainOf o.1) :=
    fun o ho hi => (hspec o.1).2.2 o ho hi rfl
  have hpos : ∀ o, o ∈ C.events → eIsIns o = true → PosChain (chainOf o.1) :=
    fun o _ _ => (hspec o.1).1
  refine ⟨chainOf, hroot, hpos, hcoord, fun o _ _ => (hspec o.1).2.1, ?_, ?_⟩
  · -- the factorization
    intro o ho e π d hop
    obtain ⟨hdt, hcase⟩ := eGen_ins_anchor hGen hEnum o ho e π d hop
    have hins := eIsIns_of_ins hop
    have hco : eCoord Γ o = π ++ Γ.enc (o.1 - d) := by
      unfold eCoord
      rw [hop]
    have hδ : 1 ≤ o.1 - d := Nat.sub_pos_of_lt hdt
    have hπa : π = coordOf Γ (chainOf d) ∧ PosChain (chainOf d) := by
      rcases hcase with ⟨h0, hπ⟩ | ⟨hd0, ⟨a, haev, havis, hai, ha1, hπe⟩, -⟩
      · rw [h0, hroot, hπ]
        exact ⟨rfl, fun x hx => absurd hx (List.not_mem_nil)⟩
      · rw [← ha1]
        exact ⟨hπe.trans (hcoord a haev hai), hpos a haev hai⟩
    refine ⟨hdt, hπa.1, ?_⟩
    apply coordOf_inj Γ (hpos o ho hins)
    · intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hπa.2 x hx'
      · rw [List.mem_singleton.mp hx']
        exact hδ
    · rw [← hcoord o ho hins, hco, hπa.1, coordOf_append]
      simp [coordOf]
  · -- non-root anchors are live vis-prior events
    intro o ho e π d hop hd0
    obtain ⟨-, hcase⟩ := eGen_ins_anchor hGen hEnum o ho e π d hop
    rcases hcase with ⟨h0, -⟩ | ⟨-, ⟨a, haev, havis, hai, ha1, -⟩, hlive⟩
    · exact absurd h0 hd0
    · exact ⟨⟨a, haev, hai, ha1, havis⟩, hlive⟩

/-- **Ancestor realization**: every node of an honest insert's chain is minted
by an actual insert event of the configuration (strong induction along the
anchor recursion). This is what lets the concrete compaction construction
classify every coordinate occurrence by the epoch of its minting event. -/
theorem EAnchored.realize {Γ : OrderedPrefixCode} {C : Configuration (E Γ α)}
    {chainOf : ℕ → List ℕ} (hA : EAnchored Γ C chainOf) :
    ∀ o, o ∈ C.events → eIsIns o = true → ∀ p d, (p ++ [d]) <+: chainOf o.1 →
      ∃ a, a ∈ C.events ∧ eIsIns a = true ∧ chainOf a.1 = p ++ [d] := by
  suffices h : ∀ t : ℕ, ∀ o, o ∈ C.events → eIsIns o = true → o.1 = t →
      ∀ p d, (p ++ [d]) <+: chainOf o.1 →
      ∃ a, a ∈ C.events ∧ eIsIns a = true ∧ chainOf a.1 = p ++ [d] by
    exact fun o ho hi => h o.1 o ho hi rfl
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro o ho hi hot p d hpre
    obtain ⟨t0, r0, op0⟩ := o
    cases op0 with
    | del x => simp [eIsIns] at hi
    | ins e π danc =>
        obtain ⟨hdt, -, hch⟩ := hA.anchored _ ho e π danc rfl
        simp only at hdt hch hot
        rw [hch] at hpre
        by_cases hfull :
            (p ++ [d]).length = (chainOf danc ++ [t0 - danc]).length
        · refine ⟨(t0, r0, EOp.ins e π danc), ho, hi, ?_⟩
          rw [hch]
          exact (hpre.eq_of_length hfull).symm
        · have hlen : (p ++ [d]).length ≤ (chainOf danc).length := by
            have h1 := hpre.length_le
            simp only [List.length_append, List.length_singleton] at h1 hfull ⊢
            omega
          have hpre' : (p ++ [d]) <+: chainOf danc :=
            List.prefix_of_prefix_length_le hpre (List.prefix_append _ _) hlen
          have hd0 : danc ≠ 0 := by
            intro h0
            rw [h0, hA.root] at hpre'
            have := hpre'.length_le
            simp at this
          obtain ⟨⟨a, haev, hai, ha1, -⟩, -⟩ :=
            hA.anchor_event _ ho e π danc rfl hd0
          refine ih a.1 ?_ a haev hai rfl p d ?_
          · rw [ha1, ← hot]
            exact hdt
          · rw [ha1]
            exact hpre'

/-! ## §4 The residue, discharged

`AnchorsFactorBeyond` reduces to a containment: the bundle's `MintAt` must
contain the *canonical chain-aligned mints beyond the cut*. For the concrete
verified compaction construction this containment is definitional. -/

/-- The canonical mint predicate at a cut `S`: `(π, δ)` is minted beyond the
cut by an actual event, `π` a positive chain's coordinate and `δ` its one new
positive delta. -/
def ChainMintBeyond (Γ : OrderedPrefixCode) (C : Configuration (E Γ α))
    (S : Set (Op (EOp α))) (chainOf : ℕ → List ℕ)
    (π : List Bool) (δ : ℕ) : Prop :=
  1 ≤ δ ∧ ∃ chA, π = coordOf Γ chA ∧ PosChain chA ∧
    ∃ o, o ∈ C.events ∧ eIsIns o = true ∧ (∀ a ∈ S, C.vis a o) ∧
      chainOf o.1 = chA ++ [δ]

/-- **`AnchorsFactorBeyond` holds** for every bundle whose `MintAt` contains
the canonical chain-aligned mints, the bridge's named residue is a theorem
of the anchored geometry, not an extra hypothesis. -/
theorem anchorsFactorBeyond_of_anchored {Γ : OrderedPrefixCode}
    {C : Configuration (E Γ α)} {chainOf : ℕ → List ℕ}
    (hA : EAnchored Γ C chainOf) (F : StablePrefixMap Γ)
    (S : Set (Op (EOp α)))
    (hMint : ∀ π δ, ChainMintBeyond Γ C S chainOf π δ → F.MintAt π δ) :
    AnchorsFactorBeyond Γ F C S := by
  intro o ho hvis e π d hop
  obtain ⟨hdt, hπ, hch⟩ := hA.anchored o ho e π d hop
  refine hMint π (o.1 - d)
    ⟨Nat.sub_pos_of_lt hdt, chainOf d, hπ, ?_, o, ho, eIsIns_of_ins hop,
      hvis, hch⟩
  by_cases hd0 : d = 0
  · rw [hd0, hA.root]
    exact fun x hx => absurd hx (List.not_mem_nil)
  · obtain ⟨⟨a, haev, hai, ha1, -⟩, -⟩ := hA.anchor_event o ho e π d hop hd0
    rw [← ha1]
    exact hA.pos a haev hai

/-! ## §5 The upgraded bridge -/

/-- **The bridge, residue-free.** `eRecode_settled_bridge` restated for
disciplined (honest) configurations: the `AnchorsFactorBeyond` hypothesis is
*gone*, replaced by the construction-checkable containment of the canonical
chain-aligned mints in the bundle's `MintAt`, no `vis`-condition survives in
the interface. At a settled cut whose state the map covers, every
continuation of events existing beyond the cut folds and reads identically
under the lazy translation. -/
theorem eRecode_settled_bridge_honest {Γ : OrderedPrefixCode}
    (F : StablePrefixMap Γ) {C : Configuration (E Γ α)}
    (hGen : GenHonest (E Γ α) eApplicable C)
    (hEnum : CausalPastEnumerable (E Γ α) C)
    {v : Version} {S : Set (Op (EOp α))} {s : EState α} {Ev : Set (Op (EOp α))}
    (hv : C.ver v = some (s, Ev)) (hsettled : SettledAtOn C Ev S)
    (hrest : ∀ x ∈ s, F.Dom x.2.2)
    (hMint : ∀ chainOf : ℕ → List ℕ, EAnchored Γ C chainOf →
      ∀ π δ, ChainMintBeyond Γ C S chainOf π δ → F.MintAt π δ)
    (τ : List (Op (EOp α))) (hτ_beyond : ∀ o ∈ τ, o ∈ C.events ∧ o ∉ Ev) :
    applySeq (E Γ α).toCRDTSig (eRemapSt F.f s) (τ.map (eRemapOp F.f))
        = eRemapSt F.f (applySeq (E Γ α).toCRDTSig s τ) ∧
      (E Γ α).query
          (applySeq (E Γ α).toCRDTSig (eRemapSt F.f s)
            (τ.map (eRemapOp F.f))) ()
        = (E Γ α).query (applySeq (E Γ α).toCRDTSig s τ) () := by
  obtain ⟨chainOf, hA⟩ := eAnchored_exists hGen hEnum
  exact eRecode_settled_bridge F hv hsettled
    (anchorsFactorBeyond_of_anchored hA F S (hMint chainOf hA))
    hrest τ hτ_beyond

/-! ## §6 Axiom audit -/

#print axioms eGen_ins_anchor
#print axioms eAnchored_exists
#print axioms EAnchored.realize
#print axioms anchorsFactorBeyond_of_anchored
#print axioms eRecode_settled_bridge_honest

end Sal.ConditionedMRDTs
