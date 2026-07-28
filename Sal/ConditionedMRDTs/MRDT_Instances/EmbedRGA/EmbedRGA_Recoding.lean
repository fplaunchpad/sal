import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA

/-!
# The re-coding theorem — state-level GC for the embed RGA

Coordinates are birth constants: a live record carries every dead ancestor's
codeword forever, so coordinate weight grows with history, not with the live
document. A GC epoch re-codes below a *stable cut*. Replicas cannot switch
in lockstep, so the model is **lazy translation**: a pure function on
coordinates applied to the state at rest and to each incoming op's carried
anchor prefix (the delta codeword an op mints is never touched).

The hypothesis bundle `StablePrefixMap` is the semantic residue of the
stable-prefix factorization `ρ̂ c = ρ (stab c) ++ rest c`
(`whiteboard/embed-recoding-note.md`): H2 = `ord` (the re-map preserves the
fold's key comparator on the coordinates at hand), H3 = `ext` (the re-map
commutes with beyond-cut extensions), and H1 (injectivity) is *derived*
(`StablePrefixMap.injOn`). The cluster:

* **T1** `eRecode_applySeq` / `eRecode_fold` — fold congruence, parametric
  in the cut state: folding translated ops over the translated state is the
  translation of the untranslated fold;
* **T2** `eRecode_reads_identical` — the element sequence of the translated
  fold is the untranslated one, verbatim: compression is invisible;
* **T3** `eRecode_fold_canon` (canonicity transports), `eRecode_sorted` /
  `eRecode_version_sorted` (the re-coded version is still canonical, no
  re-sort), `eRecode_ra_transport` (the capstone's per-version witness
  survives the re-map);
* `eRecode_ext_global_collapse`: demanding H3 at *every* historical mint
  collapses the re-map to a constant-prefix prepend, so the whole-history
  congruence is trivial and the cut-parametric statement is the only
  nontrivial formulation — re-coding is an epoch operation on states, not a
  history rewrite.

Out of scope (`whiteboard/embed-recoding-note.md` §6): the protocol half
choosing a common cut (stable delete alone does not preclude in-flight
anchors; it takes all-heads visibility), and the FugueMax tagged variant
(keys occur inside tags; the re-map would have to rewrite under the tag
structure).
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode keyLt keyLe key unaryCode binaryCode
  keyLt_total keyLt_irrefl key_inj coordOf coordOf_append PosChain)

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §1  The re-map and the hypothesis bundle -/

/-- Re-map a record's coordinate; id and element untouched. -/
def eRemapRec (f : List Bool → List Bool) (r : ERec α) : ERec α :=
  (r.1, r.2.1, f r.2.2)

/-- Re-map a state at rest: every record's coordinate, list order untouched. -/
def eRemapSt (f : List Bool → List Bool) (s : EState α) : EState α :=
  s.map (eRemapRec f)

/-- Lazy translation of an incoming op: the carried anchor prefix is
re-mapped; the delta (minted by the fold from `o.1 - a`) is not touched;
deletes are id-based and pass through. -/
def eRemapOp (f : List Bool → List Bool) (o : Op (EOp α)) : Op (EOp α) :=
  (o.1, o.2.1,
    match o.2.2 with
    | .ins e π a => .ins e (f π) a
    | .del x => .del x)

/-- **The stable-prefix re-map bundle.** `Rest` marks the coordinates of the
records at rest (the cut state's document); `MintAt π d` marks the
anchor/delta pairs of ops applied beyond the cut. `ext` is H3 (extension
commuting, automatic for a genuine stable-prefix map because a beyond-cut
mint factors at the same stable prefix as its anchor); `ord` is H2 (the
fold's comparator is preserved on the coordinates at hand, both directions,
as a Boolean equation). H1 (injectivity) is derived below. -/
structure StablePrefixMap (Γ : OrderedPrefixCode) where
  f : List Bool → List Bool
  Rest : List Bool → Prop
  MintAt : List Bool → ℕ → Prop
  ext : ∀ {π : List Bool} {d : ℕ}, MintAt π d →
    f (π ++ Γ.enc d) = f π ++ Γ.enc d
  ord : ∀ {c c' : List Bool},
    (Rest c ∨ ∃ π d, MintAt π d ∧ c = π ++ Γ.enc d) →
    (Rest c' ∨ ∃ π d, MintAt π d ∧ c' = π ++ Γ.enc d) →
    keyLt (key (f c)) (key (f c')) = keyLt (key c) (key c')

namespace StablePrefixMap

variable {Γ : OrderedPrefixCode}

/-- The coordinates at hand: at rest, or minted beyond the cut. -/
def Dom (F : StablePrefixMap Γ) (c : List Bool) : Prop :=
  F.Rest c ∨ ∃ π d, F.MintAt π d ∧ c = π ++ Γ.enc d

theorem ord' (F : StablePrefixMap Γ) {c c' : List Bool}
    (h : F.Dom c) (h' : F.Dom c') :
    keyLt (key (F.f c)) (key (F.f c')) = keyLt (key c) (key c') :=
  F.ord h h'

/-- **H1 is free**: comparator preservation (H2) plus key totality and key
injectivity force injectivity on the domain. -/
theorem injOn (F : StablePrefixMap Γ) {c c' : List Bool}
    (h : F.Dom c) (h' : F.Dom c') (heq : F.f c = F.f c') : c = c' := by
  by_contra hne
  have hk : key c ≠ key c' := fun hk => hne (key_inj hk)
  rcases keyLt_total hk with hlt | hlt
  · have hor := F.ord' h h'
    rw [heq, keyLt_irrefl, hlt] at hor
    exact Bool.noConfusion hor
  · have hor := F.ord' h' h
    rw [heq, keyLt_irrefl, hlt] at hor
    exact Bool.noConfusion hor

end StablePrefixMap

/-! ## §2  Re-map plumbing: ids, elements, membership -/

@[simp] theorem eRemapRec_fst (f : List Bool → List Bool) (r : ERec α) :
    (eRemapRec f r).1 = r.1 := rfl

theorem eIds_eRemapSt (f : List Bool → List Bool) (s : EState α) :
    eIds (eRemapSt f s) = eIds s := by
  simp only [eIds, eRemapSt, List.map_map]
  rfl

/-- The read ignores coordinates: a re-map at rest is invisible. -/
theorem eRemapSt_query (Γ : OrderedPrefixCode) (f : List Bool → List Bool)
    (s : EState α) :
    (E Γ α).query (eRemapSt f s) () = (E Γ α).query s () := by
  show (eRemapSt f s).map (fun r => r.2.1) = s.map (fun r => r.2.1)
  simp only [eRemapSt, List.map_map]
  rfl

/-- One-step record provenance: an update's output records are the input's
or the op's own mint. -/
theorem mem_eUpdate_cases {Γ : OrderedPrefixCode} {s : EState α}
    {o : Op (EOp α)} {x : ERec α} (hx : x ∈ eUpdate Γ s o) :
    x ∈ s ∨ x = eRecOf Γ o := by
  obtain ⟨t, rr, op⟩ := o
  cases op with
  | ins e π a =>
      simp only [eUpdate] at hx
      by_cases hmem : t ∈ eIds s
      · rw [if_pos hmem] at hx
        exact Or.inl hx
      · rw [if_neg hmem] at hx
        rcases mem_eInsert.mp hx with h | h
        · exact Or.inl h
        · right
          rw [h]
          rfl
  | del y => exact Or.inl (List.mem_of_mem_filter hx)

/-! ## §3  The step lemmas -/

/-- Sorted insertion commutes with the re-map when the newcomer's key
comparisons against the standing records are preserved. -/
theorem eInsert_remap (f : List Bool → List Bool) (r : ERec α) :
    ∀ (s : EState α),
    (∀ x ∈ s, keyLt (key (f x.2.2)) (key (f r.2.2))
        = keyLt (key x.2.2) (key r.2.2)) →
    eInsert (eRemapRec f r) (eRemapSt f s) = eRemapSt f (eInsert r s)
  | [], _ => rfl
  | x :: xs, h => by
      have hx := h x List.mem_cons_self
      rw [show eRemapSt f (x :: xs) = eRemapRec f x :: eRemapSt f xs from rfl]
      by_cases hc : keyLt (key x.2.2) (key r.2.2) = true
      · have hc' : keyLt (key ((eRemapRec f x).2.2))
            (key ((eRemapRec f r).2.2)) = true := by
          show keyLt (key (f x.2.2)) (key (f r.2.2)) = true
          rw [hx]
          exact hc
        rw [show eInsert (eRemapRec f r) (eRemapRec f x :: eRemapSt f xs)
              = eRemapRec f r :: eRemapRec f x :: eRemapSt f xs from by
            simp [eInsert, hc']]
        rw [show eInsert r (x :: xs) = r :: x :: xs from by simp [eInsert, hc]]
        rfl
      · have hc' : ¬ keyLt (key ((eRemapRec f x).2.2))
            (key ((eRemapRec f r).2.2)) = true := by
          show ¬ keyLt (key (f x.2.2)) (key (f r.2.2)) = true
          rw [hx]
          exact hc
        rw [show eInsert (eRemapRec f r) (eRemapRec f x :: eRemapSt f xs)
              = eRemapRec f x :: eInsert (eRemapRec f r) (eRemapSt f xs) from by
            simp [eInsert, hc']]
        rw [show eInsert r (x :: xs) = x :: eInsert r xs from by
            simp [eInsert, hc]]
        rw [eInsert_remap f r xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]
        rfl

/-- **The step lemma**: one translated op on the translated state is the
translation of the untranslated step. The insert guard is id-based
(unaffected); the mint is repaired by `ext` (H3); the sorted insertion is
repaired by `ord` (H2); the delete filters by id. -/
theorem eUpdate_remap {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    (s : EState α) (o : Op (EOp α))
    (hs : ∀ x ∈ s, F.Dom x.2.2)
    (ho : ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a)) :
    eUpdate Γ (eRemapSt F.f s) (eRemapOp F.f o)
      = eRemapSt F.f (eUpdate Γ s o) := by
  obtain ⟨t, rr, op⟩ := o
  cases op with
  | del x =>
      show (eRemapSt F.f s).filter (fun r => decide (r.1 ≠ x))
          = eRemapSt F.f (s.filter (fun r => decide (r.1 ≠ x)))
      rw [eRemapSt, eRemapSt, List.filter_map]
      exact congrArg _ (List.filter_congr (fun a _ => rfl))
  | ins e π a =>
      have hmint : F.MintAt π (t - a) := ho e π a rfl
      show eUpdate Γ (eRemapSt F.f s) (t, rr, .ins e (F.f π) a)
          = eRemapSt F.f (eUpdate Γ s (t, rr, .ins e π a))
      simp only [eUpdate]
      rw [eIds_eRemapSt]
      by_cases hmem : t ∈ eIds s
      · rw [if_pos hmem, if_pos hmem]
      · rw [if_neg hmem, if_neg hmem]
        rw [show ((t, e, F.f π ++ Γ.enc (t - a)) : ERec α)
              = eRemapRec F.f (t, e, π ++ Γ.enc (t - a)) from by
            show _ = ((t, e, F.f (π ++ Γ.enc (t - a))) : ERec α)
            rw [F.ext hmint]]
        exact eInsert_remap F.f _ s (fun x hx =>
          F.ord' (hs x hx) (Or.inr ⟨π, t - a, hmint, rfl⟩))

/-! ## §4  T1 and T2 — fold congruence and reads identical -/

/-- **T1, the re-coding theorem (cut-parametric fold congruence).** From any
cut state whose record coordinates are at hand, folding the translated
continuation over the translated state is the translation of the
untranslated fold. -/
theorem eRecode_applySeq {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ) :
    ∀ (τ : List (Op (EOp α))) (s : EState α),
    (∀ x ∈ s, F.Dom x.2.2) →
    (∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a)) →
    applySeq (E Γ α).toCRDTSig (eRemapSt F.f s) (τ.map (eRemapOp F.f))
      = eRemapSt F.f (applySeq (E Γ α).toCRDTSig s τ)
  | [], _, _, _ => rfl
  | o :: τ', s, hs, hτ => by
      show applySeq (E Γ α).toCRDTSig
          (eUpdate Γ (eRemapSt F.f s) (eRemapOp F.f o)) (τ'.map (eRemapOp F.f))
        = eRemapSt F.f (applySeq (E Γ α).toCRDTSig (eUpdate Γ s o) τ')
      rw [eUpdate_remap F s o hs
        (fun e π a h => hτ o List.mem_cons_self e π a h)]
      refine eRecode_applySeq F τ' (eUpdate Γ s o) ?_
        (fun o' ho' => hτ o' (List.mem_cons_of_mem _ ho'))
      intro x hx
      obtain ⟨t, rr, op⟩ := o
      cases op with
      | del y => exact hs x (List.mem_of_mem_filter hx)
      | ins e π a =>
          rcases mem_eUpdate_cases hx with h | h
          · exact hs x h
          · rw [h]
            exact Or.inr ⟨π, t - a,
              hτ _ List.mem_cons_self e π a rfl, rfl⟩

/-- T1 from the empty cut (pure congruence form). -/
theorem eRecode_fold {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    (τ : List (Op (EOp α)))
    (hτ : ∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a)) :
    eFold Γ (τ.map (eRemapOp F.f)) = eRemapSt F.f (eFold Γ τ) :=
  eRecode_applySeq F τ [] (fun _ hx => absurd hx (List.not_mem_nil)) hτ

/-- **T2, reads identical**: the element sequence of the translated fold is
the untranslated one, verbatim. The left-hand side re-sorts by the *new*
keys, so this is exactly the statement that the new keys induce the old
order: compression is invisible to every observer. -/
theorem eRecode_reads_identical {Γ : OrderedPrefixCode}
    (F : StablePrefixMap Γ) (s : EState α) (τ : List (Op (EOp α)))
    (hs : ∀ x ∈ s, F.Dom x.2.2)
    (hτ : ∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a)) :
    (E Γ α).query
        (applySeq (E Γ α).toCRDTSig (eRemapSt F.f s) (τ.map (eRemapOp F.f))) ()
      = (E Γ α).query (applySeq (E Γ α).toCRDTSig s τ) () := by
  rw [eRecode_applySeq F τ s hs hτ]
  exact eRemapSt_query Γ F.f _

/-- **Whole-history extension commuting collapses the re-map.**
If H3 is demanded at *every* positive mint (as the whole-history fold
congruence would require), the re-map is a constant-prefix prepend on every
chain coordinate, and compacts nothing. This is why T1 is stated from the
cut: re-coding is an epoch operation on states, not a history rewrite. -/
theorem eRecode_ext_global_collapse {Γ : OrderedPrefixCode}
    (f : List Bool → List Bool)
    (hext : ∀ (π : List Bool) (d : ℕ), 1 ≤ d →
      f (π ++ Γ.enc d) = f π ++ Γ.enc d) :
    ∀ ch : List ℕ, PosChain ch → f (coordOf Γ ch) = f [] ++ coordOf Γ ch := by
  intro ch
  induction ch using List.reverseRecOn with
  | nil =>
      intro _
      simp [coordOf]
  | append_singleton ds d ih =>
      intro hpos
      have hd : 1 ≤ d := hpos d (List.mem_append_right _ List.mem_cons_self)
      have hcd : coordOf Γ [d] = Γ.enc d := by simp [coordOf]
      rw [coordOf_append, hcd, hext _ _ hd,
        ih (fun x hx => hpos x (List.mem_append_left _ hx)),
        List.append_assoc]

/-! ## §5  T3 — transport along the re-map -/

/-- Canonicity transports: two enumerations of one event set have equal
translated folds. -/
theorem eRecode_fold_canon {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    {τ τ' : List (Op (EOp α))}
    (hwf : EWf Γ τ) (hwf' : EWf Γ τ') (hmem : ∀ o, o ∈ τ ↔ o ∈ τ')
    (hτ : ∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a)) :
    eFold Γ (τ.map (eRemapOp F.f)) = eFold Γ (τ'.map (eRemapOp F.f)) := by
  rw [eRecode_fold F τ hτ,
    eRecode_fold F τ' (fun o ho => hτ o ((hmem o).mpr ho)),
    e_fold_canon Γ hwf hwf' hmem]

/-- Sortedness transports: the re-map of a canonical (strictly descending)
state is canonical, so the re-coded document needs no re-sort. -/
theorem eRecode_sorted {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    {s : EState α} (hs : ESorted s) (hdom : ∀ x ∈ s, F.Dom x.2.2) :
    ESorted (eRemapSt F.f s) := by
  rw [eRemapSt, ESorted, List.pairwise_map]
  refine hs.imp_of_mem ?_
  intro a b ha hb hab
  show keyLt (key (F.f b.2.2)) (key (F.f a.2.2)) = true
  rw [F.ord' (hdom b hb) (hdom a ha)]
  exact hab

/-- **Version-level sortedness transport.** At an honestly delivered,
honestly reachable configuration, every registered version is the canonical
sorted document, and its re-map is again canonical: the at-rest re-coding
of any version never needs a re-sort. -/
theorem eRecode_version_sorted {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    {C : Configuration (E Γ α)} (hReach : EReach Γ C) (hHon : EHonest Γ C)
    {v : Version} {s : EState α} {Ev : Set (Op (EOp α))}
    (hv : C.ver v = some (s, Ev))
    (hdom : ∀ x ∈ s, F.Dom x.2.2) :
    ESorted s ∧ ESorted (eRemapSt F.f s) := by
  have hGood := e_goodConfig3 hReach
  obtain ⟨ρ, hperm, hresp, happ⟩ := hGood.canonical v s Ev hv
  have hin : ∀ a ∈ Ev, a ∈ (Configuration.core C).events := by
    intro a ha
    rw [core_events]
    exact hGood.ver_events_sub v s Ev hv a ha
  have hcl : ∀ a b, (Configuration.core C).vis a b →
      ¬ (E Γ α).toCRDTSig.commutes a b → b ∈ Ev → a ∈ Ev :=
    fun a b hvis _ hb => hGood.ver_causal v s Ev hv a b hvis hb
  have hwf := e_wf_of_enum (eHonest_core hHon) hin hcl hperm hresp
  have hsorted : ESorted s := by
    rw [← happ]
    exact e_fold_sorted Γ hwf
  exact ⟨hsorted, eRecode_sorted F hsorted hdom⟩

/-- **T3, the capstone's per-version statement transports.** At every
honestly reachable configuration, every version has a delivery-respecting
witness enumeration; the re-coded version state is the re-map of that
witness's fold, and it reads exactly as the witness fold reads. The
transport is at the level of states and witnesses: the re-coded history is
NOT itself an `EHonest` configuration (compacted coordinates are no longer
birth-chain telescopes), so re-invoking the capstone natively in the new
epoch is deferred with the protocol half (`whiteboard/embed-recoding-note.md` §6). -/
theorem eRecode_ra_transport {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    {C : Configuration (E Γ α)} (hReach : EReach Γ C) :
    ∀ (v : Version) (s : EState α) (Ev : Set (Op (EOp α))),
      C.ver v = some (s, Ev) →
      ∃ π : List (Op (EOp α)),
        listPermOf π Ev ∧
        respects π (Sal.Emulation.lo (Configuration.core C)) ∧
        eRemapSt F.f s = eRemapSt F.f (eFold Γ π) ∧
        (E Γ α).query (eRemapSt F.f s) () = (E Γ α).query (eFold Γ π) () := by
  intro v s Ev hv
  obtain ⟨π, hperm, hresp, happ⟩ := embed_ra_linearizable3 hReach v s Ev hv
  have hfold : eFold Γ π = s := happ
  refine ⟨π, hperm, hresp, by rw [hfold], ?_⟩
  rw [hfold]
  exact eRemapSt_query Γ F.f s

/-! ## §6  Axiom audit -/

#print axioms StablePrefixMap.injOn
#print axioms eRecode_applySeq
#print axioms eRecode_fold
#print axioms eRecode_reads_identical
#print axioms eRecode_ext_global_collapse
#print axioms eRecode_fold_canon
#print axioms eRecode_sorted
#print axioms eRecode_version_sorted
#print axioms eRecode_ra_transport

/-! ## §7  SPOT — the worked compaction, hand-derived (PASS + FAIL shaped)

The `whiteboard/embed-recoding-note.md` worked example, unary code. History: `a`(t1)←root, `b`(t2)←a,
`c`(t3)←b, then delete `a` and `b`. Cut state: one live record
`(3, 12, 101010)`, two dead codewords baked in. Compaction `gc`: the live
coordinate collapses to `10`; extensions keep their tails. Beyond the cut:
`d`(t6)←c (delta 3) and `e`(t7)←root (delta 7). Hand-derived display order
both sides: `e, c, d` (payloads `[14, 12, 13]`); hand-summed coordinate
weight 24 bits original vs 16 re-coded. FAIL companion: `badMap` sends the
live coordinate to `enc 8` (injective, extension-commuting, NOT
order-preserving: it jumps over `e`'s mint `enc 7`) and the read flips to
`c, d, e` — order preservation (H2) is the load-bearing hypothesis. -/

namespace SPOT

def c3 : List Bool := [true, false, true, false, true, false]

/-- `a`(1)←root, `b`(2)←a, `c`(3)←b, del a, del b. Payloads 10, 11, 12. -/
def preOps : List (Op (EOp ℕ)) :=
  [ (1, 0, .ins 10 [] 0)
  , (2, 0, .ins 11 [true, false] 1)
  , (3, 0, .ins 12 [true, false, true, false] 2)
  , (4, 0, .del 1)
  , (5, 0, .del 2) ]

def sCut : EState ℕ := eFold unaryCode preOps

/-- The cut state, hand-derived: one survivor carrying its dead ancestors'
codewords (6 bits for a chain of live depth 1). -/
theorem cut_state : sCut = [(3, 12, c3)] := by native_decide

/-- The worked compaction: collapse the dead chain under the one live
record; keep tails verbatim (a stable-prefix map with `ρ(101010) = 10`). -/
def gc (c : List Bool) : List Bool :=
  if c3.isPrefixOf c then true :: false :: c.drop 6 else c

/-- Beyond the cut: `d`(6)←c (delta 3), `e`(7)←root (delta 7). -/
def postOps : List (Op (EOp ℕ)) :=
  [ (6, 0, .ins 13 c3 3)
  , (7, 0, .ins 14 [] 0) ]

def finalO : EState ℕ := applySeq (E unaryCode).toCRDTSig sCut postOps

def finalR : EState ℕ :=
  applySeq (E unaryCode).toCRDTSig (eRemapSt gc sCut)
    (postOps.map (eRemapOp gc))

def coordWeight (s : EState ℕ) : ℕ := (s.map (fun r => r.2.2.length)).sum

/-- The concrete read, definitionally the instance's query (bridge below);
stated separately so the SPOT equations are `Decidable`. -/
def readE (s : EState ℕ) : List ℕ := s.map (fun r => r.2.1)

theorem readE_is_query (s : EState ℕ) : readE s = (E unaryCode).query s () :=
  rfl

/-- PASS: re-coding at rest leaves the read verbatim (and it is `[12]`,
not empty: the survivor is displayed). -/
theorem cut_read_identical :
    readE (eRemapSt gc sCut) = [12] ∧ readE sCut = [12] := by native_decide

/-- PASS: T1 concretely — the translated continuation fold IS the re-map of
the untranslated one, record for record. -/
theorem t1_concrete : finalR = eRemapSt gc finalO := by native_decide

/-- PASS: reads identical, pinned to the hand-derived order `e, c, d`. -/
theorem reads_identical :
    readE finalR = [14, 12, 13] ∧ readE finalO = [14, 12, 13] := by
  native_decide

/-- PASS: the compaction genuinely compresses: 16 < 24, hand-summed
(`c`: 6→2, `d`: 10→6, `e`: 8→8). -/
theorem size_reduced :
    coordWeight finalR = 16 ∧ coordWeight finalO = 24 := by native_decide

/-- FAIL companion's re-map: `c`'s coordinate goes to `enc 8 = 1^8 0`,
which jumps over `e`'s mint `enc 7`. Injective and extension-commuting
(H1, H3 hold); order-breaking (H2 fails). -/
def badMap (c : List Bool) : List Bool :=
  if c3.isPrefixOf c then
    true :: true :: true :: true :: true :: true :: true :: true :: false ::
      c.drop 6
  else c

def finalB : EState ℕ :=
  applySeq (E unaryCode).toCRDTSig (eRemapSt badMap sCut)
    (postOps.map (eRemapOp badMap))

/-- FAIL companion: the non-order-preserving re-map flips the read to
`c, d, e` — compression is NOT invisible without H2. -/
theorem bad_map_changes_read :
    readE finalB = [12, 13, 14] ∧ readE finalB ≠ readE finalO := by
  native_decide

/-- The hypothesis bundle is inhabited by the worked compaction: `Rest` is
the cut record's coordinate, `MintAt` the two beyond-cut mints; H3 and H2
discharge by computation on the nine at-hand pairs. -/
def gcF : StablePrefixMap unaryCode where
  f := gc
  Rest := fun c => c = c3
  MintAt := fun π d => (π = c3 ∧ d = 3) ∨ (π = [] ∧ d = 7)
  ext := by
    intro π d hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  ord := by
    intro c c' h h'
    rcases h with rfl | ⟨π, d, hm, rfl⟩
    · rcases h' with rfl | ⟨π', d', hm', rfl⟩
      · decide
      · rcases hm' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases h' with rfl | ⟨π', d', hm', rfl⟩
      · rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      · rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hm' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- T1 fired through the theorem, not recomputed: `eRecode_applySeq`'s
hypotheses discharge on the concrete instance (`gcF`), reproducing
`t1_concrete`. -/
theorem t1_via_theorem : finalR = eRemapSt gc finalO := by
  refine eRecode_applySeq (F := gcF) postOps sCut ?_ ?_
  · intro x hx
    rw [cut_state] at hx
    have hx' := List.mem_singleton.mp hx
    subst hx'
    exact Or.inl rfl
  · intro o ho e π a heq
    rcases List.mem_cons.mp ho with rfl | ho'
    · injection heq with he hπ ha
      subst he; subst hπ; subst ha
      exact Or.inl ⟨rfl, by decide⟩
    · rcases List.mem_cons.mp ho' with rfl | ho''
      · injection heq with he hπ ha
        subst he; subst hπ; subst ha
        exact Or.inr ⟨rfl, by decide⟩
      · exact absurd ho'' (List.not_mem_nil)

#print axioms cut_state
#print axioms t1_concrete
#print axioms reads_identical
#print axioms size_reduced
#print axioms bad_map_changes_read
#print axioms t1_via_theorem

end SPOT

end Sal.ConditionedMRDTs
