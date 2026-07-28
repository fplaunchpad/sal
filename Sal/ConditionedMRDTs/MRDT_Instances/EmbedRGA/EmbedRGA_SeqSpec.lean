import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA
import Sal.ConditionedMRDTs.MRDT_Instances.SeqSpec_Flat

/-!
# Sequential-spec soundness — tier 3: the embedded-chain RGA

The embed RGA, single-replica, against the naive sequential text buffer:
insert splices immediately after its anchor, delete removes. The theorem
is the strongest form the campaign admits — the canonical sorted state
*is* the spec buffer, record for record — and its heart is the
**adjacency lemma** (`chainBefore_snoc_iff`): a fresh insert's chain
`ca ++ [δ]` sits directly after its anchor's chain `ca` in the display
order, because δ (the fresh timestamp gap) exceeds every delta any
existing chain hangs off `ca` — a fact that costs nothing beyond
sum-telescoping: an extension's first delta is bounded by its own id
minus the anchor's, and every existing id is below the fresh stamp.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode PosChain coordOf coordOf_inj
  coordOf_append key_inj keyLt keyLe key keyLt_total keyLt_irrefl
  keyLt_asymm chainBefore chainBefore_total display_iff_chainBefore)

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §A  The naive sequential buffer -/

/-- The user-visible projection of a record: `(id, element)`. -/
def eProj (r : ERec α) : ℕ × α := (r.1, r.2.1)

/-- Splice `p` immediately after the entry with id `a`. (No-op when `a`
is absent — unreachable under `eSeqOK`, where anchors are live.) -/
def eInsAfter (a : ℕ) (p : ℕ × α) : List (ℕ × α) → List (ℕ × α)
  | [] => []
  | q :: qs => if q.1 = a then q :: p :: qs else q :: eInsAfter a p qs

/-- The naive sequential buffer program: front/after-anchor splice,
filter delete. -/
def eSpecStep (S : List (ℕ × α)) (o : Op (EOp α)) : List (ℕ × α) :=
  match o.2.2 with
  | .ins el _ a =>
      if a = 0 then (o.1, el) :: S else eInsAfter a (o.1, el) S
  | .del x => S.filter (fun p => decide (p.1 ≠ x))

def eSpecFold (ρ : List (Op (EOp α))) : List (ℕ × α) :=
  ρ.foldl eSpecStep []

theorem eSpecFold_snoc (ρ : List (Op (EOp α))) (o : Op (EOp α)) :
    eSpecFold (ρ ++ [o]) = eSpecStep (eSpecFold ρ) o := by
  unfold eSpecFold
  rw [List.foldl_append]
  rfl

/-! ## §B  Sequential honesty -/

/-- Sequential honesty for embed histories: stamps exceed all previous
insert stamps (Lamport), and every op is applicable at the current fold
(the §8 issuer-side guard, specialized to a linear history). -/
def eSeqOK (Γ : OrderedPrefixCode) (ρ : List (Op (EOp α))) : Prop :=
  ∀ (σ : List (Op (EOp α))) (o : Op (EOp α)) (τ : List (Op (EOp α))),
    ρ = σ ++ o :: τ →
    (∀ x ∈ eInsIds σ, x < o.1) ∧ eApplicable o (eFold Γ σ)

theorem eSeqOK_prefix {Γ : OrderedPrefixCode} {ρ : List (Op (EOp α))}
    {o : Op (EOp α)} (h : eSeqOK Γ (ρ ++ [o])) : eSeqOK Γ ρ := by
  intro σ o' τ heq
  exact h σ o' (τ ++ [o]) (by rw [heq]; simp)

/-! ## §C  Chains for every insert of the history -/

/-- Every insert of a sequentially honest history mints a positive
chain's coordinate whose deltas telescope to its (positive) id. -/
theorem e_seq_chains {Γ : OrderedPrefixCode} {ρ : List (Op (EOp α))}
    (hOK : eSeqOK Γ ρ) :
    ∀ o ∈ ρ, eIsIns o = true →
      ∃ ch, PosChain ch ∧ ch.sum = o.1 ∧ 1 ≤ o.1 ∧
        eCoord Γ o = coordOf Γ ch := by
  induction ρ using List.reverseRecOn with
  | nil =>
      intro o ho
      simp at ho
  | append_singleton ρ o' ih =>
      intro o ho hins
      rcases List.mem_append.mp ho with h | h
      · exact ih (eSeqOK_prefix hOK) o h hins
      · simp at h
        subst h
        obtain ⟨ts, r, op⟩ := o
        cases op with
        | del x => simp [eIsIns] at hins
        | ins el π a =>
            have happ := (hOK ρ (ts, r, .ins el π a) [] (by simp)).2
            simp only [eApplicable] at happ
            obtain ⟨hat, hcase⟩ := happ
            have hat' : a < ts := hat
            rcases hcase with ⟨rfl, rfl⟩ | ⟨el', hmem⟩
            · refine ⟨[ts], ?_, by simp, by show (1:ℕ) ≤ ts; omega, ?_⟩
              · intro d hd
                simp at hd
                omega
              · simp [eCoord, coordOf]
            · obtain ⟨aop, haρ, hai, hae⟩ :=
                e_fold_rec_sub Γ ρ (a, el', π) hmem
              have hπ : π = eCoord Γ aop :=
                congrArg (fun q : ERec α => q.2.2) hae
              have ha1 : aop.1 = a := (congrArg Prod.fst hae).symm
              obtain ⟨cha, hpos, hsum, -, hcoord⟩ :=
                ih (eSeqOK_prefix hOK) aop haρ hai
              refine ⟨cha ++ [ts - a], ?_, ?_,
                by show (1:ℕ) ≤ ts; omega, ?_⟩
              · intro d hd
                rcases List.mem_append.mp hd with h' | h'
                · exact hpos d h'
                · simp at h'
                  omega
              · show (cha ++ [ts - a]).sum = ts
                rw [List.sum_append, hsum, ha1]
                simp
                omega
              · show π ++ Γ.enc (ts - a) = _
                rw [coordOf_append, hπ, hcoord]
                simp [coordOf]

/-! ## §C′  Well-formedness from sequential honesty -/

theorem eInsIds_lt_of_seqOK {Γ : OrderedPrefixCode} {ρ : List (Op (EOp α))}
    {o : Op (EOp α)} (hOK : eSeqOK Γ (ρ ++ [o])) :
    ∀ x ∈ eInsIds ρ, x < o.1 :=
  (hOK ρ o [] (by simp)).1

/-- Sequential honesty gives well-formedness: fresh monotone stamps give
`ins_nodup` and `del_late`; chains + unique decodability give
`keys_inj`. -/
theorem eWf_of_seqOK {Γ : OrderedPrefixCode} {ρ : List (Op (EOp α))}
    (hOK : eSeqOK Γ ρ) : EWf Γ ρ := by
  constructor
  case ins_nodup =>
      induction ρ using List.reverseRecOn with
      | nil => simp [eInsIds]
      | append_singleton ρ o ih =>
          rw [eInsIds_append, List.nodup_append]
          refine ⟨ih (eSeqOK_prefix hOK), ?_, ?_⟩
          · cases o' : o.2.2 <;> simp [eInsIds, eIsIns, o']
          · intro a ha b hb
            have hlt := eInsIds_lt_of_seqOK hOK a ha
            have hb1 : b = o.1 := by
              simp only [eInsIds, List.mem_map, List.mem_filter] at hb
              obtain ⟨o', ⟨ho', -⟩, rfl⟩ := hb
              simp at ho'
              rw [ho']
            omega
  case del_late =>
      intro σ o τ heq hins hdel
      obtain ⟨d, hd, hddel⟩ := mem_eDels.mp hdel
      obtain ⟨σ₁, σ₂, rfl⟩ := List.append_of_mem hd
      have happ := (hOK σ₁ d (σ₂ ++ o :: τ)
        (by rw [heq]; simp)).2
      obtain ⟨ts, rr, dop2⟩ := d
      cases dop2 with
      | ins el π a => simp at hddel
      | del x =>
          simp only [eApplicable] at happ
          simp only at hddel
          injection hddel with hx
          subst hx
          obtain ⟨rec, hrec, hrx⟩ := List.mem_map.mp happ
          obtain ⟨iop, hiρ, hii, hie⟩ := e_fold_rec_sub Γ σ₁ rec hrec
          have hix : iop.1 = o.1 → False := by
            intro hcontra
            have hmem : o.1 ∈ eInsIds (σ₁ ++ (ts, rr, EOp.del o.1) :: σ₂) := by
              rw [show σ₁ ++ (ts, rr, EOp.del o.1) :: σ₂ =
                  (σ₁ ++ [(ts, rr, EOp.del o.1)]) ++ σ₂ from by simp,
                eInsIds_append, eInsIds_append]
              exact List.mem_append_left _ (List.mem_append_left _
                (mem_eInsIds.mpr ⟨iop, hiρ, hii, hcontra⟩))
            have := (hOK (σ₁ ++ (ts, rr, EOp.del o.1) :: σ₂) o τ
              (by simp [heq])).1 o.1 hmem
            omega
          apply hix
          rw [hie] at hrx
          exact hrx
  case keys_inj =>
      intro o₁ h₁ o₂ h₂ hi₁ hi₂ hne hkey
      obtain ⟨ch₁, hp₁, hs₁, -, hc₁⟩ := e_seq_chains hOK o₁ h₁ hi₁
      obtain ⟨ch₂, hp₂, hs₂, -, hc₂⟩ := e_seq_chains hOK o₂ h₂ hi₂
      rw [hc₁, hc₂] at hkey
      have hco := key_inj hkey
      have hch := coordOf_inj Γ hp₁ hp₂ hco
      rw [← hs₁, ← hs₂, hch] at hne
      exact hne rfl

/-! ## §D  Record and id uniqueness in the fold -/

theorem e_fold_recs_nodup {Γ : OrderedPrefixCode} {ρ : List (Op (EOp α))}
    (hwf : EWf Γ ρ) : (eFold Γ ρ).Nodup := by
  have hs := e_fold_sorted Γ hwf
  refine hs.imp ?_
  intro r r' hk
  intro heq
  rw [heq, keyLt_irrefl] at hk
  exact Bool.noConfusion hk

theorem e_fold_fst_inj {Γ : OrderedPrefixCode} {ρ : List (Op (EOp α))}
    (hwf : EWf Γ ρ) :
    ∀ r ∈ eFold Γ ρ, ∀ r' ∈ eFold Γ ρ, r.1 = r'.1 → r = r' := by
  intro r hr r' hr' hfst
  obtain ⟨o, ho, hi, hrec⟩ := e_fold_rec_sub Γ ρ r hr
  obtain ⟨o', ho', hi', hrec'⟩ := e_fold_rec_sub Γ ρ r' hr'
  have h1 : o.1 = o'.1 := by
    have e1 : r.1 = o.1 := by rw [hrec]; rfl
    have e2 : r'.1 = o'.1 := by rw [hrec']; rfl
    rw [← e1, ← e2, hfst]
  have : o = o' := by
    have hinj := List.inj_on_of_nodup_map
      (f := Prod.fst) (l := ρ.filter (fun o => eIsIns o)) hwf.ins_nodup
    exact hinj (List.mem_filter.mpr ⟨ho, hi⟩)
      (List.mem_filter.mpr ⟨ho', hi'⟩) h1
  rw [hrec, hrec', this]

/-! ## §E  The adjacency core -/

/-- Inversion of `chainBefore` (local copy — the canonical one lives in
the read-equivalence file, which this file cannot import without pulling
in the tombstoned RGA model). -/
theorem chainBefore_inv' {u v : List ℕ} (h : chainBefore u v) :
    (∃ ext, ext ≠ [] ∧ v = u ++ ext) ∨
    (∃ q d e c1 c2, e < d ∧ u = q ++ d :: c1 ∧ v = q ++ e :: c2) := by
  cases h with
  | ancestor ch ext hne => exact Or.inl ⟨ext, hne, rfl⟩
  | newer q d e c1 c2 hlt => exact Or.inr ⟨q, d, e, c1, c2, hlt, rfl, rfl⟩

/-- **The adjacency lemma.** Appending a delta `δ` that strictly exceeds
every delta hung off `ca` by other chains puts `ca ++ [δ]` directly
after `ca` in the display order: no other chain's verdict changes.  -/
theorem chainBefore_snoc_iff {ca cr : List ℕ} {δ : ℕ}
    (hne : cr ≠ ca)
    (hmax : ∀ d rest, cr = ca ++ d :: rest → d < δ) :
    chainBefore cr (ca ++ [δ]) ↔ chainBefore cr ca := by
  constructor
  · intro h
    rcases chainBefore_inv' h with ⟨ext, hxne, hext⟩ |
      ⟨q, d, e, c1, c2, hlt, hu, hv⟩
    · -- cr is a proper prefix of ca ++ [δ]; strip the snoc
      rcases List.eq_nil_or_concat ext with rfl | ⟨ext', lst, rfl⟩
      · exact absurd rfl hxne
      · simp only [List.concat_eq_append, ← List.append_assoc] at hext
        obtain ⟨hca, -⟩ := List.append_inj' hext rfl
        rcases List.eq_nil_or_concat ext' with rfl | ⟨e₂, l₂, rfl⟩
        · rw [List.append_nil] at hca
          exact absurd hca.symm hne
        · rw [hca]
          exact chainBefore.ancestor _ _ (by simp)
    · -- first difference: inside ca, or exactly at the snoc
      rcases List.eq_nil_or_concat c2 with rfl | ⟨c2', lst, rfl⟩
      · -- diff at the snoc position: q = ca, e = δ — refuted by hmax
        have h2 : q ++ [e] = ca ++ [δ] := by simpa using hv.symm
        obtain ⟨rfl, he⟩ := List.append_inj' h2 rfl
        simp at he
        subst he
        exact absurd (hmax d c1 hu) (by omega)
      · -- diff inside ca
        simp only [List.concat_eq_append] at hv
        have h2 : (q ++ e :: c2') ++ [lst] = ca ++ [δ] := by
          rw [List.append_assoc]
          exact hv.symm
        obtain ⟨hca, -⟩ := List.append_inj' h2 rfl
        rw [hu, ← hca]
        exact chainBefore.newer q d e c1 c2' hlt
  · intro h
    rcases chainBefore_inv' h with ⟨ext, hxne, hext⟩ |
      ⟨q, d, e, c1, c2, hlt, hu, hv⟩
    · rw [hext, List.append_assoc]
      exact chainBefore.ancestor _ _ (by simp)
    · rw [hu, hv, List.append_assoc]
      exact chainBefore.newer q d e c1 (c2 ++ [δ]) hlt

/-! ## §F  Placement: sorted insert = splice after the anchor -/

/-- When the newcomer's key beats every element, `eInsert` prepends. -/
theorem eInsert_all_lt {nr : ERec α} : ∀ {s : EState α},
    (∀ y ∈ s, keyLt (key y.2.2) (key nr.2.2) = true) →
    eInsert nr s = nr :: s
  | [], _ => rfl
  | x :: xs, h => by
      unfold eInsert
      rw [if_pos (h x List.mem_cons_self)]

/-- **Placement.** On a sorted state containing the anchor, if the
newcomer's key sits exactly between the anchor's and everything after it
(the `hiff` hypothesis — discharged by the adjacency lemma), then the
sorted insert IS the splice-after-anchor, under projection. -/
theorem eInsert_map_insAfter {a : ℕ} {nr : ERec α} :
    ∀ {s : EState α} {ar : ERec α}, ESorted s → ar ∈ s → ar.1 = a →
    (∀ r ∈ s, ∀ r' ∈ s, r.1 = r'.1 → r = r') →
    (∀ r ∈ s, key r.2.2 ≠ key nr.2.2) →
    (∀ r ∈ s, (keyLt (key nr.2.2) (key r.2.2) = true ↔
      (r = ar ∨ keyLt (key ar.2.2) (key r.2.2) = true))) →
    (eInsert nr s).map eProj = eInsAfter a (eProj nr) (s.map eProj) := by
  intro s
  induction s with
  | nil =>
      intro ar _ har
      exact absurd har (by simp)
  | cons x xs ih =>
      intro ar hsort har hara hinj hkeyne hiff
      by_cases hx : keyLt (key x.2.2) (key nr.2.2) = true
      · -- the newcomer would beat the head — impossible with the anchor
        -- present: the head dominates the anchor, hence the newcomer
        exfalso
        have hnx : ¬ (keyLt (key nr.2.2) (key x.2.2) = true) := by
          rw [keyLt_asymm hx]
          exact fun h => Bool.noConfusion h
        have hnor : ¬ (x = ar ∨ keyLt (key ar.2.2) (key x.2.2) = true) :=
          fun h => hnx ((hiff x List.mem_cons_self).mpr h)
        rcases List.mem_cons.mp har with heq | harx
        · exact hnor (Or.inl heq.symm)
        · exact hnor (Or.inr ((List.pairwise_cons.mp hsort).1 ar harx))
      · have hstep : eInsert nr (x :: xs) = x :: eInsert nr xs := by
          show (if keyLt (key x.2.2) (key nr.2.2) = true then nr :: x :: xs
            else x :: eInsert nr xs) = x :: eInsert nr xs
          rw [if_neg hx]
        rw [hstep]
        have hxk : keyLt (key nr.2.2) (key x.2.2) = true := by
          rcases keyLt_total (hkeyne x List.mem_cons_self) with h | h
          · exact absurd h hx
          · exact h
        rcases (hiff x List.mem_cons_self).mp hxk with heq | hax
        · -- the head IS the anchor: everything after it loses to the
          -- newcomer, so the tail insert prepends
          have hall : ∀ y ∈ xs, keyLt (key y.2.2) (key nr.2.2) = true := by
            intro y hy
            have hyx := (List.pairwise_cons.mp hsort).1 y hy
            have hyne : y ≠ x := by
              rintro rfl
              rw [keyLt_irrefl] at hyx
              exact Bool.noConfusion hyx
            have hrfalse :
                ¬ (y = ar ∨ keyLt (key ar.2.2) (key y.2.2) = true) := by
              rintro (rfl | hcontra)
              · exact hyne heq.symm
              · rw [← heq, keyLt_asymm hyx] at hcontra
                exact Bool.noConfusion hcontra
            have hnn : ¬ (keyLt (key nr.2.2) (key y.2.2) = true) :=
              fun h => hrfalse ((hiff y (List.mem_cons_of_mem _ hy)).mp h)
            rcases keyLt_total
              (hkeyne y (List.mem_cons_of_mem _ hy)) with h | h
            · exact h
            · exact absurd h hnn
          rw [eInsert_all_lt hall, List.map_cons]
          show eProj x :: eProj nr :: xs.map eProj =
            if (eProj x).1 = a then eProj x :: eProj nr :: xs.map eProj
            else eProj x :: eInsAfter a (eProj nr) (xs.map eProj)
          rw [if_pos (show (eProj x).1 = a from by
            show x.1 = a
            rw [heq, hara])]
        · -- the head is above the anchor: recurse
          have hxa : x.1 ≠ a := by
            intro hcontra
            have hxar : x = ar :=
              hinj x List.mem_cons_self ar har (by rw [hcontra, hara])
            rw [hxar, keyLt_irrefl] at hax
            exact Bool.noConfusion hax
          have harx : ar ∈ xs := by
            rcases List.mem_cons.mp har with heq2 | h
            · exact absurd (show x.1 = a from by rw [← heq2]; exact hara) hxa
            · exact h
          rw [List.map_cons, List.map_cons]
          show eProj x :: (eInsert nr xs).map eProj =
            if (eProj x).1 = a then
              eProj x :: eProj nr :: xs.map eProj
            else eProj x :: eInsAfter a (eProj nr) (xs.map eProj)
          rw [if_neg (show ¬ (eProj x).1 = a from hxa)]
          rw [ih (List.pairwise_cons.mp hsort).2 harx hara
            (fun r hr r' hr' => hinj r (List.mem_cons_of_mem _ hr)
              r' (List.mem_cons_of_mem _ hr'))
            (fun r hr => hkeyne r (List.mem_cons_of_mem _ hr))
            (fun r hr => hiff r (List.mem_cons_of_mem _ hr))]

/-! ## §G  Deletion commutes with projection -/

theorem map_eProj_filter (s : EState α) (x : ℕ) :
    (s.filter (fun r => decide (r.1 ≠ x))).map eProj =
      (s.map eProj).filter (fun p => decide (p.1 ≠ x)) := by
  induction s with
  | nil => rfl
  | cons r rs ih =>
      simp only [ne_eq, decide_not] at ih
      by_cases h : r.1 = x
      · simp [List.filter_cons, h, eProj, ih]
      · simp [List.filter_cons, h, eProj, ih]

/-! ## §H  The main theorem -/

/-- Chain package for a live record. -/
theorem e_fold_chain {Γ : OrderedPrefixCode} {ρ : List (Op (EOp α))}
    (hOK : eSeqOK Γ ρ) {rec : ERec α} (hrec : rec ∈ eFold Γ ρ) :
    ∃ ch, PosChain ch ∧ ch.sum = rec.1 ∧ 1 ≤ rec.1 ∧
      rec.2.2 = coordOf Γ ch := by
  obtain ⟨iop, hiρ, hii, hie⟩ := e_fold_rec_sub Γ ρ rec hrec
  obtain ⟨ch, h1, h2, h3, h4⟩ := e_seq_chains hOK iop hiρ hii
  have e1 : rec.1 = iop.1 := by rw [hie]; rfl
  have e2 : rec.2.2 = eCoord Γ iop := by rw [hie]; rfl
  exact ⟨ch, h1, by rw [e1]; exact h2, by rw [e1]; exact h3,
    by rw [e2]; exact h4⟩

/-- Live ids sit below a fresh op's stamp. -/
theorem e_fold_id_lt {Γ : OrderedPrefixCode} {ρ : List (Op (EOp α))}
    {o : Op (EOp α)} (hOK : eSeqOK Γ (ρ ++ [o])) {rec : ERec α}
    (hrec : rec ∈ eFold Γ ρ) : rec.1 < o.1 := by
  obtain ⟨iop, hiρ, hii, hie⟩ := e_fold_rec_sub Γ ρ rec hrec
  have h1 := eInsIds_lt_of_seqOK hOK iop.1
    (mem_eInsIds.mpr ⟨iop, hiρ, hii, rfl⟩)
  have e1 : rec.1 = iop.1 := by rw [hie]; rfl
  omega

/-- **The embedded-chain RGA, sequentially = the naive text buffer.**
Under the datatype's own sequential discipline the canonical state IS
the spec buffer, record for record: insert splices immediately after
its anchor (the adjacency lemma), delete removes. -/
theorem embed_seq_sound {Γ : OrderedPrefixCode} {ρ : List (Op (EOp α))}
    (hOK : eSeqOK Γ ρ) :
    (eFold Γ ρ).map eProj = eSpecFold ρ := by
  induction ρ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ρ o ih =>
      have hOK' := eSeqOK_prefix hOK
      have IH := ih hOK'
      have hwf' := eWf_of_seqOK hOK'
      rw [eFold_snoc, eSpecFold_snoc]
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | del x =>
          show ((eFold Γ ρ).filter (fun r => decide (r.1 ≠ x))).map eProj
            = _
          rw [map_eProj_filter, IH]
          rfl
      | ins el π a =>
          have happ := (hOK ρ (ts, r, .ins el π a) [] (by simp)).2
          simp only [eApplicable] at happ
          obtain ⟨hat, hcase⟩ := happ
          have hat' : a < ts := hat
          have hfresh : (ts, r, EOp.ins el π a).1 ∉ eIds (eFold Γ ρ) := by
            intro hmem
            obtain ⟨rec, hrec, hr1⟩ := List.mem_map.mp hmem
            have h1 : rec.1 < ts := e_fold_id_lt hOK hrec
            have h2 : rec.1 = ts := hr1
            omega
          show (eUpdate Γ (eFold Γ ρ) (ts, r, EOp.ins el π a)).map eProj
            = _
          simp only [eUpdate]
          rw [if_neg hfresh]
          rcases hcase with ⟨rfl, rfl⟩ | ⟨el', hmem⟩
          · -- front insert: the fresh stamp beats every chain
            have hall : ∀ y ∈ eFold Γ ρ, keyLt (key y.2.2)
                (key (((ts : ℕ), el,
                  ([] : List Bool) ++ Γ.enc (ts - 0)) : ERec α).2.2)
                = true := by
              intro y hy
              obtain ⟨chy, hpy, hsy, hy1, hcy⟩ := e_fold_chain hOK' hy
              have hylt : y.1 < ts := e_fold_id_lt hOK hy
              have hnew : ((((ts : ℕ), el,
                  ([] : List Bool) ++ Γ.enc (ts - 0)) : ERec α)).2.2
                  = coordOf Γ [ts] := by
                simp [coordOf]
              rw [hnew, hcy]
              cases chy with
              | nil =>
                  exfalso
                  simp at hsy
                  omega
              | cons d rest =>
                  have hd : d < ts := by
                    have hle : d ≤ (d :: rest).sum := by
                      simp [List.sum_cons]
                    omega
                  refine (display_iff_chainBefore Γ ?_ hpy ?_).mpr ?_
                  · intro z hz
                    simp at hz
                    omega
                  · intro hcontra
                    have := congrArg List.sum hcontra
                    simp [hsy] at this
                    omega
                  · exact chainBefore.newer [] ts d [] rest hd
            rw [eInsert_all_lt hall, List.map_cons, IH]
            simp [eProj, eSpecStep]
          · -- anchored insert: the adjacency lemma places it
            have hsort := e_fold_sorted Γ hwf'
            have hinj := e_fold_fst_inj hwf'
            obtain ⟨cha, hpa, hsa, ha1, hca⟩ := e_fold_chain hOK' hmem
            have ha0 : a ≠ 0 := by
              have h1 : (1:ℕ) ≤ a := ha1
              omega
            have hsum_a : cha.sum = a := hsa
            have hcoordnew : π ++ Γ.enc (ts - a)
                = coordOf Γ (cha ++ [ts - a]) := by
              rw [coordOf_append,
                show π = coordOf Γ cha from hca]
              simp [coordOf]
            have hpos_new : PosChain (cha ++ [ts - a]) := by
              intro d hd
              rcases List.mem_append.mp hd with h | h
              · exact hpa d h
              · simp at h
                omega
            have hcane : cha ≠ cha ++ [ts - a] := by
              intro hcontra
              have := congrArg List.length hcontra
              simp at this
            have hkeyne : ∀ rec ∈ eFold Γ ρ, key rec.2.2 ≠
                key (((ts : ℕ), el, π ++ Γ.enc (ts - a)) : ERec α).2.2 := by
              intro rec hrec hcontra
              obtain ⟨chr, hpr, hsr, -, hcr⟩ := e_fold_chain hOK' hrec
              have hrlt : rec.1 < ts := e_fold_id_lt hOK hrec
              rw [hcr, show (((ts : ℕ), el, π ++ Γ.enc (ts - a)) :
                  ERec α).2.2 = coordOf Γ (cha ++ [ts - a]) from hcoordnew]
                at hcontra
              have h1 := coordOf_inj Γ hpr hpos_new (key_inj hcontra)
              have h2 := congrArg List.sum h1
              rw [hsr, List.sum_append, hsum_a] at h2
              simp at h2
              omega
            have hiff : ∀ rec ∈ eFold Γ ρ,
                (keyLt (key (((ts : ℕ), el, π ++ Γ.enc (ts - a)) :
                    ERec α).2.2) (key rec.2.2) = true ↔
                  (rec = ((a : ℕ), el', π) ∨
                    keyLt (key (((a : ℕ), el', π) : ERec α).2.2)
                      (key rec.2.2) = true)) := by
              intro rec hrec
              by_cases hreq : rec = ((a : ℕ), el', π)
              · subst hreq
                constructor
                · intro _
                  exact Or.inl rfl
                · intro _
                  rw [show (((ts : ℕ), el, π ++ Γ.enc (ts - a)) :
                      ERec α).2.2 = coordOf Γ (cha ++ [ts - a])
                      from hcoordnew,
                    show (((a : ℕ), el', π) : ERec α).2.2 = coordOf Γ cha
                      from hca]
                  exact (display_iff_chainBefore Γ hpa hpos_new
                    hcane).mpr
                    (chainBefore.ancestor cha [ts - a] (by simp))
              · obtain ⟨chr, hpr, hsr, hr1, hcr⟩ := e_fold_chain hOK' hrec
                have hrlt : rec.1 < ts := e_fold_id_lt hOK hrec
                have hra : rec.1 ≠ a := fun hcontra =>
                  hreq (hinj rec hrec ((a : ℕ), el', π) hmem hcontra)
                have hchne : chr ≠ cha := by
                  intro hcontra
                  apply hra
                  rw [← hsr, ← hsum_a, hcontra]
                have hchne2 : chr ≠ cha ++ [ts - a] := by
                  intro hcontra
                  have h2 := congrArg List.sum hcontra
                  rw [hsr, List.sum_append, hsum_a] at h2
                  simp at h2
                  omega
                have hmax : ∀ d rest, chr = cha ++ d :: rest →
                    d < ts - a := by
                  intro d rest hcontra
                  have h2 := congrArg List.sum hcontra
                  rw [hsr, List.sum_append, hsum_a, List.sum_cons] at h2
                  have h4 : a + d ≤ rec.1 := by
                    rw [h2]
                    omega
                  have h3 : a + d < ts := lt_of_le_of_lt h4 hrlt
                  exact Nat.lt_sub_of_add_lt
                    (by rw [Nat.add_comm]; exact h3)
                rw [show (((ts : ℕ), el, π ++ Γ.enc (ts - a)) :
                    ERec α).2.2 = coordOf Γ (cha ++ [ts - a])
                    from hcoordnew,
                  show (((a : ℕ), el', π) : ERec α).2.2 = coordOf Γ cha
                    from hca,
                  show rec.2.2 = coordOf Γ chr from hcr,
                  display_iff_chainBefore Γ hpr hpos_new hchne2,
                  or_iff_right hreq,
                  display_iff_chainBefore Γ hpr hpa hchne]
                exact chainBefore_snoc_iff hchne hmax
            rw [eInsert_map_insAfter hsort hmem rfl hinj hkeyne hiff, IH]
            simp [eProj, eSpecStep, ha0]

end Sal.ConditionedMRDTs
