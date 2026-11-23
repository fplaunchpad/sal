import LeanProofs.Implementations.OptionalRegister.Definition
import Artifact.MRDTs.Paper1.SplitPolicy

/-!
# The optional register: the algebra and the policy

Merge algebra for the cells, the conflict policy `rc`, and the counting
lemmas the replay argument needs.
-/

set_option maxHeartbeats 4000000

namespace LeanProofs.Implementations.OptionalRegisterFlagAlgebra
open Artifact.MRDTs
open Artifact.MRDTs.Paper1
open Artifact.MRDTs.Foundation LeanProofs.Implementations.OptionalRegisterFlag

/-- Binary comparison join used only to prove the source ternary equations.
At equal counters false dominates, because a reset observes that same epoch. -/
def joinCell (a b : Cell) : Cell :=
  (max a.1 b.1, if a.1 < b.1 then b.2 else if b.1 < a.1 then a.2 else a.2 && b.2)
def join (a b : State) : State := fun r => joinCell (a r) (b r)

theorem source_join_of_min (l a b : Cell) (h : l.1 = min a.1 b.1) :
    mergeCell l a b = joinCell a b := by
  obtain ⟨lc,lf⟩ := l
  obtain ⟨ac,af⟩ := a
  obtain ⟨bc,bf⟩ := b
  cases af <;> cases bf
  all_goals simp only [mergeCell,mergeFlag,joinCell,Bool.and_true,Bool.and_false,
    Bool.true_and,Bool.false_and,Bool.not_true,Bool.not_false,ite_true,ite_false]
  all_goals (try split_ifs) <;> simp_all <;> omega

theorem joinCell_comm (a b : Cell) : joinCell a b = joinCell b a := by
  obtain ⟨ac,af⟩ := a
  obtain ⟨bc,bf⟩ := b
  cases af <;> cases bf
  all_goals simp only [joinCell,Bool.and_true,Bool.and_false,Bool.true_and,Bool.false_and]
  all_goals split_ifs <;> simp_all <;> omega

theorem joinCell_idem (a : Cell) : joinCell a a = a := by
  cases a
  simp [joinCell]

theorem joinCell_assoc (a b c : Cell) : joinCell (joinCell a b) c = joinCell a (joinCell b c) := by
  obtain ⟨ac,af⟩ := a
  obtain ⟨bc,bf⟩ := b
  obtain ⟨cc,cf⟩ := c
  cases af <;> cases bf <;> cases cf
  all_goals simp only [joinCell]
  all_goals split_ifs <;> simp_all <;> omega

theorem source_comm (l a b : State) : merge l a b = merge l b a := by
  funext r
  unfold merge mergeCell mergeFlag
  cases (a r).2 <;> cases (b r).2 <;> simp <;> omega

theorem source_as_join (l a b : State) (h : ∀ r, (l r).1 = min (a r).1 (b r).1) :
    merge l a b = join a b := by
  funext r
  exact source_join_of_min (l r) (a r) (b r) (h r)

theorem join_comm (a b : State) : join a b = join b a := by
  funext r; exact joinCell_comm (a r) (b r)
theorem join_assoc (a b c : State) : join (join a b) c = join a (join b c) := by
  funext r; exact joinCell_assoc (a r) (b r) (c r)
theorem join_idem (a : State) : join a a = a := by
  funext r; exact joinCell_idem (a r)

theorem join_local (t b c : State) : join (join t c) b = join (join t b) c := by
  rw [join_assoc,join_comm c b,← join_assoc]

theorem join_shared (t₁ t₂ c : State) :
    join (join t₁ c) (join t₂ c) = join (join t₁ t₂) c := by
  rw [join_assoc,← join_assoc c t₂ c,join_comm c t₂,join_assoc t₂ c c,join_idem,
    ← join_assoc]

end LeanProofs.Implementations.OptionalRegisterFlagAlgebra

namespace LeanProofs.Implementations.OptionalRegister
open Artifact.MRDTs
open Artifact.MRDTs.Paper1
open Artifact.MRDTs.Foundation

@[simp] theorem mergePayload_self (p : Payload) : mergePayload p p p = p := by
  cases p
  simp only [mergePayload,ite_true]
  congr 1
  omega

theorem mergePayload_comm (l a b : Payload) : mergePayload l a b = mergePayload l b a := by
  rcases a with ⟨ta,av⟩; rcases b with ⟨tb,bv⟩
  simp only [mergePayload]
  split_ifs <;> simp_all <;> omega

theorem sourceCell_comm (l a b : Cell) : mergeCell l a b = mergeCell l b a := by
  rcases l with ⟨⟨lc,lf⟩,lp⟩
  rcases a with ⟨⟨ac,af⟩,ap⟩
  rcases b with ⟨⟨bc,bf⟩,bp⟩
  cases af <;> cases bf
  all_goals simp only [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,Bool.and_true,Bool.and_false,
    Bool.true_and,Bool.false_and,Bool.not_false,Bool.not_true,ite_true,ite_false]
  all_goals (try split_ifs) <;> simp_all [mergePayload_comm] <;> omega

theorem source_comm (l a b : State) : merge l a b = merge l b a := by
  apply State.ext
  · simp [merge,Finset.union_comm]
  · intro r; exact sourceCell_comm _ _ _

/-- Averaging equal timestamps is not associative on arbitrary payloads.
The source branch needs timestamp/payload coherence; replacing it by max
would hide this obligation rather than certify the supplied algorithm. -/
theorem averaging_obstruction :
    mergePayload (0,0) (mergePayload (0,0) (7,0) (7,0)) (7,2) = (7,1) ∧
    mergePayload (0,0) (7,0) (mergePayload (0,0) (7,0) (7,2)) = (7,0) ∧
    mergePayload (0,0) (mergePayload (0,0) (7,0) (7,0)) (7,2) ≠
      mergePayload (0,0) (7,0) (mergePayload (0,0) (7,0) (7,2)) := by decide

/-- Same timestamp and same payload reduce the averaging branch to identity. -/
theorem coherent_tie (l a b : Payload) (same : a = b) : mergePayload l a b = a := by
  subst b
  rcases a with ⟨ta,av⟩
  simp only [mergePayload,ite_true]
  congr 1
  omega

/-- Reachable cells are ordered by Set count, with a reset dominating its
observed count. Payloads do not participate in this logical flag order. -/
abbrev CellKey := Lex (Int × Lex (Bool × Lex Payload))

def cellKey (c : Cell) : CellKey := toLex (c.1.1,toLex (!c.1.2,toLex c.2))
def keyCell (k : CellKey) : Cell :=
  (((ofLex k).1,!(ofLex (ofLex k).2).1),(ofLex (ofLex (ofLex k).2).2))

@[simp] theorem keyCell_cellKey (c : Cell) : keyCell (cellKey c) = c := by
  rcases c with ⟨⟨count,flag⟩,payload⟩
  cases flag <;> rfl
@[simp] theorem cellKey_keyCell (k : CellKey) : cellKey (keyCell k) = k := by
  rcases k with ⟨count,flag,payload⟩
  cases flag <;> rfl

def joinCell (a b : Cell) : Cell := keyCell (max (cellKey a) (cellKey b))

theorem joinCell_comm (a b : Cell) : joinCell a b = joinCell b a := by
  simp [joinCell,max_comm]
theorem joinCell_assoc (a b c : Cell) :
    joinCell (joinCell a b) c = joinCell a (joinCell b c) := by
  simp [joinCell,max_assoc]
@[simp] theorem joinCell_idem (a : Cell) : joinCell a a = a := by simp [joinCell]

/-- Explicit payload coherence needed to identify the source merge with the
comparison join. Strict count growth means the active Set timestamp grows;
equal active counts identify the same source Set and payload. -/
def CoherentCells (a b : Cell) : Prop :=
  (a.1.2 = true → b.1.2 = true →
    (a.1.1 < b.1.1 → a.2.1 < b.2.1) ∧
    (b.1.1 < a.1.1 → b.2.1 < a.2.1) ∧
    (a.1.1 = b.1.1 → a.2 = b.2)) ∧
  (a.1.2 = false → a.2 = (0,0)) ∧ (b.1.2 = false → b.2 = (0,0))

private theorem joinCell_of_lt (a b : Cell) (lt : a.1.1 < b.1.1) : joinCell a b = b := by
  have keylt : cellKey a < cellKey b := Prod.Lex.toLex_lt_toLex.mpr (Or.inl lt)
  simp [joinCell,max_eq_right (le_of_lt keylt)]

private theorem joinCell_reset_tie (a b : Cell) (same : a.1.1 = b.1.1)
    (af : a.1.2 = true) (bf : b.1.2 = false) : joinCell a b = b := by
  have keylt : cellKey a < cellKey b := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    right; refine ⟨same,?_⟩
    apply Prod.Lex.toLex_lt_toLex.mpr
    left
    simp [af,bf]
  simp [joinCell,max_eq_right (le_of_lt keylt)]

/-- Source averaging is retained. The comparison join is valid only under
these explicit count-prefix, timestamp-growth, and zero-inactive facts. -/
theorem sourceCell_as_join (l a b : Cell) (count : l.1.1 = min a.1.1 b.1.1)
    (coherent : CoherentCells a b) : mergeCell l a b = joinCell a b := by
  rcases coherent with ⟨payload,az,bz⟩
  rcases lt_trichotomy a.1.1 b.1.1 with lt | same | lt
  · rw [joinCell_of_lt a b lt]
    have lc : l.1.1 = a.1.1 := by omega
    rcases a with ⟨⟨ac,af⟩,⟨ta,av⟩⟩
    rcases b with ⟨⟨bc,bf⟩,⟨tb,bv⟩⟩
    cases af <;> cases bf
    all_goals simp only [Prod.fst,Prod.snd] at *
    all_goals simp only [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag]
    all_goals simp_all [mergePayload] <;> (try omega)
    have ts := payload.1
    simp [lt,lc,ne_of_lt ts,not_lt_of_ge (le_of_lt ts)]
  · rcases a with ⟨⟨ac,af⟩,ap⟩
    rcases b with ⟨⟨bc,bf⟩,bp⟩
    simp only [Prod.fst,Prod.snd] at *
    subst bc
    have lc : l.1.1 = ac := by omega
    cases af <;> cases bf
    · have apz := az rfl; have bpz := bz rfl
      subst ap; subst bp
      simp [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,lc,joinCell]
    · rw [joinCell_comm,joinCell_reset_tie ((ac,true),bp) ((ac,false),ap) rfl rfl rfl]
      have apz := az rfl; subst ap
      simp [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,lc]
    · rw [joinCell_reset_tie ((ac,true),ap) ((ac,false),bp) rfl rfl rfl]
      have bpz := bz rfl; subst bp
      simp [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,lc]
    · have eq := (payload rfl rfl).2.2 rfl
      subst bp
      simp [mergeCell,LeanProofs.Implementations.OptionalRegisterFlag.mergeFlag,lc,joinCell,mergePayload]
      rcases ap with ⟨ta,av⟩
      simp [keyCell,cellKey]
      omega
  · rw [sourceCell_comm,joinCell_comm]
    apply sourceCell_as_join l b a
    · simpa [min_comm] using count
    · exact ⟨fun hb ha => ⟨(payload ha hb).2.1,(payload ha hb).1,
        fun eq => ((payload ha hb).2.2 eq.symm).symm⟩,bz,az⟩
termination_by if a.1.1 < b.1.1 then 0 else 1
decreasing_by simp only [lt,if_pos]; split_ifs <;> omega

#print axioms source_comm
#print axioms joinCell_assoc
#print axioms averaging_obstruction
end LeanProofs.Implementations.OptionalRegister

namespace LeanProofs.Implementations.OptionalRegister
open Artifact.MRDTs
open Artifact.MRDTs.Paper1
open Artifact.MRDTs.Foundation

/-- Neem's operation policy: concurrent Unset precedes Set. -/
def policy : OperationPolicy Action where
  before a b := a = .unset ∧ ∃ v, b = .set v

theorem sets_commute (ta ra va tb rb vb : Nat) (different : ra ≠ rb) :
    D.toUpdateSig.commutes (ta,ra,.set va) (tb,rb,.set vb) := by
  intro s
  apply State.ext
  · simp [D,update,Op.op,Op.rep,Finset.insert_comm]
  · intro r
    simp only [D,update,Op.op,Op.rep,Op.time]
    split_ifs <;> simp_all <;> omega

theorem unsets_commute (a b : Op Action) (ha : a.op = .unset) (hb : b.op = .unset) :
    D.toUpdateSig.commutes a b := by
  intro s
  apply State.ext
  · simp [D,update,ha,hb]
  · intro r; simp [D,update,ha,hb]

theorem set_unset_noncomm (ta ra va tb rb : Nat) :
    ¬ D.toUpdateSig.commutes (ta,ra,.set va) (tb,rb,.unset) := by
  intro comm
  have h := congrArg (fun s => (s.cells ra).1.2) (comm initial)
  simp [D,update,Op.op,Op.rep,Op.time] at h

theorem guarded_exact (a b : Op Action) (different : a.rep ≠ b.rep) :
    ¬ D.toUpdateSig.commutes a b ↔ policy.before a.op b.op ∨ policy.before b.op a.op := by
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  change ra ≠ rb at different
  cases oa <;> cases ob
  · simp [policy,Op.op,sets_commute _ _ _ _ _ _ different]
  · rename_i v
    simpa [policy,Op.op] using set_unset_noncomm ta ra v tb rb
  · rename_i v
    have nc : ¬ D.toUpdateSig.commutes (ta,ra,.unset) (tb,rb,.set v) := by
      intro h
      exact set_unset_noncomm tb rb v ta ra (fun s => (h s).symm)
    simp [policy,Op.op,nc]
  · simp [policy,Op.op,unsets_commute (ta,ra,.unset) (tb,rb,.unset) rfl rfl]

/-- Swapping an Unset with a Set changes only the Set's row payload/bit;
all counters and the partial-map domain agree. -/
def DifferAt (r : Nat) (s t : State) : Prop :=
  s.domain = t.domain ∧ (∀ k, (s.cells k).1.1 = (t.cells k).1.1) ∧
    ∀ k, k ≠ r → s.cells k = t.cells k

theorem differ_update {s t : State} {r : Nat} (h : DifferAt r s t) (e : Op Action) :
    DifferAt r (update s e) (update t e) := by
  rcases h with ⟨domain,counts,rows⟩
  refine ⟨?_,?_,?_⟩
  · cases hop : e.op <;> simp [update,hop,domain]
  · intro k; cases hop : e.op <;> simp only [update,hop]
    · split_ifs <;> simp [counts]
    · exact counts k
  · intro k ne
    cases hop : e.op
    · simp [update,hop,counts,rows k ne]
    · simp [update,hop,counts]

theorem differ_fold {s t : State} {r : Nat} (h : DifferAt r s t) (ops : List (Op Action)) :
    DifferAt r (applySeq D.toUpdateSig s ops) (applySeq D.toUpdateSig t ops) := by
  induction ops generalizing s t with
  | nil => exact h
  | cons e rest ih => exact ih (differ_update h e)

theorem resolve_differ {s t : State} {r : Nat} (h : DifferAt r s t) (e : Op Action)
    (resolves : e.op = .unset ∨ (∃ v, e.op = .set v) ∧ e.rep = r) :
    update s e = update t e := by
  rcases h with ⟨domain,counts,rows⟩
  apply State.ext
  · cases hop : e.op <;> simp [update,hop,domain]
  · intro k
    rcases resolves with reset | ⟨⟨v,set⟩,own⟩
    · simp [update,reset,counts]
    · simp only [update,set]
      split_ifs with same
      · simp [counts]
      · exact rows k (by simpa [own] using same)

theorem conditional (s : State) (a b c : Op Action) (between : List (Op Action))
    (edge : policy.before a.op b.op) (conflict : ¬ D.toUpdateSig.commutes b c) :
    D.update (applySeq D.toUpdateSig (D.update (D.update s b) a) between) c =
      D.update (applySeq D.toUpdateSig (D.update (D.update s a) b) between) c := by
  obtain ⟨reset,v,set⟩ := edge
  have diff : DifferAt b.rep (update (update s b) a) (update (update s a) b) := by
    refine ⟨?_,?_,?_⟩
    · simp [update,reset,set]
    · intro k; simp only [update,reset,set]
      split_ifs <;> rfl
    · intro k ne; simp [update,reset,set,ne]
  have resolves : c.op = .unset ∨ (∃ v, c.op = .set v) ∧ c.rep = b.rep := by
    cases hc : c.op with
    | unset => exact Or.inl rfl
    | set w =>
      right
      refine ⟨⟨w,rfl⟩,?_⟩
      by_contra different
      rcases b with ⟨tb,rb,ob⟩
      rcases c with ⟨tc,rc,oc⟩
      simp only [Op.op] at set hc
      subst ob; subst oc
      exact conflict (sets_commute tb rb v tc rc w (by simpa [Op.rep,ne_comm] using different))
  exact resolve_differ (differ_fold diff between) c resolves

def laws : GuardedReplay.Laws D.toUpdateSig policy where
  noncomm_exact a b _ different := guarded_exact a b different
  no_chain a b c _ _ := by
    rintro ⟨⟨_,v,hb⟩,⟨hb',_,_⟩⟩
    simp [hb] at hb'
  conditional_commutation s a b c between _ _ _ := conditional s a b c between

def splitLaws : SplitPolicy.Laws D.toUpdateSig policy := SplitPolicy.Laws.ofGuarded laws

#print axioms splitLaws
end LeanProofs.Implementations.OptionalRegister

namespace LeanProofs.Implementations.OptionalRegister.Counts
open Artifact.MRDTs
open Artifact.MRDTs.Paper1
open Artifact.MRDTs.Foundation ConcreteMRDT

def winningAt (r : Nat) (e : Op Action) : Prop := e.rep = r ∧ e.op.isSet = true
instance (r : Nat) (e : Op Action) : Decidable (winningAt r e) := inferInstanceAs
  (Decidable (e.rep = r ∧ e.op.isSet = true))
def winners (F : Finset (Op Action)) (r : Nat) : Finset (Op Action) :=
  F.filter (winningAt r)
def count (F : Finset (Op Action)) (r : Nat) : Int := (winners F r).card

/-- Logical single-writer histories make winning prefixes comparable at each
row. This is execution evidence, not an assumed source merge equation. -/
theorem prefixes_comparable (C : ReplayContext D.toUpdateSig) (E₁ E₂ : Set (Op Action))
    (F G : Finset (Op Action)) (hF : (↑F : Set (Op Action)) = E₁)
    (hG : (↑G : Set (Op Action)) = E₂)
    (sup₁ : Supported C E₁) (sup₂ : Supported C E₂)
    (closed₁ : ∀ a b, C.vis a b → b ∈ E₁ → a ∈ E₁)
    (closed₂ : ∀ a b, C.vis a b → b ∈ E₂ → a ∈ E₂) (r : Nat) :
    winners F r ⊆ winners G r ∨ winners G r ⊆ winners F r := by
  classical
  by_cases sub : winners F r ⊆ winners G r
  · exact Or.inl sub
  · right
    obtain ⟨a,ha,absent⟩ := Finset.not_subset.mp sub
    obtain ⟨haF,ownA⟩ := Finset.mem_filter.mp ha
    have absentG : a ∉ G := by
      intro hg
      exact absent (Finset.mem_filter.mpr ⟨hg,ownA⟩)
    intro b hb
    obtain ⟨hbG,ownB⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨?_,ownB⟩
    have haE : a ∈ E₁ := by rw [← hF]; exact haF
    have hbE : b ∈ E₂ := by rw [← hG]; exact hbG
    have ne : a ≠ b := by intro eq; subst b; exact absentG hbG
    obtain ⟨ra,Sa,hLa,haS⟩ := sup₁ a haE
    obtain ⟨rb,Sb,hLb,hbS⟩ := sup₂ b hbE
    rcases C.vis_total_same_replica hLa haS hLb hbS ne (ownA.1.trans ownB.1.symm) with ab | ba
    · have ag := closed₂ a b ab hbE
      rw [← hG] at ag
      exact (absentG ag).elim
    · have bf := closed₁ b a ba haE
      rw [← hF] at bf
      exact bf

theorem winners_inter (F G : Finset (Op Action)) (r : Nat) :
    winners (F ∩ G) r = winners F r ∩ winners G r := by
  ext e; simp [winners]; tauto

theorem count_min_of_comparable (F G : Finset (Op Action)) (r : Nat)
    (h : winners F r ⊆ winners G r ∨ winners G r ⊆ winners F r) :
    count (F ∩ G) r = min (count F r) (count G r) := by
  unfold count
  rw [winners_inter]
  rcases h with sub | sub
  · rw [Finset.inter_eq_left.mpr sub]
    have bound := Finset.card_le_card sub
    omega
  · rw [Finset.inter_eq_right.mpr sub]
    have bound := Finset.card_le_card sub
    omega

theorem count_mono (F G : Finset (Op Action)) (sub : F ⊆ G) (r : Nat) :
    count F r ≤ count G r := by
  unfold count
  have sub' : winners F r ⊆ winners G r := Finset.filter_subset_filter _ sub
  exact_mod_cast Finset.card_le_card sub'

end LeanProofs.Implementations.OptionalRegister.Counts
