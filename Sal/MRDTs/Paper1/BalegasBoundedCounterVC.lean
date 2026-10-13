import Sal.MRDTs.Instances.BalegasBoundedCounter
import Sal.MRDTs.Paper1.CertifiedClosedExecution

namespace Sal.MRDTs.Paper1.BalegasBoundedCounterVC
open Foundation ConcreteMRDT Instances.BalegasBoundedCounter

/-- Visibility records the cumulative single-writer prefix even though every
raw additive effect commutes. Empty conflict metadata would erase this fact. -/
def scheme (n : Nat) (K : Int) (C : ReplayContext (D n K).toUpdateSig) :
    MetadataDependencies C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

/-- Every field is owned by the issuing row. -/
def weightR (e : Op Action) (i j : Nat) : Nat :=
  if i = e.2.1 then match e.op with
  | .increment amount => if j = i then amount else 0
  | .decrement _ => 0
  | .transfer amount target => if j = target then amount else 0
  else 0

def weightU (e : Op Action) (i : Nat) : Nat :=
  if i = e.2.1 then match e.op with
  | .decrement amount => amount
  | _ => 0
  else 0

/-- Indexed finite sums are an independent characterization of cumulative
payloads; this definition assumes no merge correctness equation. -/
def representation (n : Nat) (K : Int) : Representation (D n K) := fun C E s =>
  Supported C E ∧ ∃ F : Finset (Op Action), (↑F : Set (Op Action)) = E ∧
    (∀ i j, s.R i j = ∑ e ∈ F, weightR e i j) ∧
    (∀ i, s.U i = ∑ e ∈ F, weightU e i)

/-- Max joins associate independently of the ancestor. -/
theorem local_equation (l B t b : State) (e : Op Action) :
    merge l (merge B t (update B e)) b =
      merge B (merge l t b) (update B e) := by
  apply state_ext <;> intros <;> simp only [merge]
  all_goals omega

theorem shared_equation (t₀ t₁ t₂ B : State) (e : Op Action) :
    merge (merge B t₀ (update B e)) (merge B t₁ (update B e))
      (merge B t₂ (update B e)) = merge B (merge t₀ t₁ t₂) (update B e) := by
  apply state_ext <;> intros <;> simp only [merge]
  all_goals omega

/-- A causal delta joins exactly when the issuer's cumulative row is current.
All other rows only need the actual causal-past domination fact. -/
theorem causal_equation (s B : State) (e : Op Action)
    (row : ∀ j, s.R e.2.1 j = B.R e.2.1 j)
    (used : s.U e.2.1 = B.U e.2.1)
    (lowerR : ∀ i j, B.R i j ≤ s.R i j)
    (lowerU : ∀ i, B.U i ≤ s.U i) :
    merge B s (update B e) = update s e := by
  obtain ⟨ts,r,a⟩ := e
  cases a <;> apply state_ext
  all_goals intros
  all_goals simp only [merge,update,Op.op,bump,bumpMatrix] at *
  all_goals (try split_ifs) <;> simp_all <;> omega

/-- The execution context supplies the single-writer fact. Metadata maximality
then ensures that every observed event by this issuer lies in its causal past. -/
theorem issuer_prefix (n : Nat) (K : Int)
    (C : ReplayContext (D n K).toUpdateSig) (U : Set (Op Action)) (e : Op Action)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x)
    (supported : Supported C U) (closed : (scheme n K C).Closed U) (mem : e ∈ U)
    (maximal : ∀ x ∈ U, x ≠ e → ¬ (scheme n K C).before e x) :
    ((scheme n K C).Past e \ {e}) ⊆ (U \ {e}) ∧
    ∀ x ∈ U \ {e}, x.2.1 = e.2.1 → x ∈ (scheme n K C).Past e \ {e} := by
  refine ⟨fun x hx => ⟨(scheme n K C).past_subset U e closed mem hx.1,hx.2⟩,?_⟩
  intro x hx same
  obtain ⟨rx,Sx,hLx,hxS⟩ := supported x hx.1
  obtain ⟨re,Se,hLe,heS⟩ := supported e mem
  have ne : x ≠ e := hx.2
  have comparison := C.vis_total_same_replica hLx hxS hLe heS ne same
  refine ⟨Or.inr (.single ?_),hx.2⟩
  rcases comparison with before | after
  · exact before
  · exact (maximal x hx.1 ne after).elim

private theorem sum_owned {F G : Finset (Op Action)} {r : Nat}
    (sub : G ⊆ F) (owned : ∀ x ∈ F, x.2.1 = r → x ∈ G)
    (w : Op Action → Nat) (zero : ∀ x, x.2.1 ≠ r → w x = 0) :
    (∑ x ∈ F, w x) = ∑ x ∈ G, w x := by
  classical
  symm
  apply Finset.sum_subset sub
  intro x hx absent
  exact zero x (fun same => absent (owned x hx same))

theorem causal_payload_facts (n : Nat) (K : Int)
    (C : ReplayContext (D n K).toUpdateSig) (U : Set (Op Action))
    (s B : State) (e : Op Action)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x)
    (supported : Supported C U) (closed : (scheme n K C).Closed U) (mem : e ∈ U)
    (maximal : ∀ x ∈ U, x ≠ e → ¬ (scheme n K C).before e x)
    (hs : representation n K C (U \ {e}) s)
    (hB : representation n K C ((scheme n K C).Past e \ {e}) B) :
    (∀ j, s.R e.2.1 j = B.R e.2.1 j) ∧ s.U e.2.1 = B.U e.2.1 ∧
    (∀ i j, B.R i j ≤ s.R i j) ∧ (∀ i, B.U i ≤ s.U i) := by
  classical
  obtain ⟨_,F,hF,sR,sU⟩ := hs
  obtain ⟨_,G,hG,bR,bU⟩ := hB
  obtain ⟨subset,owned⟩ := issuer_prefix n K C U e trans irrefl supported closed mem maximal
  have sub : G ⊆ F := by
    intro x hx
    have hx' : x ∈ (scheme n K C).Past e \ {e} := by rw [← hG]; exact hx
    have fx := subset hx'
    rw [← hF] at fx
    exact fx
  have own : ∀ x ∈ F, x.2.1 = e.2.1 → x ∈ G := by
    intro x hx same
    have hx' : x ∈ U \ {e} := by rw [← hF]; exact hx
    have gx := owned x hx' same
    rw [← hG] at gx
    exact gx
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    rw [sR,bR]
    apply sum_owned sub own
    intro x ne
    simp [weightR,Ne.symm ne]
  · rw [sU,bU]
    apply sum_owned sub own
    intro x ne
    simp [weightU,Ne.symm ne]
  · intro i j
    rw [bR,sR]
    exact Finset.sum_le_sum_of_subset sub
  · intro i
    rw [bU,sU]
    exact Finset.sum_le_sum_of_subset sub

/-- All five merge VCs for the published maximum merge. The only
non-universal equation uses same-issuer visibility totality from the execution
context and metadata closure, never an assumed final Join. -/
theorem fiveVC (n : Nat) (K : Int) :
    Raw.MergeVCs (commutingPolicy Action) (representation n K) (scheme n K) := by
  constructor
  · intro C E₁ E₂ l a b _ _ _ _ _ _ _
    exact merge_comm l a b
  · intros
    exact merge_initial _
  · intro C U s B e trans irrefl supported closed mem _ maximal hs hB _ _
    obtain ⟨row,used,lowerR,lowerU⟩ :=
      causal_payload_facts n K C U s B e trans irrefl supported closed mem maximal hs hB
    exact causal_equation s B e row used lowerR lowerU
  · intro C E₁ E₂ l B t b e _ _ _ _ _ _ _ _ _ _
    exact local_equation l B t b e
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _
    exact shared_equation t₀ t₁ t₂ B e

theorem unique (n : Nat) (K : Int) : Raw.Unique (representation n K) := by
  intro C E a b ha hb
  obtain ⟨_,F,hF,aR,aU⟩ := ha
  obtain ⟨_,G,hG,bR,bU⟩ := hb
  have eq : F = G := by
    apply Finset.coe_injective
    exact hF.trans hG.symm
  subst G
  apply state_ext
  · intro i j; rw [aR,bR]
  · intro i; rw [aU,bU]

theorem initial_rep (n : Nat) (K : Int) (C : ReplayContext (D n K).toUpdateSig) :
    representation n K C ∅ initial := by
  exact ⟨fun _ h => h.elim,∅,by simp,by simp [initial],by simp [initial]⟩

theorem finite_rep (n : Nat) (K : Int) (C : ReplayContext (D n K).toUpdateSig)
    (E : Set (Op Action)) (s : State) (h : representation n K C E s) :
    ∃ π, listPermOf π E := by
  classical
  obtain ⟨_,F,hF,_,_⟩ := h
  exact ⟨F.toList,F.nodup_toList,fun x => by simp [← hF]⟩

theorem represented (n : Nat) (K : Int) (C : ReplayContext (D n K).toUpdateSig)
    (E : Set (Op Action)) (π : List (Op Action)) (perm : listPermOf π E)
    (support : Supported C E) : ∃ s, representation n K C E s := by
  classical
  refine ⟨⟨fun i j => ∑ e ∈ π.toFinset, weightR e i j,
    fun i => ∑ e ∈ π.toFinset, weightU e i⟩,support,π.toFinset,?_,?_,?_⟩
  · ext x; simp [← perm.2 x]
  · intros; rfl
  · intros; rfl

theorem update_R (s : State) (e : Op Action) (i j : Nat) :
    (update s e).R i j = s.R i j + weightR e i j := by
  obtain ⟨ts,r,a⟩ := e
  cases a <;> simp only [update,Op.op,bumpMatrix,weightR]
  all_goals (try split_ifs) <;> simp_all <;> omega

theorem update_U (s : State) (e : Op Action) (i : Nat) :
    (update s e).U i = s.U i + weightU e i := by
  obtain ⟨ts,r,a⟩ := e
  cases a <;> simp only [update,Op.op,bump,weightU]
  all_goals (try split_ifs) <;> simp_all <;> omega

theorem insert_rep (n : Nat) (K : Int) (C : ReplayContext (D n K).toUpdateSig)
    (E : Set (Op Action)) (s : State) (e : Op Action)
    (h : representation n K C E s) (support : e ∈ C.events) (absent : e ∉ E) :
    representation n K C (insert e E) (update s e) := by
  classical
  obtain ⟨sup,F,hF,hR,hU⟩ := h
  have notin : e ∉ F := by rw [← hF] at absent; exact absent
  refine ⟨?_,insert e F,by simp [hF],?_,?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact support
    · exact sup x hx
  · intro i j
    rw [update_R,hR,Finset.sum_insert notin]
    omega
  · intro i
    rw [update_U,hU,Finset.sum_insert notin]
    omega

private theorem finite_maximal {β : Type} (R : β → β → Prop)
    (trans : Transitive R) (irr : ∀ x, ¬ R x x)
    (F : Finset β) (nonempty : F.Nonempty) :
    ∃ e ∈ F, ∀ x ∈ F, x ≠ e → ¬ R e x := by
  classical
  induction F using Finset.induction_on with
  | empty => simp at nonempty
  | @insert a F absent ih =>
    by_cases hn : F.Nonempty
    · obtain ⟨e,he,maximal⟩ := ih hn
      by_cases edge : R e a
      · refine ⟨a,by simp,?_⟩
        intro x hx ne forward
        have hxF : x ∈ F := (Finset.mem_insert.mp hx).resolve_left ne
        by_cases eq : x = e
        · subst x; exact irr e (trans edge forward)
        · exact maximal x hxF eq (trans edge forward)
      · refine ⟨e,Finset.mem_insert_of_mem he,?_⟩
        intro x hx ne forward
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact edge forward
        · exact maximal x hx ne forward
    · have empty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst F
      refine ⟨a,by simp,?_⟩
      intros x hx ne
      simp at hx
      exact (ne hx).elim

theorem replay_rep (n : Nat) (K : Int) (C : ReplayContext (D n K).toUpdateSig)
    (π : List (Op Action)) (nd : π.Nodup)
    (supported : ∀ e ∈ π, e ∈ C.events) :
    representation n K C (↑π.toFinset : Set (Op Action)) (applySeq (D n K).toUpdateSig initial π) := by
  classical
  induction π using List.reverseRecOn with
  | nil => simpa [applySeq] using initial_rep n K C
  | append_singleton π e ih =>
    obtain ⟨ndπ,_,disjoint⟩ := List.nodup_append.mp nd
    have absent : e ∉ π := fun h => disjoint e h e (by simp) rfl
    have pre := ih ndπ (fun x hx => supported x (by simp [hx]))
    rw [applySeq_append_single]
    have inserted := insert_rep n K C _ _ e pre (supported e (by simp))
      (by simpa using absent)
    simpa [List.toFinset_append] using inserted

theorem canonical (n : Nat) (K : Int) (C : ReplayContext (D n K).toUpdateSig)
    (E : Set (Op Action)) (s : State) (h : representation n K C E s) :
    Canonical (commutingPolicy Action) C E s := by
  obtain ⟨π,hp⟩ := finite_rep n K C E s h
  have eqset : (↑π.toFinset : Set (Op Action)) = E := by
    ext x; simp [← hp.2 x]
  have hr := replay_rep n K C π hp.1 (fun e he => h.1 e ((hp.2 e).mp he))
  rw [eqset] at hr
  refine ⟨π,hp,?_,unique n K C E _ _ hr h⟩
  exact hp.1.imp (fun {_ _} _ => CommutingPort.order_empty (all_comm n K) C E _ _)

theorem replaySupply (n : Nat) (K : Int) (C : ReplayContext (D n K).toUpdateSig)
    (trans : Transitive C.vis) (irr : ∀ x, ¬ C.vis x x) :
    Raw.ReplaySupply (commutingPolicy Action) (representation n K) (scheme n K) C := by
  classical
  refine ⟨represented n K C,?_⟩
  intro E s hs support nonempty closed
  obtain ⟨_,F,hF,_,_⟩ := hs
  have hn : F.Nonempty := by
    obtain ⟨e,he⟩ := nonempty
    rw [← hF] at he
    exact ⟨e,he⟩
  obtain ⟨e,he,maximal⟩ := finite_maximal C.vis trans irr F hn
  have member : e ∈ E := by rw [← hF]; exact he
  have metadataMax : ∀ x ∈ E, x ≠ e → ¬ (scheme n K C).before e x := by
    intro x hx ne
    rw [← hF] at hx
    exact maximal x hx ne
  obtain ⟨π,hp⟩ := finite_rep n K C E s ⟨support,F,hF,by assumption,by assumption⟩
  have pastSub := (scheme n K C).past_subset E e closed member
  obtain ⟨pre,hpre⟩ := enumeration_subset hp (show E \ {e} ⊆ E from Set.diff_subset)
  obtain ⟨past,hpast⟩ := enumeration_subset hp
    (show (scheme n K C).Past e \ {e} ⊆ E from fun _ h => pastSub h.1)
  obtain ⟨t,ht⟩ := represented n K C _ pre hpre (fun x hx => support x hx.1)
  obtain ⟨B,hB⟩ := represented n K C _ past hpast (fun x hx => support x (pastSub hx.1))
  refine ⟨⟨e,member,?_,metadataMax,t,B,ht,hB,?_,?_⟩⟩
  · intro x _ _; exact CommutingPort.order_empty (all_comm n K) C E e x
  · have eq : insert e ((scheme n K C).Past e \ {e}) = (scheme n K C).Past e := by
      ext x
      simp only [Set.mem_insert_iff,Set.mem_diff,Set.mem_singleton_iff]
      constructor
      · rintro (rfl | hx)
        · exact Or.inl rfl
        · exact hx.1
      · intro hx
        by_cases same : x = e
        · exact Or.inl same
        · exact Or.inr ⟨hx,same⟩
    rw [← eq]
    exact insert_rep n K C _ B e hB (support e member) (by simp)
  · have eq : insert e (E \ {e}) = E := by ext x; simp; tauto
    rw [← eq]
    exact insert_rep n K C _ t e ht (support e member) (by simp)

/-- Join of causally closed histories follows through the shared five-VC
metadata induction (`Raw.representationJoin_of_vcs` calls `Raw.join_at_sizes`). -/
theorem join (n : Nat) (K : Int) : RepresentationJoin (representation n K) := by
  exact Raw.representationJoin_of_vcs (fiveVC n K) (unique n K)
    (fun C _ _ _ => initial_rep n K C) (finite_rep n K)
    (fun C _ _ _ _ trans irr _ _ _ _ => replaySupply n K C trans irr)

theorem of_canonical (n : Nat) (K : Int)
    (C : ReplayContext (D n K).toUpdateSig) (E : Set (Op Action)) (s : State)
    (sup : Supported C E)
    (h : @IsCanonicalState (D n K).toUpdateSig (EventOrder.default _) C E s) :
    representation n K C E s := by
  classical
  obtain ⟨π,hp,_,hf⟩ := h
  change List (Op Action) at π
  have eqset : (↑π.toFinset : Set (Op Action)) = E := by
    ext x; simp [← hp.2 x]
  have hr := replay_rep n K C π hp.1 (fun e he => sup e ((hp.2 e).mp he))
  rw [eqset] at hr
  simpa only [D] using hf ▸ hr

/-- The source-faithful instance needs full causal closure, available on real
version histories. Weak conflict-only closure would lose cumulative prefixes. -/
theorem causalJoin (n : Nat) (K : Int) : CausalJoin (D n K) := by
  intro C E₁ E₂ l a b trans irr sup₁ sup₂ closed₁ closed₂ hl ha hb
  have joined := join n K C E₁ E₂ l a b (fun _ _ _ => trans) irr sup₁ sup₂ closed₁ closed₂
    (of_canonical n K C _ l (fun e he => sup₁ e he.1) hl)
    (of_canonical n K C _ a sup₁ ha) (of_canonical n K C _ b sup₂ hb)
  obtain ⟨π,hp,_,hf⟩ := canonical n K C _ _ joined
  refine ⟨π,hp,?_,hf⟩
  exact hp.1.imp (fun {_ _} _ => by
    simp [loOn,UpdateSig.replayBefore,UpdateSig.replayOrder,EventOrder.default,
      EventOrder.unconstrained])

theorem canonicalConfig (n : Nat) (K : Int) {I : Issuance (D n K)}
    {C : Configuration (D n K)}
    (reach : MintCertifiedReachV (D n K) (canonicalVirtualMergeBase (D n K)) I C) :
    CanonicalConfig C :=
  CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV
    (fun C _ => causalJoin n K C.replayContext) reach

theorem representedVersions (n : Nat) (K : Int) {I : Issuance (D n K)}
    {C : Configuration (D n K)}
    (reach : MintCertifiedReachV (D n K) (canonicalVirtualMergeBase (D n K)) I C)
    (v : Version) (s : State) (E : Set (Op Action)) (hv : C.ver v = some (s,E)) :
    representation n K C.replayContext E s := by
  have good := canonicalConfig n K reach
  exact of_canonical n K C.replayContext E s
    (good.version_events_supported v s E hv) (good.canonical v s E hv)

def replayConditions (n : Nat) (K : Int) (I : Issuance (D n K)) :
    VCReplayConditions (commutingPolicy Action) I where
  representation := representation n K
  scheme := scheme n K
  laws := GuardedReplay.ofUniform (restricted_of_all_commute (all_comm n K))
  vcs := fiveVC n K
  unique := unique n K
  initial := fun C _ _ _ => initial_rep n K C
  finite := finite_rep n K
  canonical := canonical n K
  supported := fun _ _ _ h => h.1
  replaySupply := fun C _ _ _ _ trans irr _ _ _ _ => replaySupply n K C trans irr
  representedVersions := fun C reach v s E hv => representedVersions n K reach v s E hv

#print axioms representedVersions
#print axioms replayConditions

#print axioms causalJoin

#print axioms join

#print axioms fiveVC

/-- The empty-metadata causal equation fails for two distinct increments by
one issuer. Its failure is not an invariant violation or a guard rejection. -/
theorem empty_metadata_causal_obstruction :
    let e : Op Action := (2,0,.increment 1)
    let s := update initial (1,0,.increment 1)
    merge initial s (update initial e) ≠ update s e ∧
    value 1 0 (update s e) = 2 ∧ value 1 0 (merge initial s (update initial e)) = 1 := by
  simp only
  refine ⟨?_,?_,?_⟩
  · intro h
    have hx := congrArg (fun s : State => s.R 0 0) h
    norm_num [merge,update,initial,Op.op,bumpMatrix] at hx
  · norm_num [value,update,initial,Op.op,bumpMatrix,Finset.sum_range_succ]
  · norm_num [value,merge,update,initial,Op.op,bumpMatrix,Finset.sum_range_succ]

end Sal.MRDTs.Paper1.BalegasBoundedCounterVC
