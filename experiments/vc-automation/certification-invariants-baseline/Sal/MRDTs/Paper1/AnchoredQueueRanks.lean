import Sal.MRDTs.Paper1.AnchoredQueueCausality
import Sal.MRDTs.Paper1.AnchoredQueueSchedule
import Sal.MRDTs.Paper1.AnchoredQueueSupport
import Sal.MRDTs.Paper1.AnchoredQueueCommutation

/-! First-deletion ranks for the delete-first FIFO schedule. Natural-number
minimality is independent of the implementation's query and coordinate order. -/
namespace Sal.MRDTs.Paper1.AnchoredQueue
open Foundation Instances.EmbedRGA Sal.EmbedRGA Classical

def HasDeletion (H : Set Event) (birth : Event) : Prop :=
  ∃ time, ∃ d ∈ H, d.op = .del birth.time ∧ d.time = time

noncomputable def firstDeletionTime (H : Set Event) (birth : Event) : Nat :=
  if h : HasDeletion H birth then Nat.find h else 0

theorem hasDeletion_iff (H : Set Event) (birth : Event) :
    HasDeletion H birth ↔ ∃ d ∈ H, d.op = .del birth.time := by
  constructor
  · rintro ⟨t,d,hd,shape,_⟩; exact ⟨d,hd,shape⟩
  · rintro ⟨d,hd,shape⟩; exact ⟨d.time,d,hd,shape,rfl⟩

theorem firstDeletion_spec {H : Set Event} {birth : Event} (h : HasDeletion H birth) :
    ∃ d ∈ H, d.op = .del birth.time ∧ d.time = firstDeletionTime H birth := by
  simpa only [firstDeletionTime,dif_pos h] using Nat.find_spec h

theorem firstDeletion_le {H : Set Event} {birth d : Event}
    (hd : d ∈ H) (shape : d.op = .del birth.time) :
    firstDeletionTime H birth ≤ d.time := by
  have available : HasDeletion H birth := ⟨d.time,d,hd,shape,rfl⟩
  rw [firstDeletionTime,dif_pos available]
  exact Nat.find_min' available ⟨d,hd,shape,rfl⟩

/-- Causal birth predecessors have strictly earlier first removals. This
is the scheduling use of the head-only deletion theorem. -/
theorem firstDeletion_causal {C : Configuration Q}
    (execution : CertifiedExecution Q issuance C) {H : Set Event}
    (closed : ∀ a b, C.vis a b → b ∈ H → a ∈ H)
    (support : H ⊆ C.events) {x y : Event}
    (hx : x ∈ C.events) (hy : y ∈ C.events)
    (ix : eIsIns x = true) (iy : eIsIns y = true)
    (causal : C.vis x y) (removed : HasDeletion H y) :
    firstDeletionTime H x < firstDeletionTime H y := by
  obtain ⟨d,hd,shape,time⟩ := firstDeletion_spec removed
  obtain ⟨d',hd',vis,shape'⟩ :=
    causal_birth_delete_predecessor execution hx hy (support hd) ix iy causal shape
  have member := closed d' d vis hd
  have minimum := firstDeletion_le member shape'
  have strict := C.causal_mono vis
  change d'.time < d.time at strict
  exact lt_of_le_of_lt minimum (strict.trans_eq time)

/-- Even ranks mark births; odd ranks mark their original dequeue events. -/
noncomputable def deadRank (H : Set Event) (e : Event) : Nat :=
  if eIsIns e then 2 * firstDeletionTime H e else 2 * e.time + 1

theorem deadRank_birth {H : Set Event} {e : Event} (ins : eIsIns e = true) :
    deadRank H e = 2 * firstDeletionTime H e := by simp [deadRank,ins]

theorem deadRank_delete {H : Set Event} {e : Event} {target : Nat}
    (shape : e.op = .del target) : deadRank H e = 2 * e.time + 1 := by
  rcases e with ⟨t,r,op⟩
  change op = .del target at shape
  subst op
  simp [deadRank,eIsIns]

#print axioms firstDeletion_causal

/-- Every endpoint dequeue has its original unique birth in the same causal
closed endpoint, independently of the proposed scheduler. -/
theorem deletion_birth_pair {C : Configuration Q}
    (execution : CertifiedExecution Q issuance C) {H : Set Event}
    (closed : ∀ a b, C.vis a b → b ∈ H → a ∈ H)
    (support : H ⊆ C.events) {d : Event} (hd : d ∈ H)
    (deletion : eIsIns d = false) :
    ∃ b ∈ H, eIsIns b = true ∧ d.op = .del b.time := by
  have honest := eHonest_core (eHonest_of_mint (execution_weaken execution).mintHonest)
  rcases d with ⟨t,r,op⟩
  cases op with
  | ins value pref anchor => simp [eIsIns] at deletion
  | del target =>
    obtain ⟨b,hb,vis,time,ins⟩ := honest.del_has_ins (t,r,.del target) (support hd) target rfl
    exact ⟨b,closed b _ vis hd,ins,by simp only [Op.op,Op.time]; rw [time]⟩

/-- Pairing retains the given deletion list exactly, including duplicates of
the same removed identity; it does not collapse original deletion events. -/
theorem exists_birthDelete_pairs (H : Set Event) (ds : List Event)
    (births : ∀ d ∈ ds, ∃ b ∈ H, eIsIns b = true ∧ d.op = .del b.time) :
    ∃ ps : List History.BirthDelete,
      ps.map History.BirthDelete.deletion = ds ∧ ∀ p ∈ ps, p.birth ∈ H := by
  induction ds with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons d ds ih =>
    obtain ⟨b,hb,ins,target⟩ := births d List.mem_cons_self
    obtain ⟨ps,map,support⟩ := ih (fun e he => births e (List.mem_cons_of_mem d he))
    let p : History.BirthDelete := ⟨b,d,ins,target⟩
    refine ⟨p::ps,by simp [p,map],?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hb
    · exact support q hq

def chronologicalDeletes (ops : List Event) : List Event :=
  (ops.filter (fun e => ! eIsIns e)).mergeSort (fun a b => decide (a.time ≤ b.time))

theorem chronologicalDeletes_mem (ops : List Event) (d : Event) :
    d ∈ chronologicalDeletes ops ↔ d ∈ ops ∧ eIsIns d = false := by
  rw [chronologicalDeletes,(List.mergeSort_perm _ _).mem_iff]
  simp

theorem chronologicalDeletes_order (ops : List Event) :
    (chronologicalDeletes ops).Pairwise (fun a b => a.time ≤ b.time) := by
  have sorted : ((ops.filter (fun e => !eIsIns e)).mergeSort
      (fun a b => decide (a.time ≤ b.time))).Pairwise
      (fun a b => decide (a.time ≤ b.time) = true) := by
    apply List.pairwise_mergeSort
    · intro a b c ab bc
      exact decide_eq_true (Nat.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc))
    · intro a b
      simp only [Bool.or_eq_true,decide_eq_true_eq]
      exact Nat.le_total _ _
  simpa only [chronologicalDeletes,decide_eq_true_eq] using sorted

theorem chronologicalDeletes_strict {C : Configuration Q} {H : Set Event}
    (support : H ⊆ C.events) {ops : List Event} (perm : listPermOf ops H) :
    (chronologicalDeletes ops).Pairwise (fun a b => a.time < b.time) := by
  have nd : (chronologicalDeletes ops).Nodup := by
    unfold chronologicalDeletes
    exact (List.mergeSort_perm _ _).symm.nodup (perm.1.filter _)
  apply ((chronologicalDeletes_order ops).and (List.nodup_iff_pairwise_ne.mp nd)).imp_of_mem
  intro a b ha hb pair
  have distinct : a.time ≠ b.time := by
    intro eq
    exact pair.2 (C.replayContext.ts_unique
      (support ((perm.2 a).mp ((chronologicalDeletes_mem ops a).mp ha).1))
      (support ((perm.2 b).mp ((chronologicalDeletes_mem ops b).mp hb).1)) eq)
  exact lt_of_le_of_ne pair.1 distinct

/-- At a target's first occurrence in a chronological list containing every
endpoint dequeue, the chronological timestamp is its minimum removal time. -/
theorem firstDeletion_at_firstPair {H : Set Event} {ps : List History.BirthDelete}
    (support : ∀ p ∈ ps, p.deletion ∈ H)
    (complete : ∀ d ∈ H, eIsIns d = false → ∃ p ∈ ps, p.deletion = d)
    (chronological : ps.Pairwise (fun p q => p.deletion.time < q.deletion.time))
    {before after : List History.BirthDelete} {p : History.BirthDelete}
    (split : ps = before ++ p :: after)
    (first : p.birth.time ∉ before.map (fun q => q.birth.time)) :
    firstDeletionTime H p.birth = p.deletion.time := by
  have hp : p ∈ ps := by rw [split]; simp
  have available : HasDeletion H p.birth :=
    ⟨p.deletion.time,p.deletion,support p hp,p.target,rfl⟩
  obtain ⟨d,hd,shape,time⟩ := firstDeletion_spec available
  have isdel : eIsIns d = false := by
    rcases d with ⟨t,r,op⟩
    change op = .del p.birth.time at shape
    subst op
    rfl
  obtain ⟨q,hq,del⟩ := complete d hd isdel
  have qt : q.birth.time = p.birth.time := by
    have eq : EOp.del (α := Nat) q.birth.time = .del p.birth.time :=
      q.target.symm.trans ((congrArg Op.op del).trans shape)
    exact EOp.del.inj eq
  have chrono := chronological
  rw [split] at hq chrono
  rcases List.mem_append.mp hq with old | current
  · exact False.elim (first (qt ▸ List.mem_map.mpr ⟨q,old,rfl⟩))
  · rcases List.mem_cons.mp current with rfl | later
    · exact time.symm.trans (congrArg Op.time del.symm)
    · have less := (List.pairwise_cons.mp (List.pairwise_append.mp chrono).2.1).1 q later
      have minimum := firstDeletion_le (support p hp) p.target
      have dtime : q.deletion.time = firstDeletionTime H p.birth :=
        (congrArg Op.time del).trans time
      exact False.elim (not_lt_of_ge minimum (less.trans_eq dtime))

#print axioms deletion_birth_pair

/-- Concrete certified inputs to the generic delete-first scheduling
algorithm. No field assumes a legal FIFO serialization. -/
structure DeadEndpoint (C : Configuration Q) (H : Set Event) where
  pairs : List History.BirthDelete
  birthSupport : ∀ p ∈ pairs, p.birth ∈ H
  deletionSupport : ∀ p ∈ pairs, p.deletion ∈ H
  complete : ∀ d ∈ H, eIsIns d = false → ∃ p ∈ pairs, p.deletion = d
  chronological : pairs.Pairwise (fun p q => p.deletion.time < q.deletion.time)
  freshRanks : History.FreshRanks (deadRank H) [] pairs
  deletionRanks : ∀ p ∈ pairs, deadRank H p.deletion = 2 * p.deletion.time + 1

theorem exists_deadEndpoint {C : Configuration Q}
    (execution : CertifiedExecution Q issuance C) {H : Set Event}
    (closed : ∀ a b, C.vis a b → b ∈ H → a ∈ H)
    (support : H ⊆ C.events) (finite : ∃ ops, listPermOf ops H) :
    Nonempty (DeadEndpoint C H) := by
  obtain ⟨ops,perm⟩ := finite
  let ds := chronologicalDeletes ops
  have dsSupport : ∀ d ∈ ds, d ∈ H ∧ eIsIns d = false := by
    intro d hd
    have h := (chronologicalDeletes_mem ops d).mp hd
    exact ⟨(perm.2 d).mp h.1,h.2⟩
  obtain ⟨ps,map,birthSupport⟩ := exists_birthDelete_pairs H ds (by
    intro d hd
    exact deletion_birth_pair execution closed support (dsSupport d hd).1 (dsSupport d hd).2)
  have deletionSupport : ∀ p ∈ ps, p.deletion ∈ H := by
    intro p hp
    apply (dsSupport p.deletion _).1
    rw [← map]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have complete : ∀ d ∈ H, eIsIns d = false → ∃ p ∈ ps, p.deletion = d := by
    intro d hd isdel
    have member : d ∈ ds := (chronologicalDeletes_mem ops d).mpr ⟨(perm.2 d).mpr hd,isdel⟩
    rw [← map] at member
    exact List.mem_map.mp member
  have chronological : ps.Pairwise (fun p q => p.deletion.time < q.deletion.time) := by
    have sorted : (ps.map History.BirthDelete.deletion).Pairwise
        (fun a b : Event => a.time < b.time) := by
      rw [map]
      exact chronologicalDeletes_strict support perm
    exact (List.pairwise_map (f := History.BirthDelete.deletion)
      (R := fun a b : Event => a.time < b.time)).mp sorted
  have freshRanks : History.FreshRanks (deadRank H) [] ps := by
    apply History.freshRanks_of_first_occurrence
    intro before p after split first
    rw [deadRank_birth p.insertion,
      firstDeletion_at_firstPair deletionSupport complete chronological split first]
  exact ⟨⟨ps,birthSupport,deletionSupport,complete,chronological,freshRanks,
    fun p _ => deadRank_delete p.target⟩⟩

#print axioms exists_deadEndpoint

theorem DeadEndpoint.word_support {C : Configuration Q} {H : Set Event}
    (endpoint : DeadEndpoint C H) (support : H ⊆ C.events)
    {e : Event} (member : e ∈ History.deadWord [] endpoint.pairs) : e ∈ H := by
  have unique : ∀ a ∈ H, ∀ b ∈ H, a.time = b.time → a = b :=
    fun a ha b hb => C.replayContext.ts_unique (support ha) (support hb)
  have pairs : History.pairSupport H endpoint.pairs :=
    fun p hp => ⟨endpoint.birthSupport p hp,endpoint.deletionSupport p hp⟩
  have members := (History.deadWord_support unique [] endpoint.pairs
    (by simp) pairs e).mp (by simpa using member)
  rcases members with impossible | ⟨p,hp,rfl | rfl⟩
  · simp at impossible
  · exact endpoint.birthSupport p hp
  · exact endpoint.deletionSupport p hp

theorem DeadEndpoint.word_birth_removed {C : Configuration Q} {H : Set Event}
    (endpoint : DeadEndpoint C H) (support : H ⊆ C.events)
    {e : Event} (member : e ∈ History.deadWord [] endpoint.pairs)
    (ins : eIsIns e = true) : HasDeletion H e := by
  have unique : ∀ a ∈ H, ∀ b ∈ H, a.time = b.time → a = b :=
    fun a ha b hb => C.replayContext.ts_unique (support ha) (support hb)
  have pairs : History.pairSupport H endpoint.pairs :=
    fun p hp => ⟨endpoint.birthSupport p hp,endpoint.deletionSupport p hp⟩
  have members := (History.deadWord_support unique [] endpoint.pairs
    (by simp) pairs e).mp (by simpa using member)
  rcases members with impossible | ⟨p,hp,rfl | rfl⟩
  · simp at impossible
  · exact ⟨p.deletion.time,p.deletion,endpoint.deletionSupport p hp,p.target,rfl⟩
  · have target := p.target
    simp only [eIsIns,Op.op] at target ins
    rw [target] at ins
    contradiction

/-- Every specification-conflicting causal edge inside the deletion word
strictly increases the constructed first-deletion rank. -/
theorem DeadEndpoint.causalRanks {C : Configuration Q} {H : Set Event}
    (endpoint : DeadEndpoint C H)
    (execution : CertifiedExecution Q issuance C)
    (closed : ∀ a b, C.vis a b → b ∈ H → a ∈ H)
    (support : H ⊆ C.events) {a b : Event}
    (ha : a ∈ History.deadWord [] endpoint.pairs)
    (hb : b ∈ History.deadWord [] endpoint.pairs)
    (causal : C.vis a b) (conflict : History.Conflict a b) :
    deadRank H a < deadRank H b := by
  have haH := endpoint.word_support support ha
  have hbH := endpoint.word_support support hb
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  cases oa with
  | ins va pa aa =>
    cases ob with
    | ins vb pb ab =>
      have lt := firstDeletion_causal execution closed support (support haH) (support hbH)
        rfl rfl causal (endpoint.word_birth_removed support hb rfl)
      rw [deadRank_birth rfl,deadRank_birth rfl]
      exact Nat.mul_lt_mul_of_pos_left lt (by decide)
    | del target =>
      have time : ta = target := conflict
      have minimum := firstDeletion_le (birth := (ta,ra,.ins va pa aa)) hbH (by
        change EOp.del (α := Nat) target = .del ta
        rw [time])
      rw [deadRank_birth rfl,deadRank_delete rfl]
      exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 minimum) (Nat.lt_succ_self _)
  | del target =>
    cases ob with
    | del target' =>
      have lt : ta < tb := C.causal_mono causal
      rw [deadRank_delete rfl,deadRank_delete rfl]
      exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left lt (by decide)) 1
    | ins vb pb ab =>
      have time : tb = target := conflict
      have honest := eHonest_core (eHonest_of_mint (execution_weaken execution).mintHonest)
      obtain ⟨birth,hbirth,vis,btime,_⟩ :=
        honest.del_has_ins (ta,ra,.del target) (support haH) target rfl
      have eq := C.replayContext.ts_unique hbirth (support hbH) (btime.trans time.symm)
      subst birth
      have good := CertifiedRGAExecution.Embedded.canonicalConfig unaryCode (execution_weaken execution)
      exact False.elim (good.vis_irrefl _ (good.vis_trans causal vis))

#print axioms DeadEndpoint.causalRanks

theorem DeadEndpoint.removed_birth_complete {C : Configuration Q} {H : Set Event}
    (endpoint : DeadEndpoint C H) (support : H ⊆ C.events)
    {birth : Event} (member : birth ∈ H) (_ins : eIsIns birth = true)
    (removed : HasDeletion H birth) : ∃ p ∈ endpoint.pairs, p.birth = birth := by
  obtain ⟨d,hd,shape,_⟩ := firstDeletion_spec removed
  have deletion : eIsIns d = false := by
    simp only [Op.op] at shape
    simp only [eIsIns,shape]
  obtain ⟨p,hp,del⟩ := endpoint.complete d hd deletion
  have time : p.birth.time = birth.time := by
    exact EOp.del.inj (p.target.symm.trans ((congrArg Op.op del).trans shape))
  exact ⟨p,hp,C.replayContext.ts_unique
    (support (endpoint.birthSupport p hp)) (support member) time⟩

theorem DeadEndpoint.deletions_nodup {C : Configuration Q} {H : Set Event}
    (endpoint : DeadEndpoint C H) :
    (endpoint.pairs.map History.BirthDelete.deletion).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply (List.pairwise_map (f := History.BirthDelete.deletion)
    (R := fun a b : Event => a ≠ b)).mpr
  apply endpoint.chronological.imp
  intro p q less equal
  rw [equal] at less
  exact Nat.lt_irrefl _ less

/-- Surviving births cannot be specification-conflicting causal predecessors
of the deletion word. This justifies placing the survivor suffix last. -/
theorem DeadEndpoint.no_survivor_predecessor {C : Configuration Q} {H : Set Event}
    (endpoint : DeadEndpoint C H)
    (execution : CertifiedExecution Q issuance C)
    (closed : ∀ a b, C.vis a b → b ∈ H → a ∈ H)
    (support : H ⊆ C.events) {live dead : Event}
    (member : live ∈ H) (insertion : eIsIns live = true)
    (survives : ¬ HasDeletion H live)
    (deadMember : dead ∈ History.deadWord [] endpoint.pairs) :
    ¬ (C.vis live dead ∧ History.Conflict live dead) := by
  rintro ⟨causal,conflict⟩
  have deadH := endpoint.word_support support deadMember
  rcases live with ⟨tl,rl,ol⟩
  rcases dead with ⟨td,rd,od⟩
  cases ol with
  | del target => simp [eIsIns] at insertion
  | ins value pref anchor =>
    cases od with
    | ins value' pref' anchor' =>
      have removed := endpoint.word_birth_removed support deadMember rfl
      obtain ⟨d,hd,shape⟩ := removed_births_causal_downset execution closed support
        (support member) (support deadH) rfl rfl causal ((hasDeletion_iff _ _).mp removed)
      exact survives ((hasDeletion_iff _ _).mpr ⟨d,hd,shape⟩)
    | del target =>
      have time : tl = target := conflict
      apply survives
      exact ⟨td,(td,rd,.del target),deadH,by change EOp.del (α := Nat) target = .del tl; rw [time],rfl⟩

#print axioms DeadEndpoint.no_survivor_predecessor
end Sal.MRDTs.Paper1.AnchoredQueue
