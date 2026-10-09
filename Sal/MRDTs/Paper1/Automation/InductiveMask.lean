import Sal.MRDTs.Paper1.ConcreteJoin

/-! Generic collection replay adapter: birth/mask membership induction.
This module identifies semantic representations with replays; it is not the
merge-equation induction used to establish the VCs. No datatype invariant or
solved merge VC is supplied: the suffix characterization is derived from the
update equation. The order certificate concerns events, independently of
implementation states. `EfficientReplayAdapter` instantiates these certificates
to recover canonical replay from the existing efficient OR-set representation. -/
namespace InductiveMask
open Classical
variable {Record Event : Type} [DecidableEq Record]

structure UpdateCertificate (step : Finset Record → Event → Finset Record)
    (born kill : Record → Event → Prop) : Prop where
  membership : ∀ s e p, p ∈ step s e ↔ born p e ∨ (p ∈ s ∧ ¬ kill p e)

def run (step : Finset Record → Event → Finset Record) (π : List Event) :=
  π.foldl step ∅

def Suffix (born kill : Record → Event → Prop) (π : List Event) (p : Record) : Prop :=
  ∃ pre b post, π = pre ++ b :: post ∧ born p b ∧ ∀ k ∈ post, ¬ kill p k

private theorem exists_last (π : List Event) (nonempty : π ≠ []) :
    ∃ pre e, π = pre ++ [e] := by
  induction π using List.reverseRecOn with
  | nil => exact False.elim (nonempty rfl)
  | append_singleton π e _ => exact ⟨π,e,rfl⟩

omit [DecidableEq Record] in
theorem membership_iff_suffix
    {step : Finset Record → Event → Finset Record}
    {born kill : Record → Event → Prop} (certificate : UpdateCertificate step born kill)
    (π : List Event) (p : Record) : p ∈ run step π ↔ Suffix born kill π p := by
  induction π using List.reverseRecOn with
  | nil => simp [run, Suffix]
  | append_singleton π e ih =>
    simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change p ∈ step (run step π) e ↔ _
    rw [certificate.membership, ih]
    constructor
    · rintro (birth | ⟨⟨pre,b,post,eq,hb,hpost⟩,notkill⟩)
      · exact ⟨π,e,[],by simp,birth,by simp⟩
      · refine ⟨pre,b,post ++ [e],by simp [eq,List.append_assoc],hb,?_⟩
        intro k hk
        rcases List.mem_append.mp hk with old | last
        · exact hpost k old
        · simpa only [List.mem_singleton.mp last] using notkill
    · rintro ⟨pre,b,post,eq,hb,hpost⟩
      by_cases last : post = []
      · subst post
        have equal : b = e := by
          have tails := congrArg List.getLast? eq
          simpa using tails.symm
        exact Or.inl (equal ▸ hb)
      · obtain ⟨prior,k,hk⟩ := exists_last post last
        have equal : k = e := by
          have full : π ++ [e] = (pre ++ b :: prior) ++ [k] := by
            simpa [hk,List.append_assoc] using eq
          have tails := congrArg List.reverse full
          simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at tails
          exact (List.cons.inj tails).1.symm
        subst k
        have before : π = pre ++ b :: prior := by
          have eq' : π ++ [e] = (pre ++ b :: prior) ++ [e] := by
            simpa [hk,List.append_assoc] using eq
          exact List.append_cancel_right eq'
        refine Or.inr ⟨⟨pre,b,prior,before,hb,?_⟩,?_⟩
        · intro k mem
          exact hpost k (by simp [hk,mem])
        · exact hpost e (by simp [hk])

def Alive (born kill : Record → Event → Prop) (vis : Event → Event → Prop)
    (E : Set Event) (p : Record) : Prop :=
  ∃ b ∈ E, born p b ∧ ¬ ∃ k ∈ E, vis b k ∧ kill p k

def order (vis noncomm priority : Event → Event → Prop) (E : Set Event)
    (a b : Event) : Prop :=
  (vis a b ∧ noncomm a b) ∨
  (¬ vis a b ∧ ¬ vis b a ∧ priority a b ∧
    ¬ ∃ c ∈ E, vis b c ∧ noncomm b c)

/-- Certificates concern only birth/kill classification and event ordering.
`killer_priority` may combine a finite datatype policy certificate with the
framework's same-replica comparability; it is not a state/history invariant. -/
structure OrderCertificate (born kill : Record → Event → Prop)
    (vis noncomm priority : Event → Event → Prop) (E : Set Event) : Prop where
  irrefl : ∀ b, ¬ vis b b
  noncomm_symm : ∀ b k, noncomm b k → noncomm k b
  births_unique : ∀ p, ∀ b ∈ E, ∀ c ∈ E, born p b → born p c → b = c
  killed_noncomm : ∀ p, ∀ b ∈ E, ∀ k ∈ E, born p b → kill p k → b ≠ k → noncomm b k
  noncomm_kills : ∀ p, ∀ b ∈ E, ∀ k ∈ E, born p b → noncomm b k → kill p k
  killer_priority : ∀ p, ∀ b ∈ E, ∀ k ∈ E, born p b → kill p k → b ≠ k →
    vis k b ∨ vis b k ∨ priority k b

omit [DecidableEq Record] in
theorem suffix_iff_alive
    {born kill : Record → Event → Prop} {vis noncomm priority : Event → Event → Prop}
    {E : Set Event} (certificate : OrderCertificate born kill vis noncomm priority E)
    (π : List Event) (perm : Sal.MRDTs.Foundation.listPermOf π E)
    (ordered : Sal.MRDTs.Foundation.respects π (order vis noncomm priority E)) (p : Record) :
    Suffix born kill π p ↔ Alive born kill vis E p := by
  constructor
  · rintro ⟨pre,b,post,rfl,hb,hpost⟩
    have bmem : b ∈ E := (perm.2 b).mp (by simp)
    refine ⟨b,bmem,hb,?_⟩
    rintro ⟨k,kmem,vis,kill⟩
    have ne : b ≠ k := fun equal => certificate.irrefl b (equal ▸ vis)
    have nc := certificate.killed_noncomm p b bmem k kmem hb kill ne
    have mem := (perm.2 k).mpr kmem
    rcases List.mem_append.mp mem with before | after
    · exact (List.pairwise_append.mp ordered).2.2 k before b (by simp) (Or.inl ⟨vis,nc⟩)
    · rcases List.mem_cons.mp after with equal | after
      · exact ne equal.symm
      · exact hpost k after kill
  · rintro ⟨b,bmem,hb,alive⟩
    obtain ⟨pre,post,eq⟩ := List.append_of_mem ((perm.2 b).mpr bmem)
    refine ⟨pre,b,post,eq,hb,?_⟩
    subst π
    intro k after kill
    have kmem : k ∈ E := (perm.2 k).mp (by simp [after])
    have ne : b ≠ k := by
      intro equal
      subst k
      have nd := List.pairwise_cons.mp (List.pairwise_append.mp perm.1).2.1
      exact nd.1 b after rfl
    have notvis : ¬ vis b k := fun h => alive ⟨k,kmem,h,kill⟩
    have nc := certificate.killed_noncomm p b bmem k kmem hb kill ne
    have before : order vis noncomm priority E k b := by
      rcases certificate.killer_priority p b bmem k kmem hb kill ne with back | forward | policy
      · exact Or.inl ⟨back,certificate.noncomm_symm b k nc⟩
      · exact False.elim (notvis forward)
      · by_cases back : vis k b
        · exact Or.inl ⟨back,certificate.noncomm_symm b k nc⟩
        · refine Or.inr ⟨back,notvis,policy,?_⟩
          rintro ⟨c,cmem,hvis,hnc⟩
          exact alive ⟨c,cmem,hvis,certificate.noncomm_kills p b bmem c cmem hb hnc⟩
    exact (List.pairwise_cons.mp (List.pairwise_append.mp ordered).2.1).1 k after before

omit [DecidableEq Record] in
theorem replay_iff_alive
    {step : Finset Record → Event → Finset Record}
    {born kill : Record → Event → Prop} {vis noncomm priority : Event → Event → Prop}
    {E : Set Event} (updates : UpdateCertificate step born kill)
    (events : OrderCertificate born kill vis noncomm priority E)
    (π : List Event) (perm : Sal.MRDTs.Foundation.listPermOf π E)
    (ordered : Sal.MRDTs.Foundation.respects π (order vis noncomm priority E)) (p : Record) :
    p ∈ run step π ↔ Alive born kill vis E p :=
  (membership_iff_suffix updates π p).trans (suffix_iff_alive events π perm ordered p)

#print axioms membership_iff_suffix
#print axioms suffix_iff_alive
#print axioms replay_iff_alive

end InductiveMask
