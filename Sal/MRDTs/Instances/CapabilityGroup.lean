import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-! Fixed-owner specialization of Jacob–Stuber–Hartenstein, PaPoC 2026,
Spec. 2. Subjects are authenticated externally. No delegation is modeled.
The event ID is also its grant identifier; causal rank is explicit in WellFormed.
Raw insertion/union are storage operations; admissibility is a separate predicate.
-/
namespace Sal.MRDTs.Instances.CapabilityGroup

abbrev Actor := Nat
abbrev Id := Nat
abbrev Name := Nat

inductive Action where
  | grant (recipient : Actor)
  | revoke (grant : Id)
  | assign (grant : Id) (name : Name)
  deriving DecidableEq, Repr

structure Event where
  id : Id
  actor : Actor
  past : Finset Id
  action : Action
  deriving DecidableEq

abbrev State := Finset Event
abbrev before (a b : Event) : Prop := a.id ∈ b.past

def pre (s : State) (e : Event) : State := s.filter (fun g => before g e)
def step (s : State) (e : Event) : State := insert e s
def merge (_base left right : State) : State := left ∪ right

/-- The IDs encode a topological rank, not wall-clock timestamps. Closure and
uniqueness rule out invented/mutable precursor sets on a well-formed extension. -/
structure WellFormed (s : State) : Prop where
  unique : ∀ a ∈ s, ∀ b ∈ s, a.id = b.id → a = b
  closed : ∀ e ∈ s, ∀ i ∈ e.past, ∃ p ∈ s, p.id = i
  downward : ∀ e ∈ s, ∀ p ∈ s, before p e → p.past ⊆ e.past
  ranked : ∀ e ∈ s, ∀ i ∈ e.past, i < e.id

abbrev grantFor (owner : Actor) (s : State) (e : Event) (gid : Id) : Prop :=
  ∃ g ∈ s, g.id = gid ∧ before g e ∧ g.actor = owner ∧ g.action = .grant e.actor

abbrev isGrant (a : Action) : Bool := match a with | .grant _ => true | _ => false

/-- A revoke requires the grant it names as an actual precursor, as in Spec. 2.
The fixed owner is never itself revoked. -/
abbrev revokes (owner : Actor) (s : State) (r : Event) (gid : Id) : Prop :=
  r.actor = owner ∧ r.action = .revoke gid ∧
  ∃ g ∈ s, g.id = gid ∧ before g r ∧ isGrant g.action = true

abbrev authorized (owner : Actor) (s : State) (e : Event) : Prop :=
  match e.action with
  | .grant _ => e.actor = owner
  | .revoke gid => revokes owner s e gid
  | .assign gid _ => grantFor owner s e gid ∧
      ∀ r ∈ s, revokes owner s r gid → before e r

instance authorizedDecidable (owner : Actor) (s : State) (e : Event) :
    Decidable (authorized owner s e) := by
  cases ha : e.action <;> simp only [authorized, ha] <;> infer_instance

/-- Immutable admission uses only causal precursors, never concurrent events. -/
abbrev admitted (owner : Actor) (s : State) (e : Event) : Prop :=
  authorized owner (pre s e) e

abbrev isAssignment (e : Event) : Prop :=
  match e.action with | .assign _ _ => True | _ => False

instance assignmentDecidable (e : Event) : Decidable (isAssignment e) := by
  cases ha : e.action <;> simp only [isAssignment, ha] <;> infer_instance

abbrev visible (owner : Actor) (s : State) (e : Event) : Prop :=
  e ∈ s ∧ isAssignment e ∧ authorized owner s e ∧
    ∀ f ∈ s, isAssignment f → authorized owner s f → ¬ before e f

instance visibleDecidable (owner : Actor) (s : State) (e : Event) :
    Decidable (visible owner s e) := by unfold visible; infer_instance

def nameOf (e : Event) : Name := match e.action with
  | .assign _ n => n
  | _ => 0

def names (owner : Actor) (s : State) : Finset Name :=
  (s.filter (visible owner s)).image nameOf

/-- Capability query is global: a later revocation removes the grant from caps,
but does not retroactively suppress assignments in its causal past. -/
def caps (owner : Actor) (s : State) : Finset Id :=
  (s.filter (fun g => g.actor = owner ∧
    isGrant g.action = true ∧
    ∀ r ∈ s, ¬ revokes owner s r g.id)).image Event.id

@[simp] theorem mem_pre (s : State) (e g : Event) :
    g ∈ pre s e ↔ g ∈ s ∧ before g e := by simp [pre]

@[simp] theorem mem_names (owner : Actor) (s : State) (n : Name) :
    n ∈ names owner s ↔ ∃ e ∈ s, visible owner s e ∧ nameOf e = n := by
  simp [names, and_assoc]

/-- Convergence is a lattice fact and does not establish authorization safety. -/
theorem merge_comm (l a b : State) : merge l a b = merge l b a := Finset.union_comm _ _
theorem merge_assoc (l a b c : State) :
    merge l (merge l a b) c = merge l a (merge l b c) := Finset.union_assoc _ _ _
theorem merge_idem (l a : State) : merge l a a = a := Finset.union_self _
theorem names_converge (owner : Actor) {a b : State} (h : a = b) :
    names owner a = names owner b := congrArg (names owner) h

/-- New delivery cannot change an old event's immutable causal cut, provided
both states are closed and the extension preserves unique event identities. -/
theorem pre_extension {s t : State} (hs : WellFormed s) (ht : WellFormed t)
    (hst : s ⊆ t) {e : Event} (he : e ∈ s) : pre s e = pre t e := by
  ext p
  simp only [mem_pre]
  constructor
  · exact fun h => ⟨hst h.1, h.2⟩
  · rintro ⟨hp, hpe⟩
    obtain ⟨q, hq, hqid⟩ := hs.closed e he p.id hpe
    have hpq : p = q := ht.unique p hp q (hst hq) hqid.symm
    exact ⟨hpq ▸ hq, hpe⟩

theorem admission_stable {owner : Actor} {s t : State}
    (hs : WellFormed s) (ht : WellFormed t) (hst : s ⊆ t)
    {e : Event} (he : e ∈ s) : admitted owner s e ↔ admitted owner t e := by
  unfold admitted
  rw [pre_extension hs ht hst he]

theorem unauthorized_grant (owner : Actor) (s : State) (e : Event) (user : Actor)
    (ha : e.action = .grant user) (hu : e.actor ≠ owner) : ¬ authorized owner s e := by
  simp [authorized, ha, hu]

theorem unauthorized_revoke (owner : Actor) (s : State) (e : Event) (gid : Id)
    (ha : e.action = .revoke gid) (hu : e.actor ≠ owner) : ¬ authorized owner s e := by
  simp [authorized, ha, hu]

theorem assignment_requires_owner_grant {owner : Actor} {s : State} {e : Event}
    {gid : Id} {n : Name} (ha : e.action = .assign gid n)
    (h : authorized owner s e) : grantFor owner s e gid := by
  have hh := h
  simp only [authorized, ha] at hh
  exact hh.1

/-- Authorized revocations suppress exactly non-precursor uses: this includes
concurrent uses and uses after the revocation, but excludes causal predecessors. -/
theorem revoked_use_suppressed {owner : Actor} {s : State} {e r : Event}
    {gid : Id} {n : Name} (ha : e.action = .assign gid n) (hr : r ∈ s)
    (hrev : revokes owner s r gid) (hnot : ¬ before e r) :
    ¬ authorized owner s e := by
  intro h
  have hh : grantFor owner s e gid ∧ ∀ r ∈ s, revokes owner s r gid → before e r := by
    simpa only [authorized, ha] using h
  exact hnot (hh.2 r hr hrev)

theorem precursor_use_preserved {owner : Actor} {s : State} {e : Event}
    {gid : Id} {n : Name} (ha : e.action = .assign gid n)
    (hg : grantFor owner s e gid)
    (hr : ∀ r ∈ s, revokes owner s r gid → before e r) : authorized owner s e := by
  simpa only [authorized, ha] using And.intro hg hr

/-- A rejected assignment cannot appear among causally maximal names. -/
theorem rejected_assignment_invisible {owner : Actor} {s : State} {e : Event}
    (h : ¬ authorized owner s e) : ¬ visible owner s e := by
  exact fun hv => h hv.2.2.1

theorem revokes_mono {owner : Actor} {s t : State} (hst : s ⊆ t)
    {r : Event} {gid : Id} (h : revokes owner s r gid) : revokes owner t r gid := by
  obtain ⟨ha, hr, g, hg, hid, hb, hk⟩ := h
  exact ⟨ha, hr, g, hst hg, hid, hb, hk⟩

/-- Query authorization never turns an event rejected by its immutable causal
cut into an accepted event. This is separate from nonmonotone later filtering. -/
theorem discursive_implies_admission {owner : Actor} {s : State} {e : Event}
    (h : authorized owner s e) : admitted owner s e := by
  cases ha : e.action with
  | grant user => simpa only [authorized, admitted, ha] using h
  | revoke gid =>
    simp only [authorized, ha] at h
    obtain ⟨howner, hact, g, hg, hid, hb, hk⟩ := h
    simp only [admitted, authorized, ha]
    exact ⟨howner, hact, g, (mem_pre s e g).mpr ⟨hg, hb⟩, hid, hb, hk⟩
  | assign gid n =>
    simp only [authorized, ha] at h
    obtain ⟨⟨g, hg, hid, hb, ho, hact⟩, hr⟩ := h
    have hgrant : grantFor owner (pre s e) e gid :=
      ⟨g, (mem_pre s e g).mpr ⟨hg, hb⟩, hid, hb, ho, hact⟩
    have hrev : ∀ r ∈ pre s e, revokes owner (pre s e) r gid → before e r := by
      intro r hr' hrv
      exact hr r ((mem_pre s e r).mp hr').1
        (revokes_mono (fun _ hg => ((mem_pre s e _).mp hg).1) hrv)
    simpa only [admitted, authorized, ha] using And.intro hgrant hrev

/-- Named revocation affects all fresh uses, independently of which precursor
set a sender selects. Freshness rules out borrowing an already-known ID. -/
theorem revoked_grant_rejects_fresh_use {owner : Actor} {s : State} {r e : Event}
    {gid : Id} {n : Name} (hr : r ∈ s) (hrev : revokes owner s r gid)
    (ha : e.action = .assign gid n) (hfresh : ∀ p ∈ s, e.id ∉ p.past) :
    ¬ authorized owner s e :=
  revoked_use_suppressed ha hr hrev (hfresh r hr)

/-- An authorized causal successor replaces an earlier assignment at the name
query, even when both assignments individually remain authorized. -/
theorem successor_hides_assignment {owner : Actor} {s : State} {e f : Event}
    (hf : f ∈ s) (hfa : isAssignment f) (hfu : authorized owner s f)
    (hef : before e f) : ¬ visible owner s e := by
  intro h
  exact h.2.2.2 f hf hfa hfu hef

/-- Optional honest single-owner-issuer discipline. Actor authentication is
separate from replica identity; the base model permits several owner devices. -/
abbrev OwnerOrdered (owner : Actor) (s : State) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a.actor = owner → b.actor = owner →
    a = b ∨ before a b ∨ before b a

/-- An extension of a closed history cannot add a previously missing precursor. -/
theorem new_not_before_old {s t : State} (hs : WellFormed s) (ht : WellFormed t)
    (hst : s ⊆ t) {x e : Event} (hx : x ∈ t) (hnew : x ∉ s) (he : e ∈ s) :
    ¬ before x e := by
  intro h
  obtain ⟨p, hp, hpid⟩ := hs.closed e he x.id h
  have hxp := ht.unique x hx p (hst hp) hpid.symm
  exact hnew (hxp ▸ hp)

/-- Authorization safety: only an authorized newly delivered revoke can
change an old event's discursive authorization in a closed extension. -/
theorem auth_insert_of_nonrevoking (owner : Actor) (s : State) (x : Event)
    (hf : ∀ e ∈ s, ¬ before x e)
    (hx : ∀ gid, ¬ revokes owner (insert x s) x gid)
    {e : Event} (he : e ∈ s) :
    authorized owner (insert x s) e ↔ authorized owner s e := by
  have hg : ∀ gid, grantFor owner (insert x s) e gid ↔ grantFor owner s e gid := by
    intro gid
    simp [grantFor, hf e he]
  have hr : ∀ r ∈ s, ∀ gid, revokes owner (insert x s) r gid ↔ revokes owner s r gid := by
    intro r hr gid
    simp [revokes, hf r hr]
  cases ha : e.action with
  | grant user => simp only [authorized, ha]
  | revoke gid => simpa only [authorized, ha] using hr e he gid
  | assign gid n =>
    simp only [authorized, ha]
    rw [hg]
    apply and_congr_right
    intro _
    simp only [Finset.mem_insert, forall_eq_or_imp]
    constructor
    · rintro ⟨_, h⟩ r hrs hrev
      exact h r hrs ((hr r hrs _).mpr hrev)
    · intro h
      refine ⟨fun hh => False.elim (hx gid hh), ?_⟩
      intro r hrs hrev
      exact h r hrs ((hr r hrs _).mp hrev)

/-- A non-owner administrative event cannot change authorization of old events.
The no-new-precursor premise follows from well-formed closed extensions. -/
theorem unauthorized_admin_auth_unchanged (owner : Actor) (s : State) (x : Event)
    (hu : x.actor ≠ owner) (hf : ∀ e ∈ s, ¬ before x e)
    {e : Event} (he : e ∈ s) :
    authorized owner (insert x s) e ↔ authorized owner s e :=
  auth_insert_of_nonrevoking owner s x hf (fun _ h => hu h.1) he

/-- Query safety for unauthorized administrative events, including their possible
indirect effects through grant lookup and revocation checks. -/
theorem names_insert_of_auth_invariant (owner : Actor) (s : State) (x : Event)
    (hx : ¬ isAssignment x)
    (ha : ∀ {e : Event}, e ∈ s →
      (authorized owner (insert x s) e ↔ authorized owner s e)) :
    names owner (insert x s) = names owner s := by
  have hv : ∀ e, visible owner (insert x s) e ↔ visible owner s e := by
    intro e
    constructor
    · rintro ⟨he, has, hau, hm⟩
      have hes : e ∈ s := by
        rcases Finset.mem_insert.mp he with h | h
        · subst e; exact False.elim (hx has)
        · exact h
      refine ⟨hes, has, (ha hes).mp hau, ?_⟩
      intro f hfs hfa hfu
      exact hm f (Finset.mem_insert_of_mem hfs) hfa ((ha hfs).mpr hfu)
    · rintro ⟨he, has, hau, hm⟩
      refine ⟨Finset.mem_insert_of_mem he, has, (ha he).mpr hau, ?_⟩
      intro f hf' hfa hfu
      rcases Finset.mem_insert.mp hf' with h | h
      · subst f; exact False.elim (hx hfa)
      · exact hm f h hfa ((ha h).mp hfu)
  apply Finset.ext
  intro n
  simp only [names, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨e, ⟨_, he⟩, hn⟩
    exact ⟨e, ⟨((hv e).mp he).1, (hv e).mp he⟩, hn⟩
  · rintro ⟨e, ⟨he, hv'⟩, hn⟩
    exact ⟨e, ⟨Finset.mem_insert_of_mem he, (hv e).mpr hv'⟩, hn⟩

theorem unauthorized_admin_names_unchanged (owner : Actor) (s : State) (x : Event)
    (hu : x.actor ≠ owner) (hx : ¬ isAssignment x)
    (hf : ∀ e ∈ s, ¬ before x e) : names owner (insert x s) = names owner s :=
  names_insert_of_auth_invariant owner s x hx
    (fun he => unauthorized_admin_auth_unchanged owner s x hu hf he)

theorem unauthorized_admin_caps_unchanged (owner : Actor) (s : State) (x : Event)
    (hu : x.actor ≠ owner) (hf : ∀ e ∈ s, ¬ before x e) :
    caps owner (insert x s) = caps owner s := by
  have hr : ∀ r ∈ s, ∀ gid, revokes owner (insert x s) r gid ↔ revokes owner s r gid := by
    intro r hr gid
    simp [revokes, hf r hr]
  unfold caps
  congr 1
  ext g
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hg, howner, hgrant, hrev⟩
    have hgs : g ∈ s := by
      rcases Finset.mem_insert.mp hg with h | h
      · subst g; exact False.elim (hu howner)
      · exact h
    refine ⟨hgs, howner, hgrant, ?_⟩
    intro r hrs hrv
    exact hrev r (Finset.mem_insert_of_mem hrs) ((hr r hrs _).mpr hrv)
  · rintro ⟨hg, howner, hgrant, hrev⟩
    refine ⟨Finset.mem_insert_of_mem hg, howner, hgrant, ?_⟩
    intro r hrs hrv
    rcases Finset.mem_insert.mp hrs with h | h
    · subst r; exact hu hrv.1
    · exact hrev r h ((hr r h _).mp hrv)

/-- Full local observation plus a fresh topological ID. This models correct
local issuance; delivery/merge may combine concurrently issued events. -/
abbrev FreshAt (s : State) (e : Event) : Prop :=
  e.past = s.image Event.id ∧ ∀ p ∈ s, p.id < e.id

abbrev CanIssue (owner : Actor) (s : State) (e : Event) : Prop :=
  FreshAt s e ∧ admitted owner s e

theorem wellFormed_union {s t : State} (hs : WellFormed s) (ht : WellFormed t)
    (hcompat : ∀ a ∈ s, ∀ b ∈ t, a.id = b.id → a = b) : WellFormed (s ∪ t) := by
  have hu : ∀ a ∈ s ∪ t, ∀ b ∈ s ∪ t, a.id = b.id → a = b := by
    intro a ha b hb hid
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact hs.unique a ha b hb hid
    · exact hcompat a ha b hb hid
    · exact (hcompat b hb a ha hid.symm).symm
    · exact ht.unique a ha b hb hid
  refine ⟨hu, ?_, ?_, ?_⟩
  · intro e he i hi
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨p, hp, hpid⟩ := hs.closed e he i hi
      exact ⟨p, Finset.mem_union_left t hp, hpid⟩
    · obtain ⟨p, hp, hpid⟩ := ht.closed e he i hi
      exact ⟨p, Finset.mem_union_right s hp, hpid⟩
  · intro e he p hp hb
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨q, hq, hqid⟩ := hs.closed e he p.id hb
      have hpq := hu p hp q (Finset.mem_union_left t hq) hqid.symm
      subst p
      exact hs.downward e he q hq hb
    · obtain ⟨q, hq, hqid⟩ := ht.closed e he p.id hb
      have hpq := hu p hp q (Finset.mem_union_right s hq) hqid.symm
      subst p
      exact ht.downward e he q hq hb
  · intro e he i hi
    rcases Finset.mem_union.mp he with he | he
    · exact hs.ranked e he i hi
    · exact ht.ranked e he i hi

theorem wellFormed_step {s : State} (hs : WellFormed s) {e : Event}
    (hf : FreshAt s e) : WellFormed (step s e) := by
  have hnot : ∀ p ∈ s, ¬ before e p := by
    intro p hp hb
    exact Nat.lt_asymm (hf.2 p hp) (hs.ranked p hp e.id hb)
  change WellFormed (insert e s)
  constructor
  · intro a ha b hb hid
    rcases Finset.mem_insert.mp ha with ha | ha <;>
      rcases Finset.mem_insert.mp hb with hb | hb
    · exact ha.trans hb.symm
    · subst a
      exact False.elim ((Nat.ne_of_lt (hf.2 b hb)) hid.symm)
    · subst b
      exact False.elim ((Nat.ne_of_lt (hf.2 a ha)) hid)
    · exact hs.unique a ha b hb hid
  · intro p hp i hi
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst p
      rw [hf.1] at hi
      obtain ⟨q, hq, hqid⟩ := Finset.mem_image.mp hi
      exact ⟨q, Finset.mem_insert_of_mem hq, hqid⟩
    · obtain ⟨q, hq, hqid⟩ := hs.closed p hp i hi
      exact ⟨q, Finset.mem_insert_of_mem hq, hqid⟩
  · intro p hp q hq hb
    rcases Finset.mem_insert.mp hp with hp | hp <;>
      rcases Finset.mem_insert.mp hq with hq | hq
    · subst p; subst q
      intro i hi; exact hi
    · subst p
      intro i hi
      obtain ⟨r, hr, hrid⟩ := hs.closed q hq i hi
      rw [hf.1]
      exact Finset.mem_image.mpr ⟨r, hr, hrid⟩
    · subst q
      exact False.elim (hnot p hp hb)
    · exact hs.downward p hp q hq hb
  · intro p hp i hi
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst p
      rw [hf.1] at hi
      obtain ⟨q, hq, hqid⟩ := Finset.mem_image.mp hi
      exact hqid ▸ hf.2 q hq
    · exact hs.ranked p hp i hi

theorem ownerOrdered_step {owner : Actor} {s : State} (ho : OwnerOrdered owner s)
    {e : Event} (hf : FreshAt s e) : OwnerOrdered owner (step s e) := by
  intro a ha b hb hao hbo
  rcases Finset.mem_insert.mp ha with ha | ha <;>
    rcases Finset.mem_insert.mp hb with hb | hb
  · exact Or.inl (ha.trans hb.symm)
  · subst a
    right; right
    change b.id ∈ e.past
    rw [hf.1]
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  · subst b
    right; left
    change a.id ∈ e.past
    rw [hf.1]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · exact ho a ha b hb hao hbo

theorem wellFormed_empty : WellFormed (∅ : State) := by
  constructor <;> simp

@[simp] theorem pre_fresh {s : State} {e : Event} (hf : FreshAt s e) : pre s e = s := by
  ext p
  simp only [mem_pre]
  constructor
  · exact And.left
  · intro hp
    refine ⟨hp, ?_⟩
    change p.id ∈ e.past
    rw [hf.1]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

theorem authorized_at_issue {owner : Actor} {s : State} {e : Event}
    (hc : CanIssue owner s e) : authorized owner s e := by
  have h := hc.2
  unfold admitted at h
  rwa [pre_fresh hc.1] at h

abbrev LocallyAdmitted (owner : Actor) (s : State) : Prop :=
  ∀ e ∈ s, admitted owner s e

theorem locallyAdmitted_step {owner : Actor} {s : State} (hs : WellFormed s)
    (ha : LocallyAdmitted owner s) {e : Event} (hc : CanIssue owner s e) :
    LocallyAdmitted owner (step s e) := by
  have ht := wellFormed_step hs hc.1
  have hsub : s ⊆ step s e := fun _ hp => Finset.mem_insert_of_mem hp
  intro p hp
  rcases Finset.mem_insert.mp hp with hp | hp
  · subst p
    have hself : ¬ before e e := by
      intro h
      exact Nat.lt_irrefl _ (ht.ranked e (Finset.mem_insert_self _ _) e.id h)
    have hpre : pre (step s e) e = pre s e := by
      ext p
      simp only [mem_pre, step, Finset.mem_insert]
      constructor
      · rintro ⟨h | h, hb⟩
        · subst p; exact False.elim (hself hb)
        · exact ⟨h, hb⟩
      · exact fun h => ⟨Or.inr h.1, h.2⟩
    unfold admitted
    rw [hpre]
    exact hc.2
  · exact (admission_stable hs ht hsub hp).mp (ha p hp)

theorem locallyAdmitted_union {owner : Actor} {s t : State}
    (hs : WellFormed s) (ht : WellFormed t)
    (hc : ∀ a ∈ s, ∀ b ∈ t, a.id = b.id → a = b)
    (has : LocallyAdmitted owner s) (hat : LocallyAdmitted owner t) :
    LocallyAdmitted owner (s ∪ t) := by
  have hu := wellFormed_union hs ht hc
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact (admission_stable hs hu (fun _ hp => Finset.mem_union_left _ hp) he).mp (has e he)
  · exact (admission_stable ht hu (fun _ hp => Finset.mem_union_right _ hp) he).mp (hat e he)

/-- An owner's malformed revoke is also inert: ownership alone does not make a
revoke valid when its target grant is absent from its immutable precursor set. -/
theorem rejected_revoke_auth_unchanged (owner : Actor) (s : State) (x : Event)
    {gid : Id} (hx : x.action = .revoke gid)
    (hreject : ¬ authorized owner (insert x s) x) (e : Event) :
    authorized owner (insert x s) e ↔ authorized owner s e := by
  have hg : ∀ target, grantFor owner (insert x s) e target ↔ grantFor owner s e target := by
    intro target
    simp [grantFor, hx]
  have hr : ∀ r target, revokes owner (insert x s) r target ↔ revokes owner s r target := by
    intro r target
    simp [revokes, hx, isGrant]
  have hxr : ∀ target, ¬ revokes owner (insert x s) x target := by
    intro target hrev
    have ht : gid = target := by
      have hh := hrev.2.1
      rw [hx] at hh
      exact Action.revoke.inj hh
    subst target
    apply hreject
    simpa only [authorized, hx] using hrev
  cases ha : e.action with
  | grant user => simp only [authorized, ha]
  | revoke target => simpa only [authorized, ha] using hr e target
  | assign target n =>
    simp only [authorized, ha]
    rw [hg]
    apply and_congr_right
    intro _
    simp only [Finset.mem_insert, forall_eq_or_imp]
    constructor
    · rintro ⟨_, h⟩ r hrs hrev
      exact h r hrs ((hr r _).mpr hrev)
    · intro h
      refine ⟨fun hh => False.elim (hxr target hh), ?_⟩
      intro r hrs hrev
      exact h r hrs ((hr r _).mp hrev)

theorem rejected_revoke_names_unchanged (owner : Actor) (s : State) (x : Event)
    {gid : Id} (hx : x.action = .revoke gid)
    (hreject : ¬ authorized owner (insert x s) x) :
    names owner (insert x s) = names owner s := by
  apply names_insert_of_auth_invariant owner s x
  · simp [isAssignment, hx]
  · intro e _
    exact rejected_revoke_auth_unchanged owner s x hx hreject e

theorem authorization_safety {owner : Actor} {s : State} {x e : Event}
    (hs : WellFormed s) (ht : WellFormed (insert x s)) (hnew : x ∉ s)
    (he : e ∈ s) (hx : ∀ gid, ¬ revokes owner (insert x s) x gid) :
    authorized owner (insert x s) e ↔ authorized owner s e := by
  apply auth_insert_of_nonrevoking owner s x _ hx he
  intro p hp
  exact new_not_before_old hs ht (fun _ hh => Finset.mem_insert_of_mem hh)
    (Finset.mem_insert_self _ _) hnew hp

end Sal.MRDTs.Instances.CapabilityGroup
