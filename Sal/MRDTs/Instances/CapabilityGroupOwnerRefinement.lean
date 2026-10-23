import Sal.MRDTs.Instances.CapabilityGroupOwnerLinearization

namespace Sal.MRDTs.Instances.CapabilityGroup.OwnerRefinement
open OwnerLinearization OwnerOrder
namespace Seq
abbrev Store := Sal.MRDTs.Paper1.CapabilityGroupSpec.Store
abbrev project := Sal.MRDTs.Paper1.CapabilityGroupSpec.project
abbrev update := Sal.MRDTs.Paper1.CapabilityGroupSpec.update
abbrev run := Sal.MRDTs.Paper1.CapabilityGroupSpec.run
abbrev names := Sal.MRDTs.Paper1.CapabilityGroupSpec.names
end Seq

structure Tables (done : List Event) (store : Seq.Store) : Prop where
  grants : ∀ gid user, (gid,user) ∈ store.grants ↔
    ∃ g ∈ done, g.id = gid ∧ g.action = .grant user
  revoked : ∀ gid, gid ∈ store.revoked ↔ ∃ r ∈ done, r.action = .revoke gid

abbrev Accepted (owner : Actor) (s : State) (e : Event) : Prop :=
  isAssignment e ∧ authorized owner s e

abbrev visibleIn (owner : Actor) (s : State) (done : List Event) (e : Event) : Prop :=
  e ∈ done ∧ Accepted owner s e ∧
    ∀ f ∈ done, Accepted owner s f → ¬ before e f

abbrev Entries (owner : Actor) (s : State) (done : List Event) (store : Seq.Store) : Prop :=
  ∀ p, p ∈ store.entries ↔ ∃ e, visibleIn owner s done e ∧ (e.id,nameOf e) = p

@[simp] theorem tables_empty : Tables [] ({} : Seq.Store) := by
  constructor <;> intros <;> simp
@[simp] theorem entries_empty (owner : Actor) (s : State) : Entries owner s [] ({} : Seq.Store) := by
  intro p
  simp [visibleIn]

theorem visibleIn_snoc {owner : Actor} {s : State} {done : List Event} {e x : Event}
    (hself : ¬ before e e) (hfuture : ∀ f ∈ done, ¬ before e f) :
    visibleIn owner s (done ++ [e]) x ↔
      (x = e ∧ Accepted owner s e) ∨
      (visibleIn owner s done x ∧ (Accepted owner s e → ¬ before x e)) := by
  simp only [visibleIn, List.mem_append, List.mem_singleton, or_imp, forall_and]
  constructor
  · rintro ⟨hx | hx, hacc, hold, hnew⟩
    · exact Or.inr ⟨⟨hx, hacc, hold⟩, fun h => hnew e rfl h⟩
    · exact Or.inl ⟨hx, hx ▸ hacc⟩
  · rintro (⟨rfl, hacc⟩ | ⟨⟨hx, hacc, hold⟩, hnew⟩)
    · exact ⟨Or.inr rfl, hacc, fun f hf _ => hfuture f hf, fun f hf _ => hf ▸ hself⟩
    · exact ⟨Or.inl hx, hacc, hold, fun f hf hfacc => hf ▸ hnew (hf ▸ hfacc)⟩

theorem prefix_index {π done tail : List Event} {e : Event}
    (hn : π.Nodup) (hπ : π = done ++ e :: tail) (a : Event) :
    a ∈ done ↔ π.idxOf a < π.idxOf e := by
  rw [hπ] at hn ⊢
  have hen : e ∉ done := by
    intro he
    exact (List.nodup_append.mp hn).2.2 e he e (by simp) rfl
  rw [List.idxOf_append_of_notMem hen, List.idxOf_cons_self]
  simp only [Nat.add_zero]
  exact List.IsPrefix.mem_iff_idxOf_lt_length (List.prefix_append _ _) a

theorem prefix_past {s : State} {π done tail : List Event} {e : Event}
    (hp : π.Perm s.toList) (hr : Respects π before) (hπ : π = done ++ e :: tail) :
    ∀ g ∈ s, before g e → g ∈ done := by
  intro g hg hge
  apply (prefix_index (hp.nodup_iff.mpr s.nodup_toList) hπ g).mpr
  exact hr g (hp.mem_iff.mpr (Finset.mem_toList.mpr hg)) e (by rw [hπ]; simp) hge

theorem prefix_no_future {s : State} {π done tail : List Event} {e : Event}
    (hp : π.Perm s.toList) (hr : Respects π before) (hπ : π = done ++ e :: tail) :
    ∀ g ∈ done, ¬ before e g := by
  intro g hg heg
  have hge := (prefix_index (hp.nodup_iff.mpr s.nodup_toList) hπ g).mp hg
  have heg' := hr e (by rw [hπ]; simp) g (by rw [hπ]; simp [hg]) heg
  omega

theorem revoke_authorized {owner : Actor} {s : State} (hl : LocallyAdmitted owner s)
    {r : Event} (hr : r ∈ s) {gid : Id} (ha : r.action = .revoke gid) : revokes owner s r gid := by
  have h := hl r hr
  simp only [admitted, authorized, ha] at h
  exact revokes_mono (fun _ hg => ((mem_pre s r _).mp hg).1) h

theorem assignment_guard {owner : Actor} {s : State} (hl : LocallyAdmitted owner s)
    {π done tail : List Event} {e : Event} {store : Seq.Store}
    (hp : π.Perm s.toList) (hr : Respects π before) (hc : AdminPrefix owner s π)
    (hπ : π = done ++ e :: tail) (ht : Tables done store)
    {gid : Id} {n : Name} (ha : e.action = .assign gid n) :
    ((gid,e.actor) ∈ store.grants ∧ gid ∉ store.revoked) ↔ authorized owner s e := by
  have heπ : e ∈ π := by rw [hπ]; simp
  have hes : e ∈ s := Finset.mem_toList.mp (hp.mem_iff.mp heπ)
  have had := hl e hes
  simp only [admitted, authorized, ha] at had
  obtain ⟨g, hg, hgid, hge, hgo, hgact⟩ := had.1
  have hgs := ((mem_pre s e g).mp hg).1
  have hgd := prefix_past hp hr hπ g hgs hge
  have hgrant : (gid,e.actor) ∈ store.grants := (ht.grants gid e.actor).mpr ⟨g,hgd,hgid,hgact⟩
  have hgsrc : grantFor owner s e gid := ⟨g,hgs,hgid,hge,hgo,hgact⟩
  simp only [authorized, ha]
  constructor
  · rintro ⟨_, hn⟩
    refine ⟨hgsrc, ?_⟩
    intro r hrs hrev
    by_contra hnot
    have hcut := (hc done e tail hπ (by simp [isAssignment, ha]) r hrs
      ⟨hrev.1, by simp [hrev.2.1, isAdministrative]⟩).mpr hnot
    exact hn ((ht.revoked gid).mpr ⟨r,hcut,hrev.2.1⟩)
  · rintro ⟨_, hsafe⟩
    refine ⟨hgrant, ?_⟩
    intro hmem
    obtain ⟨r, hrd, hract⟩ := (ht.revoked gid).mp hmem
    have hrπ : r ∈ π := by rw [hπ]; simp [hrd]
    have hrs : r ∈ s := Finset.mem_toList.mp (hp.mem_iff.mp hrπ)
    have hrev := revoke_authorized hl hrs hract
    have hcut := (hc done e tail hπ (by simp [isAssignment, ha]) r hrs
      ⟨hrev.1, by simp [hract, isAdministrative]⟩).mp hrd
    exact hcut (hsafe r hrs hrev)

theorem entries_snoc_rejected {owner : Actor} {s : State} {done : List Event}
    {e : Event} {store : Seq.Store} (hentries : Entries owner s done store)
    (hself : ¬ before e e) (hfuture : ∀ f ∈ done, ¬ before e f)
    (hrej : ¬ Accepted owner s e) : Entries owner s (done ++ [e]) store := by
  intro p
  rw [hentries]
  simp only [visibleIn_snoc hself hfuture, hrej, and_false, false_or,
    false_implies, and_true]

theorem entries_snoc_accepted {owner : Actor} {s : State} {done : List Event}
    {e : Event} {store : Seq.Store} (hentries : Entries owner s done store)
    (hself : ¬ before e e) (hfuture : ∀ f ∈ done, ¬ before e f)
    (hacc : Accepted owner s e) : Entries owner s (done ++ [e])
      ({store with entries := insert (e.id,nameOf e) (store.entries.filter (fun p => p.1 ∉ e.past))} : Seq.Store) := by
  intro p
  simp only [Finset.mem_insert, Finset.mem_filter]
  rw [hentries]
  constructor
  · rintro (hp | ⟨⟨x,hx,hpair⟩,hnot⟩)
    · refine ⟨e, (visibleIn_snoc hself hfuture).mpr (Or.inl ⟨rfl,hacc⟩), hp.symm⟩
    · refine ⟨x, (visibleIn_snoc hself hfuture).mpr (Or.inr ⟨hx,fun _ => ?_⟩), hpair⟩
      change x.id ∉ e.past
      simpa only [← hpair] using hnot
  · rintro ⟨x,hx,hpair⟩
    rcases (visibleIn_snoc hself hfuture).mp hx with ⟨rfl,_⟩ | ⟨hx,hnot⟩
    · exact Or.inl hpair.symm
    · refine Or.inr ⟨⟨x,hx,hpair⟩, ?_⟩
      have hbe := hnot hacc
      simpa only [← hpair] using hbe

theorem tables_step {owner : Actor} {s : State} (hl : LocallyAdmitted owner s)
    {π done tail : List Event} {e : Event} {store : Seq.Store}
    (hp : π.Perm s.toList) (hr : Respects π before)
    (hπ : π = done ++ e :: tail) (ht : Tables done store) :
    Tables (done ++ [e]) (Seq.update owner store (Seq.project e)) := by
  have hes : e ∈ s := Finset.mem_toList.mp (hp.mem_iff.mp (by rw [hπ]; simp))
  cases ha : e.action with
  | grant user =>
    have ho := admin_owner hl hes (by simp [ha,isAdministrative])
    simp only [Seq.update, Seq.project, Sal.MRDTs.Paper1.CapabilityGroupSpec.update, Sal.MRDTs.Paper1.CapabilityGroupSpec.project, ha, if_pos ho]
    constructor
    · intro gid who
      simp only [Finset.mem_insert, ht.grants, List.mem_append, List.mem_singleton]
      constructor
      · rintro (heq | ⟨g,hgd,hid,hact⟩)
        · refine ⟨e,Or.inr rfl,?_,?_⟩
          · exact (congrArg Prod.fst heq).symm
          · have hw : who = user := congrArg Prod.snd heq
            exact ha.trans (congrArg Action.grant hw.symm)
        · exact ⟨g,Or.inl hgd,hid,hact⟩
      · rintro ⟨g,hgd|rfl,hid,hact⟩
        · exact Or.inr ⟨g,hgd,hid,hact⟩
        · left
          have hw : user = who := Action.grant.inj (ha.symm.trans hact)
          simp only [hid,hw]
    · intro gid
      rw [ht.revoked]
      simp only [List.mem_append,List.mem_singleton]
      constructor
      · rintro ⟨r,hr,hact⟩; exact ⟨r,Or.inl hr,hact⟩
      · rintro ⟨r,hr|rfl,hact⟩
        · exact ⟨r,hr,hact⟩
        · simp [ha] at hact
  | revoke gid =>
    have hrev := revoke_authorized hl hes ha
    obtain ⟨g,hgs,hgid,hge,hgrant⟩ := hrev.2.2
    have hgd := prefix_past hp hr hπ g hgs hge
    cases hga : g.action with
    | grant user =>
      have hknown : ∃ p ∈ store.grants, p.1 = gid :=
        ⟨(gid,user),(ht.grants gid user).mpr ⟨g,hgd,hgid,hga⟩,rfl⟩
      have hguard : e.actor = owner ∧ ∃ p ∈ store.grants, p.1 = gid := ⟨hrev.1,hknown⟩
      simp only [Seq.update,Seq.project,Sal.MRDTs.Paper1.CapabilityGroupSpec.update,Sal.MRDTs.Paper1.CapabilityGroupSpec.project,ha,if_pos hguard]
      constructor
      · intro key user'
        rw [ht.grants]
        simp only [List.mem_append,List.mem_singleton]
        constructor
        · rintro ⟨q,hq,hid,hact⟩; exact ⟨q,Or.inl hq,hid,hact⟩
        · rintro ⟨q,hq|rfl,hid,hact⟩
          · exact ⟨q,hq,hid,hact⟩
          · simp [ha] at hact
      · intro key
        simp only [Finset.mem_insert,ht.revoked,List.mem_append,List.mem_singleton]
        constructor
        · rintro (rfl | ⟨r,hr,hact⟩)
          · exact ⟨e,Or.inr rfl,ha⟩
          · exact ⟨r,Or.inl hr,hact⟩
        · rintro ⟨r,hr|rfl,hact⟩
          · exact Or.inr ⟨r,hr,hact⟩
          · exact Or.inl (Action.revoke.inj (ha.symm.trans hact)).symm
    | revoke target => simp [hga,isGrant] at hgrant
    | assign target name => simp [hga,isGrant] at hgrant
  | assign gid n =>
    have hgrants : (Seq.update owner store (Seq.project e)).grants = store.grants := by
      simp only [Seq.update,Seq.project,Sal.MRDTs.Paper1.CapabilityGroupSpec.update,Sal.MRDTs.Paper1.CapabilityGroupSpec.project,ha]; split <;> rfl
    have hrevoked : (Seq.update owner store (Seq.project e)).revoked = store.revoked := by
      simp only [Seq.update,Seq.project,Sal.MRDTs.Paper1.CapabilityGroupSpec.update,Sal.MRDTs.Paper1.CapabilityGroupSpec.project,ha]; split <;> rfl
    constructor
    · intro key user
      rw [hgrants,ht.grants]
      simp only [List.mem_append,List.mem_singleton]
      constructor
      · rintro ⟨q,hq,hid,hact⟩; exact ⟨q,Or.inl hq,hid,hact⟩
      · rintro ⟨q,hq|rfl,hid,hact⟩
        · exact ⟨q,hq,hid,hact⟩
        · simp [ha] at hact
    · intro key
      rw [hrevoked,ht.revoked]
      simp only [List.mem_append,List.mem_singleton]
      constructor
      · rintro ⟨r,hr,hact⟩; exact ⟨r,Or.inl hr,hact⟩
      · rintro ⟨r,hr|rfl,hact⟩
        · exact ⟨r,hr,hact⟩
        · simp [ha] at hact

theorem entries_step {owner : Actor} {s : State} (hs : WellFormed s)
    (hl : LocallyAdmitted owner s) {π done tail : List Event} {e : Event} {store : Seq.Store}
    (hp : π.Perm s.toList) (hr : Respects π before) (hc : AdminPrefix owner s π)
    (hπ : π = done ++ e :: tail) (ht : Tables done store)
    (hentries : Entries owner s done store) :
    Entries owner s (done ++ [e]) (Seq.update owner store (Seq.project e)) := by
  have hes : e ∈ s := Finset.mem_toList.mp (hp.mem_iff.mp (by rw [hπ]; simp))
  have hself : ¬ before e e := fun h => Nat.lt_irrefl _ (hs.ranked e hes e.id h)
  have hfuture := prefix_no_future hp hr hπ
  cases ha : e.action with
  | grant user =>
    have hrej : ¬ Accepted owner s e := by simp [Accepted,isAssignment,ha]
    have hh := entries_snoc_rejected hentries hself hfuture hrej
    intro p
    simp only [Seq.update,Seq.project,Sal.MRDTs.Paper1.CapabilityGroupSpec.update,Sal.MRDTs.Paper1.CapabilityGroupSpec.project,ha]
    split <;> exact hh p
  | revoke gid =>
    have hrej : ¬ Accepted owner s e := by simp [Accepted,isAssignment,ha]
    have hh := entries_snoc_rejected hentries hself hfuture hrej
    intro p
    simp only [Seq.update,Seq.project,Sal.MRDTs.Paper1.CapabilityGroupSpec.update,Sal.MRDTs.Paper1.CapabilityGroupSpec.project,ha]
    split <;> exact hh p
  | assign gid n =>
    have hg := assignment_guard hl hp hr hc hπ ht ha
    by_cases hacc : authorized owner s e
    · have hacc' : Accepted owner s e := ⟨by simp [isAssignment,ha],hacc⟩
      have hh := entries_snoc_accepted hentries hself hfuture hacc'
      have hguard := hg.mpr hacc
      simpa only [Seq.update,Seq.project,Sal.MRDTs.Paper1.CapabilityGroupSpec.update,Sal.MRDTs.Paper1.CapabilityGroupSpec.project,ha,if_pos hguard,nameOf] using hh
    · have hrej : ¬ Accepted owner s e := fun h => hacc h.2
      have hh := entries_snoc_rejected hentries hself hfuture hrej
      have hguard : ¬ ((gid,e.actor) ∈ store.grants ∧ gid ∉ store.revoked) :=
        fun h => hacc (hg.mp h)
      simpa only [Seq.update,Seq.project,Sal.MRDTs.Paper1.CapabilityGroupSpec.update,Sal.MRDTs.Paper1.CapabilityGroupSpec.project,ha,if_neg hguard] using hh

@[simp] theorem run_snoc (owner : Actor) (done : List Event) (e : Event) :
    Seq.run owner ((done ++ [e]).map Seq.project) =
      Seq.update owner (Seq.run owner (done.map Seq.project)) (Seq.project e) := by
  simp only [Seq.run,Sal.MRDTs.Paper1.CapabilityGroupSpec.run,List.map_append,
    List.map_singleton,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem prefix_invariants {owner : Actor} {s : State} (hs : WellFormed s)
    (hl : LocallyAdmitted owner s) {π : List Event}
    (hp : π.Perm s.toList) (hr : Respects π before) (hc : AdminPrefix owner s π)
    (done tail : List Event) (hπ : π = done ++ tail) :
    Tables done (Seq.run owner (done.map Seq.project)) ∧
      Entries owner s done (Seq.run owner (done.map Seq.project)) := by
  induction done using List.reverseRecOn generalizing tail with
  | nil => exact ⟨tables_empty, entries_empty owner s⟩
  | append_singleton done e ih =>
    have hprev : π = done ++ e :: tail := by
      simpa only [List.append_assoc,List.singleton_append] using hπ
    obtain ⟨ht,he⟩ := ih (e :: tail) hprev
    rw [run_snoc]
    exact ⟨tables_step hl hp hr hprev ht,entries_step hs hl hp hr hc hprev ht he⟩

theorem visibleIn_full {owner : Actor} {s : State} {π : List Event}
    (hp : π.Perm s.toList) (e : Event) : visibleIn owner s π e ↔ visible owner s e := by
  have hmem : ∀ x, x ∈ π ↔ x ∈ s := fun x => hp.mem_iff.trans Finset.mem_toList
  constructor
  · rintro ⟨he,ha,hm⟩
    refine ⟨(hmem e).mp he,ha.1,ha.2,?_⟩
    intro f hf hfa hfu
    exact hm f ((hmem f).mpr hf) ⟨hfa,hfu⟩
  · rintro ⟨he,ha,hu,hm⟩
    refine ⟨(hmem e).mpr he,⟨ha,hu⟩,?_⟩
    intro f hf hacc
    exact hm f ((hmem f).mp hf) hacc.1 hacc.2

/-- At each actual replay prefix, ordinary ACL admission is precisely the
source's final discursive authorization of the assignment being processed. -/
theorem assignment_run_guard {owner : Actor} {s : State} (hs : WellFormed s)
    (hl : LocallyAdmitted owner s) {π done tail : List Event} {e : Event}
    (hp : π.Perm s.toList) (hr : Respects π before) (hc : AdminPrefix owner s π)
    (hπ : π = done ++ e :: tail) {gid : Id} {n : Name} (ha : e.action = .assign gid n) :
    let store := Seq.run owner (done.map Seq.project)
    ((gid,e.actor) ∈ store.grants ∧ gid ∉ store.revoked) ↔ authorized owner s e := by
  exact assignment_guard hl hp hr hc hπ
    (prefix_invariants hs hl hp hr hc done (e :: tail) hπ).1 ha

/-- Full source entry identities, stronger than equality of projected names. -/
def sourceEntries (owner : Actor) (s : State) : Finset (Id × Name) :=
  (s.filter (visible owner s)).image (fun e => (e.id,nameOf e))

theorem run_entries_eq_source {owner : Actor} {s : State} (hs : WellFormed s)
    (hl : LocallyAdmitted owner s) {π : List Event}
    (hp : π.Perm s.toList) (hr : Respects π before) (hc : AdminPrefix owner s π) :
    (Seq.run owner (π.map Seq.project)).entries = sourceEntries owner s := by
  have hinv := (prefix_invariants hs hl hp hr hc π [] (by simp)).2
  ext p
  rw [hinv]
  simp only [sourceEntries,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨e,he,hpair⟩
    have hv := (visibleIn_full hp e).mp he
    exact ⟨e,⟨hv.1,hv⟩,hpair⟩
  · rintro ⟨e,⟨_,he⟩,hpair⟩
    exact ⟨e,(visibleIn_full hp e).mpr he,hpair⟩

/-- Complete independent sequential replay theorem. No equality with cutStore
is assumed: the grants, revoked IDs and live entry table are derived by fold
invariants over every prefix of the actual ordinary ACL run. -/
theorem run_names_eq_source {owner : Actor} {s : State} (hs : WellFormed s)
    (hl : LocallyAdmitted owner s) {π : List Event}
    (hp : π.Perm s.toList) (hr : Respects π before) (hc : AdminPrefix owner s π) :
    Seq.names (Seq.run owner (π.map Seq.project)) = names owner s := by
  have hinv := (prefix_invariants hs hl hp hr hc π [] (by simp)).2
  ext n
  constructor
  · intro hn
    obtain ⟨p,hpentry,hpn⟩ := Finset.mem_image.mp hn
    obtain ⟨e,hve,hepair⟩ := (hinv p).mp hpentry
    apply (mem_names owner s n).mpr
    have hvisible := (visibleIn_full hp e).mp hve
    refine ⟨e,hvisible.1,hvisible,?_⟩
    have hn' := congrArg Prod.snd hepair
    exact hn'.trans hpn
  · intro hn
    obtain ⟨e,_,hve,hen⟩ := (mem_names owner s n).mp hn
    apply Finset.mem_image.mpr
    refine ⟨(e.id,nameOf e), (hinv _).mpr ⟨e,(visibleIn_full hp e).mpr hve,rfl⟩,hen⟩

/-- A complete finite witness, with every causal edge retained and precisely
the source's multi-value name query in the independent sequential ACL. -/
theorem exists_sequential_replay {owner : Actor} {s : State}
    (hs : WellFormed s) (hl : LocallyAdmitted owner s) (ho : OwnerOrdered owner s) :
    ∃ π : List Event, π.Perm s.toList ∧ π.Nodup ∧ Respects π before ∧
      AdminPrefix owner s π ∧ Seq.names (Seq.run owner (π.map Seq.project)) = names owner s := by
  refine ⟨canonical owner s,canonical_perm owner s,canonical_nodup owner s,
    canonical_respects hs hl ho,canonical_adminPrefix hs hl ho,?_⟩
  exact run_names_eq_source hs hl (canonical_perm owner s)
    (canonical_respects hs hl ho) (canonical_adminPrefix hs hl ho)

namespace SPOT
private abbrev grantUser : Event := ⟨1,0,∅,.grant 1⟩
private abbrev use : Event := ⟨2,1,{1},.assign 1 10⟩
private abbrev concurrentRevoke : Event := ⟨3,0,{1},.revoke 1⟩
private abbrev laterRevoke : Event := ⟨3,0,{1,2},.revoke 1⟩
private abbrev selfGrant : Event := ⟨1,0,∅,.grant 0⟩
private abbrev selfUse : Event := ⟨2,0,{1},.assign 1 10⟩

/-- A complete witness is obtained by the universal theorem on a nonempty,
owner-ordered history whose concurrent use must be rejected. -/
theorem concurrent_revoke_witness_control :
    ∃ π : List Event, π.Perm ({grantUser,use,concurrentRevoke} : State).toList ∧
      π.Nodup ∧ Respects π before ∧ AdminPrefix 0 {grantUser,use,concurrentRevoke} π ∧
      Seq.names (Seq.run 0 (π.map Seq.project)) = ∅ := by
  have hs : WellFormed {grantUser,use,concurrentRevoke} := by constructor <;> decide
  have hh := exists_sequential_replay hs (by decide) (by decide : OwnerOrdered 0 {grantUser,use,concurrentRevoke})
  simpa only [show names 0 {grantUser,use,concurrentRevoke} = ∅ from by decide] using hh

/-- Hand-derived replay controls distinguish concurrent suppression from the
preserved use that causally precedes its revoke. -/
theorem concurrent_and_precursor_control :
    Seq.names (Seq.run 0 ([grantUser,concurrentRevoke,use].map Seq.project)) = ∅ ∧
    Seq.names (Seq.run 0 ([grantUser,concurrentRevoke,use].map Seq.project)) ≠ {10} ∧
    Seq.names (Seq.run 0 ([grantUser,use,laterRevoke].map Seq.project)) = {10} ∧
    Seq.names (Seq.run 0 ([grantUser,use,laterRevoke].map Seq.project)) ≠ ∅ := by decide

/-- Owner self-assignment participates among assignments, with its real grant
preceding it. The full replay keeps its name rather than omitting the event. -/
theorem owner_self_assignment_witness_control :
    ∃ π : List Event, π.Perm ({selfGrant,selfUse} : State).toList ∧ π.Nodup ∧
      Respects π before ∧ AdminPrefix 0 {selfGrant,selfUse} π ∧
      Seq.names (Seq.run 0 (π.map Seq.project)) = {10} := by
  have hs : WellFormed {selfGrant,selfUse} := by constructor <;> decide
  have hh := exists_sequential_replay hs (by decide) (by decide : OwnerOrdered 0 {selfGrant,selfUse})
  simpa only [show names 0 {selfGrant,selfUse} = {10} from by decide] using hh

example : Seq.names (Seq.run 0 ([selfGrant,selfUse].map Seq.project)) ≠ ∅ := by decide
end SPOT

#print axioms exists_sequential_replay
#print axioms assignment_run_guard
#print axioms run_entries_eq_source
#print axioms run_names_eq_source

end Sal.MRDTs.Instances.CapabilityGroup.OwnerRefinement
