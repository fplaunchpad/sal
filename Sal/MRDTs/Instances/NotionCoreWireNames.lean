import Mathlib.Data.Nat.Digits.Defs
import Sal.MRDTs.Instances.NotionCoreMachineSearchLabels

/-! UTF-16 code-unit names used by the pinned core source. Decimal counters are
mathematical base-ten digits; correspondence to JS Number.toString is restricted
to positive safe integers and remains a printing/extraction boundary. Sessions
may contain separators. These encodings are not the transaction sort order. -/
namespace Sal.MRDTs.Instances.NotionCoreWireNames
open NotionCorePayload (BlockKey)
open NotionRunAllocation (Id)

def decimal (n : Nat) : List Nat := (Nat.digits 10 n).reverse.map (48 + ·)

theorem decimal_injective : Function.Injective decimal := by
  intro a b equal
  have mapped := (List.map_inj_right (fun a b h => Nat.add_left_cancel h)).mp equal
  have digits : Nat.digits 10 a = Nat.digits 10 b := List.reverse_injective mapped
  exact Nat.digits_inj_iff.mp digits

theorem decimal_units {n unit : Nat} (member : unit ∈ decimal n) : 48 ≤ unit ∧ unit ≤ 57 := by
  obtain ⟨digit,member,equal⟩ := List.mem_map.mp member
  have small := Nat.digits_lt_base (by decide : 1 < 10) (List.mem_reverse.mp member)
  subst unit
  omega

theorem decimal_nonempty {n : Nat} (positive : 0 < n) : decimal n ≠ [] := by
  intro empty
  have hn : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  apply hn
  exact List.reverse_eq_nil_iff.mp (List.map_eq_nil_iff.mp empty)

/-- Recover the suffix after the final separator. Only the suffix is constrained;
the arbitrary prefix may itself contain any number of separators. -/
theorem suffix_scan (sep : Nat) (head tail : List Nat) (absent : sep ∉ tail) :
    ((head ++ [sep] ++ tail).reverse.takeWhile (fun unit => unit != sep)) = tail.reverse := by
  simp only [List.reverse_append,List.reverse_singleton,List.append_assoc]
  rw [List.takeWhile_append_of_pos]
  · simp
  · intro unit member
    have different : unit ≠ sep := by intro equal; exact absent (equal ▸ List.mem_reverse.mp member)
    simpa using different

theorem separated_suffix_injective (sep : Nat) (a b x y : List Nat)
    (hx : sep ∉ x) (hy : sep ∉ y) (same : a ++ [sep] ++ x = b ++ [sep] ++ y) :
    a = b ∧ x = y := by
  have scan := congrArg (fun units : List Nat => units.reverse.takeWhile (fun u => u != sep)) same
  dsimp only at scan
  rw [suffix_scan sep a x hx,suffix_scan sep b y hy] at scan
  have tails : x = y := List.reverse_injective scan
  subst y
  have heads : a ++ [sep] = b ++ [sep] := List.append_cancel_right same
  exact ⟨List.append_cancel_right heads,rfl⟩

/-- Source `${sessionId}-block-${counter}`. -/
def issuedBlock (id : Id) : List Nat := id.session ++ [45,98,108,111,99,107,45] ++ decimal id.counter
/-- Source `${sessionId}:${counter}` used by idKey. -/
def itemKey (id : Id) : List Nat := id.session ++ [58] ++ decimal id.counter

theorem itemKey_injective : Function.Injective itemKey := by
  intro a b same
  have apart : ∀ n, 58 ∉ decimal n := by
    intro n member
    have := decimal_units member
    omega
  obtain ⟨sessions,counters⟩ := separated_suffix_injective 58 a.session b.session
    (decimal a.counter) (decimal b.counter) (apart _) (apart _) same
  have counterEq := decimal_injective counters
  cases a; cases b
  simp_all

theorem issuedBlock_injective : Function.Injective issuedBlock := by
  intro a b same
  have apart : ∀ n, 45 ∉ decimal n := by
    intro n member
    have := decimal_units member
    omega
  have encoded : (a.session ++ [45,98,108,111,99,107]) ++ [45] ++ decimal a.counter =
      (b.session ++ [45,98,108,111,99,107]) ++ [45] ++ decimal b.counter := by
    simpa [issuedBlock,List.append_assoc] using same
  obtain ⟨sessions,counters⟩ := separated_suffix_injective 45 _ _ _ _ (apart _) (apart _) encoded
  have sessionEq := List.append_cancel_right sessions
  have counterEq := decimal_injective counters
  cases a; cases b
  simp_all

/-- Fixed demo bootstrap name `block-A`. -/
def initialBlock : List Nat := [98,108,111,99,107,45,65]

def blockKey : BlockKey → List Nat
  | .initial => initialBlock
  | .issued id => issuedBlock id


def ValidKey : BlockKey → Prop
  | .initial => True
  | .issued id => 0 < id.counter

theorem issued_ne_initial (id : Id) (positive : 0 < id.counter) : issuedBlock id ≠ initialBlock := by
  intro equal
  have nonempty := decimal_nonempty positive
  have last := List.getLast?_eq_some_getLast nonempty
  have equalLast := congrArg List.getLast? equal
  have digit : (decimal id.counter).getLast nonempty = 65 := by
    simpa [issuedBlock,initialBlock,List.getLast?_cons,last] using equalLast
  have bounded := decimal_units (List.getLast_mem nonempty)
  rw [digit] at bounded
  omega

theorem blockKey_injective {a b : BlockKey} (va : ValidKey a) (vb : ValidKey b)
    (same : blockKey a = blockKey b) : a = b := by
  cases a with
  | initial =>
    cases b with
    | initial => rfl
    | issued id => exact False.elim (issued_ne_initial id vb same.symm)
  | issued id =>
    cases b with
    | initial => exact False.elim (issued_ne_initial id va same)
    | issued other => exact congrArg BlockKey.issued (issuedBlock_injective same)

/-- The internal semantic name and the source wire name identify exactly the
same typed key on the source positive-counter domain. Neither is an order map. -/
theorem semantic_name_eq_iff {a b : BlockKey} (va : ValidKey a) (vb : ValidKey b) :
    NotionCoreMachine.blockName a = NotionCoreMachine.blockName b ↔ blockKey a = blockKey b := by
  constructor
  · intro same
    exact congrArg blockKey (NotionCoreMachine.blockName_injective same)
  · intro same
    exact congrArg NotionCoreMachine.blockName (blockKey_injective va vb same)

/-- Literal source label character offsets. All are below '|' (code124). -/
def labelUnits (label : List Nat) : List Nat := label.map (61 + ·)

theorem canonical_nodes {label : List Nat} (canonical : NotionCoreSearchLabels.Canonical label) :
    ∀ node ∈ label, NotionCoreSearchLabels.valid node := by
  induction canonical with
  | nil => simp
  | one n h => simpa using h
  | cons n h full tail ne rest ih =>
    intro node member
    rcases List.mem_cons.mp member with equal | old
    · exact equal ▸ h
    · exact ih node old

theorem label_no_separator {label : List Nat} (canonical : NotionCoreSearchLabels.Canonical label) :
    124 ∉ labelUnits label := by
  intro member
  obtain ⟨node,member,equal⟩ := List.mem_map.mp member
  have bounded := (canonical_nodes canonical node member).1
  omega

/-- Actual `${textInstanceId}|${searchLabel}` mapping key. -/
def mappingKey (key : BlockKey × List Nat) : List Nat :=
  blockKey key.1 ++ [124] ++ labelUnits key.2

theorem mappingKey_injective {a b : BlockKey × List Nat}
    (va : ValidKey a.1) (vb : ValidKey b.1)
    (ca : NotionCoreSearchLabels.Canonical a.2) (cb : NotionCoreSearchLabels.Canonical b.2)
    (same : mappingKey a = mappingKey b) : a = b := by
  obtain ⟨names,labels⟩ := separated_suffix_injective 124 _ _ _ _ (label_no_separator ca) (label_no_separator cb) same
  have keyEq := blockKey_injective va vb names
  have labelEq : a.2 = b.2 := (List.map_inj_right (fun a b h => Nat.add_left_cancel h)).mp labels
  exact Prod.ext keyEq labelEq

theorem mappingKeys_nodup (keys : List (BlockKey × List Nat)) (unique : keys.Nodup)
    (admitted : ∀ key ∈ keys, ValidKey key.1 ∧ NotionCoreSearchLabels.Canonical key.2) :
    (keys.map mappingKey).Nodup := by
  apply List.Nodup.map_on _ unique
  intro a ha b hb same
  exact mappingKey_injective (admitted a ha).1 (admitted b hb).1 (admitted a ha).2 (admitted b hb).2 same

/-- Allocation provenance discharges positive counters for actual archived
creator names; this is not an additional source-client guard. -/
theorem created_key_valid (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network)
    (entry : NotionCorePayloadNetwork.Entry) (archived : entry ∈ network.entries)
    (key : BlockKey) (born : key ∈ NotionCoreCreatorNetwork.createdBlocks entry.tx) : ValidKey key := by
  have positive := NotionCoreReplayGraph.entry_counter_positive reachable entry archived
  cases payload : entry.tx.payload <;>
    simp [NotionCoreCreatorNetwork.createdBlocks,payload] at born
  all_goals subst key
  all_goals simp [ValidKey,positive]

theorem used_key_valid (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network)
    (entry : NotionCorePayloadNetwork.Entry) (archived : entry ∈ network.entries)
    (key : BlockKey) (used : key ∈ NotionCoreMachineCreators.usedBlocks entry.tx) : ValidKey key := by
  rcases List.mem_append.mp used with born | required
  · exact created_key_valid network (NotionCoreCreatorNetwork.payload_reachable reachable) entry archived key born
  · obtain ⟨provider,member,_,born⟩ := NotionCoreCreatorNetwork.creator_provenance reachable entry archived key required
    exact created_key_valid network (NotionCoreCreatorNetwork.payload_reachable reachable) provider member key born

/-- Every actual canonical-prefix stored instance decodes to a source-admitted
positive-counter name (or the fixed bootstrap name). -/
theorem prefix_instance_valid (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (pre suffix : List NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix)
    (state : NotionCoreMachine.State) (accepted : NotionCoreMachine.replay {} pre = some state)
    (inst : Nat) (stored : inst ∈ NotionCoreMachineCreators.instanceKeys state) :
    ∃ key, NotionCoreMachine.blockName key = inst ∧ ValidKey key ∧
      NotionCoreMachineClient.decodeBlock inst = some key := by
  obtain ⟨tx,member,key,used,encoded⟩ := NotionCoreMachineCreators.replay_instance_used pre state accepted inst stored
  obtain ⟨entry,archived,equal,_⟩ := NotionCoreReconstruction.transactionsFor_received network version tx
    (position ▸ List.mem_append_left suffix member)
  have valid := used_key_valid network reachable entry archived key (equal ▸ used)
  refine ⟨key,encoded.symm,valid,?_⟩
  rw [encoded,NotionCoreMachineClient.decode_blockName]

/-- A total projection used only on stored canonical names; the theorem below
proves decodeBlock succeeds, so its default branch is unreachable in scope. -/
def wireMapping (key : Nat × List Nat) : List Nat :=
  mappingKey ((NotionCoreMachineClient.decodeBlock key.1).getD .initial,key.2)

theorem prefix_wire_mapping_unique (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (pre suffix : List NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix)
    (state : NotionCoreMachine.State) (accepted : NotionCoreMachine.replay {} pre = some state)
    (part : NotionCoreMachinePartition.Partitioned state)
    (labels : NotionCoreMachineSearchLabels.Labels)
    (good : NotionCoreMachineSearchLabels.Good (NotionCoreMachineSearchLabels.Starts state.forest) labels)
    (unique : (NotionCoreMachineSearchLabels.mappingKeys state.forest labels).Nodup) :
    ((NotionCoreMachineSearchLabels.mappingKeys state.forest labels).map wireMapping).Nodup := by
  have domain : ∀ pair ∈ NotionCoreMachineSearchLabels.mappingKeys state.forest labels,
      ∃ key, NotionCoreMachine.blockName key = pair.1 ∧ ValidKey key ∧
        NotionCoreMachineClient.decodeBlock pair.1 = some key ∧ NotionCoreSearchLabels.Canonical pair.2 := by
    intro pair hpair
    obtain ⟨owned,ownedMember,equal⟩ := List.mem_map.mp hpair
    subst pair
    obtain ⟨entry,stored,instEq⟩ := part.refsExist owned ownedMember
    have instanceMember : owned.2.start.1 ∈ NotionCoreMachineCreators.instanceKeys state :=
      List.mem_map.mpr ⟨entry,stored,instEq⟩
    obtain ⟨key,encoded,valid,decoded⟩ := prefix_instance_valid network reachable version pre suffix position state accepted _ instanceMember
    exact ⟨key,encoded,valid,decoded,good.1 owned.2.start ⟨owned,ownedMember,rfl⟩⟩
  apply List.Nodup.map_on _ unique
  intro a ha b hb same
  obtain ⟨ka,ea,va,da,ca⟩ := domain a ha
  obtain ⟨kb,eb,vb,db,cb⟩ := domain b hb
  have wireEq : mappingKey (ka,a.2) = mappingKey (kb,b.2) := by simpa [wireMapping,da,db] using same
  have pairEq := mappingKey_injective va vb ca cb wireEq
  have keyEq : ka = kb := (Prod.mk.inj pairEq).1
  have labelEq : a.2 = b.2 := (Prod.mk.inj pairEq).2
  exact Prod.ext (ea.symm.trans ((congrArg NotionCoreMachine.blockName keyEq).trans eb)) labelEq

/-- The source concatenated-string mapping guard is injective over the actual
honest replay labeling, with all positive-counter name guards derived. -/
theorem honest_wire_mapping_guard (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix) :
    ∃ state labels, NotionCoreMachine.replay {} pre = some state ∧
      NotionCoreMachineSearchLabels.LabeledReplay pre state labels ∧
      ((NotionCoreMachineSearchLabels.mappingKeys state.forest labels).map wireMapping).Nodup := by
  obtain ⟨state,labels,accepted,good,unique,labeled⟩ :=
    NotionCoreMachineSearchLabels.honest_mapping_guard network reachable version closed pre suffix position
  obtain ⟨checked,checkedReplay,part,_,_⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version network reachable version closed pre suffix position
  have equal : checked = state := Option.some.inj (checkedReplay.symm.trans accepted)
  subst checked
  exact ⟨state,labels,accepted,labeled,prefix_wire_mapping_unique network
    (NotionCoreMachineNetwork.creator_reachable reachable) version pre suffix position state accepted part labels good unique⟩

namespace SPOT
private def tricky : Id := ⟨12,[65,45,98,108,111,99,107,45,58,124]⟩
private def plain : Id := ⟨12,[65]⟩
/-- Hand-derived names retain arbitrary separator-containing session prefixes.
The final decimal suffix distinguishes identities; labels never contain '|'. -/
theorem names_control :
    issuedBlock tricky = [65,45,98,108,111,99,107,45,58,124,45,98,108,111,99,107,45,49,50] ∧
    itemKey tricky = [65,45,98,108,111,99,107,45,58,124,58,49,50] ∧
    issuedBlock tricky ≠ issuedBlock plain ∧
    mappingKey (.issued tricky,[0,15]) = issuedBlock tricky ++ [124,61,76] ∧
    mappingKey (.issued tricky,[0,15]) ≠ mappingKey (.issued tricky,[15]) := by decide
end SPOT

#print axioms decimal_injective
#print axioms separated_suffix_injective
#print axioms blockKey_injective
#print axioms mappingKey_injective
#print axioms semantic_name_eq_iff
#print axioms prefix_instance_valid
#print axioms honest_wire_mapping_guard
end Sal.MRDTs.Instances.NotionCoreWireNames
