import CaseStudies.Neem_interfaces.Set_extended
import Blaster


structure map (key:Type) [DecidableEq key] (value:Type) where
(mappings: key → value) (domain: set key)

#check map.domain

@[simp, grind]
def sel {key:Type} [DecidableEq key] {value: Type} (m: map key value) (k:key)
:=
m.mappings k

@[simp, grind]
def upd {key:Type} [DecidableEq key] {value: Type} (m: map key value) (k:key) (v:value)
:=
map.mk (fun x => if x = k then v else m.mappings x) (union (m.domain) (singleton k))

@[simp, grind]
def const {key:Type} [DecidableEq key] {value: Type} (v:value) : map key value
:=
map.mk (fun _ => v) (complement empty)

@[simp, grind]
def domain {key:Type} [DecidableEq key] {value: Type} (m: map key value) := m.domain

@[simp, grind]
def del {key:Type} [DecidableEq key] {value: Type} (m: map key value) (k: key) :=
map.mk (fun x => m.mappings x) (remove (domain m) k)

@[simp, grind]
def contains {key:Type} [DecidableEq key] {value: Type} (m: map key value) (k: key)
:=
mem k m.domain

@[simp, grind]
def concat {key:Type} [DecidableEq key] {value: Type} (m1: map key value) (m2: map key value)
:=
map.mk (fun x => if mem x (m2.domain) then m2.mappings x else m1.mappings x) (union (m1.domain) (m2.domain))

@[simp, grind]
def map_val {val1: Type} {val2: Type} (f: val1 → val2) {key:Type} [DecidableEq key] (m: map key val1) : map key val2 :=
map.mk (fun x => f (m.mappings x)) (m.domain)

@[simp, grind]
def iter_upd {key:Type} [DecidableEq key] {val1: Type} {val2: Type} (f:key → val1 → val2) (m: map key val1): map key val2 :=
map.mk (fun x => f x (m.mappings x)) (m.domain)

@[simp, grind]
def restrict {key:Type} [DecidableEq key] {value: Type} (s: set key) (m: map key value): map key value :=
map.mk (m.mappings) (intersection s m.domain)

@[simp, grind]
def const_on {key:Type} [DecidableEq key] {value: Type} (dom: set key) (v: value) : map key value :=
restrict dom (const v)

@[simp, grind]
def disjoint_dom {key: Type} [DecidableEq key] {value:Type} (m1: map key value) (m2: map key value) :=
forall x, contains m1 x → not (contains m2 x)

@[simp, grind]
def has_dom {key: Type} [DecidableEq key] {value:Type} (m: map key value) (dom: set key) :=
forall x, contains m x ↔ mem x dom


@[simp, grind?]
lemma lemma_SelUpd1 {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k:key) (v:value)
: sel (upd m k v) k = v
:= by
simp

@[simp, grind?]
lemma lemma_SelUpd2 {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k1:key) (k2: key) (v:value) :
k2 != k1 → sel (upd m k2 v) k1 = sel m k1
:= by
simp
grind

@[simp, grind?]
lemma lemma_SelConst {key: Type} [DecidableEq key] {value:Type} (v: value) (k: key) :
sel (const v) k = v := by simp

@[simp, grind?]
lemma lemma_SelRestrict  {key: Type} [DecidableEq key] {value:Type} (m: map key value) (ks: set key) (k: key):
sel (restrict ks m) k = sel m k := by simp

@[simp, grind?]
lemma lemma_SelConcat1 {key: Type} [DecidableEq key] {value:Type} (m1: map key value) (m2: map key value) (k: key):
contains m2 k →  sel (concat m1 m2) k = sel m2 k := by
simp
grind

@[simp, grind?]
lemma lemma_SelConcat2 {key: Type} [DecidableEq key] {value:Type} (m1: map key value) (m2: map key value) (k: key):
not (contains m2 k) → sel (concat m1 m2) k = sel m1 k := by
simp
grind

@[simp, grind?]
lemma lemma_SelMapVal {val1: Type} {val2: Type} (f:val1 → val2) {key: Type} [DecidableEq key] (m: map key val1) (k:key) :
sel (map_val f m) k = f (sel m k) := by simp

@[simp, grind?]
lemma lemma_IterUpd {key:Type} [DecidableEq key] {val1: Type} {val2: Type} (f:key → val1 → val2) (m: map key val1) (k:key):
sel (iter_upd f m) k = f k (sel m k) := by simp

@[simp, grind?]
lemma lemma_InDomUpd1 {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k1 k2: key) (v: value) :
contains (upd m k1 v) k2 = (k1=k2 || contains m k2) := by
simp
grind

@[simp, grind?]
lemma lemma_InDomUpd2 {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k1 k2: key) (v: value) :
(k2 != k1 → contains (upd m k2 v) k1 = contains m k1) := by
simp
grind

@[simp, grind?]
lemma lemma_InDomConstMap {key: Type} [DecidableEq key] {value: Type} (v: value) (k: key) :
contains (const v) k := by simp

@[simp, grind?]
lemma lemma_InDomConcat {key: Type} [DecidableEq key] {value: Type} (m1: map key value) (m2: map key value) (k: key) :
contains (concat m1 m2) k = (contains m1 k || contains m2 k) := by simp

@[simp, grind?]
lemma lemma_InMapVal {val1: Type} {val2: Type} (f: val1 → val2) {key:Type} [DecidableEq key] (m: map key val1) (k: key) :
contains (map_val f m) k == contains m k := by simp

@[simp, grind?]
lemma lemma_InIterUpd {key:Type} [DecidableEq key] {val1: Type} {val2: Type} (f:key → val1 → val2) (m: map key val1) (k:key):
contains (iter_upd f m) k == contains m k := by simp

@[simp, grind?]
lemma lemma_InDomRestrict {key: Type} [DecidableEq key] {value:Type} (m: map key value) (ks: set key) (k: key) :
contains (restrict ks m) k == (mem k ks && contains m k) := by simp

@[simp, grind?]
lemma lemma_ContainsDom {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k: key) :
contains m k = mem k (domain m) := by
simp

@[simp, grind?]
lemma lemma_UpdDomain {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k: key) (v: value) :
equal (domain (upd m k v)) (union (domain m) (singleton k)) := by simp

@[simp]
def map_equal {key: Type} [DecidableEq key] {value: Type} (m1: map key value) (m2: map key value) := m1 = m2

@[simp, grind?]
theorem map_lemma_equal_intro  {key: Type} [DecidableEq key] {value: Type} (m1: map key value) (m2: map key value)  :
(forall k:key, sel m1 k = sel m2 k ∧ contains m1 k = contains m2 k) ↔ map_equal m1 m2 :=
by
simp
cases m1
cases m2
aesop

@[simp]
theorem map_lemma_equal_elim {key: Type} [DecidableEq key] {value: Type} (m1: map key value) (m2: map key value) :
map_equal m1 m2 ↔ m1 = m2 := by simp
