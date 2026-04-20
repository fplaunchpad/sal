import CaseStudies.Interfaces.Set_extended
import Blaster


structure map (key:Type) [DecidableEq key] (value:Type) where
(mappings: key → value) (domain: Set key)

#check map.domain

@[simp, grind]
def sel {key:Type} [DecidableEq key] {value: Type} (m: map key value) (k:key)
:=
m.mappings k

@[simp, grind]
def upd {key:Type} [DecidableEq key] {value: Type} (m: map key value) (k:key) (v:value)
:=
map.mk (fun (x : key) => if x = k then v else m.mappings x) ((m.domain) ∪ {k})

@[simp, grind]
def const {key:Type} [DecidableEq key] {value: Type} (v:value) : map key value
:=
map.mk (fun _ => v) ({}ᶜ)

@[simp, grind]
def domain {key:Type} [DecidableEq key] {value: Type} (m: map key value) := m.domain

@[simp, grind]
def del {key:Type} [DecidableEq key] {value: Type} (m: map key value) (k: key) :=
map.mk (fun x => m.mappings x) ( (domain m) \ {k})

@[simp, grind]
def contains {key:Type} [DecidableEq key] {value: Type} (m: map key value) (k: key)
:=
k ∈ m.domain

@[simp, grind]
def map_val {val1: Type} {val2: Type} (f: val1 → val2) {key:Type} [DecidableEq key] (m: map key val1) : map key val2 :=
map.mk (fun x => f (m.mappings x)) (m.domain)

@[simp, grind]
def iter_upd {key:Type} [DecidableEq key] {val1: Type} {val2: Type} (f:key → val1 → val2) (m: map key val1): map key val2 :=
map.mk (fun x => f x (m.mappings x)) (m.domain)

@[simp, grind]
def restrict {key:Type} [DecidableEq key] {value: Type} (s: Set key) (m: map key value): map key value :=
map.mk (m.mappings) (s ∩ m.domain)

@[simp, grind]
def const_on {key:Type} [DecidableEq key] {value: Type} (dom: Set key) (v: value) : map key value :=
restrict dom (const v)


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
lemma lemma_SelRestrict  {key: Type} [DecidableEq key] {value:Type} (m: map key value) (ks: Set key) (k: key):
sel (restrict ks m) k = sel m k := by simp


@[simp, grind?]
lemma lemma_SelMapVal {val1: Type} {val2: Type} (f:val1 → val2) {key: Type} [DecidableEq key] (m: map key val1) (k:key) :
sel (map_val f m) k = f (sel m k) := by simp

@[simp, grind?]
lemma lemma_IterUpd {key:Type} [DecidableEq key] {val1: Type} {val2: Type} (f:key → val1 → val2) (m: map key val1) (k:key):
sel (iter_upd f m) k = f k (sel m k) := by simp



@[simp, grind?]
lemma lemma_InDomUpd2 {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k1 k2: key) (v: value) :
(k2 != k1 → contains (upd m k2 v) k1 = contains m k1) := by
simp
grind

@[simp, grind?]
lemma lemma_InDomConstMap {key: Type} [DecidableEq key] {value: Type} (v: value) (k: key) :
contains (const v) k := by simp
