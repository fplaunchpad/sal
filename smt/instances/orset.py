"""OR-Set -- the add-wins instance-set with kill sets (non-commuting).

Mirror of `MRDT_Instances/ORSet/ORSet.lean`:
  State = (ts,elem) -> Bool  (a set of tags), init = empty.
  do (add e)@ts s = s with tag (ts,e) staked.
  do (rem e)    s = drop every tag whose element is e.
  mergeL l a b = (l&a&b) | (a&~l) | (b&~l)     -- T8.6 shape.
  rc (add e1)(rem e2) = Snd_then_fst  if e1=e2  (add-wins)
     (rem e1)(add e2) = Fst_then_snd  if e1=e2
     otherwise Either.
Add and Rem on the SAME element do NOT commute -> ORSet is NOT all-commuting,
so its CDVC3 is config-conditioned in Lean (the trichotomy), not push-button.
"""
from z3 import (Int, Datatype, IntSort, BoolSort, ArraySort, Store, Select,
                Lambda, And, Or, Not, If, Const, K, IntVal)
from vcgen import MRDT, Ev, FST, SND, EITHER

# Point = tag (ts, el)
_P = Datatype("Tag")
_P.declare("mk", ("pts", IntSort()), ("pel", IntSort()))
Tag = _P.create()

# AppOp = add(ae) | rem(re)
_O = Datatype("ORSetOp")
_O.declare("add", ("ae", IntSort()))
_O.declare("rem", ("re", IntSort()))
ORSetOp = _O.create()

SetTag = ArraySort(Tag, BoolSort())


def _elem(app):
    return If(ORSetOp.is_add(app), ORSetOp.ae(app), ORSetOp.re(app))


def _update(s, ev):
    t = Const("_t", Tag)
    added = Store(s, Tag.mk(ev.ts, ORSetOp.ae(ev.app)), True)         # stake tag
    removed = Lambda([t], And(Select(s, t), Not(Tag.pel(t) == ORSetOp.re(ev.app))))
    return If(ORSetOp.is_add(ev.app), added, removed)


def _rc(o1, o2):
    a1, a2 = o1.app, o2.app
    return If(And(ORSetOp.is_add(a1), ORSetOp.is_rem(a2)),
              If(ORSetOp.ae(a1) == ORSetOp.re(a2), IntVal(SND), IntVal(EITHER)),
              If(And(ORSetOp.is_rem(a1), ORSetOp.is_add(a2)),
                 If(ORSetOp.re(a1) == ORSetOp.ae(a2), IntVal(FST), IntVal(EITHER)),
                 IntVal(EITHER)))


def _mk(mergeL):
    return MRDT(
        name="ORSet",
        new_state=lambda nm: Const(nm, SetTag),
        init=K(Tag, False),
        AppOp=ORSetOp,
        new_app=lambda nm: Const(nm, ORSetOp),
        update=_update,
        mergeL=mergeL,
        rc=_rc,
        rc_is_either=False,
        PointSort=Tag,
        select=lambda s, p: Select(s, p),
        new_point=lambda nm: Const(nm, Tag),
    )


def _merge_good(l, a, b):
    t = Const("_mt", Tag)
    return Lambda([t], Or(And(Select(l, t), Select(a, t), Select(b, t)),
                          And(Select(a, t), Not(Select(l, t))),
                          And(Select(b, t), Not(Select(l, t)))))


def _merge_no_lsub(l, a, b):
    # MUTATION: drop the ~l guard on the b term (a removed tag can revive).
    t = Const("_mt", Tag)
    return Lambda([t], Or(And(Select(l, t), Select(a, t), Select(b, t)),
                          And(Select(a, t), Not(Select(l, t))),
                          Select(b, t)))


ORSet = _mk(_merge_good)
ORSet_BAD = _mk(_merge_no_lsub)
ORSet_BAD.name = "ORSet(no-L-sub)"
