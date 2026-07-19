"""G-Set -- the grow-only set (lattice) calibration instance.

Mirror of `Framework/Sigma_LoOn3.lean` (GSet) and `MRDT_Instances/GSet/GSet.lean`:
  State = Set Nat, init = empty, update s o = insert (elem o) s,
  mergeL l a b = a union b   (LCA-blind), rc = Either, all ops commute.
"""
from z3 import (Int, Datatype, IntSort, BoolSort, ArraySort, Store, Select,
                EmptySet, SetUnion, SetIntersect, Const)
from vcgen import MRDT, Ev, EITHER

# AppOp = Ins(el : Int)  -- the app-op *is* the element (Lean: AppOp = Nat).
_G = Datatype("GSetOp")
_G.declare("ins", ("el", IntSort()))
GSetOp = _G.create()

SetInt = ArraySort(IntSort(), BoolSort())


def _gset(mergeL):
    return MRDT(
        name="GSet",
        new_state=lambda nm: Const(nm, SetInt),
        init=EmptySet(IntSort()),
        AppOp=GSetOp,
        new_app=lambda nm: Const(nm, GSetOp),
        update=lambda s, ev: Store(s, GSetOp.el(ev.app), True),
        mergeL=mergeL,
        rc=lambda o1, o2: __import__("z3").IntVal(EITHER),
        rc_is_either=True,
        PointSort=IntSort(),
        select=lambda s, p: Select(s, p),
        new_point=lambda nm: Int(nm),
    )


GSet = _gset(lambda l, a, b: SetUnion(a, b))
# MUTATION: merge projects to the first branch (drops the other side's inserts).
GSet_BAD = _gset(lambda l, a, b: a)
GSet_BAD.name = "GSet(proj-a)"
