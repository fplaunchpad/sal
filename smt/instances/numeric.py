"""Counter and PN-Counter -- the numeric (group) calibration instances.

Mirror of `MRDT_Instances/Counter/Counter.lean` and `PN/PN.lean`:
  State = Int, init = 0, mergeL l a b = a + b - l   (the LCA cancels the
  double-count), rc = Either, all ops commute.
"""
from z3 import Int, IntVal, Datatype, IntSort
from vcgen import MRDT, Ev, FST, SND, EITHER

# ---- Counter : AppOp = {inc} -------------------------------------------------
_CInc = Datatype("CounterOp")
_CInc.declare("inc")
CounterOp = _CInc.create()


def _counter(mergeL):
    return MRDT(
        name="Counter",
        new_state=lambda nm: Int(nm),
        init=IntVal(0),
        AppOp=CounterOp,
        new_app=lambda nm: CounterOp.inc,
        update=lambda s, ev: s + 1,
        mergeL=mergeL,
        rc=lambda o1, o2: IntVal(EITHER),
        rc_is_either=True,
    )


Counter = _counter(lambda l, a, b: a + b - l)
# MUTATION: drop the LCA subtraction (double-counts on merge).
Counter_BAD = _counter(lambda l, a, b: a + b)
Counter_BAD.name = "Counter(no-LCA-sub)"


# ---- PN-Counter : AppOp = {inc, dec} ----------------------------------------
_PN = Datatype("PNOp")
_PN.declare("inc")
_PN.declare("dec")
PNOp = _PN.create()


def _pn_update(s, ev):
    from z3 import If
    return If(PNOp.is_inc(ev.app), s + 1, s - 1)


def _pn(mergeL):
    return MRDT(
        name="PN",
        new_state=lambda nm: Int(nm),
        init=IntVal(0),
        AppOp=PNOp,
        new_app=lambda nm: __import__("z3").Const(nm, PNOp),
        update=_pn_update,
        mergeL=mergeL,
        rc=lambda o1, o2: IntVal(EITHER),
        rc_is_either=True,
    )


PN = _pn(lambda l, a, b: a + b - l)
# MUTATION: max-ing the branches instead of the group merge (loses decrements /
# double counts) -- breaks the delta laws for a non-idempotent state.
PN_BAD = _pn(lambda l, a, b: __import__("z3").If(a >= b, a, b))
PN_BAD.name = "PN(max-merge)"
