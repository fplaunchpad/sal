"""#49 REPAIR -- remove-wins set, rem-records compacted to per-element max-ts.

The literal SET + LCA-conditioned-supersession design (`rwset.py`) fails the
delta laws (feasible_redistribute / feasible_local_redistribute come back SAT):
the LCA-conditioned drop is order-sensitive, so mergeL is not a convergent
semilattice.  Minimal repair the loop forces: normalise the rem-records to the
per-element MAXIMUM timestamp (the fully-GC'd normal form -- a rem-record
superseded by a higher one for the same element is intrinsically absent), and
do the same for adds.  merge becomes a product of two max-semilattices, LCA-
blind, hence the delta laws hold UNCONDITIONALLY and all eight VCs discharge.

Semantics preserved exactly: element e is present iff maxAdd(e) > maxRem(e)
(strict => remove-wins on ties; a strictly-later add resurrects).

state = Elem -> (mAdd : max-add-ts, mRem : max-rem-ts)   with a bottom.
"""
from z3 import (Datatype, IntSort, BoolSort, ArraySort, Store, Select, Lambda,
                And, Or, Not, If, Const, K, IntVal)
from vcgen import MRDT, Ev, EITHER

# RBot = bot | rv(Int)  -- max timestamp with a least element (matches LWW).
_R = Datatype("RBot")
_R.declare("bot")
_R.declare("rv", ("rvv", IntSort()))
RBot = _R.create()

# RPair = (mAdd, mRem) per element.
_P = Datatype("RPair")
_P.declare("rpair", ("mAdd", RBot), ("mRem", RBot))
RPair = _P.create()

_O = Datatype("RwCOp")
_O.declare("add", ("cae", IntSort()))
_O.declare("rem", ("cre", IntSort()))
RwCOp = _O.create()

St = ArraySort(IntSort(), RPair)          # element -> RPair
EMPTY = K(IntSort(), RPair.rpair(RBot.bot, RBot.bot))


def _maxRB(x, y):
    return If(RBot.is_bot(x), y,
              If(RBot.is_bot(y), x,
                 If(RBot.rvv(x) >= RBot.rvv(y), x, y)))


def _elem(app):
    return If(RwCOp.is_add(app), RwCOp.cae(app), RwCOp.cre(app))


def _update(s, ev):
    e = _elem(ev.app)
    old = Select(s, e)
    newp = If(RwCOp.is_add(ev.app),
              RPair.rpair(_maxRB(RPair.mAdd(old), RBot.rv(ev.ts)), RPair.mRem(old)),
              RPair.rpair(RPair.mAdd(old), _maxRB(RPair.mRem(old), RBot.rv(ev.ts))))
    return Store(s, e, newp)


def _mk(mergeL, name):
    return MRDT(
        name=name,
        new_state=lambda nm: Const(nm, St),
        init=EMPTY,
        AppOp=RwCOp,
        new_app=lambda nm: Const(nm, RwCOp),
        update=_update,
        mergeL=mergeL,
        rc=lambda o1, o2: IntVal(EITHER),
        rc_is_either=True,
        PointSort=IntSort(),
        select=lambda s, p: Select(s, p),
        new_point=lambda nm: Const(nm, IntSort()),
        cell_sort=RPair,
    )


def _merge_good(l, a, b):
    e = Const("_e", IntSort())
    return Lambda([e], RPair.rpair(
        _maxRB(RPair.mAdd(Select(a, e)), RPair.mAdd(Select(b, e))),
        _maxRB(RPair.mRem(Select(a, e)), RPair.mRem(Select(b, e)))))


def _merge_min_rem(l, a, b):
    """KILL (compacted analogue of eager-GC): MIN the rem-ts on merge -- loses a
    higher remove, so it is not the join; breaks mergeL_init and idempotence."""
    e = Const("_e", IntSort())
    minRB = lambda x, y: If(RBot.is_bot(x), RBot.bot,
                            If(RBot.is_bot(y), RBot.bot,
                               If(RBot.rvv(x) <= RBot.rvv(y), x, y)))
    return Lambda([e], RPair.rpair(
        _maxRB(RPair.mAdd(Select(a, e)), RPair.mAdd(Select(b, e))),
        minRB(RPair.mRem(Select(a, e)), RPair.mRem(Select(b, e)))))


RwSetC = _mk(_merge_good, "RwSetC(compacted)")
RwSetC_MIN = _mk(_merge_min_rem, "RwSetC(min-rem)")
