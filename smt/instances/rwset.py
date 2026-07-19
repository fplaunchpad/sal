"""#49 SUCCESS METRIC -- remove-wins set with LCA-GC'd rem-records.

state = a set of tags (ts, elem) each carrying two bits:
  .a  -- an add-record was staked at this tag
  .r  -- a rem-record was staked at this tag
adds and rems are staked by disjoint update ops on the SAME tag space, so both
updates are monotone record insertions => every pair of ops COMMUTES
(all_comm) => CDVC3 discharges via cdVC3_of_all_comm, push-button.

Query (not a VC; documents intent): element e is PRESENT iff some add-tag
(ta,e) is not superseded by a rem-record (tr,e) with tr >= ta  (remove-wins:
a rem beats concurrent/earlier adds; a strictly-later add resurrects).

merge mergeL l a b (the LCA-GC rule):
  adds : grow-only union (LCA-blind).
  rems : keep every rem-record, EXCEPT drop one that is *present in the LCA l*
         and *superseded* (a strictly-later add for the same element exists) --
         such a rem-record can never again change the query, and being in the
         LCA it is causally stable, so dropping it is convergence-safe.
"""
from z3 import (Datatype, IntSort, BoolSort, ArraySort, Store, Select, Lambda,
                And, Or, Not, If, Const, K, IntVal, Exists)
from vcgen import MRDT, Ev, FST, SND, EITHER

_T = Datatype("RwTag")
_T.declare("mk", ("tts", IntSort()), ("tel", IntSort()))
RwTag = _T.create()

_C = Datatype("RwCell")
_C.declare("cell", ("ca", BoolSort()), ("cr", BoolSort()))
RwCell = _C.create()

_O = Datatype("RwOp")
_O.declare("add", ("rae", IntSort()))
_O.declare("rem", ("rre", IntSort()))
RwOp = _O.create()

St = ArraySort(RwTag, RwCell)
EMPTY = K(RwTag, RwCell.cell(False, False))


def _elem(app):
    return If(RwOp.is_add(app), RwOp.rae(app), RwOp.rre(app))


def _update(s, ev):
    tg = RwTag.mk(ev.ts, _elem(ev.app))
    old = Select(s, tg)
    newc = If(RwOp.is_add(ev.app),
              RwCell.cell(True, RwCell.cr(old)),
              RwCell.cell(RwCell.ca(old), True))
    return Store(s, tg, newc)


def _rc(o1, o2):
    return IntVal(EITHER)   # all ops commute


def _dominated(t, l, a, b):
    """A strictly-later add for the same element exists (rem superseded)."""
    t2 = Const("_t2", RwTag)
    return Exists([t2], And(RwTag.tel(t2) == RwTag.tel(t),
                            RwTag.tts(t2) > RwTag.tts(t),
                            Or(RwCell.ca(Select(a, t2)), RwCell.ca(Select(b, t2)),
                               RwCell.ca(Select(l, t2)))))


def _merge_good(l, a, b):
    t = Const("_mt", RwTag)
    A_m = Or(RwCell.ca(Select(a, t)), RwCell.ca(Select(b, t)))
    R_raw = Or(RwCell.cr(Select(a, t)), RwCell.cr(Select(b, t)), RwCell.cr(Select(l, t)))
    R_m = And(R_raw, Not(And(RwCell.cr(Select(l, t)), _dominated(t, l, a, b))))
    return Lambda([t], RwCell.cell(A_m, R_m))


def _merge_eager_gc(l, a, b):
    """KILL 1: GC too eagerly -- drop a superseded rem even when NOT in the LCA."""
    t = Const("_mt", RwTag)
    A_m = Or(RwCell.ca(Select(a, t)), RwCell.ca(Select(b, t)))
    R_raw = Or(RwCell.cr(Select(a, t)), RwCell.cr(Select(b, t)), RwCell.cr(Select(l, t)))
    R_m = And(R_raw, Not(_dominated(t, l, a, b)))           # LCA guard dropped
    return Lambda([t], RwCell.cell(A_m, R_m))


def _merge_addwins(l, a, b):
    """KILL 2: remove-wins/add-wins boundary -- an add-wins-leaning, asymmetric
    merge that lets an add suppress the PEER's rem-record (b's rems are GC'd on
    supersession, a's are always kept).  Non-convergent: order of branches now
    matters, so mergeL is not commutative."""
    t = Const("_mt", RwTag)
    A_m = Or(RwCell.ca(Select(a, t)), RwCell.ca(Select(b, t)))
    # a's rems always survive; b's rems dropped when superseded by any add.
    R_m = Or(RwCell.cr(Select(a, t)),
             And(RwCell.cr(Select(b, t)), Not(_dominated(t, l, a, b))))
    return Lambda([t], RwCell.cell(A_m, R_m))


def _mk(mergeL, name):
    return MRDT(
        name=name,
        new_state=lambda nm: Const(nm, St),
        init=EMPTY,
        AppOp=RwOp,
        new_app=lambda nm: Const(nm, RwOp),
        update=_update,
        mergeL=mergeL,
        rc=_rc,
        rc_is_either=True,
        PointSort=RwTag,
        select=lambda s, p: Select(s, p),
        new_point=lambda nm: Const(nm, RwTag),
        cell_sort=RwCell,
    )


RwSet = _mk(_merge_good, "RwSet")
RwSet_EAGER = _mk(_merge_eager_gc, "RwSet(eager-GC)")
RwSet_ADDWINS = _mk(_merge_addwins, "RwSet(add-wins-tie)")
