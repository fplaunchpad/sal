"""vcgen.py -- SMT translator for the flat-MRDT verification conditions.

Translation-validation layer for task #99 / #49.  The Lean metatheory
(`Sal/ConditionedMRDTs/**`) stays the source of truth; this module discharges,
per flat instance, the eight verification conditions that the flat capstone
`flat_ra_linearizable3_eq` consumes, by reduction to SMT queries.

The eight VCs (see `Framework/VC_Set.lean`, `Framework/Sigma_LoOn3.lean`):

  UpdateVCs (3):  rc_non_comm_directional, no_rc_chain, cond_comm_lift
  CoreVCs3CD:     mergeL_comm
  FeasibleDelta3: feasible_init, feasible_local_redistribute, feasible_redistribute
  CDVC3:          the ternary causal-delta bound

Discharge forms actually proved by the Lean instances (unconditional algebraic
laws that IMPLY the config-conditioned VCs via the reduction lemmas in
`Metatheory/Adequacy.lean`):

  feasible_init            <-  mergeL_init:         mergeL init init s = s
  feasible_local_redist    <-  local_redistribute
  feasible_redistribute    <-  redistribute
  CDVC3 (commuting class)  <-  all_comm  (cdVC3_of_all_comm)

Op = (ts:Int, rep:Int, appop:AppOp).  commutes o1 o2 := forall s. do o2 (do o1 s)
= do o1 (do o2 s).  distinctOps := ts1 != ts2.  differentReplicas := rep1 != rep2.
"""
from dataclasses import dataclass, field
from typing import Callable, Optional, Any
import time
from z3 import (Int, Const, Function, BoolSort, IntSort, ForAll, Exists, Not,
                And, Or, Implies, Solver, sat, unsat, Lambda, Select, ExprRef,
                SortRef, DatatypeSortRef)

# RcRes encoded as an Int enum, matching Base/CRDT_Signature.lean.
FST, SND, EITHER = 0, 1, 2   # Fst_then_snd, Snd_then_fst, Either


@dataclass
class Ev:
    """An event = Op AppOp = (timestamp, replica, app-op)."""
    ts: ExprRef
    rep: ExprRef
    app: ExprRef


@dataclass
class MRDT:
    """A flat MRDT signature, expressed as SMT terms.

    state_sort/new_state : how to make a fresh symbolic state constant.
    init                 : the initial state (Z3 term of the state sort).
    AppOp                : Z3 datatype sort for the abstract op; new_app makes a const.
    update(state, Ev)    : do_  (Z3 term).
    mergeL(l,a,b)        : ternary merge (Z3 term).
    rc(Ev, Ev)           : RcRes as an Int term (FST/SND/EITHER).
    rc_is_either         : fast-path flag; True when rc == Either everywhere.
    PointSort/select     : pointwise reader for set-shaped states (enables the
                           sound fold abstraction used by cond_comm_lift).
    """
    name: str
    new_state: Callable[[str], ExprRef]
    init: ExprRef
    AppOp: DatatypeSortRef
    new_app: Callable[[str], ExprRef]
    update: Callable[[ExprRef, Ev], ExprRef]
    mergeL: Callable[[ExprRef, ExprRef, ExprRef], ExprRef]
    rc: Callable[[Ev, Ev], ExprRef]
    rc_is_either: bool = False
    PointSort: Optional[SortRef] = None
    select: Optional[Callable[[ExprRef, ExprRef], ExprRef]] = None
    new_point: Optional[Callable[[str], ExprRef]] = None
    cell_sort: Optional[SortRef] = None   # codomain of a set/map state array

    def new_ev(self, nm: str) -> Ev:
        return Ev(Int(nm + "_ts"), Int(nm + "_rep"), self.new_app(nm + "_app"))


# --- extensional / pointwise helpers ---------------------------------------
# For set-shaped states (PointSort given) we reason POINTWISE at a symbolic
# point p -- exactly the `funext t; cases ...` shape of the Lean proofs -- which
# keeps every query quantifier-free (or, for commutation, a tiny Bool*Point
# quantifier) and avoids extensional array reasoning over Lambda-defined merges.
from z3 import K, Bool


def sneq(m: MRDT, lhs: ExprRef, rhs: ExprRef) -> ExprRef:
    """Formula asserting lhs != rhs (state disequality); pointwise for sets."""
    if m.PointSort is None:
        return lhs != rhs
    p = m.new_point("_p")
    return m.select(lhs, p) != m.select(rhs, p)


def _cell_sort(m: MRDT):
    return m.cell_sort if m.cell_sort is not None else BoolSort()


def _upd_at(m: MRDT, v: ExprRef, o: Ev, p: ExprRef) -> ExprRef:
    """New cell value at point p after `do o` on a state whose cell p is v.
    Justified by update-locality (checked by `update_pointwise`)."""
    return m.select(m.update(K(m.PointSort, v), o), p)


def commute_neg(m: MRDT, o1: Ev, o2: Ev) -> ExprRef:
    """A witness that o1, o2 do NOT commute (free constants; no quantifier).
    Uses a free witness state + point for set-states (a model is exhibited)."""
    if m.PointSort is None:
        s = m.new_state("_cs")
        return m.update(m.update(s, o1), o2) != m.update(m.update(s, o2), o1)
    s, p = m.new_state("_cs"), m.new_point("_cp")
    return m.select(m.update(m.update(s, o1), o2), p) != \
        m.select(m.update(m.update(s, o2), o1), p)


def commute_all(m: MRDT, o1: Ev, o2: Ev) -> ExprRef:
    """`commutes o1 o2` = forall states. (positive; used only where forced)."""
    if m.PointSort is None:
        s = m.new_state("_cs")
        return ForAll([s], m.update(m.update(s, o1), o2)
                      == m.update(m.update(s, o2), o1))
    v, p = Const("_v", _cell_sort(m)), m.new_point("_cp")
    return ForAll([v, p], _upd_at(m, _upd_at(m, v, o1, p), o2, p)
                  == _upd_at(m, _upd_at(m, v, o2, p), o1, p))


def distinct(o1: Ev, o2: Ev) -> ExprRef:
    return o1.ts != o2.ts


def diff_rep(o1: Ev, o2: Ev) -> ExprRef:
    return o1.rep != o2.rep


# --- the VC encoders -------------------------------------------------------
# Each returns a list of Query(name, goal, negation, quantified).  We prove the
# VC by asserting `negation` and checking UNSAT.

@dataclass
class Query:
    vc: str            # the VC name
    sub: str           # sub-query label
    negation: ExprRef  # assert this; UNSAT => VC valid
    quantified: bool    # does the encoding contain a genuine quantifier?


def q_mergeL_comm(m: MRDT):
    l, a, b = m.new_state("l"), m.new_state("a"), m.new_state("b")
    return [Query("mergeL_comm", "-", sneq(m, m.mergeL(l, a, b),
                                          m.mergeL(l, b, a)), False)]


def q_feasible_init(m: MRDT):
    # feasible_init  <-  mergeL_init : mergeL init init s = s
    s = m.new_state("s")
    return [Query("feasible_init", "mergeL_init",
                  sneq(m, m.mergeL(m.init, m.init, s), s), False)]


def q_feasible_redistribute(m: MRDT):
    mm, x0, x1, x2, c = (m.new_state("m"), m.new_state("x0"), m.new_state("x1"),
                         m.new_state("x2"), m.new_state("c"))
    lhs = m.mergeL(m.mergeL(mm, x0, c), m.mergeL(mm, x1, c), m.mergeL(mm, x2, c))
    rhs = m.mergeL(mm, m.mergeL(x0, x1, x2), c)
    return [Query("feasible_redistribute", "redistribute", sneq(m, lhs, rhs), False)]


def q_feasible_local_redistribute(m: MRDT):
    l, mm, x, c, y = (m.new_state("l"), m.new_state("m"), m.new_state("x"),
                      m.new_state("c"), m.new_state("y"))
    lhs = m.mergeL(l, m.mergeL(mm, x, c), y)
    rhs = m.mergeL(mm, m.mergeL(l, x, y), c)
    return [Query("feasible_local_redistribute", "local_redistribute",
                  sneq(m, lhs, rhs), False)]


def q_no_rc_chain(m: MRDT):
    o1, o2, o3 = m.new_ev("p"), m.new_ev("q"), m.new_ev("r")
    neg = And(distinct(o1, o2), distinct(o2, o3),
              m.rc(o1, o2) == FST, m.rc(o2, o3) == FST)
    return [Query("no_rc_chain", "-", neg, False)]


def q_rc_non_comm_directional(m: MRDT):
    # VC:  distinct & diff_rep  ->  (~commutes  <->  rc-edge)
    # Two directions, split so that only the "overspec" arm needs a quantifier.
    o1, o2 = m.new_ev("o1"), m.new_ev("o2")
    edge = Or(m.rc(o1, o2) == FST, m.rc(o2, o1) == FST)
    guard = And(distinct(o1, o2), diff_rep(o1, o2))
    # underspec: a non-commuting witness with NO rc edge  (QF)
    under = And(guard, commute_neg(m, o1, o2), Not(edge))
    # overspec: an rc edge but the pair actually commutes (forall states)
    over = And(guard, edge, commute_all(m, o1, o2))
    return [Query("rc_non_comm_directional", "underspec(~comm->edge)", under, False),
            Query("rc_non_comm_directional", "overspec(edge->~comm)", over, True)]


def q_cond_comm_lift(m: MRDT):
    # cond_comm_lift: rc e e' = Fst & ~commutes e' e'' =>
    #   do e'' (fold pi (do e (do e' s))) = do e'' (fold pi (do e' (do e s)))
    e, e2, e3 = m.new_ev("e"), m.new_ev("e2"), m.new_ev("e3")
    if m.rc_is_either:
        # Premise rc e e' = Fst is unsatisfiable => VC vacuously valid.  QF.
        neg = And(distinct(e, e2), distinct(e, e3), distinct(e2, e3),
                  m.rc(e, e2) == FST)
        return [Query("cond_comm_lift", "rc-Either-vacuous", neg, False)]
    # General set-shaped case: sound pointwise-fold abstraction.
    assert m.PointSort is not None and m.select is not None, \
        "cond_comm_lift on a non-Either instance needs a pointwise set state"
    s = m.new_state("s")
    foldp = Function("foldp", BoolSort(), m.PointSort, BoolSort())
    p = m.new_point("p")
    X = m.update(m.update(s, e2), e)     # do e (do e' s)
    Y = m.update(m.update(s, e), e2)     # do e' (do e s)
    foldX = Lambda([p], foldp(m.select(X, p), p))
    foldY = Lambda([p], foldp(m.select(Y, p), p))
    lhs = m.update(foldX, e3)
    rhs = m.update(foldY, e3)
    ncomm = commute_neg(m, e2, e3)       # ~commutes e' e''
    neg = And(distinct(e, e2), distinct(e, e3), distinct(e2, e3),
              m.rc(e, e2) == FST, ncomm, sneq(m, lhs, rhs))
    # foldp is a *free* function: UNSAT means the law holds for every pointwise
    # fold, hence for the real applySeq.  (Soundness side-check: update_pointwise.)
    return [Query("cond_comm_lift", "fold-abstraction", neg, False)]


def q_cdvc3_via_allcomm(m: MRDT):
    # CDVC3 is discharged for the commuting class via cdVC3_of_all_comm.
    # Sufficient condition: all_comm  (forall o1 o2 states. commute).
    o1, o2 = m.new_ev("c1"), m.new_ev("c2")
    return [Query("CDVC3", "via-all_comm", commute_neg(m, o1, o2), False)]


ALL_VCS = [q_rc_non_comm_directional, q_no_rc_chain, q_cond_comm_lift,
           q_mergeL_comm, q_feasible_init, q_feasible_local_redistribute,
           q_feasible_redistribute, q_cdvc3_via_allcomm]


def update_pointwise_ok(m: MRDT):
    """Soundness side-check for the fold abstraction: `update` is pointwise."""
    if m.PointSort is None:
        return None
    s, s2 = m.new_state("s"), m.new_state("s2")
    o = m.new_ev("o")
    p = m.new_point("p")
    neg = And(m.select(s, p) == m.select(s2, p),
              m.select(m.update(s, o), p) != m.select(m.update(s2, o), p))
    return Query("update_pointwise", "soundness", neg, False)


def run_query(qy: Query, timeout_ms: int = 10000):
    """Return (result, model_str, elapsed_s).  result in
    unsat / sat / timeout / unknown (unknown = solver incompleteness, NOT a
    wall-clock timeout -- reported honestly and distinctly)."""
    sv = Solver()
    sv.set("timeout", timeout_ms)
    sv.add(qy.negation)
    t0 = time.time()
    r = sv.check()
    dt = time.time() - t0
    if r == unsat:
        return ("unsat", None, dt)
    if r == sat:
        return ("sat", str(sv.model()), dt)
    reason = sv.reason_unknown()
    if "timeout" in reason or "canceled" in reason:
        return ("timeout", reason, dt)
    return ("unknown", reason, dt)
