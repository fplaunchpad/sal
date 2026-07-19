"""LWW register -- last-writer-wins by lex (ts, rep, val) with a bottom.

Mirror of `MRDT_Instances/LWWRegister/LWWRegister.lean`:
  State = WithBot (Lex (ts, rep, val)), init = bottom.
  do s (write v)@(ts,rep) = max s (ts,rep,v).
  mergeL _ a b = max a b   (the state only moves up; LCA redundant).
  rc = Either, all ops commute.  Arbitration lives entirely in the payload.
"""
from z3 import Datatype, IntSort, If, And, Or, Not, Const, IntVal
from vcgen import MRDT, Ev, EITHER

# State = Bot | W(wts, wrep, wval)
_S = Datatype("LWWState")
_S.declare("bot")
_S.declare("w", ("wts", IntSort()), ("wrep", IntSort()), ("wval", IntSort()))
LWWState = _S.create()

# AppOp = write(v)
_O = Datatype("LWWOp")
_O.declare("write", ("wv", IntSort()))
LWWOp = _O.create()


def _le(x, y):
    """Lex total order (ts, rep, val) with bottom least. Reflexive."""
    lex = Or(LWWState.wts(x) < LWWState.wts(y),
             And(LWWState.wts(x) == LWWState.wts(y),
                 Or(LWWState.wrep(x) < LWWState.wrep(y),
                    And(LWWState.wrep(x) == LWWState.wrep(y),
                        LWWState.wval(x) <= LWWState.wval(y)))))
    return If(LWWState.is_bot(x), True,
              If(LWWState.is_bot(y), False, lex))


def _mx_good(x, y):
    return If(_le(x, y), y, x)


def _mx_bad(x, y):
    # MUTATION: arbitrate on timestamp only, ties -> first argument (not a
    # symmetric total order) -- "comparing with <= on ts instead of the full
    # lex order".  Breaks commutativity on equal-ts concurrent writes.
    return If(Or(LWWState.is_bot(y),
                 And(Not(LWWState.is_bot(x)),
                     LWWState.wts(x) >= LWWState.wts(y))),
              x, y)


def _mk(mx):
    return MRDT(
        name="LWW",
        new_state=lambda nm: Const(nm, LWWState),
        init=LWWState.bot,
        AppOp=LWWOp,
        new_app=lambda nm: Const(nm, LWWOp),
        update=lambda s, ev: mx(s, LWWState.w(ev.ts, ev.rep, LWWOp.wv(ev.app))),
        mergeL=lambda l, a, b: mx(a, b),
        rc=lambda o1, o2: IntVal(EITHER),
        rc_is_either=True,
    )


LWW = _mk(_mx_good)
LWW_BAD = _mk(_mx_bad)
LWW_BAD.name = "LWW(ts-only,tie->first)"
