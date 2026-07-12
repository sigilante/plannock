"""nockplan — a PLAN evaluator expressed as a Nock 4K noun.

Falsification target: the claim "Nock cannot implement PLAN."

Architecture
------------
  * Host machine: pinochle's Nock 4K interpreter (unmodified).
  * This module builds a single Nock *core* — a noun [battery sample] in
    the classic Hoon layout — whose battery arms implement the PLAN spec
    judgments: E, A, X, S, C, R, L, B, I, N, F, plus nat arithmetic
    helpers (Nock has increment only; dec/add/sub/mul/lte are loops).
  * PLAN values are encoded as tagged nouns:
        nat n         [0 n]
        pin <i>       [1 i]
        law {m a b}   [2 name arity body]     (name/arity raw atoms)
        app (f x)     [3 f x]
        hole <>       [4 0]
  * Oracle: marduk's spec-faithful Python runtime. The test harness
    encodes marduk Vals to nouns, evaluates in Nock, decodes, compares.

Declared semantic deltas vs marduk (all analyzed up front):
  1. No update-in-place => no memoization/sharing. Performance-only;
     unobservable in results.
  2. Letrec (L) threads the environment functionally. Backward refs and
     self-recursion (ref 0 = the law itself) are exact. *Productive
     cyclic letrec* (knot-tying data cycles) is not supported: a forward
     reference embeds a hole, and forcing a hole crashes — the pure
     analogue of marduk's PlanLoop.
  3. Law construction skips the construction-time B spine walk (a
     forcing side effect); crashes it would surface at construction
     surface at first use instead. Values are unaffected.

Everything else is intended to match the oracle bit-for-bit.
"""

from __future__ import annotations

import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "pinochle", "packages", "pinochle"))

import importlib
_pn = importlib.import_module('pinochle.nock')
from pinochle.nock import to_noun
from pinochle.noun import Cell, deep

# ---------------------------------------------------------------------------
# Axis algebra
# ---------------------------------------------------------------------------

def peg(a: int, b: int) -> int:
    """Axis of the sub-noun at axis b within the noun at axis a.
    Hoon's +peg. peg(a,1)=a, peg(a,2)=2a, peg(a,3)=2a+1."""
    if b == 1:
        return a
    return 2 * peg(a, b // 2) + (b % 2)


# Component offsets within a PLAN value noun (value at axis 1):
#   tag at 2; payload at 3.
#   nat n at 3; pin item at 3; app f at 6, x at 7;
#   law name at 6, arity at 14, body at 15.
_COMPONENT = {
    "tag": 2, "n": 3, "item": 3,
    "f": 6, "x": 7,
    "name": 6, "arity": 14, "body": 15,
}


# ---------------------------------------------------------------------------
# Formula combinators (build Nock formulas as nested tuples)
# ---------------------------------------------------------------------------

def Q(x):            return (1, x)                    # quote
def INC(f):          return (4, f)                    # increment
def EQ(f, g):        return (5, f, g)                 # equality
def IF(t, y, n):     return (6, t, y, n)              # branch
CRASH = (0, 0)                                        # axis 0 = crash

# PLAN value constructors as formulas
def VNAT(f):         return (Q(0), f)                 # [0 n]
def VPIN(f):         return (Q(1), f)                 # [1 item]
def VAPP(f, x):      return (Q(3), (f, x))            # [3 f x]
def VLAW(m, a, b):   return (Q(2), (m, (a, b)))       # [2 name arity body]
Q_HOL  = Q((4, 0))
Q_NAT0 = Q((0, 0))
Q_NAT1 = Q((0, 1))


# ---------------------------------------------------------------------------
# Core builder
#
# An arm is compiled against a context: a dict mapping names to axes in
# the arm's subject. '$core' is the axis of the [battery sample] core
# (1 at arm entry; pushed deeper by each LET). Sample argument names are
# assigned axes within axis 3.
# ---------------------------------------------------------------------------

class CoreBuilder:
    def __init__(self):
        self.order: list[str] = []          # arm names, battery order
        self.samples: dict[str, list[str]] = {}
        self.builders: dict[str, callable] = {}
        self.ax: dict[str, int] = {}        # arm name -> battery axis
        self.jets: dict[str, str] = {}      # arm name -> jet hint tag
        self.battery_noun = None

    def arm(self, name: str, sample: list[str], jet: str | None = None):
        """Decorator: register an arm. The decorated fn takes a ctx dict
        and returns a formula tuple. `jet` names an opcode-11 hint tag —
        semantically transparent; a jet-aware host may accelerate it."""
        def reg(fn):
            self.order.append(name)
            self.samples[name] = sample
            self.builders[name] = fn
            if jet is not None:
                self.jets[name] = jet
            return fn
        return reg

    # -- context helpers ----------------------------------------------------

    def _sample_axes(self, names: list[str]) -> dict[str, int]:
        axs, ax = {}, 3
        for i, nm in enumerate(names):
            if i == len(names) - 1:
                axs[nm] = ax
            else:
                axs[nm] = peg(ax, 2)
                ax = peg(ax, 3)
        return axs

    def resolve(self, ctx: dict, path: str) -> int:
        """'v.f.x.tag' -> axis, chaining component offsets."""
        parts = path.split(".")
        ax = ctx[parts[0]]
        for comp in parts[1:]:
            ax = peg(ax, _COMPONENT[comp])
        return ax

    def S(self, ctx, path):
        return (0, self.resolve(ctx, path))

    def TAGEQ(self, ctx, path, t: int):
        return EQ(self.S(ctx, path + ".tag"), Q(t))

    def CALL(self, ctx, name: str, argf):
        """Invoke arm `name` with sample = argf (evaluated against the
        current subject). Hoon-style: edit sample, kick arm."""
        return (9, self.ax[name], (10, (3, argf), (0, ctx["$core"])))

    def LET(self, ctx, name: str, valf, body_fn):
        """Push a value; body_fn receives the shifted context."""
        new = {k: peg(3, v) for k, v in ctx.items()}
        new[name] = 2
        return (8, valf, body_fn(new))

    # -- assembly -----------------------------------------------------------

    def build(self):
        # Pass 1: battery axes. Battery at axis 2 of the core; arms in a
        # right-nested chain: arm_i head at each level, last arm is the tail.
        ax = 2
        for i, nm in enumerate(self.order):
            if i == len(self.order) - 1:
                self.ax[nm] = ax
            else:
                self.ax[nm] = peg(ax, 2)
                ax = peg(ax, 3)
        # Pass 2: compile bodies (CALL needs self.ax complete).
        compiled = {}
        for nm in self.order:
            ctx = {"$core": 1}
            ctx.update(self._sample_axes(self.samples[nm]))
            body = self.builders[nm](ctx)
            if nm in self.jets:
                tag = _str_nat(self.jets[nm])
                body = (11, (tag, (1, 0)), body)
            compiled[nm] = body
        # Right-nested battery tuple.
        bat = compiled[self.order[-1]]
        for nm in reversed(self.order[:-1]):
            bat = (compiled[nm], bat)
        self.battery_noun = to_noun(bat)
        return self

    def kick(self, name: str, sample_noun):
        """Run arm `name` with the given sample noun; return product."""
        subj = Cell(self.battery_noun, sample_noun)
        return _pn.nock(subj, to_noun((9, self.ax[name], (0, 1))))


K = CoreBuilder()
S_, TAGEQ, CALL, LET = K.S, K.TAGEQ, K.CALL, K.LET


# ---------------------------------------------------------------------------
# Arithmetic arms (raw atoms). Nock only has increment; everything else
# is a counting loop. O(n) dec is the classic Nock cost model — this is
# exactly what opcode-11 jet hints exist for in production runtimes.
# ---------------------------------------------------------------------------

@K.arm("deca", ["n", "c"])
def _deca(c):
    return IF(EQ(INC(S_(c, "c")), S_(c, "n")),
              S_(c, "c"),
              CALL(c, "deca", (S_(c, "n"), INC(S_(c, "c")))))

@K.arm("dec", ["n"], jet="dec")
def _dec(c):
    return IF(EQ(S_(c, "n"), Q(0)), CRASH,
              CALL(c, "deca", (S_(c, "n"), Q(0))))

@K.arm("add", ["a", "b"], jet="add")
def _add(c):
    return IF(EQ(S_(c, "b"), Q(0)), S_(c, "a"),
              CALL(c, "add", (INC(S_(c, "a")), CALL(c, "dec", S_(c, "b")))))

@K.arm("sub", ["a", "b"], jet="sub")   # assumes b <= a
def _sub(c):
    return IF(EQ(S_(c, "b"), Q(0)), S_(c, "a"),
              CALL(c, "sub", (CALL(c, "dec", S_(c, "a")),
                              CALL(c, "dec", S_(c, "b")))))

@K.arm("mula", ["a", "b", "acc"])
def _mula(c):
    return IF(EQ(S_(c, "b"), Q(0)), S_(c, "acc"),
              CALL(c, "mula", (S_(c, "a"),
                               (CALL(c, "dec", S_(c, "b")),
                                CALL(c, "add", (S_(c, "acc"), S_(c, "a")))))))

@K.arm("mul", ["a", "b"], jet="mul")
def _mul(c):
    return CALL(c, "mula", (S_(c, "a"), (S_(c, "b"), Q(0))))

@K.arm("ltea", ["a", "b", "k"])
def _ltea(c):
    # count k upward; whichever of a/b it hits first decides. a==b -> yes.
    return IF(EQ(S_(c, "k"), S_(c, "a")), Q(0),
              IF(EQ(S_(c, "k"), S_(c, "b")), Q(1),
                 CALL(c, "ltea", (S_(c, "a"), (S_(c, "b"), INC(S_(c, "k")))))))

@K.arm("lte", ["a", "b"], jet="lte")   # loobean: 0 yes, 1 no
def _lte(c):
    return CALL(c, "ltea", (S_(c, "a"), (S_(c, "b"), Q(0))))


# ---------------------------------------------------------------------------
# PLAN spec arms
# ---------------------------------------------------------------------------

@K.arm("A", ["v"])
def _A(c):
    """Arity.  A@=0  A{a m b}=a  A<{a m b}>=a  A<i>=1  A(f x)=max(0,Af-1)."""
    def app_case(ctx):
        return LET(ctx, "af", CALL(ctx, "A", S_(ctx, "v.f")),
                   lambda c2: IF(EQ(S_(c2, "af"), Q(0)), Q(0),
                                 CALL(c2, "dec", S_(c2, "af"))))
    return IF(TAGEQ(c, "v", 0), Q(0),
           IF(TAGEQ(c, "v", 2), S_(c, "v.arity"),
           IF(TAGEQ(c, "v", 1),
              IF(TAGEQ(c, "v.item", 2), S_(c, "v.item.arity"), Q(1)),
           IF(TAGEQ(c, "v", 3), app_case(c),
              CRASH))))                       # hole


@K.arm("E", ["v"])
def _E(c):
    """Evaluate to WHNF.  E<> crashes; E(f x) = Ef; Ho(Af); Eo = o.
    Ho1 = X then re-E (the spec's cyclic-update tail loop, expressed as
    a recursive call since we are pure)."""
    def app_case(ctx):
        def with_ef(c2):
            def with_ar(c3):
                vp = VAPP(S_(c3, "ef"), S_(c3, "v.x"))
                return IF(EQ(S_(c3, "ar"), Q(1)),
                          CALL(c3, "E",
                               LET(c3, "vp", vp,
                                   lambda c4: CALL(c4, "X",
                                                   (S_(c4, "vp"), S_(c4, "vp"))))),
                          vp)
            return LET(c2, "ar", CALL(c2, "A", S_(c2, "ef")), with_ar)
        return LET(ctx, "ef", CALL(ctx, "E", S_(ctx, "v.f")), with_ef)
    return IF(TAGEQ(c, "v", 4), CRASH,
           IF(TAGEQ(c, "v", 3), app_case(c),
              S_(c, "v")))


@K.arm("X", ["k", "e"])
def _X(c):
    """Execute a saturated form. Descend k through the App spine to the
    leaf head; dispatch on pinned-nat (S), pinned law, or bare law (B)."""
    return IF(TAGEQ(c, "k", 3),
              CALL(c, "X", (S_(c, "k.f"), S_(c, "e"))),
           IF(TAGEQ(c, "k", 1),
              IF(TAGEQ(c, "k.item", 0),
                 # Xe(<o:@> x) = Ex; Sox — arg is e's last tail
                 CALL(c, "S0", (S_(c, "k.item.n"),
                                CALL(c, "E", S_(c, "e.x")))),
              IF(TAGEQ(c, "k.item", 2),
                 CALL(c, "Bx", (S_(c, "k.item.arity"),
                                (S_(c, "k.item.arity"),
                                 (S_(c, "e"),
                                  (S_(c, "k.item.body"), S_(c, "k.item.body")))))),
                 CRASH)),
           IF(TAGEQ(c, "k", 2),
              CALL(c, "Bx", (S_(c, "k.arity"),
                             (S_(c, "k.arity"),
                              (S_(c, "e"),
                               (S_(c, "k.body"), S_(c, "k.body")))))),
              CRASH)))


@K.arm("S0", ["opn", "arg"])
def _S0(c):
    """Primop dispatch. opn 0 = core PLAN (Pin/Law/Elim by structural
    pattern on the arg spine depth + leaf); opn 66 = BPLAN subset."""
    # --- depth 1, leaf 0: Pin ------------------------------------------
    pin_case = IF(EQ(S_(c, "arg.f.n"), Q(0)),
                  LET(c := c, "i", CALL(c, "E", S_(c, "arg.x")),
                      lambda c2: VPIN(S_(c2, "i"))),
                  CRASH)
    # --- depth 3, leaf 1: Law ------------------------------------------
    def law_case(ctx):
        def with_av(c2):
            def with_bv(c3):
                def with_mv(c4):
                    return VLAW(S_(c4, "mv.n"), S_(c4, "av.n"), S_(c4, "bv"))
                return LET(c3, "mv", CALL(c3, "Nx", S_(c3, "arg.f.x")), with_mv)
            return IF(EQ(S_(c2, "av.n"), Q(0)), CRASH,
                      LET(c2, "bv", CALL(c2, "E", S_(c2, "arg.x")), with_bv))
        return IF(EQ(S_(ctx, "arg.f.f.f.n"), Q(1)),
                  LET(ctx, "av", CALL(ctx, "Nx", S_(ctx, "arg.f.f.x")), with_av),
                  CRASH)
    # --- depth 6, leaf 2: Elim ------------------------------------------
    def elim_case(ctx):
        def with_ov(c2):
            return CALL(c2, "C6",
                        (S_(c2, "arg.f.f.f.f.f.x"),            # p
                         (S_(c2, "arg.f.f.f.f.x"),             # l
                          (S_(c2, "arg.f.f.f.x"),              # a (app handler)
                           (S_(c2, "arg.f.f.x"),               # z
                            (S_(c2, "arg.f.x"),                # m
                             S_(c2, "ov")))))))                # o (forced)
        return IF(EQ(S_(ctx, "arg.f.f.f.f.f.f.n"), Q(2)),
                  LET(ctx, "ov", CALL(ctx, "E", S_(ctx, "arg.x")), with_ov),
                  CRASH)
    deep6 = IF(TAGEQ(c, "arg.f.f.f", 3),
            IF(TAGEQ(c, "arg.f.f.f.f", 3),
            IF(TAGEQ(c, "arg.f.f.f.f.f", 3),
            IF(TAGEQ(c, "arg.f.f.f.f.f.f", 0),
               elim_case(c),
               CRASH), CRASH), CRASH), CRASH)
    core = IF(TAGEQ(c, "arg", 3),
           IF(TAGEQ(c, "arg.f", 0),
              pin_case,
           IF(TAGEQ(c, "arg.f", 3),
              IF(TAGEQ(c, "arg.f.f", 0),
                 CRASH,                                  # depth 2: no core op
              IF(TAGEQ(c, "arg.f.f", 3),
                 IF(TAGEQ(c, "arg.f.f.f", 0),
                    law_case(c),
                    deep6),
                 CRASH)),
              CRASH)),
           CRASH)
    return IF(EQ(S_(c, "opn"), Q(0)), core,
           IF(EQ(S_(c, "opn"), Q(66)), CALL(c, "BP", S_(c, "arg")),
              CRASH))


@K.arm("C6", ["p", "l", "az", "z", "m", "o"])
def _C6(c):
    """The eliminator.  Cp____<i> = p i;  C_l___{a m b} = l a m b;
    C__a__(x e) = a x e;  C___z_0 = z;  C____m(o:@) = m (o-1)."""
    law_res = VAPP(VAPP(VAPP(S_(c, "l"), VNAT(S_(c, "o.name"))),
                        VNAT(S_(c, "o.arity"))),
                   S_(c, "o.body"))
    return IF(TAGEQ(c, "o", 1), VAPP(S_(c, "p"), S_(c, "o.item")),
           IF(TAGEQ(c, "o", 2), law_res,
           IF(TAGEQ(c, "o", 3), VAPP(VAPP(S_(c, "az"), S_(c, "o.f")), S_(c, "o.x")),
           IF(TAGEQ(c, "o", 0),
              IF(EQ(S_(c, "o.n"), Q(0)), S_(c, "z"),
                 VAPP(S_(c, "m"), VNAT(CALL(c, "dec", S_(c, "o.n"))))),
              CRASH))))


@K.arm("Ix", ["f", "o", "n"])
def _Ix(c):
    """I0(e x)=x; In(e x)=I(n-1)e; In_ = fallback f (marduk's I)."""
    return IF(EQ(S_(c, "n"), Q(0)),
              IF(TAGEQ(c, "o", 3), S_(c, "o.x"), S_(c, "o")),
              IF(TAGEQ(c, "o", 3),
                 CALL(c, "Ix", (S_(c, "f"),
                                (S_(c, "o.f"), CALL(c, "dec", S_(c, "n"))))),
                 S_(c, "f")))


@K.arm("R3", ["n", "e", "b"])
def _R3(c):
    """Body reduction.  Rne(b:@)|b<=n = I(n-b)e;
    Rne(0 f x) = (Rnef Rnex);  Rne(0 x) = x;  Rnex = x."""
    ref = IF(EQ(CALL(c, "lte", (S_(c, "b.n"), S_(c, "n"))), Q(0)),
             CALL(c, "Ix", (S_(c, "b"),
                            (S_(c, "e"),
                             CALL(c, "sub", (S_(c, "n"), S_(c, "b.n")))))),
             S_(c, "b"))
    apply2 = VAPP(CALL(c, "R3", (S_(c, "n"), (S_(c, "e"), S_(c, "b.f.x")))),
                  CALL(c, "R3", (S_(c, "n"), (S_(c, "e"), S_(c, "b.x")))))
    return IF(TAGEQ(c, "b", 0), ref,
           IF(TAGEQ(c, "b", 3),
              IF(TAGEQ(c, "b.f", 3),
                 IF(TAGEQ(c, "b.f.f", 0),
                    IF(EQ(S_(c, "b.f.f.n"), Q(0)), apply2, S_(c, "b")),
                    S_(c, "b")),                       # len > 3: pass through
                 IF(TAGEQ(c, "b.f", 0),
                    IF(EQ(S_(c, "b.f.n"), Q(0)), S_(c, "b.x"), S_(c, "b")),
                    S_(c, "b"))),
              S_(c, "b")))


@K.arm("envset", ["e", "d", "val"])
def _envset(c):
    """Functional slot update at depth d in the left App spine — the pure
    replacement for marduk's Val.update on the letrec env."""
    return IF(EQ(S_(c, "d"), Q(0)),
              IF(TAGEQ(c, "e", 3), VAPP(S_(c, "e.f"), S_(c, "val")), CRASH),
              IF(TAGEQ(c, "e", 3),
                 VAPP(CALL(c, "envset",
                           (S_(c, "e.f"),
                            (CALL(c, "dec", S_(c, "d")), S_(c, "val")))),
                      S_(c, "e.x")),
                 CRASH))


@K.arm("Lx", ["i", "n", "e", "b"])
def _Lx(c):
    """Line(1 v b) = Ev; Iie#Rnev; L(i+1)neb;  Linex = Rnex.
    Env threading replaces slot mutation (see module docstring, delta 2)."""
    fallback = CALL(c, "R3", (S_(c, "n"), (S_(c, "e"), S_(c, "b"))))
    def let_case(ctx):
        def with_val(c2):
            def with_e2(c3):
                return CALL(c3, "Lx",
                            (INC(S_(c3, "i")),
                             (S_(c3, "n"), (S_(c3, "e2"), S_(c3, "b.x")))))
            return LET(c2, "e2",
                       CALL(c2, "envset",
                            (S_(c2, "e"),
                             (CALL(c2, "sub", (S_(c2, "n"), S_(c2, "i"))),
                              S_(c2, "val")))),
                       with_e2)
        return LET(ctx, "val",
                   CALL(ctx, "R3", (S_(ctx, "n"), (S_(ctx, "e"), S_(ctx, "b.f.x")))),
                   with_val)
    return IF(TAGEQ(c, "b", 3),
              IF(TAGEQ(c, "b.f", 3),
                 IF(TAGEQ(c, "b.f.f", 0),
                    IF(EQ(S_(c, "b.f.f.n"), Q(1)), let_case(c), fallback),
                    fallback),
                 fallback),
              fallback)


@K.arm("Bx", ["a", "n", "e", "b", "x"])
def _Bx(c):
    """Baneb(1 _ k) = Ba(n+1)(e <>)bk;  Banebx = L(a+1)neb."""
    hand_off = CALL(c, "Lx", (INC(S_(c, "a")),
                              (S_(c, "n"), (S_(c, "e"), S_(c, "b")))))
    recurse = CALL(c, "Bx",
                   (S_(c, "a"),
                    (INC(S_(c, "n")),
                     (VAPP(S_(c, "e"), Q_HOL),
                      (S_(c, "b"), S_(c, "x.x"))))))
    return IF(TAGEQ(c, "x", 3),
              IF(TAGEQ(c, "x.f", 3),
                 IF(TAGEQ(c, "x.f.f", 0),
                    IF(EQ(S_(c, "x.f.f.n"), Q(1)), recurse, hand_off),
                    hand_off),
                 hand_off),
              hand_off)


@K.arm("Nx", ["v"])
def _Nx(c):
    """N: force; nat passes, everything else coerces to nat 0."""
    return LET(c, "w", CALL(c, "E", S_(c, "v")),
               lambda c2: IF(TAGEQ(c2, "w", 0), S_(c2, "w"), Q_NAT0))


@K.arm("NN", ["v"])
def _NN(c):
    """N, unwrapped to a raw atom (for arithmetic primops)."""
    return LET(c, "w", CALL(c, "Nx", S_(c, "v")),
               lambda c2: S_(c2, "w.n"))


@K.arm("Fx", ["v"])
def _Fx(c):
    """Force to normal form along the App spine (spec F)."""
    return LET(c, "w", CALL(c, "E", S_(c, "v")),
               lambda c2: IF(TAGEQ(c2, "w", 3),
                             VAPP(CALL(c2, "Fx", S_(c2, "w.f")),
                                  CALL(c2, "Fx", S_(c2, "w.x"))),
                             S_(c2, "w")))


# ---------------------------------------------------------------------------
# BPLAN (<66>) subset: the ops the fixtures use. Name atoms are the
# LSB-first string-nats marduk uses; computed at build time.
# ---------------------------------------------------------------------------

def _str_nat(s: str) -> int:
    return int.from_bytes(s.encode(), "little")

@K.arm("mkLaw", ["a", "m", "b"])
def _mkLaw(c):
    """Shared Law construction: S0(1 a m b) and BPLAN Law."""
    def with_av(c2):
        def with_bv(c3):
            return LET(c3, "mv", CALL(c3, "Nx", S_(c3, "m")),
                       lambda c4: VLAW(S_(c4, "mv.n"), S_(c4, "av.n"),
                                       S_(c4, "bv")))
        return IF(EQ(S_(c2, "av.n"), Q(0)), CRASH,
                  LET(c2, "bv", CALL(c2, "E", S_(c2, "b")), with_bv))
    return LET(c, "av", CALL(c, "Nx", S_(c, "a")), with_av)


@K.arm("BP", ["arg"])
def _BP(c):
    """(<66> (Name ...args)) — dispatch on spine depth, then leaf name."""
    def nm(s): return Q(_str_nat(s))
    # 1-arg ops: arg = App(name, x)
    def one_arg(ctx):
        x = S_(ctx, "arg.x")
        return \
            IF(EQ(S_(ctx, "arg.f.n"), nm("Inc")),
               VNAT(INC(CALL(ctx, "NN", x))),
            IF(EQ(S_(ctx, "arg.f.n"), nm("Dec")),
               LET(ctx, "xn", CALL(ctx, "NN", x),
                   lambda c2: IF(EQ(S_(c2, "xn"), Q(0)), Q_NAT0,
                                 VNAT(CALL(c2, "dec", S_(c2, "xn"))))),
            IF(EQ(S_(ctx, "arg.f.n"), nm("Pin")),
               LET(ctx, "i", CALL(ctx, "E", x),
                   lambda c2: VPIN(S_(c2, "i"))),
               CRASH)))
    # 2-arg ops: arg = App(App(name, x), y)
    def two_arg(ctx):
        def with_xy(c2):
            xn, yn = S_(c2, "xn"), S_(c2, "yn")
            name = S_(c2, "arg.f.f.n")
            return \
                IF(EQ(name, nm("Add")), VNAT(CALL(c2, "add", (xn, yn))),
                IF(EQ(name, nm("Mul")), VNAT(CALL(c2, "mul", (xn, yn))),
                IF(EQ(name, nm("Sub")),
                   # saturating: y > x -> 0
                   IF(EQ(CALL(c2, "lte", (yn, xn)), Q(0)),
                      VNAT(CALL(c2, "sub", (xn, yn))), Q_NAT0),
                IF(EQ(name, nm("Eq")),
                   IF(EQ(xn, yn), Q_NAT1, Q_NAT0),
                IF(EQ(name, nm("Le")),
                   IF(EQ(CALL(c2, "lte", (xn, yn)), Q(0)), Q_NAT1, Q_NAT0),
                IF(EQ(name, nm("Lt")),
                   IF(EQ(xn, yn), Q_NAT0,
                      IF(EQ(CALL(c2, "lte", (xn, yn)), Q(0)), Q_NAT1, Q_NAT0)),
                IF(EQ(name, nm("Gt")),
                   IF(EQ(CALL(c2, "lte", (xn, yn)), Q(0)), Q_NAT0, Q_NAT1),
                IF(EQ(name, nm("Ge")),
                   IF(EQ(CALL(c2, "lte", (yn, xn)), Q(0)), Q_NAT1, Q_NAT0),
                IF(EQ(name, nm("Ne")),
                   IF(EQ(xn, yn), Q_NAT0, Q_NAT1),
                   CRASH)))))))))
        return LET(ctx, "xn", CALL(ctx, "NN", S_(ctx, "arg.f.x")),
                   lambda cx: LET(cx, "yn", CALL(cx, "NN", S_(cx, "arg.x")),
                                  with_xy))
    # 3-arg ops: arg = App(App(App(name, x1), x2), x3)
    def three_arg(ctx):
        x1, x2, x3 = S_(ctx, "arg.f.f.x"), S_(ctx, "arg.f.x"), S_(ctx, "arg.x")
        name = S_(ctx, "arg.f.f.f.n")
        # If c t e: e iff c forces to exactly nat 0; cells are truthy.
        # Branches are returned UNforced (laziness is what makes
        # recursion terminate).
        def if_like(t_f, e_f):
            def with_cw(c2):
                zero = IF(EQ(S_(c2, "cw.n"), Q(0)), e_f(c2), t_f(c2))
                return IF(TAGEQ(c2, "cw", 0), zero, t_f(c2))
            return LET(ctx, "cw", CALL(ctx, "E", x1), with_cw)
        sx2 = lambda c2: S_(c2, "arg.f.x")
        sx3 = lambda c2: S_(c2, "arg.x")
        return \
            IF(EQ(name, nm("Law")),
               CALL(ctx, "mkLaw", (x1, (x2, x3))),
            IF(EQ(name, nm("If")),  if_like(sx2, sx3),
            IF(EQ(name, nm("Ifz")), if_like(sx3, sx2),
            IF(EQ(name, nm("Case2")),
               LET(ctx, "xn", CALL(ctx, "NN", x1),
                   lambda c2: IF(EQ(S_(c2, "xn"), Q(0)),
                                 S_(c2, "arg.f.x"), S_(c2, "arg.x"))),
               CRASH))))
    # 4-arg ops: arg = App^4(name, x1, x2, x3, x4)
    def four_arg(ctx):
        return IF(EQ(S_(ctx, "arg.f.f.f.f.n"), nm("Case3")),
                  LET(ctx, "xn", CALL(ctx, "NN", S_(ctx, "arg.f.f.f.x")),
                      lambda c2:
                      IF(EQ(S_(c2, "xn"), Q(0)), S_(c2, "arg.f.f.x"),
                      IF(EQ(S_(c2, "xn"), Q(1)), S_(c2, "arg.f.x"),
                         S_(c2, "arg.x")))),
                  CRASH)
    # 6-arg ops: arg = App^6(name, p, l, a, z, m, o)
    def six_arg(ctx):
        def with_ov(c2):
            return CALL(c2, "C6",
                        (S_(c2, "arg.f.f.f.f.f.x"),
                         (S_(c2, "arg.f.f.f.f.x"),
                          (S_(c2, "arg.f.f.f.x"),
                           (S_(c2, "arg.f.f.x"),
                            (S_(c2, "arg.f.x"), S_(c2, "ov")))))))
        return IF(EQ(S_(ctx, "arg.f.f.f.f.f.f.n"), nm("Elim")),
                  LET(ctx, "ov", CALL(ctx, "E", S_(ctx, "arg.x")), with_ov),
                  CRASH)
    deep = IF(TAGEQ(c, "arg.f.f.f", 0), three_arg(c),
           IF(TAGEQ(c, "arg.f.f.f", 3),
              IF(TAGEQ(c, "arg.f.f.f.f", 0), four_arg(c),
              IF(TAGEQ(c, "arg.f.f.f.f", 3),
              IF(TAGEQ(c, "arg.f.f.f.f.f", 3),
              IF(TAGEQ(c, "arg.f.f.f.f.f.f", 0), six_arg(c),
                 CRASH), CRASH), CRASH)),
              CRASH))
    return IF(TAGEQ(c, "arg", 3),
              IF(TAGEQ(c, "arg.f", 0), one_arg(c),
              IF(TAGEQ(c, "arg.f", 3),
                 IF(TAGEQ(c, "arg.f.f", 0), two_arg(c),
                 IF(TAGEQ(c, "arg.f.f", 3), deep, CRASH)),
                 CRASH)),
              CRASH)


K.build()


# ---------------------------------------------------------------------------
# marduk Val <-> noun bridge
# ---------------------------------------------------------------------------

def enc(v) -> "noun":
    """marduk Val -> tagged noun."""
    t = v.type
    if t == "nat":
        return Cell(0, v.nat)
    if t == "pin":
        return Cell(1, enc(v.item))
    if t == "app":
        return Cell(3, Cell(enc(v.head), enc(v.tail)))
    if t == "law":
        return Cell(2, Cell(v.name.nat, Cell(v.args.nat, enc(v.body))))
    if t == "hol":
        return Cell(4, 0)
    raise ValueError(t)


def dec_(n):
    """Tagged noun -> marduk Val (for oracle comparison)."""
    from marduk.runtime import Nat, Pin, App, Law, Hol
    tag = n.head
    if tag == 0:
        return Nat(int(n.tail))
    if tag == 1:
        return Pin(dec_(n.tail))
    if tag == 3:
        return App(dec_(n.tail.head), dec_(n.tail.tail))
    if tag == 2:
        return Law(Nat(int(n.tail.head)), Nat(int(n.tail.tail.head)),
                   dec_(n.tail.tail.tail))
    if tag == 4:
        return Hol()
    raise ValueError(tag)


def nock_whnf(v):
    """Evaluate a marduk Val to WHNF via the Nock core."""
    return dec_(K.kick("E", enc(v)))

def nock_force(v):
    """Evaluate a marduk Val to normal form via the Nock core."""
    return dec_(K.kick("Fx", enc(v)))
