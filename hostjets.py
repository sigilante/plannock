"""Jet dispatch for pinochle's Nock interpreter — the standard Nock
acceleration architecture (Vere does exactly this for Hoon's dec/add).

Mechanism: arm bodies get wrapped in a dynamic opcode-11 hint,
    [11 [tag [1 0]] body]
which is semantically transparent per Nock 4K (the hint is computed and
discarded). A jet-aware interpreter recognizes registered tags and runs
a native implementation instead of the formula. Correctness contract:
jet(subject) == *[subject body], enforced empirically by VALIDATE mode,
which runs both paths and asserts equality on every dispatch.

Nothing about the noun or its semantics changes. A pure interpreter runs
the same core, just slower — the earlier test suites do exactly that.
"""

from __future__ import annotations

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "pinochle", "packages", "pinochle"))

import importlib
_pn = importlib.import_module('pinochle.nock')
from pinochle.noun import Cell, deep


def _str_nat(s: str) -> int:
    return int.from_bytes(s.encode(), "little")


#: tag atom -> native fn(subject_noun) -> noun
REGISTRY: dict[int, callable] = {}

#: run both paths and assert equality (slow; for certification runs)
VALIDATE = False

#: master switch
ENABLED = True


def _atom(n):
    if deep(n):
        raise ValueError("expected atom")
    return int(n)


# --- native implementations --------------------------------------------
# Each jet sees the arm's subject [battery sample]; sample is the tail.

def _j_dec(subj):
    n = _atom(subj.tail)
    if n == 0:
        raise Exception("fail: dec 0")          # match formula crash
    return n - 1

def _j_add(subj):
    s = subj.tail
    return _atom(s.head) + _atom(s.tail)

def _j_sub(subj):
    s = subj.tail
    a, b = _atom(s.head), _atom(s.tail)
    if b > a:
        raise Exception("fail: sub underflow")  # formula would loop/crash
    return a - b

def _j_mul(subj):
    s = subj.tail
    return _atom(s.head) * _atom(s.tail)

def _j_lte(subj):
    s = subj.tail
    return 0 if _atom(s.head) <= _atom(s.tail) else 1


JETS = {
    "dec": _j_dec,
    "add": _j_add,
    "sub": _j_sub,
    "mul": _j_mul,
    "lte": _j_lte,
}

for name, fn in JETS.items():
    REGISTRY[_str_nat(name)] = fn


# --- interpreter patch ---------------------------------------------------

_orig_nock = _pn.nock


def _jet_nock(a, formula):
    """Front-end for pinochle's nock: intercept registered opcode-11
    dynamic hints; delegate everything else. Recursive calls inside the
    original resolve through the module global, so all depths route here."""
    if ENABLED and deep(formula) and not deep(formula.head) \
            and formula.head == 11:
        ft = formula.tail
        if deep(ft) and deep(ft.head) and not deep(ft.head.head):
            tag = int(ft.head.head)
            fn = REGISTRY.get(tag)
            if fn is not None:
                if VALIDATE:
                    want = _orig_nock(a, ft.tail)
                    got = fn(a)
                    assert _pn.to_noun(got) == _pn.to_noun(want), \
                        (tag, got, want)
                    return got
                return fn(a)
    return _orig_nock(a, formula)


def install():
    _pn.nock = _jet_nock


def uninstall():
    _pn.nock = _orig_nock
