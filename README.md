# nockplan — PLAN, implemented in Nock

Empirical response to the claim: **"PLAN can implement Nock, but Nock
cannot implement PLAN."**

The evaluator here is a single Nock noun — a Hoon-style core of ~25
battery arms — executed by an off-the-shelf Nock 4K interpreter
(sigilante/pinochle, unmodified semantics). It is validated against a
spec-faithful PLAN runtime (sigilante/marduk) as oracle, using marduk's
own frontend and marduk's own test corpus: we swap one function pointer
(`PlanKernelEvaluator._backend`) and run their tests on our machine.

## Results

| Suite | Result |
|---|---|
| Unit tests (arity, E, X, S, C, R/L/B, letrec, BPLAN arith) | 32/32, oracle-exact |
| marduk fixtures (id, k, s, arithmetic, elim, church_bool) | 6/6, expected values |
| marduk tutorials 01–04, every code cell, incl. recursion (fact, fib, accumulator loops) | 56/56, byte-identical to committed outputs |
| Jet certification (VALIDATE: native + formula both run, asserted equal) | clean |

## What the claim gets wrong

PLAN-in-Nock is not merely possible-by-Turing-handwave; it is a direct,
small, structural embedding. Each spec judgment (E, A, X, S, C, R, L, B,
I, N, F) is one battery arm. PLAN values are tagged nouns. Recursion
needs no cyclic data: PLAN's ref-0-is-self bottoms out at the spine head
(`I(n)e`), which is ordinary acyclic structure.

## What the claim gets right (the honest residue)

Two implementation-level asymmetries, both predicted before writing code
and both confirmed empirically:

1. **Cost model.** Nock atoms expose increment and equality only, so
   pure-formula `dec` is O(n) — arithmetic-heavy cells are intractable
   pure. The fix is Nock's own canonical answer: opcode-11 jet hints
   (`hostjets.py`), the same architecture Vere uses for Hoon's `dec`.
   Jets are certified by running both paths and asserting equality.
2. **Observable sharing.** PLAN's spec assumes an updatable shared heap
   (`Ho1 = o#Xoo`, letrec via hole mutation). Everything except
   *productive cyclic letrec* survives functional env threading;
   `test_delta.py` shows the one divergence: a forward-referencing
   binding resolves on marduk's mutable heap and crashes (stale hole)
   on the pure machine — the pure analogue of marduk's `PlanLoop`.
   Notably, marduk's own `force` observably mutates its input term:
   PLAN's "sharing" is semantic, not an optimization. Supporting it
   fully in Nock means an explicit heap (store-passing) — a deeper
   embedding, not an impossibility.

So the defensible version of the claim is: *no zero-cost shallow
embedding of PLAN's mutable-heap semantics exists in pure Nock* — the
same relationship Haskell has to C. "Cannot implement" is falsified.

## Layout

    nockplan.py       assembler (peg/axis algebra, core builder) + arms
    hostjets.py       opcode-11 jet dispatch + VALIDATE mode
    test_core.py      bottom-up unit tests vs oracle
    test_fixtures.py  marduk fixtures, backend-swapped
    test_tutorials.py marduk tutorials 01-04, backend-swapped
    test_delta.py     the declared divergence, demonstrated both ways

Run with marduk and pinochle checked out as siblings:

    NOCKPLAN_JETS=validate python3 test_core.py      # certify jets
    NOCKPLAN_JETS=0        python3 test_fixtures.py  # pure Nock
    python3 test_tutorials.py                        # jets on (default)
    python3 test_delta.py

## Declared deltas vs marduk

1. No update-in-place → no memoization. Performance-only.
2. Letrec env threaded functionally: backward refs and self-recursion
   exact; productive cyclic letrec crashes (see above).
3. Law construction skips the construction-time B spine-forcing walk;
   affects crash *timing* only, never values.
