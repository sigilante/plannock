"""The declared delta, demonstrated.

Productive cyclic letrec: a let-binding that *forward-references* a later
slot. marduk's runtime resolves it — slots are shared mutable cells, and
the later L pass updates the hole that the earlier binding embedded.
Our pure-Nock evaluator threads the environment functionally: the
forward reference embeds a hole *value*, the later update cannot reach
it, and forcing crashes — the pure analogue of PlanLoop.

Law under test (arity 1, two lets; refs: 0=self 1=arg 2=A 3=B):

    {f 1 (1 A=(0 ref1 ref3)      ; A = (arg B)   <- forward ref to B
         (1 B=(0 42)             ; B = quote 42
            ref2))}              ; body = A

    (f id)  ->  marduk: (id 42) -> 42
            ->  nock:   forcing A hits the stale hole -> crash
"""
import sys, os, threading

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "marduk", "packages", "marduk"))
sys.path.insert(0, os.path.join(HERE, "..", "marduk", "packages", "plan-kernel"))

sys.setrecursionlimit(400_000)


def main():
    from marduk.runtime import Nat, App, Law, force
    from nockplan import nock_force

    def ap(f, x):
        return App(App(Nat(0), f), x)          # body-form apply
    def quote(x):
        return App(Nat(0), x)                  # body-form quote

    def build():
        # (1 A (1 B body)) — fresh per engine: marduk's evaluator
        # update-in-place mutates its input term.
        body = App(App(Nat(1), ap(Nat(1), Nat(3))),      # A = (arg B)
                   App(App(Nat(1), quote(Nat(42))),      # B = '42
                       Nat(2)))                          # body = A
        f = Law(Nat(0x66), Nat(1), body)
        idl = Law(Nat(0x6469), Nat(1), Nat(1))
        return App(f, idl)

    print("oracle (mutable heap):", force(build()))

    try:
        r = nock_force(build())
        print("nock (pure):", r, "— UNEXPECTED: delta analysis wrong")
    except Exception as e:
        print(f"nock (pure): crash ({e}) — as declared: forward-ref "
              f"letrec needs update-in-place")


if __name__ == "__main__":
    threading.stack_size(512 << 20)
    t = threading.Thread(target=main)
    t.start()
    t.join()
