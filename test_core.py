"""Bottom-up tests: arithmetic arms, then spec arms, then oracle diffs."""
import sys, os, threading

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "marduk", "packages", "marduk"))
sys.path.insert(0, os.path.join(HERE, "..", "marduk", "packages", "plan-kernel"))

sys.setrecursionlimit(400_000)

def main():
    import hostjets
    mode = os.environ.get("NOCKPLAN_JETS", "1")
    if mode != "0":
        hostjets.VALIDATE = (mode == "validate")
        hostjets.install()
        print(f"[jets: on, validate={hostjets.VALIDATE}]")
    else:
        print("[jets: off — pure Nock]")
    from nockplan import K, enc, dec_, nock_whnf, nock_force
    from pinochle.noun import Cell
    from marduk.runtime import Nat, Pin, App, Law, evaluate, force

    ok = fail = 0
    def check(name, got, want):
        nonlocal ok, fail
        if repr(got) == repr(want):
            ok += 1
            print(f"  ok   {name}: {got!r}")
        else:
            fail += 1
            print(f"  FAIL {name}: got {got!r} want {want!r}")

    print("== arithmetic arms ==")
    check("dec 7",    K.kick("dec", 7), 6)
    check("add 3 4",  K.kick("add", Cell(3, 4)), 7)
    check("sub 9 3",  K.kick("sub", Cell(9, 3)), 6)
    check("mul 3 4",  K.kick("mul", Cell(3, 4)), 12)
    check("lte 3 3",  K.kick("lte", Cell(3, 3)), 0)
    check("lte 4 3",  K.kick("lte", Cell(4, 3)), 1)
    check("lte 3 4",  K.kick("lte", Cell(3, 4)), 0)

    print("== arity ==")
    idl = Law(Nat(0x6469), Nat(1), Nat(1))       # {id 1 1}: body = ref 1
    kl  = Law(Nat(0x6b), Nat(2), Nat(1))         # {k 2 1}:  returns arg1
    check("A nat",       K.kick("A", enc(Nat(5))), 0)
    check("A law",       K.kick("A", enc(kl)), 2)
    check("A pin law",   K.kick("A", enc(Pin(kl))), 2)
    check("A pin nat",   K.kick("A", enc(Pin(Nat(0)))), 1)
    check("A app",       K.kick("A", enc(App(kl, Nat(9)))), 1)

    print("== E: the article's worked examples ==")
    # id 42 -> 42
    check("id 42", nock_force(App(idl, Nat(42))), force(App(idl, Nat(42))))
    # k 7 99 -> 7
    t = App(App(kl, Nat(7)), Nat(99))
    check("k 7 99", nock_force(t), force(t))
    # over-application: (id 1) 2 -> stuck app (1 2)
    t = App(App(idl, Nat(1)), Nat(2))
    check("(id 1) 2", nock_force(t), force(t))
    # under-application: (k 7) stays partial
    t = App(kl, Nat(7))
    check("(k 7)", nock_force(t), force(t))

    print("== self-reference: ref 0 is the law ==")
    # {f 1 0}: body = ref 0 = the law itself -> (f x) reduces to f... which
    # is WHNF (a law). Oracle agrees?
    selfl = Law(Nat(0x66), Nat(1), Nat(0))
    t = App(selfl, Nat(5))
    check("self law", nock_force(t), force(t))

    print("== S0: primop construction via pinned nat <0> ==")
    # (<0> (0 x)) -> pin x
    t = App(Pin(Nat(0)), App(Nat(0), Nat(42)))
    check("mk pin", nock_force(t), force(t))
    # (<0> (1 a m b)) -> law
    t = App(Pin(Nat(0)),
            App(App(App(Nat(1), Nat(2)), Nat(0x6b)), Nat(1)))
    check("mk law", nock_force(t), force(t))

    print("== S0: elim ==")
    # elim on nat 0 -> z; on nat k -> (m (k-1)); on pin -> (p i)
    def elim(o):
        return App(Pin(Nat(0)),
                   App(App(App(App(App(App(Nat(2),
                        Nat(10)), Nat(11)), Nat(12)), Nat(13)), idl), o))
    for o, tag in [(Nat(0), "z"), (Nat(5), "m"), (Pin(Nat(9)), "p"),
                   (App(App(kl, Nat(1)), Nat(2)), "a-stuck"),
                   (kl, "l")]:
        t = elim(o)
        check(f"elim {tag}", nock_force(t), force(t))

    print("== law with apply body: S combinator-ish ==")
    # {ap 2 (0 1 2)}: body = apply ref1 to ref2 -> (x y)
    ap_body = App(App(Nat(0), Nat(1)), Nat(2))
    apl = Law(Nat(0x7061), Nat(2), ap_body)
    t = App(App(apl, idl), Nat(42))     # (id 42) -> 42
    check("apply law", nock_force(t), force(t))

    print("== law with quote body ==")
    # {q 1 (0 7)}: quote — body is literally nat 7 regardless of arg?
    # (0 x) = quote x: body (0 7) -> 7... but 7 > n so plain 7 also passes
    # through. Use quote of ref-shaped nat: (0 1) -> literal nat 1.
    ql = Law(Nat(0x71), Nat(1), App(Nat(0), Nat(1)))
    t = App(ql, Nat(99))
    check("quote law", nock_force(t), force(t))

    print("== letrec: backward reference ==")
    # {f 1 (1 v=(0 (0 1) (0 1)) body=2)}: let v = (arg arg); return v
    # refs: n=1 (one arg) + 1 let -> let slot is ref 2.
    body = App(App(Nat(1),
                   App(App(Nat(0), Nat(1)), Nat(1))),   # v = (ref1 ref1)
               Nat(2))                                  # body = ref2 = v
    letl = Law(Nat(0x6c), Nat(1), body)
    t = App(letl, idl)                                  # (id id) -> id
    check("letrec bwd", nock_force(t), force(t))

    print("== BPLAN arithmetic ==")
    def strnat(s): return Nat(int.from_bytes(s.encode(), "little"))
    def bp(name, *args):
        spine = strnat(name)
        for a in args:
            spine = App(spine, a)
        return App(Pin(Nat(66)), spine)
    for expr, label in [
        (bp("Add", Nat(1), bp("Mul", Nat(2), Nat(3))), "1+(2*3)"),
        (bp("Sub", Nat(3), Nat(5)), "3-5 monus"),
        (bp("Dec", Nat(0)), "dec 0"),
        (bp("Eq", Nat(4), Nat(4)), "eq"),
        (bp("Le", Nat(5), Nat(4)), "le"),
    ]:
        check(f"bplan {label}", nock_force(expr), force(expr))

    print(f"\n{ok} ok, {fail} failed")
    return fail

if __name__ == "__main__":
    t = threading.Thread(target=lambda: sys.exit(main()) if False else main(),
                         name="big-stack")
    threading.stack_size(512 << 20)
    t = threading.Thread(target=main)
    t.start()
    t.join()
