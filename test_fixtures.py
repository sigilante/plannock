"""Acceptance: marduk's six fixture programs, evaluated on the Nock core.

For each fixture we run the full plan-kernel pipeline twice:
  oracle:  stock backend (marduk's spec evaluator)
  nock:    same pipeline, _backend swapped for nock_force
and require identical rendered output, which must also equal the
expected values hard-coded in marduk's own test_fixtures.py.
"""
import sys, os, threading, time, pathlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "marduk", "packages", "marduk"))
sys.path.insert(0, os.path.join(HERE, "..", "marduk", "packages", "plan-kernel"))

sys.setrecursionlimit(400_000)

FIXTURES = pathlib.Path(HERE, "..", "marduk", "packages",
                        "plan-kernel", "tests", "fixtures")

# Expectations copied from marduk's test_fixtures.py.
EXPECT = {
    "id":          "42",
    "k":           "7",
    "s":           "42",
    "arithmetic":  "7",
    "elim":        "1",
    "church_bool": "20",
}


def main():
    import hostjets
    mode = os.environ.get("NOCKPLAN_JETS", "1")
    if mode != "0":
        hostjets.VALIDATE = (mode == "validate")
        hostjets.install()
        print(f"[jets: on, validate={hostjets.VALIDATE}]")
    else:
        print("[jets: off — pure Nock]")
    from plan_kernel.evaluator import PlanKernelEvaluator
    from nockplan import nock_force

    ok = fail = 0
    for name, expected in EXPECT.items():
        src = (FIXTURES / f"{name}.plan").read_text()

        ev_o = PlanKernelEvaluator()
        r_o = ev_o.eval_cell(src)

        ev_n = PlanKernelEvaluator()
        ev_n._backend = nock_force
        t0 = time.time()
        try:
            r_n = ev_n.eval_cell(src)
            n_text, n_err = r_n.value_text, r_n.error
        except Exception as e:                       # noqa: BLE001
            n_text, n_err = None, repr(e)
        dt = time.time() - t0

        o_text = r_o.value_text
        status = "ok  " if (n_err is None and n_text == o_text == expected) \
                 else "FAIL"
        if status == "ok  ":
            ok += 1
        else:
            fail += 1
        print(f"{status} {name:12s} oracle={o_text!r} nock={n_text!r} "
              f"expected={expected!r} err={n_err} [{dt:.1f}s]")
    print(f"\n{ok} ok, {fail} failed")


if __name__ == "__main__":
    threading.stack_size(512 << 20)
    t = threading.Thread(target=main)
    t.start()
    t.join()
