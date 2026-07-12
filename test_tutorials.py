"""Acceptance: marduk's tutorial notebooks (01-04) on the Nock core.

Every code cell of every tutorial runs through a persistent
PlanKernelEvaluator whose backend is nock_force. Cell outputs must match
the committed notebook outputs (which marduk's own test_tutorials.py
holds its stock evaluator to). One evaluator per notebook — bindings
made in earlier cells (all computed by the Nock machine) feed later
cells, so notebook 04's recursive programs exercise the full
E->X->B->L->R->S0->C6 loop over Nock-computed environments.
"""
import sys, os, threading, time, json

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "marduk", "packages", "marduk"))
sys.path.insert(0, os.path.join(HERE, "..", "marduk", "packages", "plan-kernel"))

sys.setrecursionlimit(400_000)

TUTORIALS = os.path.join(HERE, "..", "marduk", "packages",
                         "plan-kernel", "tutorials")
NOTEBOOKS = [
    "01-numbers-and-pins.ipynb",
    "02-laws.ipynb",
    "03-elim-and-cases.ipynb",
    "04-recursion.ipynb",
]


def _code_cells(nb):
    for i, cell in enumerate(nb["cells"]):
        if cell["cell_type"] != "code":
            continue
        src = cell["source"]
        if isinstance(src, list):
            src = "".join(src)
        outputs = cell.get("outputs", [])
        text_out = ""
        if outputs:
            data = outputs[0].get("data", {})
            text_out = data.get("text/plain", "")
            if isinstance(text_out, list):
                text_out = "".join(text_out)
        yield i, src, text_out


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

    picks = sys.argv[1:]
    books = [n for n in NOTEBOOKS
             if not picks or any(p in n for p in picks)]

    total_ok = total_fail = 0
    for name in books:
        path = os.path.join(TUTORIALS, name)
        with open(path) as f:
            nb = json.load(f)

        ev = PlanKernelEvaluator()
        ev._backend = nock_force
        ok = fail = 0
        t0 = time.time()
        for i, src, expected in _code_cells(nb):
            tc = time.time()
            try:
                r = ev.eval_cell(src)
                # %backend magic reverts per-cell but also our _backend
                # assignment survives (we set the attribute directly and
                # eval_cell restores it after the cell) — re-pin anyway.
                ev._backend = nock_force
                got, err = r.value_text, r.error
            except Exception as e:               # noqa: BLE001
                got, err = None, repr(e)
            print(f"  cell {i:3d} [{time.time()-tc:6.1f}s] "
                  f"{(got or '').split(chr(10))[0][:60]}", flush=True)
            if err is None and (got or "") == (expected or ""):
                ok += 1
            else:
                fail += 1
                print(f"  FAIL {name} cell {i}: got={got!r} "
                      f"expected={expected!r} err={err}")
                print(f"       src: {src[:140]!r}")
        dt = time.time() - t0
        total_ok += ok
        total_fail += fail
        print(f"{name}: {ok} ok, {fail} failed [{dt:.1f}s]")
    print(f"\nTOTAL: {total_ok} ok, {total_fail} failed")


if __name__ == "__main__":
    threading.stack_size(512 << 20)
    t = threading.Thread(target=main)
    t.start()
    t.join()
