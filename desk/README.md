# lib/plan — PLAN, evaluated natively in Nock (Hoon)

A faithful Hoon port of `nockplan.py`: the PLAN spec evaluator, written as
an ordinary Hoon `|%` core. Hoon compiles to Nock, so the compiled battery
*is* a PLAN evaluator that runs unmodified on any Nock runtime (Vere, Ares,
nockup, …) — the same claim `nockplan` makes, now in native Urbit source
rather than hand-assembled Nock formulas.

## Arm ↔ spec map

| arm       | spec | role                                             |
|-----------|------|--------------------------------------------------|
| `whnf`    | E    | evaluate to weak head normal form                |
| `norm`    | F    | force to normal form (`nockplan.nock_force`)     |
| `ari`     | A    | arity of a value                                 |
| `exec`    | X    | execute a saturated form (spine descent)         |
| `s0`      | S    | primop dispatch — core opcodes 0/1/2; `<66>`     |
| `c6`      | C    | the six-way eliminator                           |
| `ix`      | I    | reference resolution down the argument spine     |
| `r3`      | R    | body reduction (refs, quote, apply)              |
| `lx`      | L    | letrec line processing                           |
| `bx`      | B    | environment build (hole-push for lets)           |
| `nx`/`nn` | N    | force-to-nat                                      |
| `bp`      | —    | BPLAN (`<66>`) named-op subset                    |

`+val` is the native value type. `+from-noun`/`+to-noun` bridge the
numeric-tagged encoding nockplan uses (`[0 n] [1 i] [2 nam ari bod] [3 f x]
[4 0]`) for interop with the existing corpus. `+na`/`+pi`/`+la`/`+ap`/`+aps`
are value constructors.

Where nockplan implements `dec`/`add`/`sub`/`mul`/`lte` as counting loops
(raw Nock has only increment), this port uses the jetted standard-library
gates — exactly the cost-model asymmetry the nockplan README calls out. On a
real runtime the arithmetic is free.

Semantic deltas vs the marduk oracle are inherited verbatim from nockplan:
no shared-heap memoisation; letrec threaded functionally (productive cyclic
letrec crashes); law construction skips the build-time spine walk. Values
are unaffected.

## Running it

On any Urbit ship, drop `lib/plan.hoon` into a desk and build it:

```
|mount %base
:: cp desk/lib/plan.hoon <pier>/base/lib/plan.hoon
|commit %base
=plan -build-file /===/lib/plan/hoon
```

PLAN body encoding, for reference when hand-writing laws: inside a law body
a bare nat `k ≤ arity` is **reference k** (ref 0 = the law itself); a literal
must be quoted `(0 k)`; an application must be an apply-node `(0 f x)`.
BPLAN calls are `(<66> op args…)` and nest as ordinary values.

### Validation

Ported behaviour was checked against nockplan's own unit cases on a fakezod
(`urbit-408k-rc1` pill). All match:

- **arity**: `A` of nat/law/pin-law/pin-nat/app → `0/2/2/1/1`
- **evaluation**: `id 42 → 42`, `k 7 99 → 7`, over-application `(id 1) 2`
  stays stuck `(1 2)`, partial `(k 7)` stays a law-app
- **self-reference**: `{f 1 0} 5 → {f 1 0}` (ref 0 = the law)
- **S0 construction**: `(<0> (0 42)) → <42>`; `(<0> (1 2 k 1)) → {k 2 1}`
- **eliminator**: on nat `0 → z`; on nat `5 → (m 4)`; on `<9> → (p 9)`
- **apply-body law** `{ap 2 (0 1 2)}`: `(ap id 42) → 42`
- **letrec** backward-ref `(id id) → id`
- **BPLAN**: `Add(1,Mul(2,3))=7`, `Sub(3,5)=0` (monus), `Dec(0)=0`,
  `Eq(4,4)=1`, `Le(5,4)=0`, `Case2`, `Ifz`
- **recursion** (native): a factorial law computes `fact 3=6`, `fact 5=120`,
  `fact 0=1` — letrec + `If`-laziness + self-reference together
- **noun bridge**: `from-noun (to-noun v)` is identity
```
