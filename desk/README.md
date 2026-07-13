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

## lib/plan-asm — a text front-end

`lib/plan-asm.hoon` is a two-stage assembler mirroring reaver's
`PlanAssembler.hs`:

- `+read  text -> (list sexp)` — the generic S-expression reader (gaps,
  `;`-comments, `(…)` lists, decimal/string/symbol atoms).
- `+load  text -> [val env]`  — macroexpand + compile: `#bind` fills a
  global symbol table, `#pin` pins, and `#law` compiles a body to
  ref-encoded `+val` (a bound symbol → its ref index, a bare literal →
  quoted `(0 n)`, an application → apply-node `(0 f x)`, a free symbol →
  quoted global constant).

Surface subset (a clean, fully-specified dialect):

```
42                              a literal nat
"abc"                           a string (LSB-first cord nat)
name                            symbol: ref in a body, else a global
_0 _1 ...                       explicit refs in a body (_0 = the law)
(f x y)                         application
(#pin v)                        a pin
(#law tag (_0 _1 ..) body)      a law; arity = #args after self
(#bind name v)                  bind name in the global env
```

This is **not** byte-faithful Plan-Asm — that additionally needs
`#app`/`#macro`/`#export`/`#juxt`, the `natE`/`(1 n)` literal wrapping, and
the explicit `0`-tagged apply convention (bare `0` = ref 0, not literal).
The subset above is a friendlier surface over the same value model.

Validated on the fakezod (`text → load → norm:plan`):

- reader: `(a (b 42) c)` → the expected nested S-expression
- `(twice 7)` with `twice = \n. id (id n)` → `7` (globals embedded in a body,
  apply-node encoding)
- `(ap5 id)` with `ap5 = \n. (n 5)` → `5` (literal quoting inside a body)
- `(k 7 99)` with `k = {107 2 _1}` → `7` (multi-arg law, refs)

### Hoon notes (recursive-parser gotchas)

Two non-obvious pitfalls surfaced building this on a 408k pill:

1. A recursive `+$` whose recursion goes through `(list sexp)` sends the
   mull into an infinite grow **unless** you pin the mold's default with an
   explicit `$~` (here `$~ [%n 0]`).
2. Wet list gates (`snag`/`slag`/`rear`) over a list whose *element* type is
   recursive blow up the same mull. Destructure with plain `?~` /
   head-tail wings instead.

## Shortfalls & limitations

Read before relying on either lib. Nothing here is a silent
approximation — every gap below fails loud (crashes) rather than
returning a wrong value, except where noted as performance-only.

### Evaluator (`lib/plan`)

- **Inherited semantic deltas** (from nockplan, vs the marduk oracle):
  no shared-heap memoisation (performance only, values unaffected);
  letrec is threaded functionally, so *productive cyclic* letrec crashes
  on a stale hole where marduk's mutable heap would resolve it; law
  construction skips the build-time spine-forcing walk, which changes
  crash *timing* (surfaces at first use) but never values.
- **BPLAN coverage is the fixture subset only.** Implemented: `Inc Dec
  Pin` / `Add Sub Mul Eq Le Lt Gt Ge Ne` / `Law If Ifz Case2` / `Case3`
  / `Elim`. **Not** implemented — and present in `output.plan`: `Div`,
  `Mod`, `Lsh`, `Rsh`, `Bex`, `Seq`, and any other named op. An unknown
  op crashes rather than reducing.
- **No trampoline.** `whnf`/`norm` recurse on the host Nock stack, so
  extremely deep PLAN recursion can exhaust the runtime stack — the
  analogue of nockplan's Python deep-recursion caveat.
- **Opaque failures.** Malformed values fail with a bare `!!`; there are
  no source locations or messages, since PLAN values carry none.

### Text front-end (`lib/plan-asm`)

- **Not byte-faithful Plan-Asm.** Missing `#app`/`#macro`/`#export`/
  `#juxt`, the `natE`/`(1 n)` literal wrapping, and the raw `0`-tagged
  apply convention (bare `0` = ref 0). It will **not** round-trip
  `output.plan` verbatim — it is a friendlier surface over the same value
  model, not the reference reader.
- **`#law` letrec bindings are ignored.** Only `tag`, `sig`, and `body`
  compile; any forms between the sig and the body (the letrec binds) are
  dropped. Multi-binding letrec laws are unsupported.
- **Only `()` lists.** `{}` (curl) and `[]` (brak) are not handled and
  will fail to parse.
- **`#pin` content is evaluated structurally, not deep-forced.** Reaver's
  `mkPin` forces to normal form; here a pin wrapping a reducible
  application is left unreduced.
- **No diagnostics.** Parse/compile errors crash without location; `read`
  must consume the entire input (trailing garbage fails).

### Validation

- Checked against nockplan's **documented** expected values, not a live
  `marduk` oracle (marduk is not vendored in this repo). An independent
  oracle cross-check is future work.
- Exercised on the `urbit-408k-rc1` **fakezod** only; not yet run under
  production Vere or Ares.
- `tests/plan.hoon` is build-and-inspect (`=t -build-file …`, then
  `ok:t`); it is not wired into a `-test` / CI harness.
