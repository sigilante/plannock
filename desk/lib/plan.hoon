::  /lib/plan: PLAN, evaluated natively in Nock
::
::    A faithful Hoon port of the PLAN-in-Nock evaluator (`nockplan.py`),
::    the empirical rebuttal to "Nock cannot implement PLAN". Where
::    nockplan hand-assembles a Nock core out of raw formula combinators,
::    this is the same evaluator written as an ordinary Hoon `|%` core:
::    Hoon compiles to Nock, so the compiled battery *is* a PLAN evaluator
::    that runs unmodified on any Nock runtime (Vere, Ares, nockup, ...).
::
::    Each PLAN spec judgment is one arm:
::
::      ari   A   arity of a value
::      whnf  E   evaluate to weak head normal form
::      norm  F   force to normal form (the article's `nock_force`)
::      exec  X   execute a saturated form (spine descent + dispatch)
::      s0    S   primop dispatch (core opcodes 0/1/2; BPLAN via <66>)
::      c6    C   the six-way eliminator
::      ix    I   reference resolution down the argument spine
::      r3    R   body reduction (refs, quote, apply)
::      lx    L   letrec line processing
::      bx    B   environment build (hole-push for lets)
::      nx    N   force-to-nat (non-nats coerce to 0)
::      bp        BPLAN (<66>) primitive subset
::
::    nockplan's arithmetic arms (dec/add/sub/mul/lte as counting loops,
::    since raw Nock has only increment) collapse here to the jetted
::    standard-library gates. That is precisely the cost-model asymmetry
::    the nockplan README calls out: on a real runtime the jets are free.
::
::    Declared semantic deltas vs the marduk oracle are inherited verbatim
::    from nockplan (no shared-heap memoisation; letrec threaded
::    functionally, so productive cyclic letrec crashes; law construction
::    skips the build-time spine walk). Values are unaffected.
::
|%
::  +val: a PLAN value
::
::    The native representation. `+from-noun`/`+to-noun` bridge the
::    numeric-tagged encoding nockplan uses ([0 n] [1 i] [2 nam ari bod]
::    [3 f x] [4 0]) for interop with the existing corpus.
::
+$  val
  $%  [%nat n=@]                                       ::  a natural
      [%pin i=val]                                     ::  <i>   a pin
      [%law nam=@ ari=@ bod=val]                       ::  {n a b}  a law
      [%app f=val x=val]                               ::  (f x)  an app
      [%hol ~]                                         ::  <>    a hole
  ==
::                                                      ::
::::  entry points                                      ::
::                                                      ::
::  +whnf: evaluate to weak head normal form (spec E)
::
++  whnf
  |=  v=val
  ^-  val
  ?-  -.v
    %nat  v                                            ::  already WHNF
    %pin  v                                            ::
    %law  v                                            ::
    %hol  !!                                            ::  E<> crashes
      %app
    =/  ef  $(v f.v)                                   ::  force the head
    =/  ar  (ari ef)                                   ::  its arity
    =/  vp  `val`[%app ef x.v]                         ::  the fresh app
    ?.  =(1 ar)  vp                                    ::  unsaturated: stuck
    $(v (exec vp vp))                                  ::  saturated: run + re-E
  ==
::  +norm: force to normal form (spec F, the article's nock_force)
::
++  norm
  |=  v=val
  ^-  val
  =/  w  (whnf v)
  ?.  ?=(%app -.w)  w
  [%app $(v f.w) $(v x.w)]                             ::  force both legs
::                                                      ::
::::  spec judgments                                    ::
::                                                      ::
::  +ari: arity of a value (spec A)
::
++  ari
  |=  v=val
  ^-  @
  ?-  -.v
    %nat  0                                            ::  A@ = 0
    %law  ari.v                                        ::  A{a m b} = a
    %hol  !!                                            ::  A<> crashes
      %pin                                             ::  A<i>: law? its a; else 1
    =/  it  i.v
    ?:(?=(%law -.it) ari.it 1)
      %app                                             ::  A(f x) = max(0, Af - 1)
    =/  af  $(v f.v)
    ?:(=(0 af) 0 (dec af))
  ==
::  +exec: execute a saturated form (spec X)
::
::    Descend `k` through the App spine to the leaf head, then dispatch:
::    pinned-nat -> primop (S); pinned/bare law -> body reduction (B).
::
++  exec
  |=  [k=val e=val]
  ^-  val
  ?+  -.k  !!                                          ::  bare nat / hole: crash
    %app  $(k f.k)                                     ::  descend the spine
    %law  (bx ari.k ari.k e bod.k bod.k)               ::  bare law
      %pin
    =/  it  i.k
    ?+  -.it  !!
      %law  (bx ari.it ari.it e bod.it bod.it)         ::  pinned law
        %nat                                           ::  pinned nat: primop
      ?>  ?=([%app *] e)                               ::  e is (<o> arg)
      (s0 n.it (whnf x.e))
    ==
  ==
::  +s0: primop dispatch (spec S)
::
::    opn 0  = core PLAN: Pin/Law/Elim, chosen by spine depth (1/3/6)
::             and the structural leaf nat (0/1/2).
::    opn 66 = BPLAN named-op subset (see +bp).
::
++  s0
  |=  [opn=@ arg=val]
  ^-  val
  ?:  =(66 opn)  (bp arg)
  ?.  =(0 opn)  !!
  =/  sp  (spyne arg)                                  ::  flatten the spine
  =/  hd  hed.sp
  ?>  ?=([%nat *] hd)                                  ::  leaf must be a nat
  =/  op  n.hd                                         ::  the structural opcode
  =/  as  arg.sp
  =/  ln  (lent as)
  ?:  &(=(1 ln) =(0 op))                               ::  (0 x): Pin
    [%pin (whnf (snag 0 as))]
  ?:  &(=(3 ln) =(1 op))                               ::  (1 a m b): Law
    (mklaw (snag 0 as) (snag 1 as) (snag 2 as))
  ?:  &(=(6 ln) =(2 op))                               ::  (2 p l a z m o): Elim
    %-  c6
    :*  (snag 0 as)  (snag 1 as)  (snag 2 as)
        (snag 3 as)  (snag 4 as)  (whnf (snag 5 as))
    ==
  !!
::  +c6: the six-way eliminator (spec C)
::
++  c6
  |=  [p=val l=val az=val z=val m=val o=val]
  ^-  val
  ?-  -.o
    %pin  [%app p i.o]                                 ::  <i>       -> (p i)
    %law  [%app [%app [%app l [%nat nam.o]] [%nat ari.o]] bod.o]  ::  {n a b} -> l n a b
    %app  [%app [%app az f.o] x.o]                     ::  (f x)     -> (a f x)
    %hol  !!                                           ::  <>        crashes
      %nat                                             ::  0 -> z ; n -> (m (n-1))
    ?:(=(0 n.o) z [%app m [%nat (dec n.o)]])
  ==
::  +ix: reference resolution (spec I)
::
::    Walk `n` steps down the head of the App spine `o`; `f` is the
::    fallback when the spine runs out.
::
++  ix
  |=  [f=val o=val n=@]
  ^-  val
  ?:  =(0 n)  ?:(?=(%app -.o) x.o o)
  ?.  ?=(%app -.o)  f
  $(o f.o, n (dec n))
::  +r3: body reduction (spec R)
::
::    Rne(b:@)|b<=n = I(n-b)e ; Rne(0 f x) = (Rnef Rnex) ;
::    Rne(0 x) = x ; otherwise pass through.
::
++  r3
  |=  [n=@ e=val b=val]
  ^-  val
  ?-  -.b
    %pin  b
    %law  b
    %hol  b
      %nat                                             ::  reference or literal
    ?.  (lte n.b n)  b                                 ::  b > n: literal nat
    (ix b e (sub n n.b))                               ::  b <= n: resolve
      %app
    ?-  -.f.b
      %pin  b
      %law  b
      %hol  b
      %nat  ?:(=(0 n.f.b) x.b b)                       ::  (0 x): quote -> x
        %app                                           ::  (0 f x): apply both
      ?:  ?&(?=(%nat -.f.f.b) =(0 n.f.f.b))
        [%app (r3 n e x.f.b) (r3 n e x.b)]
      b                                                ::  spine too long: pass
    ==
  ==
::  +lx: letrec line processing (spec L)
::
::    A let line has the form (1 v b'). Its value is reduced, written into
::    the env slot at depth (n-i), and processing continues with b'.
::    Non-let bodies hand off to +r3.
::
++  lx
  |=  [i=@ n=@ e=val b=val]
  ^-  val
  ?.  ?=(%app -.b)      (r3 n e b)
  ?.  ?=(%app -.f.b)    (r3 n e b)
  ?.  ?=(%nat -.f.f.b)  (r3 n e b)
  ?.  =(1 n.f.f.b)      (r3 n e b)
  =/  w   (r3 n e x.f.b)                               ::  reduce the bound value
  =/  e2  (envset e (sub n i) w)                       ::  functional slot update
  $(i +(i), e e2, b x.b)                               ::  continue with b'
::  +bx: environment build (spec B)
::
::    Each leading (1 _ k) binder pushes a hole onto the env and recurses;
::    when the binders run out, hand off to +lx.
::
++  bx
  |=  [a=@ n=@ e=val b=val x=val]
  ^-  val
  ?.  ?=(%app -.x)      (lx +(a) n e b)
  ?.  ?=(%app -.f.x)    (lx +(a) n e b)
  ?.  ?=(%nat -.f.f.x)  (lx +(a) n e b)
  ?.  =(1 n.f.f.x)      (lx +(a) n e b)
  $(n +(n), e [%app e [%hol ~]], x x.x)                ::  push a hole
::  +nx: force to a nat (spec N); non-nats coerce to nat 0
::
++  nx
  |=  v=val
  ^-  val
  =/  w  (whnf v)
  ?:(?=(%nat -.w) w [%nat 0])
::  +nn: +nx unwrapped to a raw atom (for arithmetic primops)
::
++  nn
  |=  v=val
  ^-  @
  =/  w  (nx v)
  ?>(?=(%nat -.w) n.w)
::  +mklaw: shared law construction (S0 (1 a m b) and BPLAN Law)
::
++  mklaw
  |=  [a=val m=val b=val]
  ^-  val
  =/  av  (nn a)
  ?<  =(0 av)                                          ::  arity 0 is illegal
  =/  bv  (whnf b)                                     ::  body to WHNF
  [%law (nn m) av bv]
::  +envset: functional slot update at depth `d` in the env's left spine
::
::    The pure replacement for marduk's Val.update on the letrec env.
::
++  envset
  |=  [e=val d=@ nv=val]
  ^-  val
  ?>  ?=(%app -.e)
  ?:  =(0 d)  [%app f.e nv]
  [%app (envset f.e (dec d) nv) x.e]
::  +bp: BPLAN (<66>) named-op subset
::
::    Dispatch by argument count, then by the leaf name-nat. Names are
::    LSB-first byte strings -- i.e. ordinary Hoon cords, so 'Add' matches
::    directly. Branch-selecting ops (If/Ifz/Case2/Case3) return the
::    chosen branch *unforced*: whnf re-drives it, and that laziness is
::    what lets recursion terminate.
::
++  bp
  |=  arg=val
  ^-  val
  =/  sp  (spyne arg)
  =/  hd  hed.sp
  ?>  ?=([%nat *] hd)
  =/  nm  n.hd
  =/  as  arg.sp
  =/  ln  (lent as)
  ::  1-ary: Inc / Dec / Pin
  ?:  =(1 ln)
    =/  x  (snag 0 as)
    ?:  =(nm 'Inc')  [%nat +((nn x))]
    ?:  =(nm 'Dec')  =/(xn (nn x) ?:(=(0 xn) [%nat 0] [%nat (dec xn)]))
    ?:  =(nm 'Pin')  [%pin (whnf x)]
    !!
  ::  2-ary: Add / Mul / Sub / Eq / Le / Lt / Gt / Ge / Ne
  ?:  =(2 ln)
    =/  xn  (nn (snag 0 as))
    =/  yn  (nn (snag 1 as))
    ?:  =(nm 'Add')  [%nat (add xn yn)]
    ?:  =(nm 'Mul')  [%nat (mul xn yn)]
    ?:  =(nm 'Sub')  ?:((lte yn xn) [%nat (sub xn yn)] [%nat 0])
    ?:  =(nm 'Eq')   ?:(=(xn yn) [%nat 1] [%nat 0])
    ?:  =(nm 'Le')   ?:((lte xn yn) [%nat 1] [%nat 0])
    ?:  =(nm 'Lt')   ?:(=(xn yn) [%nat 0] ?:((lte xn yn) [%nat 1] [%nat 0]))
    ?:  =(nm 'Gt')   ?:((lte xn yn) [%nat 0] [%nat 1])
    ?:  =(nm 'Ge')   ?:((lte yn xn) [%nat 1] [%nat 0])
    ?:  =(nm 'Ne')   ?:(=(xn yn) [%nat 0] [%nat 1])
    !!
  ::  3-ary: Law / If / Ifz / Case2
  ?:  =(3 ln)
    =/  x1  (snag 0 as)
    =/  x2  (snag 1 as)
    =/  x3  (snag 2 as)
    ?:  =(nm 'Law')  (mklaw x1 x2 x3)
    ?:  =(nm 'If')
      =/  cw  (whnf x1)
      ?.  ?=(%nat -.cw)  x2                            ::  cells are truthy
      ?:(=(0 n.cw) x3 x2)
    ?:  =(nm 'Ifz')
      =/  cw  (whnf x1)
      ?.  ?=(%nat -.cw)  x3
      ?:(=(0 n.cw) x2 x3)
    ?:  =(nm 'Case2')  ?:(=(0 (nn x1)) x2 x3)
    !!
  ::  4-ary: Case3
  ?:  =(4 ln)
    ?.  =(nm 'Case3')  !!
    =/  sel  (nn (snag 0 as))
    ?:(=(0 sel) (snag 1 as) ?:(=(1 sel) (snag 2 as) (snag 3 as)))
  ::  6-ary: Elim
  ?:  =(6 ln)
    ?.  =(nm 'Elim')  !!
    %-  c6
    :*  (snag 0 as)  (snag 1 as)  (snag 2 as)
        (snag 3 as)  (snag 4 as)  (whnf (snag 5 as))
    ==
  !!
::                                                      ::
::::  helpers                                           ::
::                                                      ::
::  +spyne: flatten an App spine into its leaf head and ordered args
::
::    (((h a0) a1) a2) -> [hed=h arg=~[a0 a1 a2]]
::
++  spyne
  |=  v=val
  ^-  [hed=val arg=(list val)]
  =|  as=(list val)
  |-  ^-  [val (list val)]
  ?.  ?=(%app -.v)  [v as]
  $(v f.v, as [x.v as])
::                                                      ::
::::  interop with the nockplan numeric-tagged encoding ::
::                                                      ::
::  +from-noun: decode a tagged PLAN noun into a +val
::
++  from-noun
  |=  n=*
  ^-  val
  ?>  ?=([@ *] n)
  ?+  -.n  !!
    %0  ?>(?=(@ +.n) [%nat +.n])
    %1  [%pin (from-noun +.n)]
    %4  [%hol ~]
      %2
    =/  r  +.n
    ?>  ?=([@ @ *] r)
    [%law -.r +<.r (from-noun +>.r)]
      %3
    =/  r  +.n
    ?>  ?=(^ r)
    [%app (from-noun -.r) (from-noun +.r)]
  ==
::  +to-noun: encode a +val back to a tagged PLAN noun
::
++  to-noun
  |=  v=val
  ^-  *
  ?-  -.v
    %nat  [0 n.v]
    %pin  [1 (to-noun i.v)]
    %law  [2 nam.v ari.v (to-noun bod.v)]
    %app  [3 (to-noun f.v) (to-noun x.v)]
    %hol  [4 0]
  ==
::                                                      ::
::::  value constructors (ergonomics)                   ::
::                                                      ::
++  na  |=(n=@ `val`[%nat n])                           ::  a nat
++  pi  |=(v=val `val`[%pin v])                         ::  a pin
++  ho  `val`[%hol ~]                                   ::  a hole
++  la  |=([nam=@ ari=@ bod=val] `val`[%law nam ari bod])
++  ap  |=([f=val x=val] `val`[%app f x])               ::  one application
::  +aps: apply a head to a list of arguments, left to right
::
++  aps
  |=  [hed=val arg=(list val)]
  ^-  val
  ?~  arg  hed
  $(hed [%app hed i.arg], arg t.arg)
--
