::  /lib/plan-asm: a text front-end for lib/plan
::
::    A two-stage assembler, mirroring reaver's PlanAssembler.hs:
::
::      +read   text  -> (list sexp)     the generic S-expression reader
::      +load   text  -> [val env]       macroexpand + compile to +val
::
::    Surface subset (a clean, fully-specified dialect — NOT byte-faithful
::    Plan-Asm, which additionally needs #app/#macro/#export/#juxt, the
::    natE/`(1 n)` literal wrapping, and the explicit `0`-tagged apply
::    convention; see the README for the fidelity gap):
::
::      42            a literal nat
::      "abc"         a string literal (LSB-first cord nat)
::      name          a symbol: inside a law body, a ref; else a global
::      _0 _1 ...     explicit refs inside a law body (_0 = the law itself)
::      (f x y)       application, left-nested
::      (#pin v)      a pin of v
::      (#law "tag" (_0 _1 ..) body)   a law; arity = #args after self
::      (#bind name v)                 bind name in the global env
::
::    Inside a law body the compiler does the ref-encoding automatically:
::    a bound symbol becomes its ref index, a bare literal is quoted `(0 n)`,
::    an application becomes an apply-node `(0 f x)`, and a free symbol is
::    embedded as a quoted global constant.
::
/+  plan
=,  plan
|%
+$  sexp                                                ::  read result
  $~  [%n 0]
  $%  [%n p=@]                                          ::  literal nat
      [%s p=@]                                          ::  symbol / name
      [%l p=(list sexp)]                                ::  ( ... )
  ==
+$  env  (map @ val)                                    ::  global symbol table
::                                                      ::
::::  stage 1: the reader                               ::
::                                                      ::
++  exclude  ~[' ' '\0a' '\09' '\0d' ';' '(' ')' '[' ']' '{' '}' '"']
++  toksym   ;~(less (mask exclude) next)               ::  a symbol char
++  comment  ;~(pfix (just ';') (star ;~(less (just '\0a') next)))
++  gap      (star ;~(pose (just ' ') (just '\0a') (just '\09') (just '\0d') comment))
++  strlit   (ifix [(just '"') (just '"')] (star ;~(less (just '"') next)))
++  form                                                ::  one S-expr (eats lead gap)
  |=  tub=nail
  ^-  (like sexp)                                        ::  cast pins recursion
  %.  tub
  ;~  pfix  gap
    ;~  pose
      (stag %l (ifix [(just '(') ;~(pfix gap (just ')'))] (star form)))
      (stag %n (cook crip strlit))
      (stag %n dem:ag)                                  ::  decimal literal
      (stag %s (cook crip (plus toksym)))               ::  symbol / name
    ==
  ==
++  read  |=(txt=@t (scan (trip txt) ;~(sfix (star form) gap)))
::                                                      ::
::::  stage 2: macroexpand + compile                    ::
::                                                      ::
::  +load: read a program, returning the last value and the global env
::
++  load
  |=  txt=@t
  ^-  [val env]
  =|  en=env
  =/  out=val  [%nat 0]
  =/  fs  (read txt)
  |-  ^-  [val env]
  ?~  fs  [out en]
  =/  f  i.fs
  ?:  ?&  ?=(%l -.f)
          ?=(^ p.f)
          ?=(%s -.i.p.f)
          =('#bind' p.i.p.f)
      ==
    =/  xs=(list sexp)  p.f
    ?~  xs  !!
    ?~  t.xs  !!
    ?~  t.t.xs  !!
    =/  nm  i.t.xs
    ?>  ?=(%s -.nm)
    =/  vv  (ev en i.t.t.xs)
    $(en (~(put by en) p.nm vv), fs t.fs)
  $(out (ev en f), fs t.fs)
::  +ev: evaluate a top-level sexp to a value (structural; #-forms expand)
::
++  ev
  |=  [en=env s=sexp]
  ^-  val
  ?-  -.s
    %n  [%nat p.s]
    %s  (~(got by en) p.s)                              ::  global reference
    %l  (evl en p.s)
  ==
++  evl
  |=  [en=env xs=(list sexp)]
  ^-  val
  ?~  xs  !!
  =/  hd  i.xs
  ?.  ?=(%s -.hd)
    (apps (turn xs |=(s=sexp `val`(ev en s))))
  ?:  =('#pin' p.hd)
    ?~  t.xs  !!
    [%pin (ev en i.t.xs)]
  ?:  =('#law' p.hd)  (complaw en t.xs)
  (apps (turn xs |=(s=sexp `val`(ev en s))))
::  +apps: fold a list of values into a left-nested application
::
++  apps
  |=  vs=(list val)
  ^-  val
  ?~  vs  !!
  |-  ^-  val
  ?~  t.vs  i.vs
  $(i.vs [%app i.vs i.t.vs], t.vs t.t.vs)
::  +complaw: compile a (#law tag sig .. body) form
::
++  complaw
  |=  [en=env fs=(list sexp)]                           ::  fs = tag sig body
  ^-  val
  ?~  fs  !!                                            ::  tag
  ?~  t.fs  !!                                          ::  sig
  ?~  t.t.fs  !!                                        ::  body
  =/  tv  (ev en i.fs)
  ?>  ?=(%nat -.tv)
  =/  sig  i.t.fs
  ?>  ?=(%l -.sig)
  =/  body-s  i.t.t.fs                                  ::  ignoring letrec binds
  =/  syms=(list @)
    %+  turn  p.sig
    |=(s=sexp ?>(?=(%s -.s) p.s))
  ?~  syms  !!                                          ::  need at least self
  =/  ari  (dec (lent syms))
  =/  loc=(map @ @)
    %-  ~(gas by *(map @ @))
    (spin-locals syms)
  [%law n.tv ari (comp en loc body-s)]
::  +spin-locals: [_0 _1 _2] -> {[_0 0] [_1 1] [_2 2]}
::
++  spin-locals
  |=  syms=(list @)
  ^-  (list [@ @])
  =/  ix  0
  |-  ^-  (list [@ @])
  ?~  syms  ~
  [[i.syms ix] $(syms t.syms, ix +(ix))]
::  +comp: compile a sexp *inside a law body* to ref-encoded val
::
++  comp
  |=  [en=env loc=(map @ @) s=sexp]
  ^-  val
  ?-  -.s
    %n  [%app [%nat 0] [%nat p.s]]                      ::  literal: quote (0 n)
      %s
    =/  hit  (~(get by loc) p.s)
    ?^  hit  [%nat u.hit]                               ::  a reference
    [%app [%nat 0] (~(got by en) p.s)]                  ::  global: quote (0 gv)
      %l
    ?:  ?&  ?=(^ p.s)
            ?=(%s -.i.p.s)
            ?|(=('#pin' p.i.p.s) =('#law' p.i.p.s))
        ==
      [%app [%nat 0] (evl en p.s)]                      ::  nested #-form: quote
    (applynodes (turn p.s |=(s2=sexp `val`(comp en loc s2))))
  ==
::  +applynodes: fold compiled parts into apply-nodes (0 f x)
::
++  applynodes
  |=  cs=(list val)
  ^-  val
  ?~  cs  !!
  |-  ^-  val
  ?~  t.cs  i.cs
  $(i.cs [%app [%app [%nat 0] i.cs] i.t.cs], t.cs t.t.cs)
--
