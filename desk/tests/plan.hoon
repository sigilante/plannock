::  /tests/plan: assertions for lib/plan and lib/plan-asm
::
::    Build and inspect on a ship:
::      =t -build-file /===/tests/plan/hoon
::      ok:t            ::  %.y iff every case passes
::      fails:t         ::  the labels of any failing cases
::
::    Each case is [label ?]; the whole suite mirrors the dojo checks in
::    ../README.md (evaluator + text front-end), so a green `ok` reproduces
::    that validation from source.
::
/+  plan, plan-asm
=,  plan
|%
::  builders / bplan helpers
::
++  b66  (pi (na 66))                                   ::  <66>
++  bp1  |=([nm=@ x=val] (ap b66 (ap (na nm) x)))
++  bp2  |=([nm=@ x=val y=val] (ap b66 (aps (na nm) ~[x y])))
++  a0   |=([f=val x=val] (aps (na 0) ~[f x]))          ::  body apply-node (0 f x)
++  qq   |=(k=@ (ap (na 0) (na k)))                     ::  body literal (0 k)
::  a factorial law, arity 1: if n==0 then 1 else n*fact(n-1)
::
++  fact
  ^-  val
  =/  rn   (na 1)                                        ::  ref: the argument n
  =/  rf   (na 0)                                        ::  ref: the law itself
  =/  cnd  (a0 b66 (a0 (a0 (na 'Eq') rn) (qq 0)))        ::  (<66> (Eq n 0))
  =/  dcn  (a0 b66 (a0 (na 'Dec') rn))                   ::  (<66> (Dec n))
  =/  rec  (a0 rf dcn)                                   ::  (fact (Dec n))
  =/  els  (a0 b66 (a0 (a0 (na 'Mul') rn) rec))          ::  (<66> (Mul n rec))
  =/  ifs  (a0 (a0 (a0 (na 'If') cnd) (qq 1)) els)       ::  (If cnd 1 els)
  (la 0x66 1 (a0 b66 ifs))
::  parser programs (numeric law tags avoid nested quotes)
::
++  p-twice
  '(#bind id (#law 105 (_0 _1) _1)) (#bind twice (#law 2 (_0 _1) (id (id _1)))) (twice 7)'
++  p-ap5
  '(#bind id (#law 105 (_0 _1) _1)) (#bind ap5 (#law 1 (_0 _1) (_1 5))) (ap5 id)'
++  p-k
  '(#bind k (#law 107 (_0 _1 _2) _1)) (k 7 99)'
::  ~laws used across cases
::
++  idl  (la 0x6469 1 (na 1))                            ::  {id 1 1}
++  kl   (la 0x6b 2 (na 1))                              ::  {k 2 1}
::  the suite
::
++  cases
  ^-  (list [@t ?])
  |^
  ^-  (list [@t ?])
  :~  ['A nat' (nats 0 (ari (na 5)))]
      ['A law' (nats 2 (ari kl))]
      ['A pin-law' (nats 2 (ari (pi kl)))]
      ['A pin-nat' (nats 1 (ari (pi (na 0))))]
      ['A app' (nats 1 (ari (ap kl (na 9))))]
    ::
      ['id 42' (natv 42 (norm (ap idl (na 42))))]
      ['k 7 99' (natv 7 (norm (aps kl ~[(na 7) (na 99)])))]
      ['over-app (id 1) 2' =([%app [%nat 1] [%nat 2]] (norm (aps idl ~[(na 1) (na 2)])))]
      ['self law' =([%law 0x66 1 [%nat 0]] (norm (ap (la 0x66 1 (na 0)) (na 5))))]
    ::
      ['S0 mk-pin' =([%pin [%nat 42]] (norm (ap (pi (na 0)) (ap (na 0) (na 42)))))]
      ['S0 mk-law' =([%law 0x6b 2 [%nat 1]] (norm (ap (pi (na 0)) (aps (na 1) ~[(na 2) (na 0x6b) (na 1)]))))]
      ['elim z' (natv 13 (norm (elim (na 0))))]
      ['elim m' (natv 4 (norm (elim (na 5))))]
      ['elim p' =([%app [%nat 10] [%nat 9]] (norm (elim (pi (na 9)))))]
    ::
      ['bplan add/mul' (natv 7 (norm (bp2 'Add' (na 1) (bp2 'Mul' (na 2) (na 3)))))]
      ['bplan monus' (natv 0 (norm (bp2 'Sub' (na 3) (na 5))))]
      ['bplan dec0' (natv 0 (norm (bp1 'Dec' (na 0))))]
      ['bplan eq' (natv 1 (norm (bp2 'Eq' (na 4) (na 4))))]
      ['bplan le' (natv 0 (norm (bp2 'Le' (na 5) (na 4))))]
    ::
      ['fact 3' (natv 6 (norm (ap fact (na 3))))]
      ['fact 5' (natv 120 (norm (ap fact (na 5))))]
      ['fact 0' (natv 1 (norm (ap fact (na 0))))]
    ::
      ['noun roundtrip' =(fact (from-noun (to-noun fact)))]
    ::
      ['asm read' =(~[[%l ~[[%s 97] [%l ~[[%s 98] [%n 42]]] [%s 99]]]] (read:plan-asm '(a (b 42) c)'))]
      ['asm twice 7' (natv 7 (norm -:(load:plan-asm p-twice)))]
      ['asm ap5 -> 5' (natv 5 (norm -:(load:plan-asm p-ap5)))]
      ['asm k 7 99' (natv 7 (norm -:(load:plan-asm p-k)))]
  ==
  ::  local predicates
  ++  nats  |=([a=@ b=@] =(a b))
  ++  natv  |=([n=@ v=val] =(`val`[%nat n] v))
  ::  elim: (<0> (2 10 11 12 13 id o)) — p=10 l=11 az=12 z=13 m=id
  ++  elim
    |=  o=val
    (ap (pi (na 0)) (aps (na 2) ~[(na 10) (na 11) (na 12) (na 13) idl o]))
  --
++  fails  (murn cases |=([l=@t p=?] ?:(p ~ (some l))))
++  ok     ?=(~ fails)
--
