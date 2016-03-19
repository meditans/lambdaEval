-- * Examples

-- Long notation:
-- LC>-- eval (A (L x (A (Var x) (Var x))) (L y (A (Var y) (Var z))))
-- LC>-- -- A (Var (VC 0 "z")) (Var (VC 0 "z"))

-- Short notation:
-- LC> eval $ (x ^ x # x) # (y ^ y # z)
-- LC> -- z z

-- The following example checks the hygiene of substitutions:

-- LC> -- eval (L a (A (L x (L a (A (Var x) (Var a)))) (Var a)))
-- LC> --- - L (VC 0 "a") (L (VC 1 "a") (A (Var (VC 0 "a")) (Var (VC 1 "a"))))

-- LC> eval $ a ^ (x ^ a ^ a # x) # (a # x)
-- LC> --- (\a. (\a~1. a~1 (a x)))

-- LC> subst (c^c)  (VC 1 "c") c
-- LC> -- (\c~2. c~2)

-- LC> -- Substituting (c~1 c~2) for c in (\c~1. c (c~1 (c~2 c~3)))
-- LC> subst (L (VC 1 "c") (A (Var (VC 0 "c")) (A (Var (VC 1 "c")) (A (Var (VC 2 "c")) (Var (VC 3 "c") ))))) (VC 0 "c") (A (Var (VC 1 "c")) (Var (VC 2 "c")))
-- LC> -- (\c~4. c~1 c~2 (c~4 (c~2 c~3)))

-- Now check eta-reductions:
-- LC> eval $ a ^ (x ^ a ^ x # a) # a
-- LC> --- (\a. a)

-- LC> eval $ a ^ (x ^ b ^ x # a) # a
-- LC> --- (\a. (\b. a a))

-- LC>-- compute a*(a+b)
-- LC> eval $ (a ^ b ^ f ^ a # (x ^ ((b # f) # (a # f # x))))
-- LC>  # (f ^ x ^ f # (f # x)) -- Numeral 2
-- LC>  # (f ^ x ^ f # x)               -- Numeral 1

-- LC> --- (\f. (\x. f (f (f (f (f (f x)))))))

-- Check determining the list of free variables in a term
-- LC> free_vars $ (x^x^y)#(x#y#z)         -- [y,x,y,z]
-- LC> free_vars $ eval $ (x^x^y)#(x#y#z)  -- [y]

-- We can compare two terms modulo alpha-renaming of bound identifiers
-- LC> term_equal_p (x^x^x#y) $ x^z^z#y  -- True
-- LC> term_equal_p (x^x^x#y) $ z^x^z#y  -- False

-- Evaluate and print an "infinite" term
-- LC> let y_comb = f^((p^p#p) # (c ^ f#(c#c))) in eval $ y_comb#c
-- LC> -- c (c (c (c (c (c (c (c (c (c (...))))))))))

-- * More extensive test cases

-- > -- Generic tester
-- > expectg (==) exp expected_result =
-- >        exp == expected_result ||
-- >        error ("Test case failure: Expected " ++ (show expected_result)
-- >              ++ ", received: " ++ (show exp))
-- > expect:: (Eq a,Show a) => a -> a -> Bool
-- > expect = expectg (==)
-- > expectd = expectg term_equal_p -- test using comparison modulo alpha-renaming
-- > notexpectd = expectg (\x y -> not $ term_equal_p x y)

-- > free_var_tests = and [
-- >    expect (map Var (free_vars $ x))  [x],
-- >    expect (map Var (free_vars $ x^x)) [],
-- >    expect (map Var (free_vars $ p#y#z)) [p,y,z],
-- >    expect (map Var (free_vars $ x^x#y)) [y],
-- >    expect (map Var (free_vars $ (x^x#y)#(x#y#z))) [y,x,y,z],
-- >    expect (map Var (free_vars $ (x^x^x#y)#(x^y^x#y))) [y]
-- >    ]

-- > alpha_comparison_tests = and [
-- >    expectd    x x,
-- >    notexpectd x y,
-- >    expectd    (x) x,
-- >    expectd    x  ((x)),
-- >    expectd    (x) ((x)),
-- >    expectd    (a#b#(c)) ((a#b)#c),
-- >    expectd    (((a#(b#c))#(q))#(p#f)) (a#(b#c)#q#(p#f)),
-- >    notexpectd (a#(b#c)#q#(p#f)) (a#b#c#q#(p#f)),
-- >    notexpectd (x^x) (x^y),
-- >    expectd    (x^x) (y^y),
-- >    expectd    (x^x^x) (y^y^y),
-- >    notexpectd (x^(x#x)) $ y^(y#x),
-- >    notexpectd (y^(y#x)) $ x^(x#x),
-- >    expectd    (y^(y#x)) $ z^(z#x),
-- >    notexpectd (x^y^(x#y)) $ f^f^(f#f),
-- >    expectd    (x^x^(x#x)) $ f^f^(f#f),
-- >    expectd    (x^y^(y#y)) $ f^f^(f#f),
-- >    expectd    (f^x^f#x) $ f^x^f#x,
-- >    notexpectd (f^x^f#x) $ f^x^x,
-- >    expectd    (f^x^f#x) $ g^x^(g#x),
-- >    expectd    (f^x^f#x) $ g^y^g#y,
-- >    expectd    (g^y^g#y) $ f^x^f#x,
-- >    notexpectd (g^y^g#x) $ f^x^f#x,
-- >    notexpectd (f^x^f#x) (g^y^g#x)
-- >    ]
-- >
-- > subst_tests = and [
-- >   expectd (subst (c^c)  (VC 1 "c") c) (z^z),
-- >   expectd (subst (L (VC 1 "c") (A (Var (VC 0 "c")) (A (Var (VC 1 "c"))
-- >                  (A (Var (VC 2 "c")) (Var (VC 3 "c") )))))
-- >                  (VC 0 "c") (A (Var (VC 1 "c")) (Var (VC 2 "c"))))
-- >         (a^(Var $ VC 1 "c")#(Var $ VC 2 "c")#
-- >            (a#((Var $ VC 2 "c")#(Var $ VC 3 "c"))))
-- >   ]
-- >
-- > eval_tests = and [
-- >    expectd (eval $ ((x^(a#b#x))#(a^a#b))) $
-- >               (a#b#(p^p#b)),
-- >    expectd (eval $ (((f^x^(f#x))#g)#z))
-- >       (g#z),
-- >    expectd (eval $ ((c^f^x^f#(c#f#x))#(f^x^x)))
-- >       (f^f),
-- >    expectd (((x^x#x)#(x^x#x)))
-- >       ((p^p#p)#(q^q#q)),
-- >    expectd (eval $ ((x^y)#((x^x#x)#(x^x#x))))
-- >       y,
-- >    expectd (eval $ ((x^y^(f#x#y#y))#(g#y)))
-- >       (z^(f#(g#y)#z#z)),
-- >    expectd (eval $ ((c^f^x^f#(c#f#x))#(f^x^(f#x))))
-- >       (g^x^(g#(g#x))),
-- >    expectd (eval $ a ^ (x ^ a ^ a # x) # (a # x))
-- >       (a^b^(b#(a#x))),
-- >    expectd (eval $ a ^ (x ^ a ^ x # a) # a)
-- >       (z^z),
-- >    expectd (eval $ a ^ (x ^ b ^ x # a) # a)
-- >          (a^b^a#a)
-- >    ]
-- > mweval_tests = and [
-- >    expectd (fst $ mweval $ ((x^(a#b#x))#(a^a#b))) $
-- >               (a#b#(p^p#b)),
-- >    expectd (fst $ mweval $ (((f^x^(f#x))#g)#z))
-- >       (g#z),
-- >    expectd (fst $ mweval $ ((c^f^x^f#(c#f#x))#(f^x^x)))
-- >       (f^f),
-- >    expectd (fst $ mweval $ ((x^y)#((x^x#x)#(x^x#x))))
-- >       y,
-- >    expectd (fst $ mweval $ ((x^y^(f#x#y#y))#(g#y)))
-- >       (z^(f#(g#y)#z#z)),
-- >    expectd (fst $ mweval $ ((c^f^x^f#(c#f#x))#(f^x^(f#x))))
-- >       (g^x^(g#(g#x))),
-- >    expectd (fst $ mweval $ a ^ (x ^ a ^ a # x) # (a # x))
-- >       (a^b^(b#(a#x))),
-- >    expectd (fst $ mweval $ a ^ (x ^ a ^ x # a) # a)
-- >       (z^z),
-- >    expectd (fst $ mweval $ a ^ (x ^ b ^ x # a) # a)
-- >          (a^b^a#a),
-- >    expect (show $ mweval $ a ^ (x ^ a ^ x # a) # a)
-- >           "((\\a. a),[(\"beta\",(\\x. (\\a. x a)) a),(\"eta\",(\\a~1. a a~1))])"
-- >    ]
-- >
-- > all_tests = and [ free_var_tests, alpha_comparison_tests,
-- >                   subst_tests, eval_tests, mweval_tests ]
