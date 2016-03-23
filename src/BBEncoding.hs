-- * Notes on the Bohm Berarducci encoding
-- Through the notes of Oleg

data Exp = Lit Int
         | Neg Exp
         | Add Exp Exp

ti1 = Add (Lit 8) (Neg (Add (Lit 1) (Lit 2)))

view:: Exp -> String
view (Lit n) = show n
view (Neg e) = "(-" ++ view e ++ ")"
view (Add e1 e2) = "(" ++ view e1 ++ " + " ++ view e2 ++ ")"

ti1_view = view ti1
-- "(8 + (-(1 + 2)))"

push_neg :: Exp -> Exp
push_neg e@Lit{} = e
push_neg e@(Neg (Lit _)) = e
push_neg (Neg (Neg e)) = push_neg e
push_neg (Neg (Add e1 e2)) = Add (push_neg (Neg e1)) (push_neg (Neg e2))
push_neg (Add e1 e2) = Add (push_neg e1) (push_neg e2)

ti1_norm = push_neg ti1
ti1_norm_view = view ti1_norm
-- "(8 + ((-1) + (-2)))"

-- Add an extra negation
ti1n_norm_view = view (push_neg (Neg ti1))
-- "((-8) + (1 + 2))"
