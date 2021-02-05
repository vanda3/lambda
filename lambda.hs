-- Vanda Azevedo 2019

import Data.List
import Debug.Trace

-- var (variable), abs (lambda abstraction), app (application)
data Term = Var String
        | App Term Term
        | Abs String Term
        deriving Eq

instance Show Term where
        show (Abs s t) = "(\\" ++ (id s) ++ "." ++ show t ++ ")"
        show (App m n) = "(" ++ show m ++ " " ++ show n ++ ")"
        show (Var s) = (id s)

subst :: Term -> String -> Term -> Term
-- subst y x L = y[L/x]
subst (Var y) x l = 
        if x==y then (if (Var x)/=l -- test (\x.x)x
                        then l 
                        else error("Trying to substitute bv("++x++") by fv("++x++")"))
        else Var y
-- subs M N x L = (MN)[L/x]
subst (App m n) x l = App (subst m x l) (subst n x l)
-- subst y M x L = (\y.M)[L/x]
subst (Abs y m) x l = 
        if ((overlap (bv (Abs x (Abs y m)) []) (fv l []))==[])
                then (if x==y 
                        then (Abs y m) 
                        else (Abs y (subst m x l)))
        else error("bv("++show (Abs x (Abs y m))++") intersect fv("++show l++") = "++ show (overlap (bv (Abs x (Abs y m)) []) (fv l [])))

redex :: Term -> Term -> Term
-- beta rule (\x.M)N -> M[N/x]
redex (Abs x m) n = normalise (subst (normalise m) x n)
-- (x M) 
redex (Var x) m = (App (Var x) (normalise m))
-- (M N) 
redex m n = if (isNormal m) && (isNormal n) 
        then App m n
        else normalise (App (normalise m) (normalise n))

normalise :: Term -> Term 
normalise (Var x) = (Var x)
normalise (Abs x m) = (Abs x (normalise m))
normalise (App m n) = redex m n

-- AUX
overlap :: Eq a => [a] -> [a] -> [a]
overlap [] _ = []
overlap (x:xs) ys = if x `elem` ys
        then x:overlap xs (delete x ys)
        else overlap xs ys

isNormal :: Term -> Bool
isNormal t = (normalise t == t)

fv :: Term -> [String] -> [String]
fv (Var y) ls = ls++[y]
fv (Abs x (Var y)) ls = if x/=y then (ls++[y]) else ls
fv (Abs x (Abs y z)) ls = (fv (Abs x z) ls) ++ (fv (Abs y z) ls)
fv (Abs x (App m n)) ls = (fv (Abs x m) ls) ++ (fv (Abs x n) ls)
fv (App m n) ls = (fv m ls) ++ (fv n ls)

bv :: Term -> [String] -> [String]
bv (Var y) ls = []
bv (Abs x (Var y)) ls = if x==y then (ls++[y]) else ls
bv (Abs x (Abs y n)) ls = (bv (Abs x n) ls) ++ (bv (Abs y n) ls)
bv (Abs x (App m n)) ls = (bv (Abs x m) ls) ++ (bv (Abs x n) ls)
bv (App m n) ls = (bv m ls) ++ (bv n ls)


-- Examples
x = Var "x"
y = Var "y"
z = Var "z"
k = Var "k"
c = Var "c"

-- omega
ex0 = normalise(App (Abs "x" (App x x)) (Abs "x" (App x x)))
-- (\x.(\y.(x y))) (\x.(x y)) = \y.(y y) -> FAIL
ex1 = normalise (App (Abs "x" (Abs "y" (App x y))) (Abs "x" (App x y)))
p = Abs "y" (App (App y y) y)
-- (\x.z) ((\y.((y y) y)) (\y.((y y) y))) = z
ex2 = normalise(App (Abs "x" z) (App p p))
-- \x.(k x) = \x.(k x)
ex3 = normalise(Abs "x" (App k x))
-- \y.(z y) = \y.(z y)
ex4 = normalise(Abs "y" (App z y))
-- ((\y.(z y)) c) = (z c)
ex5 = normalise(App (Abs "y" (App z y)) c)
-- (\x.(k x)) ((\y.(z y)) c) = (k (z c))
ex6 = normalise(App (Abs "x" (App k x)) (App (Abs "y" (App z y)) c))
-- (((\x.x) (\y.y)) z) = z
ex7 = normalise(App (App (Abs "x" x) (Abs "y" y)) z)
-- \x.((\y.y) (\y.y)) = \x.(\y.y)
ex8 = normalise(Abs "x" (App (Abs "y" y) (Abs "y" y)))
-- \x.((\x.x) x) = \x.x -> FAIL
ex9 = normalise(Abs "x" (App (Abs "x" x) x))
-- (\x.\y.(x y)) y -> FAIL
ex10 =  normalise(App (Abs "x" (Abs "y" (App x y))) y)
-- (\x.((\z.z) x)(\y.(z y)) = \y.(z y)
ex11 = normalise(App (Abs "x" (App (Abs "z" z) x)) (Abs "y" (App z y)))
-- (\x.(x y))y = (y y)
ex12 = normalise(App (Abs "x" (App x y)) y)
-- (\x.\y.(x y z)) (x y)
ex13 = normalise(App (Abs "x" (Abs "y" (App (App x y) z))) (App x y))
-- (\x.\y.(x y)) -> FAIL
ex14 =  normalise(Abs "x" (Abs "y" (App x y)))