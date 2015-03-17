module Eval where

import Datatypes
import Data.List ((\\),nub)

eval' :: Term -> Term
eval' c@(Const _)  = c
eval' v@(Var _)    = v
eval' (Not t)      = Not (eval' t)
eval' (t1 :/\: t2) = (eval' t1) :/\: (eval' t2)
eval' (Lambda n t) = etaReduce $ Lambda n (eval' t)
eval' ((Lambda n t1) :@: t2) = eval' $ substitute t1 n t2
eval' (t1@(_:@:_):@:t2) = case eval' t1 of 
                          t@(Lambda _ _) -> eval' (t:@:t2)
                          t              -> t:@:(eval' t2)
eval' (t1 :@: t2) = t1 :@: (eval' t2)
eval' t           = t

etaReduce :: Term -> Term
etaReduce t@(Lambda n (t' :@: (Var n'))) 
  | n == n' && notFree n t'  = t' 
  | otherwise                = t
etaReduce t                  = t 

notFree :: Int -> Term -> Bool
notFree n (Var n')     = n /= n'
notFree n (Not t)      = notFree n t
notFree n (Lambda n' t) | n == n'   = True 
                        | otherwise = notFree n t
notFree n (t1 :/\: t2) = notFree n t1 && notFree n t2
notFree n (t1 :@:  t2) = notFree n t1 && notFree n t2
notFree _ _            = True

data Context = Hole 
             | CAppL Context Term 
             | CAppR Term Context 
             | CAndL Context Term 
             | CAndR Term Context 
             | CNot Context  
             | CLambda Int Context 
             | CReset Flavor Context 
           deriving (Eq,Show)

type Thread = [Context]
type Zipper = (Thread,Term) 

exampleTerm = (Lambda 1 (Not ((Const "fish") :/\: (Var 1)))) 
          :@: (Const "chips")

exampleZipper = ([CAndR (Const "fish") Hole,
                  CNot Hole,
                  CLambda 1 Hole,
                  CAppL Hole (Const "chips")],
                 Var 1)

unwind :: Zipper -> Term
unwind ([],t) = t
unwind ((CAppR t _)  :ts,t') = unwind (ts,t  :@:  t')
unwind ((CAppL _ t)  :ts,t') = unwind (ts,t' :@:  t )
unwind ((CAndR t _)  :ts,t') = unwind (ts,t  :/\: t')
unwind ((CAndL _ t)  :ts,t') = unwind (ts,t' :/\: t )
unwind ((CNot _)     :ts,t') = unwind (ts,Not t')
unwind ((CLambda n _):ts,t ) = unwind (ts,Lambda n t)
unwind ((CReset f _) :ts,t ) = unwind (ts,Reset  f t)

unwind1 :: Zipper -> Zipper
unwind1 z@([],t) = z
unwind1 ((CAppR t _)  :ts,t') = (ts,t  :@:  t')
unwind1 ((CAppL _ t)  :ts,t') = (ts,t' :@:  t )
unwind1 ((CAndR t _)  :ts,t') = (ts,t  :/\: t')
unwind1 ((CAndL _ t)  :ts,t') = (ts,t' :/\: t )
unwind1 ((CNot _)     :ts,t') = (ts,Not t')
unwind1 ((CLambda n _):ts,t ) = (ts,Lambda n t)
unwind1 ((CReset f _) :ts,t ) = (ts,Reset  f t)

eval :: Zipper -> [Zipper]

eval z@(_,Const _) = [ z ]
eval z@(_,Var _)   = [ z ]

eval (thread,Lambda n t) = map unwind1 $ 
                           eval ((CLambda n Hole):thread,t)

eval (th,(Lambda n t1):@:t2) = eval (th,substitute t1 n t2) 

eval (thread,t1@(_:@:_) :@: t2) = 
     (concat $ map (evalL . unwind1) $ 
               eval ((CAppR t1 Hole):thread,t2))
     ++
     (concat $ map (evalR . unwind1) $ 
               eval ((CAppL Hole t2):thread,t1)) 
  
  where 
  
     evalL (th,y) = case y of 
                    (a:@:b) -> map unwind1 $ 
                               eval ((CAppL Hole b):th,a)
                    t       -> eval (th,t)
     evalR (th,y) = case y of 
                    (a@(Lambda _ _):@:b) -> eval (th,a:@:b) 
                    (a :@: b) -> map unwind1 $ 
                                 eval ((CAppR a Hole):th,b) 
                    t         -> eval (th,t)

eval (thread,t@(t1:@:t2)) = map unwind1 $ 
                            eval ((CAppR t1 Hole):thread,t2)

eval (thread,Not t) = map unwind1 $ 
                      eval ((CNot Hole):thread,t)

eval (thread,t1 :/\: t2) = (concat $ map (evalR . unwind1) $ 
                            eval ((CAndL Hole t2):thread,t1))
                           ++
                           (concat $ map (evalL . unwind1) $ 
                            eval ((CAndR t1 Hole):thread,t2))
 
   where 
  
    evalL (th,y) = case y of 
                   (a :/\: b) -> map unwind1 $ 
                                 eval ((CAndL Hole b):th,a)
                   t          -> eval (th,t)
    evalR (th,y) = case y of 
                   (a :/\: b) -> map unwind1 $ 
                                 eval ((CAndR a Hole):th,b)
                   t          -> eval (th,t)

eval (thread,Reset f t) 
     | pure f t  = eval (thread,t)
     | otherwise = concat $ map (eval . unwind1) $ 
                   eval ((CReset f Hole):thread,t)

eval z@(thread,Shift m f n t) 
  | noResets f thread = [ z ]
  | otherwise         =  map unwind1 $ concat 
                 [ eval (th2,substitute t n (reify f th1)) | 
                   (th1,th2) <- filter (admissible m f) $ 
                                splitt f [] thread ]

eval z@(_,_) = [ z ]

splitt :: Flavor -> Thread -> Thread -> [(Thread,Thread)]
splitt _ _ [] = []
splitt f thread (c@(CReset f' _):cs) 
  | f == f'   = (thread,(c:cs)) : (splitt f (thread++[c]) cs)
  | otherwise = splitt f (thread++[c]) cs
splitt f thread (c:cs) = splitt f (thread++[c]) cs

admissible :: Mode -> Flavor -> (Thread,Thread) -> Bool 
admissible Weak   f ((c:cs),_) = noResets f cs 
                            && pureThread f cs 
admissible Strong f ((c:cs),_) = noResets f cs
admissible _ _ _               = True 

noResets :: Flavor -> Thread -> Bool
noResets f thread = null $ filter (== CReset f Hole) thread

pureThread :: Flavor -> Thread -> Bool 
pureThread f []                = True
pureThread f ((CAppL c t):cs)  = pure f t 
                              && pureThread f cs 
pureThread f ((CReset _ c):cs) = pureThread f [c] 
                              && pureThread f cs 
pureThread f (_:cs)            = pureThread f cs

pure :: Flavor -> Term -> Bool 
pure f (Lambda _ t)      = pure f t
pure f (t1 :@: t2)       = pure f t1 && pure f t2
pure f (Not t)           = pure f t
pure f (t1 :/\: t2)      = pure f t1 && pure f t2
pure f (Reset _ t)       = pure f t
pure f (Shift _ f' _ _)  = f /= f'
pure _ _                 = True 

reify :: Flavor -> Thread -> Term 
reify f thread = Lambda fresh 
                 (Reset f (unwind (thread,Var fresh)))
  where  fresh = (maxList $ concat $ map varsC thread) + 1

varsC :: Context -> [Int]
varsC Hole          = []
varsC (CAppL _ t)   = variables t
varsC (CAppR t _)   = variables t
varsC (CAndL _ t)   = variables t
varsC (CAndR t _)   = variables t
varsC (CLambda n _) = [n]
varsC (CNot _ )     = []
varsC (CReset _ _)  = []

variables :: Term -> [Int] 
variables (Var n)         = [n] 
variables (Not t)         = variables t 
variables (t1 :/\: t2)    = variables t1 ++ variables t2 
variables (t1 :@:  t2)    = variables t1 ++ variables t2 
variables (Lambda n body) = n : (variables body) 
variables (Shift _ _ n t) = n : (variables t) 
variables (Reset _ t)     = variables t
variables _               = []

maxList :: [Int] -> Int
maxList [] = 0
maxList xs = maximum xs

evaluate :: Term -> [Term]
evaluate t = map eta $ nub $ map snd $ eval ([],t) 

eta :: Term -> Term
eta t@((Op _) :@: Lambda _ _) = t
eta t@(Lambda n (t' :@: (Var n'))) 
    | n == n' && notFree n t' = t' 
    | otherwise               = t
eta (t1 :@:  t2)              = (eta t1) :@:  (eta t2) 
eta (t1 :/\: t2)              = (eta t1) :/\: (eta t2) 
eta (Not t)                   = Not (eta t)
eta (Reset f t)               = Reset f (eta t)
eta (Shift m f n t)           = Shift m f n (eta t)
eta t                         = t

substitute :: Term -> Int -> Term -> Term
 
substitute c@(Const _) _ _             = c
substitute v@(Var n1) n2 t | n1 == n2  = t
                           | otherwise = v

substitute (Not t') n t     = Not $ substitute t' n t
substitute (t1 :/\: t2) n t = (substitute t1 n t) 
                         :/\: (substitute t2 n t)
substitute (t1 :@:  t2) n t = (substitute t1 n t) 
                          :@: (substitute t2 n t)

substitute (Lambda n' body) n t 
    | n' == n = Lambda n' body
    | n' `elem` (variables t) = 
         let 
            fresh = (maximum (n':(variables body))) + 1
            body' = substitute body n' (Var fresh) 
         in  
            substitute (Lambda fresh body') n t
    | otherwise = Lambda n' (substitute body n t)
 
substitute (Shift m f n body) n' t 
     | n' `elem` (variables t) = 
          let 
             fresh = (maxList $ (n':(variables body))) + 1
             body' = substitute body n' (Var fresh)
          in  
             substitute (Shift m f fresh body') n' t
     | otherwise = Shift m f n (substitute body n' t)

substitute (Reset f t') n t = Reset f (substitute t' n t)

substitute t@(Op _) _ _ = t
