module FrontEnd where 

import Datatypes
import Lexicon
import Displacement
import Eval
import Data.Char (toLower,isSpace)
import Data.List ((\\))

data SO = LI String
        | M1 SO SO
        | M2 SO SO SO
        | RM SO
     deriving (Eq,Show)

parse :: String -> SO
parse s@('(' : xs) = parseCon ((init . tail) 
                               (upToClosingBracket s))
parse s            = LI s

parseCon :: String -> SO
parseCon s = case op of 
                 "M1" -> M1 (parse func) (parse arg1)
                 "M2" -> M2 (parse func) (parse arg1) 
                                         (parse arg2)
                 "RM" -> RM (parse func)
  where op   = head (wordz s)
        func = head (tail (wordz s))
        arg1 = head (tail (tail (wordz s)))
        arg2 = last (wordz s)

wordz :: String -> [String]
wordz [] = []
wordz s | head s == '(' = (upToClosingBracket s) : 
            (wordz $ remove (length (upToClosingBracket s)+1) s)
        | otherwise     = firstWord : 
            (wordz $ remove (length firstWord + 1) s)
  where firstWord = fst $ break (==' ') s

remove :: Int -> String -> String
remove n s = s \\ (take n s)

upToClosingBracket :: String -> String
upToClosingBracket s = head [ x | x <- prefixes s, 
                                  bracketsFine x ]

prefixes s = [ ys | ys <- [take i s | i <- [1..(length s)]]]

bracketsFine x = (count '(' x) == (count ')' x)

count y [] = 0
count y (z:zs) | y == z    = 1 + count y zs
               | otherwise = count y zs

trans :: SO -> WhPar -> SpecPar -> [Exp]
trans (LI string)      _  _    = [lookUp string]
trans (M1 so1 so2)     wh spec = glueM wh (trans so1 wh spec) 
                                          (trans so2 wh spec)
trans (M2 so1 so2 so3) wh spec = 
                 glueM wh (glueM wh (trans so1 wh spec) 
                                    (trans so2 wh spec)) 
                          (trans so3 wh spec)
trans (RM so) wh spec = glueRM spec (trans so wh spec)

glueM :: WhPar -> [Exp] -> [Exp] -> [Exp]
glueM p xs ys = [ z | x <- xs,
                      y <- ys,
                      z <- merge p x y ]

glueRM :: SpecPar -> [Exp] -> [Exp]
glueRM p xs = map (remerge p) xs 

build :: WhPar -> SpecPar -> String -> [Exp]
build wh spec string = filter converged $ 
                       trans (parse string) wh spec

converged :: Exp -> Bool
converged (Simple _ _) = True
converged _            = False

lookUp :: String -> Exp
 
lookUp "enkidu"     = enkidu 
lookUp "gilgamesh"  = gilgamesh 
lookUp "ishtar"     = ishtar 
lookUp "who"        = who 
lookUp "whom"       = whom 
lookUp "what"       = what 
lookUp "king"       = king 
lookUp "beast"      = beast
lookUp "man"        = man 
lookUp "citizen"    = citizen 
lookUp "goddess"    = goddess 
lookUp "that"       = that 
lookUp "epsilon"    = epsilon 
lookUp "sought"     = sought 
lookUp "liked"      = liked 
lookUp "met"        = met 
lookUp "fought"     = fought 
lookUp "left"       = left 
lookUp "died"       = died 
lookUp "great"      = great 
lookUp "wild"       = wild 
lookUp "some"       = some 
lookUp "every"      = every
lookUp "which"      = which 
lookUp "epsilonWh"  = epsilonWh 
lookUp "everyone"   = everyone
lookUp "someone"    = someone 
lookUp "everything" = everything 
lookUp "something"  = something 

s1 = "(M1 that (M2 fought (M1 some beast) gilgamesh))"
s2 = "(RM (M1 epsilonWh (M2 liked whom enkidu)))"
s3 = "(RM (M1 epsilonWh (M1 died (M1 which (M1 great man)))))"
s4 = "(RM (M1 epsilonWh (M2 liked what who)))"
s5 = "(RM (M1 epsilonWh (M2 fought whom who)))"
s6 = "(M1 epsilon (M2 liked something everyone))"
