module Lexicon where

import Datatypes

enkidu,gilgamesh,ishtar :: Exp

enkidu    = Simple (Syn "Enkidu"    NP [])        
                   [Sem (Const "enkidu")    Entity]
gilgamesh = Simple (Syn "Gilgamesh" NP [])        
                   [Sem (Const "gilgamesh") Entity]
ishtar    = Simple (Syn "Ishtar"    NP [])
                   [Sem (Const "ishtar")    Entity]

everyone,everything,someone,something :: Exp

everyone   = Simple (Syn "everyone"   NP [])        
                    [Sem  everyone'   gq]
everything = Simple (Syn "everything" NP [])        
                    [Sem  everything' gq]
someone    = Simple (Syn "someone"    NP [])
                    [Sem  someone'    gq]
something  = Simple (Syn "something"  NP [])
                    [Sem  something'  gq]

gq = Cont Entity Q Bool Bool

someone'    = Shift Free Q 1   ((Op Exists) :@: Lambda 2 
                    (((Const "person") :@: (Var 2)) 
                         :/\: ((Var 1) :@: (Var 2))))

something'  = Shift Free Q 1   ((Op Exists) :@: Lambda 2 
                    (((Const "thing")  :@: (Var 2)) 
                         :/\: ((Var 1) :@: (Var 2))))

everyone'   = Shift Strong Q 1 ((Op ForAll) :@: Lambda 2 
               (impl ((Const "person") :@: (Var 2)) 
                              ((Var 1) :@: (Var 2))))

everything' = Shift Strong Q 1 ((Op ForAll) :@: Lambda 2 
               (impl ((Const "thing")  :@: (Var 2)) 
                             ((Var 1)  :@: (Var 2))))

who,whom,what ::Exp

who   = Simple (Syn "who"  NP [Goal Wh])  
               [Sem  who'  (Cont Entity Wh Bool Question)]
whom  = Simple (Syn "whom" NP [Goal Wh]) 
               [Sem  who'  (Cont Entity Wh Bool Question)]
what  = Simple (Syn "what" NP [Goal Wh]) 
               [Sem  what' (Cont Entity Wh Bool Question)]

who'  = Shift Strong Wh 1 ((Op W) :@: Lambda 2 
          (((Const "person") :@: (Var 2)) 
               :/\: ((Var 1) :@: (Var 2))))

what' = Shift Strong Wh 1 ((Op W) :@: Lambda 2 
          (((Const "thing")  :@: (Var 2)) 
               :/\: ((Var 1) :@: (Var 2))))

intransVerb = Slash (L NP) VP
transVerb   = Slash NP (Slash (L NP) VP)

et  = Entity :->: Bool
eet = Entity :->: (Entity :->: Bool)

sought,liked,met,fought :: Exp

sought = Simple (Syn "sought" transVerb []) 
                [Sem (Const "seek")  eet]
liked  = Simple (Syn "liked"  transVerb []) 
                [Sem (Const "like")  eet] 
met    = Simple (Syn "met"    transVerb []) 
                [Sem (Const "meet")  eet] 
fought = Simple (Syn "fought" transVerb []) 
                [Sem (Const "fight") eet] 

left,died :: Exp

left = Simple (Syn "left" intransVerb []) 
              [Sem (Const "leave") et]
died = Simple (Syn "died" intransVerb []) 
              [Sem (Const "die")   et] 

some,every,which :: Exp

some  = Simple 
        (Syn "some"  (Slash N NP) [])        
        [Sem  some'  (et :->: Cont Entity Q  Bool Bool)]
every = Simple 
        (Syn "every" (Slash N NP) [])        
        [Sem  every' (et :->: Cont Entity Q  Bool Bool)]
most  = Simple 
        (Syn "most"  (Slash N NP) [])
        [Sem most'   (et :->: Cont Entity Q  Bool Bool)]
which = Simple 
        (Syn "which" (Slash N NP) [Goal Wh]) 
        [Sem  which' (et :->: Cont Entity Wh Bool Question)]

some'  = Lambda 3 (Shift Strong Q 1 ((Op Exists):@: Lambda 2 
            (((Var 3) :@: (Var 2))
        :/\: ((Var 1) :@: (Var 2)))))

every' = Lambda 3 (Shift Strong Q 1 ((Op ForAll):@: Lambda 2 
       (impl ((Var 3) :@: (Var 2)) 
             ((Var 1) :@: (Var 2)))))

most'  = Lambda 3 (Shift Strong Q 1 ((Op Most)  :@: Lambda 2 
            (((Var 3) :@: (Var 2)) 
        :/\: ((Var 1) :@: (Var 2)))))

which' = Lambda 3 (Shift Strong Wh 1 ((Op W)    :@: Lambda 2 
            (((Var 3) :@: (Var 2)) 
        :/\: ((Var 1) :@: (Var 2)))))

king,beast,man,citizen,goddess :: Exp

king    = Simple (Syn "king"    N []) 
                 [Sem (Const "king")    et]
beast   = Simple (Syn "beast"   N []) 
                 [Sem (Const "beast")   et]
man     = Simple (Syn "man"     N []) 
                 [Sem (Const "man")     et]
citizen = Simple (Syn "citizen" N []) 
                 [Sem (Const "citizen") et]
goddess = Simple (Syn "goddess" N []) 
                 [Sem (Const "goddess") et]

adjType = (Entity :->: Bool) :->: (Entity :->: Bool)

adjMeaning :: String -> Term 
adjMeaning s = Lambda 1 (Lambda 2 (((Var 1)  :@: (Var 2)) 
                             :/\: ((Const s) :@: (Var 2))))

wild,great,brave :: Exp

wild  = Simple (Syn "wild"  (Slash N N) []) 
               [Sem  (adjMeaning "wild") adjType]
great = Simple (Syn "great" (Slash N N) []) 
               [Sem (adjMeaning "great") adjType]
brave = Simple (Syn "brave" (Slash N N) []) 
               [Sem (adjMeaning "brave") adjType]

that,epsilon,epsilonWh,whether :: Exp

tt = Bool :->: Bool
tq = Bool :->: Question

that      = Simple 
            (Syn "that" (Slash VP CP) []) 
            [Sem (Lambda 1 (Reset Q (Var 1))) tt] 

epsilon   = Simple 
            (Syn "" (Slash VP CP) []) 
            [Sem (Lambda 1 (Reset Q (Var 1))) tt]
 
epsilonWh = Simple 
            (Syn "" (Slash VP CP) [Probe Wh]) 
            [Sem (Lambda 1 (Reset Wh (Reset Q (Var 1)))) tt]

whether   = Simple 
            (Syn "whether" (Slash VP CP) []) 
            [Sem (Lambda 1 (Reset Wh (Reset Q (Var 1)))) tq]
