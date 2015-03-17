module Datatypes where 

data Exp = Simple  Form [Meaning] 
         | Complex Form Exp
     deriving Eq

instance Show Exp where
  show (Simple  f  ms) = "("++ show f  ++","++ show ms ++")"
  show (Complex e1 e2) = "<"++ show e1 ++","++ show e2 ++">"

data Form    = Syn String Cat [Feat]   deriving Eq
data Meaning = Sem Term Type           deriving Eq

instance Show Form where 
  show (Syn s c fs) = s ++ "::" ++ show c ++" "++ show fs 
instance Show Meaning where 
  show (Sem t tau)  = show t ++ "::" ++ show tau

data Cat  = NP 
          | N 
          | VP  
          | CP 
          | L Cat 
          | Slash Cat Cat
          | Str  
     deriving Eq

instance Show Cat where 
  show NP           = "NP"
  show N            = "N"
  show VP           = "VP"
  show CP           = "CP"
  show (L c)        = (show c) ++ "<"
  show (Slash c c') = "("++(show c)++" -> "++(show c')++")"
  show Str          = "String"

data Feat  = Goal  Value 
           | Probe Value 
     deriving (Eq,Show)

data Value = Wh 
           | Top
           | Q 
     deriving (Eq,Show) 

data Type = Entity 
          | Bool 
          | Question
          | Type :->: Type 
          | Cont Type Value Type Type 
     deriving Eq

instance Show Type where 
  show Entity       = "e"
  show Bool         = "t"
  show Question     = "q"
  show (t1 :->: t2) = "("++ show t1 ++" -> "++ show t2 ++")"
  show (Cont t1 v t2 t3) = show t1 
      ++ "_(" ++ show v ++ ":" ++ show t2 ++ ")" 
      ++ "^(" ++ show v ++ ":" ++ show t3 ++ ")"

data Term = Const String 
          | Var Int 
          | Lambda Int Term 
          | Term :@: Term
          | Op Operator
          | Not Term 
          | Term :/\: Term  
          | Shift Mode Flavor Int Term 
          | Reset Flavor Term 
     deriving Eq

data Operator = Exists 
              | ForAll 
              | Most 
              | W
     deriving (Eq,Show)

data Mode   = Weak 
            | Strong
            | Free 
     deriving Eq

type Flavor = Value

instance Show Mode where
  show Weak   = "'"
  show Strong = ""
  show Free   = "^free"

instance Show Term where 
  show (Const s)       = s
  show (Var n)         = show n
  show ((Op o) :@: Lambda n t) = show o ++ 
                               " "++ show n ++ "." ++ show t
  show (Lambda n t)    = "Lambda "++ show n ++ "." ++ show t
  show (t1 :@: t2)     = "("++ show t1 ++" "++ show t2 ++")"
  show (Not (t1 :/\: (Not t2))) = show t1 ++" => "++ show t2
  show (Not t)         = "(Not " ++ show t ++ ")"
  show (t1 :/\: t2)    = "("++show t1++" And "++show t2++")"
  show (Shift m Q n t) = "Shift" ++ show m ++ 
                             " " ++ show n ++ "." ++ show t
  show (Shift m f n t) = "Shift" ++ show m ++ "_" ++ show f 
                           ++" " ++ show n ++ "." ++ show t
  show (Reset Q t)     = "<" ++ show t ++ ">"
  show (Reset f t)     = "<" ++ show t ++ ">_" ++ show f

impl :: Term -> Term -> Term 
impl t1 t2 = Not (t1 :/\: (Not t2))
