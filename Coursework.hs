
--------------------------------------------
--                                        --
-- CM20256/CM50262 Functional Programming --
--                                        --
--         Coursework 2020/2021           --
--                                        --
--------------------------------------------


------------------------- Auxiliary functions

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m


------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"


------------------------- Assignment 1

occurs :: Atom -> Type -> Bool
occurs x (At a)
    | x == a = True
occurs x (At a :-> s)
    | x == a = True
    | otherwise = occurs x s
occurs x (a :-> s)
    | occurs x a = True
    | otherwise = occurs x s
occurs x _ = False

findAtoms :: Type -> [Atom]
findAtoms (At a) = [a]
findAtoms (At a :-> s) = merge [a] ( findAtoms s)
findAtoms (a :-> s) =    merge (findAtoms a)  (findAtoms s)

------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2
sub :: Sub -> Type -> Type
sub (x, k) (At j)
   | occurs x (At j)  = k
   | otherwise = At j

sub (x, k) (At z :-> s)
   | occurs x (At z)  = k :-> sub (x, k) s
   | otherwise = At z :-> sub (x, k) s

sub (x, k) (t :-> s)
   | occurs x t  = sub (x, k) t :-> sub (x, k) s
   | otherwise = t :-> sub (x, k) s

subs :: [Sub] -> Type -> Type
subs x a
    | null x = a
    | otherwise = subs (take (length x -1 )x) (sub (x!!(length x-1)) a)

------------------------- Unification

type Upair = (Type,Type)
type State = ([Sub],[Upair])

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])


------------------------- Assignment 3

sub_u :: Sub -> [Upair] -> [Upair]
sub_u s [] = []
sub_u s ((a, b) : xs) = (sub s a , sub s b) : sub_u s xs

step :: State -> State
--case a
step (xs,(At a, At b):ys)
    | a == b = (xs, ys)
--case b
step (xs, (At x,y):ys)
    | occurs x y = error $ "Step: atom " ++ x ++ " occurs in " ++ show y
    | otherwise = ([(x,y)] ++ xs, sub_u (x,y) ys)
step (xs, (x,At y):ys)
    | occurs y x = error $ "Step: atom " ++ y ++ " occurs in " ++ show x
    | otherwise = ([(y,x)] ++ xs, sub_u (y,x) ys)
--case c
step (xs, (a :-> b, c :-> d):ys) = (xs, (a,c):(b,d):ys)

loop:: State -> State
loop (x,y)
    | null y = (x,y)
    | otherwise = loop (step (x,y))

unify :: [Upair] -> [Sub]
unify x = fst $ loop ([], x)

------------------------- Assignment 4

type Context   = [(Atom,Type)]
type Judgement = (Context, Term, Type)

data Derivation =
       Axiom  Judgement
      |Abstraction  Judgement Derivation
      |Application  Judgement Derivation Derivation

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")


d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )

d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )


conclusion :: Derivation -> Judgement
conclusion (Axiom x) = x
conclusion (Abstraction x y) = x
conclusion (Application x y z) = x


subs_ctx :: [Sub] -> Context -> Context
subs_ctx x [] = []
subs_ctx x ((a,b):ys) = (a,subs x b): subs_ctx x ys

subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg a (x, y, z) = (subs_ctx a x, y, subs a z)

subs_der :: [Sub] -> Derivation -> Derivation
subs_der a (Axiom x) = Axiom (subs_jdg a x)
subs_der a (Abstraction x y) = Abstraction (subs_jdg a x) (subs_der a y)
subs_der a (Application x y z) = Application (subs_jdg a x) (subs_der a y) (subs_der a z)

------------------------- Typesetting derivations


instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])


------------------------- Assignment 5

derive0 :: Term -> Derivation
derive0 term = aux (map (\x -> (x, At "")) (free term), term, At "")
 where
    aux :: Judgement -> Derivation
    aux (cnx, Variable c, d) = Axiom (cnx,Variable c, d)
    aux (cnx, Lambda c d, e)
      | c `elem` (map fst cnx) = Abstraction (cnx, Lambda c d, e) (aux (cnx , d,At ""))
      | otherwise              = Abstraction (cnx, Lambda c d, e) (aux ((c, At "") : cnx, d,At ""))
    aux (cnx, Apply c d, e) = Application (cnx, Apply c d, e) (aux (cnx, c, At "")) (aux (cnx, d, At ""))

derive1 :: Term -> Derivation
derive1 term = aux (drop (free_varible_len + 1) atoms) (zipWith (\x y -> (x, At y)) (free term) (tail atoms), term, At (head atoms))
 where
    free_varible_len = length (free term)
    aux :: [Atom] -> Judgement -> Derivation
    aux _ (cnx, Variable c, d) = Axiom (cnx,Variable c, d)
    aux atoms (cnx, Lambda c d, e) 
       | c `elem` (map fst cnx) = Abstraction (cnx, Lambda c d, e) (aux rem_atoms ((c, At a1) : filter (\(x, _) -> x /= c) cnx, d, At a2))
       | otherwise              = Abstraction (cnx, Lambda c d, e) (aux rem_atoms ((c, At a1) : cnx, d, At a2))
      where
        a1 = atoms !! 0
        a2 = atoms !! 1
        rem_atoms = drop 2 atoms
    aux atoms (cnx, Apply c d, e) = Application (cnx, Apply c d, e) (aux odd_rem_atoms (cnx, c, At a1)) (aux even_rem_atoms (cnx, d, At a2))
      where
        a1 = atoms !! 0
        a2 = atoms !! 1
        rem_atoms = drop 2 atoms
        odd_rem_atoms = [rem_atoms!!i | i <- [1,3..]]
        even_rem_atoms = [rem_atoms!!i | i <- [0,2..]]


upairs :: Derivation -> [Upair]
upairs (Axiom (cnx,Variable c, d)) = (d, find c cnx) : []
upairs (Abstraction (cnx, Lambda c d, e) premise) = (e, find c cnx_premise :-> type_premise) : upairs premise
  where
    (cnx_premise, _, type_premise) = conclusion premise
upairs (Application (cnx, Apply c d, e) premise1 premise2) = (type_premise1, type_premise2 :-> e) : upairs premise1 ++ upairs premise2
  where
    (cnx_premise1, _, type_premise1) = conclusion premise1
    (cnx_premise2, _, type_premise2) = conclusion premise2


derive :: Term -> Derivation
derive term = subs_der (unify (upairs (derive1 term))) (derive1 term)