import Data.List (find)
import Debug.Trace

data Mode
  = Quot
  | Norm
  | Type

data Term
  = Err
  | Set
  | Var Int
  | Lam Term (Term -> Term)
  | All Term (Term -> Term)
  | App Term Term
  | Box Term
  | Put Term
  | Dup Term (Term -> Term)
  | Hol (Mode -> Term)

equals :: Term -> Term -> Bool
equals a b = go 0 a b where
  go lv Err Err                 = True
  go lv Set Set                 = True
  go lv (Var ax)    (Var bx)    = ax == bx
  go lv (Lam ax ay) (Lam bx by) = go lv ax bx && go (lv+1) (ay Err) (by Err) 
  go lv (All ax ay) (All bx by) = go lv ax bx && go (lv+1) (ay Err) (by Err)
  go lv (App ax ay) (App bx by) = go lv ax bx && go lv ay by
  go lv (Box ax)    (Box bx)    = go lv ax bx
  go lv (Put ax)    (Put bx)    = go lv ax bx
  go lv (Dup ax ay) (Dup bx by) = go lv ax bx && go (lv+1) (ay Err) (by Err)
  go lv (Hol ax)    (Hol bx)    = False
  go lv a           b           = False

display :: Term -> String
display = go 0 where
  go lvl term = case term of
    Err         -> "?"
    Set         -> "*"
    Var idx     -> alphabet !! (idx+1)
    Lam typ bod -> "#" ++ alphabet !! (lvl+1) ++ " " ++ go lvl typ ++ " " ++ go (lvl+1) (bod Err)
    All typ bod -> "@" ++ alphabet !! (lvl+1) ++ " " ++ go lvl typ ++ " " ++ go (lvl+1) (bod Err)
    App fun arg -> ":" ++ go lvl fun ++ " " ++ go lvl arg
    Box val     -> "!" ++ go lvl val
    Put val     -> "|" ++ go lvl val
    Dup val bod -> "=" ++ alphabet !! (lvl+1) ++ " " ++ go lvl val ++ " " ++ go (lvl+1) (bod Err)
    Hol hol     -> "_"
  alphabet :: [String]
  alphabet = [""] ++ concatMap prefixAlphabet alphabet where
    prefixAlphabet str = map (: str)  ['a' .. 'z']

parse :: String -> Term
parse str = end (parseTerm str []) [] where
  end :: (String, [(String,Bool,Int,Int)], [(String,Term)] -> Term) -> [(String,Term)] -> Term
  end (a,b,c) = c

  box :: [(String,Bool,Int,Int)] -> [(String,Bool,Int,Int)]
  box = map (\ (nam,linear,used,boxed) -> (nam,linear,used,boxed+1))

  unbox :: [(String,Bool,Int,Int)] -> [(String,Bool,Int,Int)]
  unbox = map (\ (nam,linear,used,boxed) -> (nam,linear,used,boxed-1))

  use :: String -> [(String,Bool,Int,Int)] -> [(String,Bool,Int,Int)]
  use nam ((nam',linear,used,boxed) : xs) 
    | nam == nam' = (nam',linear,used+1,boxed) : xs
    | otherwise   = (nam',linear,used,boxed) : use nam xs

  parseName :: String -> [(String,Bool,Int,Int)] -> (String, [(String,Bool,Int,Int)], String)
  parseName "" scp0 = ("", scp0, "")
  parseName (' ' : s0) scp0 = (s0, scp0, "")
  parseName ('\n' : s0) scp0 = (s0, scp0, "")
  parseName (chr : s0) scp0 = let
    (s1, scp1, nam) = parseName s0 scp0
    in (s1, scp1, chr : nam)

  parseTerm :: String -> [(String,Bool,Int,Int)] -> (String, [(String,Bool,Int,Int)], [(String,Term)] -> Term)
  parseTerm (' ' : s0) scp0 = parseTerm s0 scp0
  parseTerm ('?' : s0) scp0 = (s0, scp0, \ ctx -> Err)
  parseTerm ('*' : s0) scp0 = (s0, scp0, \ ctx -> Set)
  parseTerm ('#' : s0) scp0 = let
    (s1, scp1, nam) = parseName s0 scp0
    (s2, scp2, typ) = parseTerm s1 scp1
    (s3, scp3, bod) = parseTerm s2 ((nam,True,0,0) : scp2)
    in (s3, tail scp3, \ ctx -> Lam (typ ctx) (\ v -> bod ((nam,v) : ctx)))
  parseTerm ('@' : s0) scp0 = let
    (s1, scp1, nam) = parseName s0 scp0
    (s2, scp2, typ) = parseTerm s1 scp1
    (s3, scp3, bod) = parseTerm s2 ((nam,True,0,0) : scp2)
    in (s3, tail scp3, \ ctx -> All (typ ctx) (\ v -> bod ((nam,v) : ctx)))
  parseTerm (':' : s0) scp0 = let
    (s1, scp1, fun) = parseTerm s0 scp0
    (s2, scp2, arg) = parseTerm s1 scp1
    in (s2, scp2, \ ctx -> App (fun ctx) (arg ctx))
  parseTerm ('!' : s0) scp0 = let
    (s1, scp1, val) = parseTerm s0 scp0
    in (s1, scp1, \ ctx -> Box (val ctx))
  parseTerm ('|' : s0) scp0 = let
    (s1, scp1, val) = parseTerm s0 (box scp0)
    in (s1, unbox scp1, \ ctx -> Put (val ctx))
  parseTerm ('=' : s0) scp0 = let
    (s1, scp1, nam) = parseName s0 scp0
    (s2, scp2, typ) = parseTerm s1 scp1
    (s3, scp3, bod) = parseTerm s2 ((nam,False,0,0) : scp2)
    in (s3, tail scp3, \ ctx -> Dup (typ ctx) (\ v -> bod ((nam,v) : ctx)))
  parseTerm (chr : s0) scp0 = let
    (s1, scp1, nam) = parseName (chr : s0) scp0
    in case find (\ (nam',_,_,_) -> nam == nam') scp1 of
      Nothing -> error ("Unbound variable " ++ nam ++ ".")
      Just (nam',linear,used,boxes) -> let
        var ctx = case find (\ (n,_) -> nam == n) ctx of
          Nothing    -> Err
          Just (_,v) -> v
        in if linear && used > 0 && nam /= "P"
          then error ("Used linear variable '" ++ nam ++ " more than once.")
          else if linear && boxes > 0 && nam /= "P"
            then error ("Used linear variable inside a box: '" ++ nam ++ "'.")
            else if not linear && boxes /= 1 && nam /= "P"
              then error ("Exponential variable '" ++ nam ++ "' should have 1 surrounding box, but has " ++ show boxes ++ ".")
              else (s1, use nam scp1, var)
  parseTerm a b = trace (show (a,b)) (error "??")

hol :: Term -> Term -> Term -> Term
hol quo nor typ = Hol $ \t -> case t of { Quot -> quo; Norm -> nor; Type -> typ }

reduce :: Term -> Mode -> Term
reduce = go 0 where

  go lvl Err Quot = Err
  go lvl Err Norm = Err
  go lvl Err Type = Err

  go lvl Set Quot = Set
  go lvl Set Norm = Set
  go lvl Set Type = Set

  go lvl (Var idx) Quot = Var idx
  go lvl (Var idx) Norm = Var idx
  go lvl (Var idx) Type = Var idx

  go lvl (Lam typ bod) Quot = let 
    typQ = go lvl typ Quot
    bodQ = \v -> go (lvl+1) (bod (hol (Var lvl) (Var lvl) typ)) Quot
    in Lam typQ bodQ
  go lvl (Lam typ bod) Norm = let
    typN = go lvl typ Norm
    bodN = \v -> go (lvl+1) (bod (hol (Var lvl) v typN)) Norm
    in Lam typN bodN
  go lvl (Lam typ bod) Type = let
    typN = go lvl typ Norm
    bodT = \v -> go (lvl+1) (bod (hol (Var lvl) v typN)) Type
    in case go lvl (All typN bodT) Type of
      Set       -> All typN bodT
      otherwise -> Err

  go lvl (All typ bod) Quot = let 
    typQ = go lvl typ Quot
    bodQ = \v -> go (lvl+1) (bod (hol (Var lvl) (Var lvl) typ)) Quot
    in All typQ bodQ
  go lvl (All typ bod) Norm = let
    typN = go lvl typ Norm
    bodN = \v -> go (lvl+1) (bod (hol (Var lvl) v typN)) Norm
    in All typN bodN
  go lvl (All typ bod) Type = let
    typN = go lvl typ Norm
    typT = go lvl typ Type
    bodT = \v -> go (lvl+1) (bod (hol (Var lvl) v typN)) Type
    bodQ = go lvl (bodT Err) Quot
    in case (typT, bodQ) of
      (Set, Set) -> Set
      otherwise  -> Err

  go lvl (App fun arg) Quot = let
    funQ = go lvl fun Quot
    argQ = go lvl arg Quot
    in App funQ argQ
  go lvl (App fun arg) Norm = let
    funN = go lvl fun Norm
    argN = go lvl arg Norm
    in case funN of
      Lam ftyp fbod -> fbod arg
      otherwise     -> App funN argN
  go lvl (App fun arg) Type = let
    funT = go lvl fun Type
    argT = go lvl arg Type
    argN = go lvl arg Norm
    in case funT of
      All ftyp fbod ->
        if equals (go lvl argT Quot) (go lvl ftyp Quot)
          then fbod argN
          else Err
      otherwise -> Err

  go lvl (Box val) Quot = let
    valQ = go lvl val Quot
    in Box valQ
  go lvl (Box val) Norm = let
    valN = go lvl val Norm
    in Box valN
  go lvl (Box val) Type = let
    valT = go lvl val Type
    in if equals (go lvl valT Quot) Set
      then Set
      else Err

  go lvl (Put val) Quot = let
    valQ = go lvl val Quot
    in Put valQ
  go lvl (Put val) Norm = let
    valN = go lvl val Norm
    in valN
  go lvl (Put val) Type = let
    valT = go lvl val Type
    in if not (equals (go lvl valT Quot) Err)
        then Box valT
        else Err

  go lvl (Dup val bod) Quot = let
    valQ = go lvl val Quot
    bodQ = \v -> go (lvl+1) (bod (hol (Var lvl) (go lvl val Type) (Var lvl))) Quot
    in Dup valQ bodQ
  go lvl (Dup val bod) Norm = let
    valN = go lvl val Norm
    bodN = \v -> go lvl (bod v) Norm
    in go lvl (bodN valN) Norm
  go lvl (Dup val bod) Type = let
    valN = go lvl val Norm
    valT = go lvl val Type
    in case valT of
      Set       -> go (lvl+1) (bod (hol (Var lvl) valN valT)) Type
      Box valT  -> go (lvl+1) (bod (hol (Var lvl) valN valT)) Type
      otherwise -> Err

  go lvl (Hol hol) Quot = hol Quot
  go lvl (Hol hol) Norm = hol Norm
  go lvl (Hol hol) Type = hol Type


qt :: Term -> Term
qt t = reduce t Quot

nf :: Term -> Term
nf t = qt (reduce t Norm)

ty :: Term -> Term
ty t = qt (reduce t Type)

main :: IO ()
main
  = putStrLn . display . nf
  $ parse "\
    \=Nat |@P * @s !@n P P !@z P P \
    \=c2  |#P * #s !@n P P =S s |#z P :S :S z \
    \=c3  |#P * #s !@n P P =S s |#z P :S :S :S z \
    \=the |#P * #x P x \
    \=add |#a Nat #b Nat #P * #s !@n P P =S s =f ::a P | S =g ::b P | S | #z P :f :g z \
    \=mul |#a Nat #b Nat #P * #s !@n P P ::a P ::b P s \
    \=exp |#a Nat #b !Nat #P * =B b ::a !@x P P |:B P   \
    \| ::mul c3 c3"
