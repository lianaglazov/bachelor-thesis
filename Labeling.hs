import Data.List
import Data.Set as Set
import Data.Map as Map
import Data.Maybe

import Models (State, Model(..), Model2(..)) 

import Study.Case 
import Study.Case2
data CTL
    = Top
    | Bottom
    | Atomic String
    | Not CTL
    | And CTL CTL
    | Or CTL CTL
    | Implication CTL CTL
    | AX CTL 
    | EX CTL 
    | AF CTL 
    | EF CTL 
    | AG CTL 
    | EG CTL 
    | AU CTL CTL
    | EU CTL CTL
    deriving (Show, Ord, Eq)

m :: Model
m = Study.Case.model
m2 :: Model2
m2 = Study.Case2.model2


-- formule

-- daca trenul 1 se afla intre A si B, atunci trenul 2 nu se va afla intre A si B
safety :: CTL
safety = AG (Implication (Or (Atomic "t1AB") (Atomic "t1BA")) (Not (Or (Atomic "t2AB") (Atomic "t2BA"))))

-- daca trenul 1 se afla la statia A, acesta va avea acces la statia C eventual
liveness :: CTL
liveness = AG (Implication (Atomic "t1A") (EF (Atomic "t1C")))


transform :: CTL -> CTL
transform Top = Not Bottom
transform (Implication f1 f2) = transform (Or (Not (transform f1)) (transform f2))
transform (And f1 f2) = And (transform f1) (transform f2)
transform (Or f1 f2) = transform (Not (And (Not (transform f1)) (Not (transform f2))))
transform (AX f) = transform (Not (EX (Not (transform f))))
transform (EF f) = EU (transform Top) (transform f)
transform (AG f) = transform (Not (transform (EF (Not (transform f)))))
transform (EG f) = transform (Not (AF (Not (transform f))))
transform (AU f1 f2) = transform (Not (Or (EU (Not (transform f2)) (And (Not (transform f1)) (Not (transform f2)))) (transform (EG (Not (transform f2))))))
transform (AF f) = AF (transform f)
transform (EU f1 f2) = EU (transform f1) (transform f2)
transform (EX f) = EX (transform f)
transform (Not (Not f)) = transform f
transform (Not f) = Not (transform f)
transform f = f

previousStates :: Model -> State -> [State]
previousStates m s = [p | p <- states m, s `elem` transition m p]

fix :: (Eq x) => (x -> x) -> x -> x
fix f x = if f x == x then x else fix f (f x)

lfp f = fix f []

-- model checker-ul primeste un model si o formula CTL si returneaza starile din model care satisfac formula
modelChecker :: Model -> CTL -> [State]
modelChecker m Bottom = []
modelChecker m (Atomic p) = [s | s <- states m, p `elem` labels m s]
modelChecker m (And p q) = [s | s <- states m, s `elem` modelChecker m p, s `elem` modelChecker m q]
modelChecker m (Not p) = [s | s <- states m, s `notElem` modelChecker m p]
modelChecker m (EX p) = let s1 = modelChecker m p
                            s = s1 >>= previousStates m 
                        in nub s
modelChecker m (AF p) = lfp (\x -> nub (modelChecker m p ++ getAX m x))
                            where getAX m x = [s | s <- states m, all (`elem` x) (transition m s)] 
modelChecker m (EU p q) = lfp (\x -> nub (modelChecker m q ++ intersect (modelChecker m p) (getEX m x)))
                            where getEX m x = [s | s <- states m, any (`elem` x) (transition m s)] 

-- getAX si getEX sunt de tip Model -> [State] -> [State]
-- getAX returneaza starile care au toti succesorii in lista de stari x
-- getEX returneaza starile care au cel putin un succesor in x

-- folosim Set in locul listelor pentru output
fix2 :: (Eq a) => (a -> a)-> a -> a
fix2 f x = if x == f x then x else fix2 f (f x)

lfp2 f = fix2 f Set.empty

modelChecker2 :: Model -> CTL -> Set State
modelChecker2 m Bottom = Set.empty
modelChecker2 m (Atomic p) = Set.fromList [s | s <- states m, p `elem` labels m s]
modelChecker2 m (And p q) = let mcp = modelChecker2 m p
                                mcq = modelChecker2 m q
                             in Set.intersection mcp mcq
modelChecker2 m (Not p) = let mcp = modelChecker2 m p
                           in Set.difference (Set.fromList (states m)) mcp 

modelChecker2 m (EX p) = let mcp = modelChecker2 m p
                         in Set.fromList [s | s <- states m, any (`Set.member` mcp) (transition m s)]
modelChecker2 m (AF p) = lfp2 (\x -> Set.union (modelChecker2 m p) (getAX m x))
                         where getAX m x = Set.fromList [s | s <- states m, all (`Set.member` x) (transition m s)] 

modelChecker2 m (EU p q) = lfp2 (\x -> Set.union (modelChecker2 m q) (Set.intersection (modelChecker2 m p) (getEX m x)))
                           where getEX m x = Set.fromList [s | s <- states m, any (`Set.member` x) (transition m s)] 

-- acelasi algoritm pe versiunea optimizata a modelului

modelChecker3 :: Model2 -> CTL -> Set.Set State
modelChecker3 m Bottom = Set.empty

modelChecker3 m (Atomic p) = Set.fromList [s | s <- Set.toList (states2 m), let labels = fromJust (Map.lookup s (labels2 m)), p `Set.member` labels]

modelChecker3 m (And p q) = let mcp = modelChecker3 m p
                                mcq = modelChecker3 m q
                              in Set.intersection mcp mcq

modelChecker3 m (Not p) = let mcp = modelChecker3 m p
                           in Set.difference (states2 m) mcp

modelChecker3 m (EX p) = let mcp = modelChecker3 m p
                         in Set.fromList [s | s <- Set.toList (states2 m), let transition = fromJust(Map.lookup s (transition2 m)), any (`Set.member` mcp) transition]

modelChecker3 m (AF p) = lfp2 (\x -> Set.union (modelChecker3 m p) (getAX m x))
                         where getAX m x = Set.fromList [s | s <- Set.toList (states2 m), let transition = fromJust (Map.lookup s (transition2 m)), all (`Set.member` x) transition]

modelChecker3 m (EU p q) = lfp2 (\x -> Set.union (modelChecker3 m q) (Set.intersection (modelChecker3 m p) (getEX m x)))
                           where getEX m x = Set.fromList [s | s <- Set.toList (states2 m), let transition = fromJust (Map.lookup s (transition2 m)), any (`Set.member` x) transition]




