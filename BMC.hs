import Data.List
import SAT.MiniSat as MS

import Models (State, Model(..))

import Study.Case 

data LTL
    = LTop
    | LBottom
    | LAtomic String
    | LNot LTL
    | LAnd LTL LTL
    | LOr LTL LTL
    | LImplication LTL LTL
    | X LTL
    | F LTL
    | G LTL
    | U LTL LTL
    deriving (Show, Eq)

m :: Model
m = Study.Case.model

-- formule

-- daca trenul 1 se afla intre A si B, atunci trenul 2 nu se va afla intre A si B
safety :: LTL
safety = G (LImplication (LOr (LAtomic "t1AB") (LAtomic "t1BA")) (LNot (LOr (LAtomic "t2AB") (LAtomic "t2BA"))))

-- exista circulatie in sistem - cel putin un tren va ajunge din statia A in alta statie
liveness :: LTL
liveness = LOr (LImplication (LAtomic "t1A") (LOr (F (LAtomic "t1B")) (F (LAtomic "t1C")))) (LImplication (LAtomic "t2A") (LOr (F (LAtomic "t2B")) (F (LAtomic "t2C"))))

-- daca un tren s-a aflat la un moment dat intre A si B asta inseamna ca s-a aflat si in A si in B la momente diferite de timp
f :: LTL
f = LOr (LImplication (F (LOr (LAtomic "t1AB") (LAtomic "t1BA"))) (LAnd (F (LAtomic "t1A")) (F (LAtomic "t1B")))) (LImplication (F (LOr (LAtomic "t2AB") (LAtomic "t2BA"))) (LAnd (F (LAtomic "t2A")) (F (LAtomic "t2B"))))

-- unroll the transition function from a given state k times
unrollState :: (State -> [State]) -> Int -> State -> [[State]]
unrollState transition 0 s = [[s]]
unrollState transition k s =  let nextStates = transition s in
                         [s:path| nextState <- nextStates, path <- unrollState transition (k-1) nextState]

-- unroll from the initial states of a model
unroll :: Model -> Int -> [[State]]
unroll m k = concatMap (unrollState (transition m) (k - 1) ) (initialStates m)

-- check if there is a loop
-- it takes the last state in a list of states and checks if any of its successors is already in the list
loop :: Model -> [State] -> Bool
loop m [x] = let y = transition m x in
                not $ null ([z | z <-y, z == x])
loop m (x:xs) = let y = transition m (last xs) in
                  not $ null ([z | z <-y, z `elem` (x:xs)])

-- for a list of states for which we detected a loop, return the subpaths representing the loops
loopSubpaths :: Model -> [State] -> [[State]]
loopSubpaths m s =  let y = transition m (last s)
                    in [sub z s| z <- y, z `elem` s]
                    where sub z (x:xs) | x == z = (x:xs)
                                       | otherwise = sub z xs

-- translation of an LTL Formula for a path whithout a loop
ltlToProp :: [State] -> LTL -> Formula String
ltlToProp [] _ = No
ltlToProp (x:xs) (LAtomic s) = Var $ s ++ x
ltlToProp x (LNot f) = Not $ ltlToProp x f
ltlToProp x (LOr f g) =  ltlToProp x f :||: ltlToProp x g
ltlToProp x (LAnd f g) = ltlToProp x f :&&: ltlToProp x g
ltlToProp x (LImplication f g) = ltlToProp x (LNot f) :||: ltlToProp x g
ltlToProp (x:xs) (G f) = ltlToProp (x:xs) f :&&: ltlToProp xs (G f)
ltlToProp (x:xs) (F f) = ltlToProp (x:xs) f :||: ltlToProp xs (F f)
ltlToProp (x:xs) (U f g) = ltlToProp (x:xs) g :||: ( ltlToProp (x:xs) f :&&: ltlToProp xs (U f g) )
ltlToProp (x:xs) (X f) = ltlToProp xs f

-- translation of an LTL formula for a path with loop
-- the list of states is the full path, the second is the subpath representing the loop, with the last element having a transition to the first
-- the function is the same, but instead of the base case being bottom it starts again with the second list
ltlToPropLoop :: [State] -> [State] -> LTL -> Formula String
ltlToPropLoop [] ls (G f) = ltlToPropLoop ls ls f -- avoid infinite loops for G

ltlToPropLoop (x:xs) ls (G f) | length (x:xs) > length ls = ltlToPropLoop (x:xs) ls f :&&: ltlToPropLoop xs ls (G f)
                                -- if we are past the start of the loop we go back to it
                                -- check which of the two lists has more elements: if the first is greater, then it means that we did not enter 
                                -- the loop yet, otherwise, we need to ensure that G f is true accross the entire loop, so we go back to the begining
                              | otherwise = globalLoop ls ls (G f) where
                                globalLoop [] ls (G f) = ltlToPropLoop ls ls f
                                globalLoop (x:xs) ls (G f) = ltlToPropLoop (x:xs) ls f :&&: globalLoop xs ls (G f)
-- analog for F
ltlToPropLoop [] ls (F f) = ltlToPropLoop ls ls f
ltlToPropLoop (x:xs) ls (F f) | length (x:xs) > length ls  = ltlToPropLoop (x:xs) ls f :||: ltlToPropLoop xs ls (F f)
                              | otherwise = futureLoop ls ls (F f) where
                                futureLoop [] ls (F f) = ltlToPropLoop ls ls f
                                futureLoop (x:xs) ls (F f) = ltlToPropLoop (x:xs) ls f :||: futureLoop xs ls (F f)

-- for U we compute the function until we reached [] (i = k+1) then we compute the fixed point for each state in the loop
-- for U we approximate the least fixed point so we start from bottom ; more explanations in the paper
ltlToPropLoop [] ls (U f g) = untilLoop ls ls (U f g) where
                              untilLoop [] ls (U f g) = No -- = fixpointU [] ls (U f g) = no
                              untilLoop (x:xs) ls (U f g) = fixpointU (x:xs) ls (U f g) :||: untilLoop xs ls (U f g)
                              fixpointU (x:xs) ls (U f g) = ltlToPropLoop (x:xs) ls g :||: ( ltlToPropLoop (x:xs) ls f :&&: fixpointU xs ls (U f g) )
ltlToPropLoop (x:xs) ls (U f g) = ltlToPropLoop (x:xs) ls g :||: (ltlToPropLoop (x:xs) ls f :&&: ltlToPropLoop xs ls (U f g) )

ltlToPropLoop [] ls f = ltlToPropLoop ls ls f
ltlToPropLoop (x:xs) ls (LAtomic s) = Var $ s ++ x
ltlToPropLoop x ls (LNot f) = Not $ ltlToPropLoop x ls f
ltlToPropLoop x ls (LOr f g) = ltlToPropLoop x ls f :||: ltlToPropLoop x ls g
ltlToPropLoop x ls (LAnd f g) = ltlToPropLoop x ls f :&&: ltlToPropLoop x ls g
ltlToPropLoop x ls (LImplication f g) = ltlToPropLoop x ls (LNot f) :||: ltlToPropLoop x ls g
ltlToPropLoop (x:xs) ls (X f) = ltlToPropLoop xs ls f

-- labeling constraints 
-- get the variables corresponding to the labeling function of the model

collectVars :: Formula String -> [String]
collectVars No = []
collectVars (Var x) = [x]
collectVars (Not p) = collectVars p
collectVars (p :&&: q) = collectVars p ++ collectVars q
collectVars (p :||: q) = collectVars p ++ collectVars q

labelFormula :: Model -> [State] -> Formula String
labelFormula m s = listToProp $ getF m s where
                    getF m [x] = [Var (l++x) |l <- labels m x]
                    getF m (x:xs) = [Var (l++x) |l <- labels m x] ++ getF m xs
                    listToProp [x] = x
                    listToProp (x:xs) =  x :&&: listToProp xs

-- given the model prop we got from ltlToProp adds the constraints for 

addNotLabeled :: [String] -> [String] -> Formula String -- gets the atoms of the labels variables, the atoms of the encoding for ltl constraint and returns the entire labels constraint
addNotLabeled l [f] | f `elem` l = Var f
                    | otherwise = Not (Var f)

addNotLabeled l (f:fs) | f `elem` l = Var f :&&: addNotLabeled l fs
                       | otherwise =  Not (Var f) :&&: addNotLabeled l fs

getLabelConstraints :: Model -> [State] -> Formula String -> Formula String
getLabelConstraints m s f = let lf = labelFormula m s
                                at = collectVars f
                                lat = collectVars lf
                            in addNotLabeled lat at

-- algorithm: unroll the model starting with k = 3 (or a low number) 
-- for every path: check if there is a loop then construct the propositional formula for Not (LTL constraint) accordingly
--                 if the formula is satisfiable then the model does not respect the constraint

-- construct the formula for a path with no loops in the model
getBMCformulaPath :: Model -> [State] -> LTL -> Formula String
getBMCformulaPath m s f = let prop = ltlToProp s f
                              lprop =  getLabelConstraints m s prop
                              formula = prop :&&: lprop
                          in formula

-- construct the formula for a path with loop, and a loop
getBMCloop :: Model -> [State] -> [State] -> LTL -> Formula String
getBMCloop m s ls f = let prop = ltlToPropLoop s ls f
                          lprop =  getLabelConstraints m s prop
                          formula = prop :&&: lprop
                          in formula

-- check if there is a kpath that satisfies the formula
checkPath :: Model -> [[State]] -> LTL -> Maybe [State]
checkPath m [] f = Nothing
checkPath m (x:xs) f | null $ loopSubpaths m x =  let prop = getBMCformulaPath m x f
                      in if satisfiable prop then Just x else checkPath m xs f
                     | otherwise = let subPaths = loopSubpaths m x --when we have a path with a loop from the last state to another state in the path or to itself
                                                             --check all the possible loops
                     in if checkEachPath m x subPaths f == Nothing then checkPath m xs f else Just x
                     where checkEachPath m x [] f = Nothing
                           checkEachPath m x (l:ls) f = let prop = getBMCloop m x l f
                                                        in if satisfiable prop then Just x else checkEachPath m x ls f

boundedMC :: Model -> LTL -> Int -> Int -> Maybe [State]
boundedMC m f k max | k <= max = let paths = unroll m k
                                     isSAT = checkPath m paths f
                                  in if isSAT == Nothing then boundedMC m f (k+1) max else isSAT
                    | otherwise = Nothing