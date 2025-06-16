module Models where

import Data.Set as Set
import Data.Map as Map

type State = String
data Model = Model {
        states :: [State],
        initialStates :: [State],
        transition :: State -> [State],
        labels :: State -> [String] 
    }

-- model optimizat - in locul listelor folosim Set iar functiile sunt inlocuite cu dictionare
data Model2 = Model2 {
  states2 :: Set.Set State,                     
  initialStates2 :: Set.Set State,
  transition2 :: Map.Map State (Set.Set State),  
  labels2 :: Map.Map State (Set.Set String)       
}
