import Petri

import Decidable.Equality
import Decidable.Decidable
import Data.List.Elem

import Debug.Trace


bfs_rec : DecEq mark
        => Net mark -- The net
        -> mark -- The current mark
        -> (goal: mark -> Type) -- Goal
        -> ((gm: mark) -> Dec (goal gm))
        -> (List (String, mark) -> List (String, mark)) -- heuristic
        -> String -- last name
        -> List mark -- visited
        -> List (String, mark) -- queue
        -> Bool -- path
bfs_rec n m g ig h s v q =
  case trace s (ig m) of
    Yes _ => True
    No _ =>
      let q' = q ++ enabled n m in
        case q' of
          Nil => False
          (s', m') :: q'' =>
            bfs_rec n m' g ig h s' (m :: v) (h new_queue) where
              filterElem : DecEq x => List x -> List (a, x) -> List (a, x)
              filterElem _ [] = []
              filterElem l ((s, x) :: xs) = case isElem x l of
                Yes _ => (s, x) :: filterElem l xs
                No _ => filterElem l xs
              new_queue : List (String, mark)
              new_queue = filterElem (m :: v) $ q ++ enabled n m

              
export
bfs : DecEq mark
    => Net mark
    -> mark
    -> (goal: mark -> Type)
    -> ((gm: mark) -> Dec (goal gm))
    -> (List (String, mark) -> List (String, mark))
    -> Bool
bfs n m g ig h = bfs_rec n m g ig h "INIT" [] []

