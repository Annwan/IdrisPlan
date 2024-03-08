module ChildSnack.Instances

import ChildSnack.Token
import ChildSnack.Predicate
import ChildSnack.Domain

import Utils

import Decidable.Equality
import Decidable.Decidable

import Data.List
import Data.List.Elem

namespace I1
  public export
  init : Mark
  init =
    { at := [At (Tray n, Place "kitchen") | n <- [1..3]]
    , at_kitchen_bread := [Bread n | n <- [1..10]]
    , at_kitchen_content := [Content n | n <- [1..10]]
    , no_gluten_bread := [Bread n | n <- [2, 9, 4, 8]]
    , no_gluten_content := [Content n | n <- [2, 8, 4, 1]]
    , allergic_gluten := [Child n | n <- [1, 10, 3, 4]]
    , not_allergic_gluten := [Child n | n <- [2, 5, 6, 7, 8, 9]]
    , waiting := [ Waiting (Child 1, Place "table 2")
                 , Waiting (Child 2, Place "table 1")
                 , Waiting (Child 3, Place "table 1")
                 , Waiting (Child 4, Place "table 2")
                 , Waiting (Child 5, Place "table 3")
                 , Waiting (Child 6, Place "table 3")
                 , Waiting (Child 7, Place "table 3")
                 , Waiting (Child 8, Place "table 2")
                 , Waiting (Child 9, Place "table 1")
                 , Waiting (Child 10, Place "table 3")
                 ]
    , not_exist_sandwich := [Sandwich n | n <- [1..13]]
    } emptyMarking

  public export
  Goal : Mark -> Type
  Goal m = ( Elem (Child 1) m.served
           , Elem (Child 2) m.served
           , Elem (Child 3) m.served
           , Elem (Child 4) m.served
           , Elem (Child 5) m.served
           , Elem (Child 6) m.served
           , Elem (Child 7) m.served
           , Elem (Child 8) m.served
           , Elem (Child 9) m.served
           , Elem (Child 10) m.served
           )
  public export 
  isGoal : (m: Mark) -> Dec (Goal m)
  isGoal m = decPair (isElem (Child 1) m.served)
           $ decPair (isElem (Child 2) m.served)
           $ decPair (isElem (Child 3) m.served)
           $ decPair (isElem (Child 4) m.served)
           $ decPair (isElem (Child 5) m.served)
           $ decPair (isElem (Child 6) m.served)
           $ decPair (isElem (Child 7) m.served)
           $ decPair (isElem (Child 8) m.served)
           $ decPair (isElem (Child 9) m.served)
                     (isElem (Child 10) m.served)
