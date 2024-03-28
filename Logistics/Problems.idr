module Logistics.Problems

import Logistics.Domain
import Utils
import Petri

import Decidable.Equality
import Data.List.Elem

namespace P1
  
  public export init : Mark
  init =
    { -- objects and their types
      type_airport := ["apt1", "apt2"]
    , type_location := ["pos1", "pos2"]
    , type_place := ["apt1", "apt2", "pos1", "pos2"]
    , type_truck := ["tru1", "tru2"]
    , type_plane := ["apn1"]
    , type_vehicle := ["tru1", "tru2", "apn1"]
    , type_package := ["obj23", "obj22", "obj21", "obj13", "obj12", "obj11"]
    , type_physobj := ["tru1", "tru2", "apn1", "obj23", "obj22", "obj21", "obj13", "obj12", "obj11"]
    , type_city := ["cit2", "cit1"]
      -- predicates and their values
    , pred_at := [ ("apn1", "apt2")
                 , ("tru1", "pos1")
                 , ("obj11", "pos1")
                 , ("obj12", "pos1")
                 , ("obj13", "pos1")
                 , ("tru2", "pos2")
                 , ("obj21", "pos2")
                 , ("obj22", "pos2")
                 , ("obj23", "pos2")
                 ]
    , pred_in_city := [ ("pos1", "cit1")
                      , ("apt1", "cit1")
                      , ("pos2", "cit2")
                      , ("apt2", "cit2")
                      ]
    } emptyMark
  
  public export Goal : Mark -> Type
  Goal m = ( Elem ("obj11", "apt1") m.pred_at
           , Elem ("obj23", "pos1") m.pred_at
           , Elem ("obj13", "apt1") m.pred_at
           , Elem ("obj21", "pos1") m.pred_at
           )
   
  public export  decGoal : (m: Mark) -> Dec (Goal m)
  decGoal m = decPair (isElem ("obj11", "apt1") m.pred_at)
            $ decPair (isElem ("obj23", "pos1") m.pred_at)
            $ decPair (isElem ("obj13", "apt1") m.pred_at)
            $ (isElem ("obj21", "pos1") m.pred_at)

  public export test_plan : List (Transition Mark String, List String)
  test_plan =
    [ (t_load_truck, ["obj23", "tru2", "pos2"])
    , (t_load_truck, ["obj21", "tru2", "pos2"])
    , (t_load_truck, ["obj13", "tru1", "pos1"])
    , (t_load_truck, ["obj11", "tru1", "pos1"])
    , (t_drive_truck, ["tru2", "pos2", "apt2", "cit2"])
    , (t_unload_truck, ["obj23", "tru2", "apt2"])
    , (t_load_plane, ["obj23", "apn1", "apt2"])
    , (t_unload_truck, ["obj21", "tru2", "apt2"])
    , (t_load_plane, ["obj21", "apn1", "apt2"])
    , (t_fly_plane,  ["apn1", "apt2", "apt1"])
    , (t_unload_plane, ["obj23", "apn1", "apt1"])
    , (t_unload_plane, ["obj21", "apn1", "apt1"])
    , (t_drive_truck, ["tru1", "pos1", "apt1", "cit1"])
    , (t_load_truck, ["obj23", "tru1", "apt1"])
    , (t_load_truck, ["obj21", "tru1", "apt1"])
    , (t_unload_truck, ["obj13", "tru1", "apt1"])
    , (t_unload_truck, ["obj11", "tru1", "apt1"])
    , (t_drive_truck, ["tru1", "apt1", "pos1", "cit1"])
    , (t_unload_truck, ["obj23", "tru1", "pos1"])
    , (t_unload_truck, ["obj21", "tru1", "pos1"])
    ]
