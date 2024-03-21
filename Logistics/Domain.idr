module Logistics.Domain

import Decidable.Equality
import Decidable.Decidable
import Data.List.Elem

import Petri
import Utils

public export Token : Type
Token = String

public export
record Mark where
  constructor MkMark
  -- Types
  type_city : List Token
  type_place : List Token
  type_physobj : List Token
  type_package : List Token
  type_vehicle : List Token
  type_truck : List Token
  type_plane : List Token
  type_airport : List Token
  type_location : List Token
  -- Other predicates
  pred_in_city : List (Token, Token)
  pred_at : List (Token, Token)
  pred_in : List (Token, Token)

DecEq Mark where
  decEq (MkMark tcity tplace tphysobj tpackage tvehicle ttruck tplane tairport tlocation pin_city pat pin)
        (MkMark tcity' tplace' tphysobj' tpackage' tvehicle' ttruck' tplane' tairport' tlocation' pin_city' pat' pin') =
      case decEq tcity tcity' of
        No c => No $ \p => c (cong type_city p)
        Yes Refl => case decEq tplace tplace' of
          No c => No $ \p => c (cong type_place p)
          Yes Refl => case decEq tphysobj tphysobj' of
            No c => No $ \p => c (cong type_physobj p)
            Yes Refl => case decEq tpackage tpackage' of
              No c => No $ \p => c (cong type_package p)
              Yes Refl => case decEq tvehicle tvehicle' of
                No c => No $ \p => c (cong type_vehicle p)
                Yes Refl => case decEq ttruck ttruck' of
                  No c => No $ \p => c (cong type_truck p)
                  Yes Refl => case decEq tplane tplane' of
                    No c => No $ \p => c (cong type_plane p)
                    Yes Refl => case decEq tairport tairport' of
                      No c => No $ \p => c (cong type_airport p)
                      Yes Refl => case decEq tlocation tlocation' of
                        No c => No $ \p => c (cong type_location p)
                        Yes Refl => case decEq pin_city pin_city' of
                          No c => No $ \p => c (cong pred_in_city p)
                          Yes Refl => case decEq pat pat' of
                            No c => No $ \p => c (cong pred_at p)
                            Yes Refl => case decEq pin pin' of
                              No c => No $ \p => c (cong pred_in p)
                              Yes Refl => Yes $ Refl


public export emptyMark : Mark
emptyMark = MkMark [] [] [] [] [] [] [] [] [] [] [] []

namespace Search
  public export
  action_load_truck : Mark -> List Mark
  action_load_truck m =
    [ { pred_at := deleteDec (var_pkg, var_loc) m.pred_at
      , pred_in := (var_pkg, var_truck) :: m.pred_in
      } m
    | var_pkg <- m.type_package
    , var_truck <- m.type_truck
    , var_loc <- m.type_place
    , isYes $ isElem (var_truck, var_loc) m.pred_at
    , isYes $ isElem (var_pkg, var_loc) m.pred_at
    ]
  public export action_load_plane : Mark -> List Mark
  action_load_plane m =
    [ { pred_at := deleteDec (var_pkg, var_loc) m.pred_at
      , pred_in := (var_pkg, var_plane) :: m.pred_in
      } m
    | var_pkg <- m.type_package
    , var_plane <- m.type_plane
    , var_loc <- m.type_place
    , isYes $ isElem (var_plane, var_loc) m.pred_at
    , isYes $ isElem (var_pkg, var_loc) m.pred_at
    ]
  public export action_unload_truck : Mark -> List Mark
  action_unload_truck m =
    [ { pred_at := (var_pkg, var_loc) :: m.pred_at
      , pred_in := deleteDec (var_pkg, var_truck) m.pred_in
      } m
    | var_pkg <- m.type_package
    , var_truck <- m.type_truck
    , var_loc <- m.type_place
    , isYes $ isElem (var_truck, var_loc) m.pred_at
    , isYes $ isElem (var_pkg, var_truck) m.pred_in
    ]
  public export action_unload_plane : Mark -> List Mark
  action_unload_plane m =
    [ { pred_at := (var_pkg, var_loc) :: m.pred_at
      , pred_in := deleteDec (var_pkg, var_plane) m.pred_in
      } m
    | var_pkg <- m.type_package
    , var_plane <- m.type_plane
    , var_loc <- m.type_place
    , isYes $ isElem (var_plane, var_loc) m.pred_at
    , isYes $ isElem (var_pkg, var_plane) m.pred_in
    ]
  public export action_fly_plane : Mark -> List Mark
  action_fly_plane m =
    [ { pred_at := (var_plane, var_to) :: deleteDec (var_plane, var_from) m.pred_at
      } m
    | var_plane <- m.type_plane
    , var_from <- m.type_airport
    , var_to <- m.type_airport
    , isYes $ isElem (var_plane, var_from) m.pred_at
    ]
  public export action_drive_truck : Mark -> List Mark
  action_drive_truck m =
    [ { pred_at := (var_truck, var_to) :: deleteDec (var_truck, var_from) m.pred_at
      } m
    | var_truck <- m.type_truck
    , var_from <- m.type_place
    , var_to <- m.type_place
    , var_city <- m.type_city
    , isYes $ isElem (var_truck, var_from) m.pred_at
    , isYes $ isElem (var_from, var_city) m.pred_in_city
    , isYes $ isElem (var_to, var_city) m.pred_in_city
    ]
  
  public export theNet : Net Mark
  theNet = MkNet [ MkTransition "load_truck" action_load_truck
                 , MkTransition "load_plane" action_load_plane
                 , MkTransition "unload_truck" action_unload_truck
                 , MkTransition "unload_plane" action_unload_plane
                 , MkTransition "fly_plane" action_fly_plane
                 , MkTransition "drive_truck" action_drive_truck
                 ]
namespace Run
  public export action_load_truck : Mark -> List Token -> Maybe Mark
  action_load_truck m [var_pkg, var_truck, var_loc] =
    case isElem var_pkg m.type_package of
      No _ => Nothing
      Yes _ => case isElem var_truck m.type_truck of
        No _ => Nothing
        Yes _ => case isElem var_loc m.type_place of
          No _ => Nothing
          Yes _ => case isElem (var_truck, var_loc) m.pred_at of
            No _ => Nothing
            Yes _ => case isElem (var_pkg, var_loc) m.pred_at of
              No _ => Nothing
              Yes _ => Just $ { pred_at := deleteDec (var_pkg, var_loc) m.pred_at
                              , pred_in := (var_pkg, var_truck) :: m.pred_in
                              } m
  action_load_truck _ _ = Nothing
  
  public export action_load_plane : Mark -> List Token -> Maybe Mark
  action_load_plane m [var_pkg, var_plane, var_loc] =
    case isElem var_pkg m.type_package of
      No _ => Nothing
      Yes _ => case isElem var_plane m.type_plane of
        No _ => Nothing
        Yes _ => case isElem var_loc m.type_place of
          No _ => Nothing
          Yes _ => case isElem (var_plane, var_loc) m.pred_at of
            No _ => Nothing
            Yes _ => case isElem (var_pkg, var_loc) m.pred_at of
              No _ => Nothing
              Yes _ => Just $ { pred_at := deleteDec (var_pkg, var_loc) m.pred_at
                              , pred_in := (var_pkg, var_plane) :: m.pred_in
                              } m
  action_load_plane _ _ = Nothing
  
  public export action_unload_truck : Mark -> List Token -> Maybe Mark
  action_unload_truck m [var_pkg, var_truck, var_loc] =
    case isElem var_pkg m.type_package of
      No _ => Nothing
      Yes _ => case isElem var_truck m.type_truck of
        No _ => Nothing
        Yes _ => case isElem var_loc m.type_place of
          No _ => Nothing
          Yes _ => case isElem (var_truck, var_loc) m.pred_at of
            No _ => Nothing
            Yes _ => case isElem (var_pkg, var_truck) m.pred_in of
              No _ => Nothing
              Yes _ => Just $ { pred_in := deleteDec (var_pkg, var_truck) m.pred_in
                              , pred_at := (var_pkg, var_loc) :: m.pred_at
                              } m
  action_unload_truck _ _ = Nothing
  public export action_unload_plane : Mark -> List Token -> Maybe Mark
  action_unload_plane m [var_pkg, var_plane, var_loc] =
    case isElem var_pkg m.type_package of
      No _ => Nothing
      Yes _ => case isElem var_plane m.type_plane of
        No _ => Nothing
        Yes _ => case isElem var_loc m.type_place of
          No _ => Nothing
          Yes _ => case isElem (var_plane, var_loc) m.pred_at of
            No _ => Nothing
            Yes _ => case isElem (var_pkg, var_plane) m.pred_in of
              No _ => Nothing
              Yes _ => Just $ { pred_in := deleteDec (var_pkg, var_plane) m.pred_in
                              , pred_at := (var_pkg, var_loc) :: m.pred_at
                              } m
  action_unload_plane _ _ = Nothing
  
  public export action_fly_plane : Mark -> List Token -> Maybe Mark
  action_fly_plane m [var_plane, var_from, var_to] =
    case isElem var_plane m.type_plane of
      No _ => Nothing
      Yes _ => case isElem var_from m.type_airport of
        No _ => Nothing
        Yes _ => case isElem var_to m.type_airport of
          No _ => Nothing
          Yes _ => case isElem (var_plane, var_from) m.pred_at of
            No _ => Nothing
            Yes _ => Just $ { pred_at := (var_plane, var_to) :: deleteDec (var_plane, var_from) m.pred_at
                            } m
  action_fly_plane _ _ = Nothing
  
  public export action_drive_truck : Mark -> List Token -> Maybe Mark
  action_drive_truck m [var_truck, var_from, var_to, var_city] =
    case isElem var_truck m.type_truck of
      No _ => Nothing
      Yes _ => case isElem var_from m.type_place of
        No _ => Nothing
        Yes _ => case isElem var_to m.type_place of
          No _ => Nothing
          Yes _ => case isElem var_city m.type_city of
            No _ => Nothing
            Yes _ => case isElem (var_truck, var_from) m.pred_at of
              No _ => Nothing
              Yes _ => case isElem (var_from, var_city) m.pred_in_city of
                No _ => Nothing
                Yes _ => case isElem (var_to, var_city) m.pred_in_city of
                  No _ => Nothing
                  Yes _ => Just $ { pred_at := (var_truck, var_to) :: deleteDec (var_truck, var_from) m.pred_at
                                  } m
  action_drive_truck _ _ = Nothing
  
  
  public export t_load_truck : Transition Mark Token
  t_load_truck = MkTransition "load_truck" action_load_truck
  
  public export t_load_plane : Transition Mark Token
  t_load_plane = MkTransition "load_plane" action_load_plane
  
  public export t_unload_truck : Transition Mark Token
  t_unload_truck = MkTransition "unload_truck" action_unload_truck
  
  public export t_unload_plane : Transition Mark Token
  t_unload_plane = MkTransition "unload_plane" action_unload_plane
  
  public export t_fly_plane : Transition Mark Token
  t_fly_plane = MkTransition "fly_plane" action_fly_plane
  
  public export t_drive_truck : Transition Mark Token
  t_drive_truck = MkTransition "drive_truck" action_drive_truck

