module ChildSnack.Domain

import ChildSnack.Token
import ChildSnack.Predicate
import Decidable.Equality
import Decidable.Decidable
import Petri
import Utils

||| Petri Places
||| PDDL predicates and specifics
public export
record Mark where
  constructor MkMark 
  -- Specifics
  places : List Token
  -- Predicates
  at_kitchen_bread : List Token
  at_kitchen_content : List Token
  at_kitchen_sandwich : List Token
  no_gluten_bread : List Token
  no_gluten_content : List Token
  ontray : List Predicate
  no_gluten_sandwich : List Token
  allergic_gluten : List Token
  not_allergic_gluten : List Token
  served : List Token
  waiting : List Predicate
  at : List Predicate
  not_exist_sandwich : List Token
  
public export
DecEq Mark where
  decEq m1@(MkMark p1 akb1 akc1 aks1 ngb1 ngc1 ot1 ngs1 ag1 nag1 s1 w1 a1 nes1)
        m2@(MkMark p2 akb2 akc2 aks2 ngb2 ngc2 ot2 ngs2 ag2 nag2 s2 w2 a2 nes2) =
  case decEq p1 p2 of
    No c => No $ \p => c (cong places p)
    Yes Refl => case decEq akb1 akb2 of
      No c => No $ \p => c (cong at_kitchen_bread p)
      Yes Refl => case decEq akc1 akc2 of
        No c => No $ \p => c (cong at_kitchen_content p)
        Yes Refl => case decEq aks1 aks2 of
          No c => No $ \p => c (cong at_kitchen_sandwich p)
          Yes Refl => case decEq ngb1 ngb2 of
            No c => No $ \p => c (cong no_gluten_bread p)
            Yes Refl => case decEq ngc1 ngc2 of
              No c => No $ \p => c (cong no_gluten_content p)
              Yes Refl => case decEq ot1 ot2 of
                No c => No $ \p => c (cong ontray p)
                Yes Refl => case decEq ngs1 ngs2 of
                  No c => No $ \p => c (cong no_gluten_sandwich p)
                  Yes Refl => case decEq ag1 ag2 of
                    No c => No $ \p => c (cong allergic_gluten p)
                    Yes Refl => case decEq nag1 nag2 of
                      No c => No $ \p => c (cong not_allergic_gluten p)
                      Yes Refl => case decEq s1 s2 of
                        No c => No $ \p => c (cong served p)
                        Yes Refl => case decEq w1 w2 of
                          No c => No $ \p => c (cong waiting p)
                          Yes Refl => case decEq a1 a2 of
                            No c => No $ \p => c (cong at p)
                            Yes Refl => case decEq nes1 nes2 of
                              No c => No $ \p => c (cong not_exist_sandwich p)
                              Yes Refl => Yes Refl

public export
make_sandwich : Mark -> List Mark
make_sandwich m = do
  (aBread, otherBreads) <- select (.at_kitchen_bread m)
  (aContent, otherContents) <- select (.at_kitchen_content m)
  (aSandwich, otherSandwiches) <- select (.not_exist_sandwich m)
  [ ( { at_kitchen_bread := otherBreads
      , at_kitchen_content := otherContents
      , not_exist_sandwich := otherSandwiches
      , at_kitchen_sandwich := aSandwich :: (.at_kitchen_sandwich m)
      }
      m
    )
  ]
  
public export
make_sandwich' : Mark -> List Mark
make_sandwich' m =
  [ { at_kitchen_bread := deleteDec bread m.at_kitchen_bread
    , at_kitchen_content := deleteDec content m.at_kitchen_content
    , not_exist_sandwich := deleteDec sandwich m.not_exist_sandwich
    , at_kitchen_sandwich := sandwich :: m.at_kitchen_sandwich
    } m
  | bread <- m.at_kitchen_bread
  , content <- m.at_kitchen_content
  , sandwich <- m.not_exist_sandwich]


public export
t_make_sandwich : Transition Mark
t_make_sandwich = MkTransition "make_sandwich" make_sandwich'

public export
make_sandwich_no_gluten : Mark -> List Mark
make_sandwich_no_gluten m = do
  (aBread, otherBreads) <- select (.at_kitchen_bread m)
  (aContent, otherContents) <- select (.at_kitchen_content m)
  (aSandwich, otherSandwiches) <- select (.not_exist_sandwich m)
  (aNoGlutenBread, _) <- select (.no_gluten_bread m)
  (aNoGlutenContent, _) <- select (.no_gluten_content m)
  case decEq (aBread, aContent) (aNoGlutenBread, aNoGlutenContent) of
    Yes Refl =>
      [({ at_kitchen_bread := otherBreads
        , at_kitchen_content := otherContents
        , not_exist_sandwich := otherSandwiches
        -- no_gluten_bread static
        -- no_gluten_content static
        , at_kitchen_sandwich := aSandwich :: (at_kitchen_sandwich m)
        , no_gluten_sandwich := aSandwich :: (no_gluten_sandwich m)
        } m
      )]
    No contra => []

public export
make_sandwich_no_gluten' : Mark -> List Mark
make_sandwich_no_gluten' m =
  [ { at_kitchen_bread := deleteDec bread m.at_kitchen_bread
    , at_kitchen_content := deleteDec content m.at_kitchen_content
    , not_exist_sandwich := deleteDec sandwich m.not_exist_sandwich
    , at_kitchen_sandwich := sandwich :: m.at_kitchen_sandwich
    , no_gluten_sandwich := sandwich :: m.no_gluten_sandwich
    } m
  | bread <- m.at_kitchen_bread
  , content <- m.at_kitchen_content
  , sandwich <- m.not_exist_sandwich
  , ngbread <- m.no_gluten_bread
  , ngcontent <- m.no_gluten_content
  , isYes $ decEq bread ngbread
  , isYes $ decEq content ngcontent
  ]

{-
msng'' : Mark -> List Mark
msng'' m = filterDec (\(b, _, _, nb, _) => decEQ b nb )  [ (bread, content, sandwich, ngbread, ngcontent, { at_kitchen_bread := deleteDec bread m.at_kitchen_bread
    , at_kitchen_content := deleteDec content m.at_kitchen_content
    , not_exist_sandwich := deleteDec sandwich m.not_exist_sandwich
    , at_kitchen_sandwich := sandwich :: m.at_kitchen_sandwich
    , no_gluten_sandwich := sandwich :: m.no_gluten_sandwich
    } m)
  | bread <- m.at_kitchen_bread
  , content <- m.at_kitchen_content
  , sandwich <- m.not_exist_sandwich
  , ngbread <- m.no_gluten_bread
  , ngcontent <- m.no_gluten_content
  ]
-}
public export
t_make_sandwich_no_gluten : Transition Mark
t_make_sandwich_no_gluten = MkTransition "make_sandwich_no_gluten" make_sandwich_no_gluten'

public export
put_on_tray : Mark -> List Mark
put_on_tray m = do
  (aSandwich, otherSandwiches) <- select (.at_kitchen_sandwich m)
  (anAt, _) <- select (.at m)
  case anAt of
    (At (aTray, Place "kitchen")) =>
      [({ at_kitchen_sandwich := otherSandwiches
        , ontray := (OnTray (aSandwich, aTray)) :: (ontray m)
        } m
      )]
    _ => []

public export
t_put_on_tray : Transition Mark
t_put_on_tray = MkTransition "put_on_tray" put_on_tray

public export
move_tray : Mark -> List Mark
move_tray m = do
  (anAt, otherAts) <- select (.at m)
  (aPlace, _) <- select (places m)
  case anAt of
    (At (aTray,p)) => case decEq aPlace p of
      Yes Refl => []
      No contra =>
        [({ at := (At (aTray, aPlace)) :: otherAts } m)]
    _ => []

public export
t_move_tray : Transition Mark
t_move_tray = MkTransition "move_tray" move_tray

public export
serve_sandwich : Mark -> List Mark
serve_sandwich m = do
  (anOnTray, otherOnTrays) <- select (.ontray m)
  (anAt, _) <- select (.at m)
  (aWaiting, _) <- select (.waiting m)
  (aChild, _) <- select (.not_allergic_gluten m)
  case (guard anOnTray anAt aWaiting aChild) of
    Just c =>
      [({ ontray := otherOnTrays
        , served := c :: (.served m)
        } m
      )]
    Nothing => []
  where
    guard : Predicate -> Predicate -> Predicate -> Token -> Maybe Token
    guard (OnTray (_, t)) (At (t', p)) (Waiting (c, p')) c' =
      case decEq (t, p, c) (t', p', c') of
        Yes Refl => Just c
        No contra => Nothing
    guard _ _ _ _ = Nothing

public export
t_serve_sandwich : Transition Mark
t_serve_sandwich = MkTransition "serve_sandwich" serve_sandwich

public export
serve_sandwich_no_gluten : Mark -> List Mark
serve_sandwich_no_gluten m = do
  (aNonGlutenSandwich, _) <- select (.no_gluten_sandwich m)
  (anOnTray, otherOnTrays) <- select (.ontray m)
  (anAt, _) <- select (.at m)
  (aWaiting, _) <- select (.waiting m)
  (aChild, _) <- select (.allergic_gluten m)
  case (guard anAt aWaiting aChild anOnTray aNonGlutenSandwich) of
    Just c =>
      [({ ontray := otherOnTrays
        , served := c :: (.served m)
        } m
      )]
    Nothing => []
  where
    guard : Predicate -> Predicate -> Token -> Predicate -> Token -> Maybe Token
    guard (At (t', p)) (Waiting (c, p')) c' (OnTray (s, t)) s' =
      case decEq (t, c, p, s) (t', c', p', s') of
        Yes Refl => Just c
        No contra => Nothing
    guard _ _ _ _ _ = Nothing
  
public export
t_serve_sandwich_no_gluten : Transition Mark
t_serve_sandwich_no_gluten = MkTransition "serve_sandwich_no_gluten" serve_sandwich_no_gluten

public export
theNet : Net Mark
theNet = MkNet [ t_make_sandwich
               , t_make_sandwich_no_gluten
               , t_put_on_tray
               , t_move_tray
               , t_serve_sandwich
               , t_serve_sandwich_no_gluten
               ]

public export
emptyMarking : Mark
emptyMarking = MkMark Nil Nil Nil Nil Nil Nil Nil Nil Nil Nil Nil Nil Nil Nil
