module ChildSnack.Token

import Decidable.Equality
-- the objects
public export
data Token = Bread Int
           | Content Int
           | Sandwich Int
           | Tray Int
           | Place String
           | Child Int
           
||| Two Breads are different if they do not have the same identifier
notSameBread : (i = j -> Void) -> Bread i = Bread j -> Void
notSameBread contra Refl = contra Refl
||| Two Contents are different if they do not have the same identifier
notSameContent : (i = j -> Void) -> Content i = Content j -> Void
notSameContent contra Refl = contra Refl
||| Two Sandwiches are different if they do not have the same identifier
notSameSandwich : (i = j -> Void) -> Sandwich i = Sandwich j -> Void
notSameSandwich contra Refl = contra Refl
||| Two Trays are different if they do not have the same identifier
notSameTray : (i = j -> Void) -> Tray i = Tray j -> Void
notSameTray contra Refl = contra Refl
||| Two Places are different if they do not have the same identifier
notSamePlace : (i = j -> Void) -> Place i = Place j -> Void
notSamePlace contra Refl = contra Refl
||| Two Childs are different if they do not have the same identifier
notSameChild : (i = j -> Void) -> Child i = Child j -> Void
notSameChild contra Refl = contra Refl

Uninhabited (Bread i    = Content j)  where uninhabited Refl impossible
Uninhabited (Bread i    = Sandwich j) where uninhabited Refl impossible
Uninhabited (Bread i    = Tray j)     where uninhabited Refl impossible
Uninhabited (Bread i    = Place j)    where uninhabited Refl impossible
Uninhabited (Bread i    = Child j)    where uninhabited Refl impossible
Uninhabited (Content i  = Bread j)    where uninhabited Refl impossible
Uninhabited (Content i  = Sandwich j) where uninhabited Refl impossible
Uninhabited (Content i  = Tray j)     where uninhabited Refl impossible
Uninhabited (Content i  = Place j)    where uninhabited Refl impossible
Uninhabited (Content i  = Child j)    where uninhabited Refl impossible
Uninhabited (Sandwich i = Bread j)    where uninhabited Refl impossible
Uninhabited (Sandwich i = Content j)  where uninhabited Refl impossible
Uninhabited (Sandwich i = Tray j)     where uninhabited Refl impossible
Uninhabited (Sandwich i = Place j)    where uninhabited Refl impossible
Uninhabited (Sandwich i = Child j)    where uninhabited Refl impossible
Uninhabited (Tray i     = Bread j)    where uninhabited Refl impossible
Uninhabited (Tray i     = Content j)  where uninhabited Refl impossible
Uninhabited (Tray i     = Sandwich j) where uninhabited Refl impossible
Uninhabited (Tray i     = Place j)    where uninhabited Refl impossible
Uninhabited (Tray i     = Child j)    where uninhabited Refl impossible
Uninhabited (Place i    = Bread j)    where uninhabited Refl impossible
Uninhabited (Place i    = Content j)  where uninhabited Refl impossible
Uninhabited (Place i    = Sandwich j) where uninhabited Refl impossible
Uninhabited (Place i    = Tray j)     where uninhabited Refl impossible
Uninhabited (Place i    = Child j)    where uninhabited Refl impossible
Uninhabited (Child i    = Bread j)    where uninhabited Refl impossible
Uninhabited (Child i    = Content j)  where uninhabited Refl impossible
Uninhabited (Child i    = Sandwich j) where uninhabited Refl impossible
Uninhabited (Child i    = Tray j)     where uninhabited Refl impossible
Uninhabited (Child i    = Place j)    where uninhabited Refl impossible


||| Objects aren't other objects
public export
DecEq Token where
  decEq (Bread i) (Bread j) = case decEq i j of
    Yes Refl => Yes Refl
    No contra => No $ notSameBread contra
  decEq (Content i) (Content j) = case decEq i j of
    Yes Refl => Yes Refl
    No contra => No $ notSameContent contra
  decEq (Sandwich i) (Sandwich j) = case decEq i j of
    Yes Refl => Yes Refl
    No contra => No $ notSameSandwich contra
  decEq (Tray i) (Tray j) = case decEq i j of
    Yes Refl => Yes Refl
    No contra => No $ notSameTray contra
  decEq (Place i) (Place j) = case decEq i j of
    Yes Refl => Yes Refl
    No contra => No $ notSamePlace contra
  decEq (Child i) (Child j) = case decEq i j of
    Yes Refl => Yes Refl
    No contra => No $ notSameChild contra
  decEq (Bread _)    (Content _)  = No absurd
  decEq (Bread _)    (Sandwich _) = No absurd
  decEq (Bread _)    (Tray _)     = No absurd
  decEq (Bread _)    (Place _)    = No absurd
  decEq (Bread _)    (Child _)    = No absurd
  decEq (Content _)  (Bread _)    = No absurd
  decEq (Content _)  (Sandwich _) = No absurd
  decEq (Content _)  (Tray _)     = No absurd
  decEq (Content _)  (Place _)    = No absurd
  decEq (Content _)  (Child _)    = No absurd
  decEq (Sandwich _) (Bread _)    = No absurd
  decEq (Sandwich _) (Content _)  = No absurd
  decEq (Sandwich _) (Tray _)     = No absurd
  decEq (Sandwich _) (Place _)    = No absurd
  decEq (Sandwich _) (Child _)    = No absurd
  decEq (Tray _)     (Bread _)    = No absurd
  decEq (Tray _)     (Content _)  = No absurd
  decEq (Tray _)     (Sandwich _) = No absurd
  decEq (Tray _)     (Place _)    = No absurd
  decEq (Tray _)     (Child _)    = No absurd
  decEq (Place _)    (Bread _)    = No absurd
  decEq (Place _)    (Content _)  = No absurd
  decEq (Place _)    (Sandwich _) = No absurd
  decEq (Place _)    (Tray _)     = No absurd
  decEq (Place _)    (Child _)    = No absurd
  decEq (Child _)    (Bread _)    = No absurd
  decEq (Child _)    (Content _)  = No absurd
  decEq (Child _)    (Sandwich _) = No absurd
  decEq (Child _)    (Tray _)     = No absurd
  decEq (Child _)    (Place _)    = No absurd


  
  

