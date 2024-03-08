module ChildSnack.Predicate

import ChildSnack.Token
import Decidable.Equality


public export
data Predicate = Served Token
               | OnTray (Token, Token)
               | Waiting (Token, Token)
               | At (Token, Token)


notSameServed : (t = t' -> Void) -> Served t = Served t' -> Void
notSameServed contra Refl = contra Refl
notSameOnTray : (t = t' -> Void) -> OnTray t = OnTray t' -> Void
notSameOnTray contra Refl = contra Refl
notSameWaiting : (t = t' -> Void) -> Waiting t = Waiting t' -> Void
notSameWaiting contra Refl = contra Refl
notSameAt : (t = t' -> Void) -> At t = At t' -> Void
notSameAt contra Refl = contra Refl

Uninhabited (Served i  = OnTray j)  where uninhabited Refl impossible  
Uninhabited (Served i  = Waiting j) where uninhabited Refl impossible  
Uninhabited (Served i  = At j)      where uninhabited Refl impossible  
Uninhabited (OnTray i  = Served j)  where uninhabited Refl impossible
Uninhabited (OnTray i  = Waiting j) where uninhabited Refl impossible  
Uninhabited (OnTray i  = At j)      where uninhabited Refl impossible  
Uninhabited (Waiting i = Served j)  where uninhabited Refl impossible
Uninhabited (Waiting i = OnTray j)  where uninhabited Refl impossible  
Uninhabited (Waiting i = At j)      where uninhabited Refl impossible  
Uninhabited (At i      = Served j)  where uninhabited Refl impossible
Uninhabited (At i      = OnTray j)  where uninhabited Refl impossible  
Uninhabited (At i      = Waiting j) where uninhabited Refl impossible  

public export
DecEq Predicate where
  decEq (Served i) (Served j) = case decEq i j of
    Yes Refl => Yes Refl
    No contra => No $ notSameServed contra
  decEq (OnTray i) (OnTray j) = case decEq i j of
    Yes Refl => Yes Refl
    No contra => No $ notSameOnTray contra
  decEq (Waiting i) (Waiting j) = case decEq i j of
    Yes Refl => Yes Refl
    No contra => No $ notSameWaiting contra
  decEq (At i) (At j) = case decEq i j of
    Yes Refl => Yes Refl
    No contra => No $ notSameAt contra
  decEq (Served _)  (OnTray _)  = No absurd
  decEq (Served _)  (Waiting _) = No absurd
  decEq (Served _)  (At _)      = No absurd
  decEq (OnTray _)  (Served _)  = No absurd
  decEq (OnTray _)  (Waiting _) = No absurd
  decEq (OnTray _)  (At _)      = No absurd
  decEq (Waiting _) (Served _)  = No absurd
  decEq (Waiting _) (OnTray _)  = No absurd
  decEq (Waiting _) (At _)      = No absurd
  decEq (At _)      (Served _)  = No absurd
  decEq (At _)      (OnTray _)  = No absurd
  decEq (At _)      (Waiting _) = No absurd
