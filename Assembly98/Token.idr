module Assembly98.Token

import Decidable.Equality

public export
data Token = Assembly Int
           | Resource Int

notSameAssembly : (i = j -> Void) -> Assembly i = Assembly j -> Void
notSameAssembly contra Refl = contra Refl
notSameResource : (i = j -> Void) -> Resource i = Resource j -> Void
notSameResource contra Refl = contra Refl

Uninhabited (Assembly i = Resource j) where uninhabited Refl impossible
Uninhabited (Resource i = Assembly j) where uninhabited Refl impossible

public export
DecEq Token where
  decEq (Assembly i) (Assembly j) = case decEq i j of
    Yes Refl => Yes Refl
    No contra => No $ notSameAssembly contra
  decEq (Resource i) (Resource j) = case decEq i j of
    Yes Refl => Yes Refl
    No contra => No $ notSameResource contra
  decEq (Assembly _) (Resource _) = No absurd
  decEq (Resource _) (Assembly _) = No absurd
