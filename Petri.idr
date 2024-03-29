module Petri

import Decidable.Decidable
import Data.Maybe

import Utils

namespace Search

  public export
  record Transition mark where
    constructor MkTransition
    name : String
    action : mark -> List mark
  
  public export
  record Net mark where
    constructor MkNet
    trans : List (Transition mark)

  export
  select : List a -> List (a, List a)
  select Nil = Nil
  select (x :: xs) = (x, xs) :: [(y, (x :: ys)) | (y, ys) <- select xs]

  export
  enabled : Net m -> m -> List (String, m)
  enabled net marking =
    [ (transName, nextMarking)
    | (transName, ms) <- [ (name t, action t marking) 
                         | t <- trans net
                         ]
    , nextMarking <- ms
    ]

namespace Run

  public export
  record Transition mark token where
    constructor MkTransition
    name : String
    action : mark -> List token -> Maybe mark

  public export Plan: (mark: Type) -> (token: Type) -> Type
  Plan mk t = List (Transition mk t, List t)

  public export
  run : Plan mark token -> mark -> Maybe mark
  run l m = foldlM (\mk => \(t, a) => t.action mk a) m l

  public export decIsPlanValid : (p: Plan mark token) -> (i: mark)
                               -> Dec (IsJust (Run.run p i))
  decIsPlanValid p i = isItJust $ run p i

  public export decIsPlanCorrect : (p: Plan mark token) -> (i: mark) 
                                 -> {auto valid: IsJust (Run.run p i)} 
                                 -> {goal: mark -> Type}
                                 -> ((m: mark) -> Dec (goal m))
                                 -> Dec (goal $ fromJust $ Run.run p i)
  decIsPlanCorrect p i g = g $ fromJust $ run p i

