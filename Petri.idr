module Petri

import Decidable.Decidable
import Data.Maybe
import Data.List
import Debug.Trace

import Utils

namespace Search

  public export
  record Transition mark token where
    constructor MkTransition
    name : String
    action : mark -> List (List token, mark)
  
  public export
  record Net mark token where
    constructor MkNet
    trans : List (Transition mark token)

  export
  select : List a -> List (a, List a)
  select Nil = Nil
  select (x :: xs) = (x, xs) :: [(y, (x :: ys)) | (y, ys) <- select xs]

  export
  enabled : Net m t -> m -> List ((String, List t), m)
  enabled net marking =
    [ ((transName, args), nextMarking)
    | (transName, ms) <- [ (name t, action t marking) 
                         | t <- trans net
                         ]
    , (args, nextMarking) <- ms
    ]

  search_rec : {token : Type} -> {mark : Type}
             -> Net mark token
             -> {goal : mark -> Type} -> ((x : mark) -> Dec (goal x))
             -> (mark -> Nat)
             -> List (List (String, List token), mark, Nat)
             -> Maybe (List (String, List token))
  search_rec net isGoal h [] = Nothing
  search_rec net isGoal h ((p, m, s) :: rest) = case isGoal m of
    Yes _ => Just p
    No _ => let new = map (\v@(np, nm) => (np, nm, length np + h nm))
                    . map (\(x, nm) => ((x :: p), nm))
                    $ enabled net m
                queue = sortBy (\(_, _, v) => \(_, _, v') => compare v v') (rest ++ new)
            in search_rec net isGoal h queue
  
  export search : {token : Type} -> {mark : Type}
                -> Net mark token
                -> {goal : mark -> Type} -> ((x : mark) -> Dec (goal x))
                -> (mark -> Nat)
                -> mark -> Maybe (List (String, List token))
  search net isGoal h init = search_rec net isGoal h [([], init, 0)]
                
{-  
  search_rec : {token: Type} -> Net mark token
             -> {goal : mark -> Type} -> ((x: mark) -> Dec (goal x))
             -> ((List (String, List token), mark) -> Int) 
             -> List (List (String, List token), mark)
             -> Maybe $ List (String, List token)
  search_rec _ _ _ [] = Nothing
  search_rec n ig h ((p, m) :: xs) = case ig m of
    Yes _ => Just p
    No _ => search_rec n ig h $ ?sort $ xs ++ (reformat (p) (enabled n m))
      where
        Args : Type
        Args = List token
        reformat : List (String, Args)
                 -> List ((String, Args), mark)
                 -> List (List (String, Args), mark)
        reformat plan [] = []
        reformat plan ((p, m) :: xs) = ((p :: plan), m) :: reformat plan xs 
    
  export
  search : {token : Type} -> Net mark token
         -> mark -> {goal: mark -> Type} -> ((x: mark) -> Dec (goal x))
         -> ((List (String, List token), mark) -> String) 
            -> List (List (String, List token), mark)
         ->  Maybe $ List (String, List token)
  search n i ig h = search_rec n ig h [([], i)]
  
-}
  
namespace Run

  public export
  record Transition mark token where
    constructor MkTransition
    name : String
    action : mark -> List token -> Maybe mark

  public export Plan: (mark: Type) -> (token: Type) -> Type
  Plan mk t = List (Run.Transition mk t, List t)

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

