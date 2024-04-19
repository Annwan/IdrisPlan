module Heuristics

import Petri

public export Heuristic : {mark: Type} -> {token : Type} -> Type
Heuristic = Monoid mark => Net mark token
            -> {goal : mark -> Type} -> ((x : mark) -> Dec (goal x))
            -> mark -> Nat

export plain : Heuristic
plain _ _ _ = 0

not_ff_rec : Monoid mark => Nat 
       -> Net mark token
       -> {goal : mark -> Type} -> ((x : mark) -> Dec (goal x))
       -> mark -> Nat
not_ff_rec depth net isGoal mark = case isGoal mark of
  Yes _ => depth
  No _ => not_ff_rec (depth + 1) net isGoal $ concat $ mark :: ( map snd $ enabled net mark)

export not_ff : Monoid mark => Net mark token
          -> {goal : mark -> Type} -> ((x : mark) -> Dec (goal x))
          -> mark -> Nat
not_ff net isGoal mark = not_ff_rec 0 net isGoal mark

