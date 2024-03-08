module Petri

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
