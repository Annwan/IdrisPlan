module Main
import Petri
import Utils
import Logistics.Domain
import Logistics.Problems
import Data.Maybe

export main : IO ()
main = do
  case decIsPlanValid invalid_plan init of
    Yes valid => case decIsPlanCorrect invalid_plan init decGoal of
      Yes correct => putStrLn "plan correct"
      No incorrect => putStrLn "plan incorrect"
    No invalid => putStrLn "plan invalid"

