module Main
import Petri
import Utils
import Logistics.Domain
import Logistics.Problems
import Data.Maybe

export main : IO ()
main =
  let plan = search theNet Ptest2.init Ptest2.decGoal id
  in case plan of
    Nothing => putStrLn "No plan"
    Just p => putStrLn $ concatMap (\x => show x ++ "\n") $ reverse p
