module Main
import Petri
import Utils
import Logistics.Domain
import Logistics.Problems
import Data.Maybe
import Heuristics
import Transl.SExp

export main : IO ()
main = do
  print (SExpList [])
  print (SExpList [SExpId $ MkId "domain", SExpId $ MkId "logistics"])

export main' : IO ()
main' =
  let
    plan = search theNet Ptest.decGoal (not_ff theNet Ptest.decGoal) Ptest.init
  in case plan of
    Nothing => putStrLn "No plan"
    Just p => putStrLn $ concatMap (\x => show x ++ "\n") $ reverse p
