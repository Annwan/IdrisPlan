module Transl.PDDL

import Data.Vect
import Text.Parser.Core

%default total



public export
data Tree : (a : Type) -> Type where
  Node : a -> List (Tree a) -> Tree a

public export
data Predicate : Type where
  MkPredicate : (name : String) -> (args : List Type) -> Predicate

public export
record Variable where
  constructor MkVar
  name: String
  type: String

public export
data Action : Type where
  MkAction : (name : String)
           -> (args: List Variable)
           -> (precond: List (Predicate, List Variable))
           -> (add: List (Predicate, List Variable))
           -> (del: List (Predicate, List Variable))
           -> Action

public export
data Constant : Type where
  MkConstant : (name : String) -> (Type : String) -> Constant

public export
record Domain where
  constructor MkDomain
  type_hierarchy : Tree String
  constants : List Constant  
  predicates : List Predicate
  actions: List Action

data Token : Type where
  TOParen : Token
  TCParen : Token
  TVar : (name : String) -> Token -- ?var
  TId: (name : String) -> Token -- other identifiers
  TKeyword: (name : String) -> Token -- :keyword

data NExp : Type where
  NList : List NExp -> NExp
  NVar : String -> NExp
  NId : String -> NExp
  NKeyword : String -> NExp


