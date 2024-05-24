module Transl.PDDL

import Data.SortedMap

import Data.Either
import Data.List
import Data.List1
import Data.String
import Data.String.Extra

import System.File.Handle
import System.File.ReadWrite
import System.File.Mode

import Text.Lexer
import Text.Parser

import Utils

data PDDLTokenKind
  = TIgnore -- comments and whitespace
  | TOpen -- '('
  | TClose -- ')'
  | TDefine -- 'define'
  | TDomain -- 'domain'
  | TName -- a plain name
  | TRequirements -- ':requirements'
  | TTName -- a :name
  | TTypes -- ':types'
  | TDash -- '-'
  | TConstants -- ':constants'
  | TPredicates -- ':predicates'#
  | TVar -- a ?name
  | TEither -- 'either'
  | TAction -- ':action'
  | TParameters -- ':parameters'
  | TPrecondition -- ':precondition'
  | TEffect -- ':effect'
  | TAnd -- 'and'
  | TNot -- 'not'

Eq PDDLTokenKind where
  TIgnore == TIgnore = True
  TOpen == TOpen = True
  TClose == TClose = True
  TDefine == TDefine = True
  TDomain == TDomain = True
  TName == TName = True
  TRequirements == TRequirements = True
  TTName == TTName = True
  TTypes == TTypes = True
  TDash == TDash = True
  TConstants == TConstants = True
  TPredicates == TPredicates = True
  TVar == TVar = True
  TEither == TEither = True
  TAction == TAction = True
  TParameters == TParameters = True
  TPrecondition == TPrecondition = True
  TEffect == TEffect = True
  TAnd == TAnd = True
  TNot == TNot = True
  _ == _ = False

PDDLToken : Type
PDDLToken = Token PDDLTokenKind

TokenKind PDDLTokenKind where
  TokType TName = String
  TokType TTName = String
  TokType TVar = String
  TokType _ = ()

  tokValue TName s = s
  tokValue TTName s = s
  tokValue TVar s = s
  tokValue TIgnore _ = ()
  tokValue TOpen _ = ()
  tokValue TClose _ = ()
  tokValue TDefine _ = ()
  tokValue TDomain _ = ()
  tokValue TRequirements _ = ()
  tokValue TTypes _ = ()
  tokValue TDash _ = ()
  tokValue TConstants _ = ()
  tokValue TPredicates _ = ()
  tokValue TEither _ = ()
  tokValue TAction _ = ()
  tokValue TParameters _ = ()
  tokValue TPrecondition _ = ()
  tokValue TEffect _ = ()
  tokValue TAnd _ = ()
  tokValue TNot _ = ()
    
ignored : WithBounds PDDLToken -> Bool
ignored (MkBounded (Tok TIgnore _) _ _) = True
ignored _ = False

name : Lexer
name = alpha <+> many (alphaNum <|> oneOf "_-")

var : Lexer
var = is '?' <+> name

tag : Lexer
tag = is ':' <+> name

comment : Lexer
comment = lineComment (exact ";")

keywords : List (String, PDDLTokenKind)
keywords =
  [ ("define", TDefine)
  , ("domain", TDomain)
  , (":requirements", TRequirements)
  , (":types", TTypes)
  , (":constants", TConstants)
  , (":predicates", TPredicates)
  , ("either", TEither)
  , (":action", TAction)
  , (":parameters", TParameters)
  , (":precondition", TPrecondition)
  , (":effect", TEffect)
  , ("and", TAnd)
  , ("not", TNot)
  ]
  
pddlTokenMap : TokenMap PDDLToken
pddlTokenMap =
  toTokenMap [(spaces, TIgnore), (comment, TIgnore)]  ++ [ (name, \s =>
                 case lookup s keywords of
                   (Just k) => Tok k s
                   Nothing => Tok TName s
       ),
       (tag, \s =>
                case lookup s keywords of
                  (Just k) => Tok k s
                  Nothing => Tok TTName s
       )
     ]
  ++ toTokenMap [ (is '(', TOpen)
                , (is ')', TClose)
                , (is '-', TDash)
                , (var, TVar)
                ]


PDDLGrammar : (state: Type) -> (rType: Type) -> Type
PDDLGrammar state = Grammar state PDDLToken True

inParens : {x: Type} -> PDDLGrammar state x -> PDDLGrammar state x
inParens {x} g = do
  match TOpen
  v <- g
  match TClose
  pure v



data TypeDef = Object | Subtype String TypeDef
Show TypeDef where
  show Object = "object"
  show (Subtype name type) = assert_total $ show type ++ ":" ++ name 
data Variable = Var String
Show Variable where show (Var s) = "?" ++ s 
Eq Variable where (Var s1) == (Var s2) = s1 == s2
Ord Variable where
  (Var s1) < (Var s2) = s1 < s2
data Term = C String | V Variable
Show Term where
  show (C c) = c
  show (V v) = show v
Eq Term where
  (C _) == (V _) = False
  (V _) == (C _) = False
  (C a) == (C b) = a == b
  (V a) == (V b) = a == b
Ord Term where
  (C _) < (V _) = True
  (V _) < (C _) = False
  (C a) < (C b) = a < b
  (V a) < (V b) = a < b 
data Effect = Add String (List Term) | Del String (List Term)
Show Effect where
  show (Add n ts) = "< + " ++ n ++ concatMap (showArg) ts ++ ">"
  show (Del n ts) = "< - " ++ n ++ concatMap (showArg) ts ++ ">"
data GD = Goal String (List Term)
Show GD where
  show (Goal n ts) = "<" ++ n ++ concatMap (showArg) ts ++ ">"
data Predicate = Pred String (List (List TypeDef))
Show Predicate where
  show (Pred n args) = "<" ++ n
                     ++ listargs
                     ++ ">"
  where
    listargs : String
    listargs = concatMap ((" "++) . concatMap ((++ ";") . show)) args  
record Action where
  constructor MkAction
  name : String
  vars : List (Variable, TypeDef)
  precond : List GD
  effect : List Effect
Show Action where
  show a = "Action " ++ a.name ++ " ("
         ++ "\n variables : " ++ show a.vars
         ++ "\n precond : " ++ show a.precond
         ++ "\n effect : " ++ show a.effect
         ++ ")"

record Domain where
  constructor MkDomain
  name : String
  reqs : List String
  types : SortedMap String TypeDef
  constants : SortedMap String TypeDef
  predicates : SortedMap String Predicate
  actions : SortedMap String Action

Show Domain where
  show d = "Domain " ++ d.name ++ " ("
         ++ "\n reqs : " ++ show d.reqs  
         ++ "\n types : " ++ show d.types
         ++ "\n constants : " ++ show d.constants
         ++ "\n predicates : " ++ show d.predicates
         ++ "\n actions : " ++ show d.actions
         ++ "\n )"

resolveTypes : (typeMap : SortedMap String TypeDef)
             -> (input : List (List t, String))
             -> List (t, TypeDef)
resolveTypes tm = concat . map (\(ns, t) => map (\n => (n, recklessLookup t tm)) ns)
where
  recklessLookup : String -> SortedMap String TypeDef -> TypeDef 
  recklessLookup a tm = case lookup a tm of
                          Just x => x
                          Nothing => abort "invalid input"
resolveTypeLists : (typeMap : SortedMap String TypeDef)
                 -> (input: List (List t, List String))
                 -> List (t, List TypeDef)
resolveTypeLists tm = concat . map h1
where
  h2 : List String -> t -> (t, List TypeDef)
  h2 ts n = (n, map (\x => case lookup x tm of {Just y => y; Nothing => abort "invalid input" }) ts)
  h1 : (List t, List String) -> List (t, List TypeDef)
  h1 (ns, ts) = map (h2 ts) ns
mutual
  domain : PDDLGrammar state Domain
  domain = inParens $ do
    match TDefine
    thename <- inParens $ do
      match TDomain
      match TName
    thereqs <- option [":strips"] require_def
    thetypes <- option [] types_def
    let
      a : List (String, String)
      a = ("object", "object") :: (concat $ map (\(sts, t) => map (\st => (st, t)) sts) thetypes)
      b : List (String, Either String TypeDef)
      b = map (\(st, t) => (st, Left t)) a
      buildTypes : List (String, Either String TypeDef) -> List (String, Either String TypeDef)
      buildTypes l =
        if all (isRight . snd) l
        then l
        else
          buildTypes $ concat$ map (
            \(st, t) => case t of
              Right _ => [(st, t)]
              Left name => case st of
                "object" => [("object", Right Object)]
                _ => case lookup name l of
                  Nothing => [ (st, Right $ Subtype st $ Subtype name Object)
                             , (name, Right $ Subtype name Object)
                             ]
                  Just (Right t) => [(st, Right $ Subtype st t)]
                  Just (Left n) => [(st, t)]
          ) l
      builtTypes : List (String, TypeDef)
      builtTypes = map (\(x, e) => case e of {Right t => (x, t); Left s => handwave_impossibility "buildTypes wouldn't have terminated with that"}) $ buildTypes b
      typ : SortedMap String TypeDef
      typ = fromList builtTypes
    theconsts <- option [] $ constants_def typ
    thepreds <- option [] $ predicates_def typ
    thestructs <- option [] $ many $ action_def typ
    pure $
      MkDomain
        thename
        thereqs
        typ
        (fromList theconsts)
        (fromList $ map (\(n, vs) => (n, Pred n $ map snd vs)) thepreds)
        (fromList $ map (\a => (a.name, a)) thestructs)

  require_def : PDDLGrammar state (List String) 
  require_def = inParens $ do
    match TRequirements
    thekeys <- some require_key
    pure $ forget thekeys
  
  require_key : PDDLGrammar state String
  require_key = match TTName
    
  types_def : PDDLGrammar state (List (List String, String))
  types_def = inParens $ do
    match TTypes
    typed_list $ match TName
    
  constants_def : SortedMap String TypeDef -> PDDLGrammar state (List (String, TypeDef))
  constants_def types = inParens $ do
    match TConstants
    thelist <- typed_list $ match TName
    pure $ resolveTypes types thelist
    
  predicates_def : SortedMap String TypeDef -> PDDLGrammar state (List (String, List (Variable, List TypeDef)))
  predicates_def types = inParens $ do
    match TPredicates
    thelist <- some $ atomic_formula_skeleton types
    pure $ forget thelist
  
  atomic_formula_skeleton : SortedMap String TypeDef -> PDDLGrammar state (String, List (Variable, List TypeDef))
  atomic_formula_skeleton types = inParens $ do
    name <- match TName
    args <- typed_varlist
    pure (name, resolveTypeLists types args)
    
  variable : PDDLGrammar state Variable
  variable = do
    tok <- match TVar
    pure $ case strM tok of
      StrNil => Var "__unnamed__"
      StrCons _ name => Var name
  
  typed_list : {t: Type}
             -> PDDLGrammar state t
             -> PDDLGrammar state (List (List t, String))
  typed_list x =
    ( do
        names <- some x
        match TDash
        thetype <- type
        rest <- option [] $ typed_list x
        pure $ (forget names, thetype) :: rest
    )
    <|> (
      do
      names <- some x
      pure [(forget names, "object")]
    )

  type : PDDLGrammar state String
  type = match TName

  typed_varlist : PDDLGrammar state (List (List Variable, List String))
  typed_varlist =
    ( do
        names <- some $ match TVar
        match TDash
        thetypes <- vartype
        rest <- option [] typed_varlist
        pure $ (map (Var) $ forget names, thetypes) :: rest
    )


  vartype : PDDLGrammar state (List String)
  vartype = ( inParens $ do
           match TEither
           names <- some $ match TName
           pure $ forget names
         ) <|> ( do
           n <- match TName
           pure [n]
         )
         
  emptyOr : {t : Type}
          -> (x: PDDLGrammar state t)
          -> PDDLGrammar state (Maybe t)
  emptyOr x =
    ( do
        v <- x
        pure $ Just v
    ) <|> ( do
      match TOpen
      match TClose
      pure Nothing
    )

  action_def : SortedMap String TypeDef -> PDDLGrammar state Action
  action_def types = inParens $ do
    match TAction
    name <- match TName
    match TParameters
    params <- inParens $ typed_list variable
    body <- action_def_body
    pure $ MkAction name (resolveTypes types params) (fst body) (snd body)
    
  action_def_body : Grammar state PDDLToken False (List GD, List Effect)
  action_def_body = do
    precond <- optional $ do
      match TPrecondition 
      emptyOr gd
    effects <- optional $ do
      match TEffect
      emptyOr effect
    let
      effects' = case effects of
        Nothing => []
        Just Nothing => []
        Just (Just x) => x
      
      precond' = case precond of
        Nothing => []
        Just Nothing => []
        Just (Just x) => map (\g => Goal (fst g) (snd g)) x
    pure (precond', effects')

  gd : PDDLGrammar state (List (String, List Term))
  gd =
    ( inParens $ do
      match TAnd
      gds <- some gd
      pure $ concat gds
    ) <|> ( do
      x <- atomic_formula term
      pure [x]
    )

  atomic_formula : {t : Type}
                 -> PDDLGrammar state t
                 -> PDDLGrammar state (String, List t)
  atomic_formula x = inParens $ do
    pred <- match TName
    args <- many x
    pure (pred, args)
    
  term : PDDLGrammar state Term
  term = ( do
      v <- variable
      pure $ V v
    ) <|> do
      n <- match TName
      pure (C n)
    
  
  effect : PDDLGrammar state (List Effect)
  effect =
    ( inParens $ do
        match TAnd
        effects <- many effect
        pure $ concat effects 
    ) <|> ( do
       e <- p_effect
       pure [e]
    )
 
  p_effect : PDDLGrammar state Effect
  p_effect =
    ( inParens $ do
      match TNot
      x <- atomic_formula term
      pure $ Del (fst x) (snd x)
    ) <|>
    ( do
        x <- atomic_formula term
        pure $ Add (fst x) (snd x)
    )

lexPDDL : String -> Maybe (List (WithBounds PDDLToken))
lexPDDL s = case lex pddlTokenMap s of
  (ts, _, _, "") => Just ts
  _ => Nothing
parsePDDL : List (WithBounds PDDLToken) -> Either String Domain
parsePDDL ts =
  case parse domain $ filter (not . ignored) ts of
    Right (l, []) => Right l
    Right e => Left "Stray Tokens at end of input"
    Left e => Left "Parsing Error"

parse : String -> Either String Domain
parse s = case lexPDDL s of {Just ts => parsePDDL ts; Nothing => Left "Lexing Error"}

partial
export 
run : String -> IO ()
run path = do
  Right file <- readFile path
  case parse file of
    Left e => putStrLn e
    Right d => printLn d 
  