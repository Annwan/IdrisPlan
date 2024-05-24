module Utils

import Decidable.Equality
import Decidable.Decidable
import Data.Maybe

export decPair : Dec a -> Dec b -> Dec (a, b)
decPair (Yes a) (Yes b) = Yes (a, b)
decPair (No contra) _ = No $ \(a, _) => contra a
decPair _ (No contra) = No $ \(_, b) => contra b

export decEither : Dec a -> Dec b -> Dec (Either a b)
decEither (Yes a) _ = Yes (Left a)
decEither _ (Yes b) = Yes (Right b)
decEither (No contra_a) (No contra_b) = No $ \e =>
  case e of
    Left a => contra_a a
    Right b => contra_b b

export eitherCommut : Either a b -> Either b a
eitherCommut (Left a) = Right a
eitherCommut (Right b) = Left b 

export pairCommut : (a, b) -> (b, a)
pairCommut (a, b) = (b, a)

export eitherCommut_roundtrip : (x: Either a b) -> x = (eitherCommut (eitherCommut x))
eitherCommut_roundtrip (Left x) = Refl
eitherCommut_roundtrip (Right x) = Refl

export pairCommut_roundtrip : (x : (a, b)) -> x = pairCommut (pairCommut x)
pairCommut_roundtrip (a, b) = Refl

export filterDec : (a -> Dec x) -> List a -> List a
filterDec _ [] = []
filterDec d (x :: xs) = case d x of
  Yes _ => x :: filterDec d xs
  No _ => filterDec d xs

export deleteDec : DecEq a => a -> List a -> List a
deleteDec a [] = []
deleteDec a (x :: xs) = case decEq a x of
    Yes _ => deleteDec a xs
    No _ => x :: deleteDec a xs

||| Handwave a reason for impossibilty, if it turns out to somehow happen crash
||| the program
export
handwave_impossibility : (reason : String) -> a
handwave_impossibility r = assert_total $ idris_crash r

export
||| Abort the program due to malformed or nonsensical input to a function
abort : (reason : String) -> a
abort r = assert_total $ idris_crash r
