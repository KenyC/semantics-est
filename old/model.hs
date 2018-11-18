{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeFamilies, TypeOperators #-}

import qualified Data.Tree as Internal
import qualified Data.Map as Map
import Control.Applicative

-- BASIC TYPES

type E = String
type D = Int
type T = Bool

-- backwards functional applications
(|->) :: (Applicative f) => f (a -> b) -> f a -> f b
f |-> x = f <*> x

(<-|) :: (Applicative f) => (f a) -> f (a -> b) -> f b
(<-|) = flip (|->)

-- defining domains for types

class (Eq a) => Domain a where
    domain :: [a]

inDom :: (Domain a) => a -> T
inDom = (`elem` domain)

-- Predicate Modification for all conjoinable types

class Conjoinable a where
    con :: a -> a -> a 

instance Conjoinable T where
    con = (&&)

instance (Conjoinable a) => Conjoinable (b -> a) where
    con f g = \x -> (f x) `con` (g x)
 
type Assignement = Map.Map String E
type Context a = Assignement -> a

-- Lambda Abstraction

binder :: String -> (Context a) -> (Context (E -> a))
binder index argument g x = argument g1 where g1 = Map.insert index x g

variable :: String -> (Context E)
variable index g = toUndef (Map.lookup index g) 
   where toUndef (Just s) = s
         toUndef Nothing = undefined

-- HELPER FUNCTIONS

-- from a list of individuals to a predicate
listToPred :: (Eq a) => [a] -> Context (a -> T)
listToPred l = pure (`elem` l)

-- from a map of people and maximal values on a scale to a degree-individual predicate
mapToDeg :: (Map.Map E D) -> D -> E -> T
mapToDeg m d x = case Map.lookup x m of
                Just max -> d <= max
                Nothing -> False

-- value in empty contexts
value :: Context a -> a
value d = d Map.empty


-- PREDICATES



--et
_inds = ["Lara", "Indiana", "Drake"]
inds = listToPred _inds

_tombs = ["Xerxes", "Akhenaten", "Sargon"]
tombs = listToPred _tombs

domainE = _tombs ++ _inds

-- domains (for quantification)

instance Domain D where
    domain = [1 .. 200]

instance Domain E where
    domain = domainE

-- edt
_big :: Map.Map E D
_big = Map.fromList [("Xerxes", 50), ("Akhenaten", 40), ("Sargon", 60)]
big :: Context (D -> E -> T)
big = pure $ mapToDeg _big

-- edet
-- Here, I simplify somewhat and assume that "excavate" take the time degree as an argument directly ; that avoids having to deal with yet another indefinite

-- QUANTIFIER

-- these are cross-categorial quantifiers so they can be used for both degrees and individuals
exists :: (Domain a) => Context ((a -> T) -> (a -> T) -> T)
_exists f g = any (\x -> (f x) && (g x)) domain
exists = pure _exists


forall :: (Domain a) => Context ((a -> T) -> (a -> T) -> T)
_forall f g = all (\x -> not (f x) || (g x)) domain
forall = pure _forall

-- a synonym for exists for a more transparent object language
some :: (Domain a) => Context ((a -> T) -> (a -> T) -> T)
some = exists


-- SUPERLATIVES

-- superlative takes scope below the subject ; has a covert domain restriction 
_est :: (E -> T) -> (D -> E -> T) -> (E -> T)
_est covert degP x = _exists  (inDom) (best)
                where best d = (degP d x) && _forall (\x1 -> x1/= x && (covert x1)) (\x1 -> not (degP d x1))
est :: (E -> T) -> Context ((D -> E -> T) -> (E -> T))
est = pure <$> _est

-- one useful superlative
estInds :: Context ((D -> E -> T) -> (E -> T))
estInds = est (value inds)



-- Sentence "Akhenaten is the biggest tomb"
degree = variable "d"
lambda_d = binder "d"

{-LF : 

[ Akhenaten
    [ est(tombs)
        [ lambda_d
            [ d big ]
                tomb

-}
{-sentence = "Akhenaten" <-| (estInds |-> (lambda_d $ (degree <-| big) `con` tombs))-}
sentence = (degree <-| big) `con` tombs
