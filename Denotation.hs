{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeFamilies, TypeOperators, FunctionalDependencies #-}

module Denotation where

import qualified Data.Map as Map
import Control.Applicative
import Grammar

-- ######################################################################
-- MODEL 
-- ######################################################################
-- define denotations of lexical items

-- HELPER FUNCTIONS & CLASSES

-- from a list of individuals to a predicate
listToPred :: (Eq a) => [a] -> a -> T
listToPred l = (`elem` l)

-- from a map of people and maximal values on a scale to a degree-individual predicate
mapToDeg :: (Map.Map E D) -> D -> E -> T
mapToDeg m d x = case Map.lookup x m of
                Just max -> d <= max
                Nothing -> False

-- value in empty contexts
value :: Context a -> a
value d = d (Map.empty, Map.empty)

-- domains (for quantification)

class (Eq a) => Domain a where
    domain :: [a]

inDom :: (Domain a) => a -> T
inDom = (`elem` domain)

instance Domain D where
    domain = [1 .. 200]




-- PREDICATES

--et
_ind = ["Lara", "Indiana", "Drake"]
ind :: Context (E -> T)
ind = pure $ listToPred _ind

_tomb = ["Xerxes", "Akhenaten", "Sargon"]
tomb :: Context (E -> T)
tomb = pure $ listToPred _tomb

domainE = _tomb ++ _ind

instance Domain E where
    domain = domainE

-- edt
_big :: Map.Map E D
_big = Map.fromList [("Xerxes", 50), ("Akhenaten", 40), ("Sargon", 60)]
big :: Context (D -> E -> T)
big = pure $ mapToDeg _big

-- edet
-- Here, I simplify somewhat and assume that "excavate" take the time degree as an argument directly ; that avoids having to deal with yet another indefinite

-- *TODO*


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


-- SUPERLATIVE

-- superlative takes scope below the subject ; has a covert domain restriction 
_est :: (E -> T) -> (D -> E -> T) -> (E -> T)
_est covert degP x = _exists  (inDom) (best)
                where best d = (degP d x) && _forall (\x1 -> x1/= x && (covert x1)) (\x1 -> not (degP d x1))
est :: (E -> T) -> Context ((D -> E -> T) -> (E -> T))
est = pure <$> _est

-- one useful superlative
estInds :: Context ((D -> E -> T) -> (E -> T))
estInds = est (value ind)


-- ######################################################################
-- SENTENCES 
-- ######################################################################
-- use lexical items to construct sentences


-- SENTENCE 1 
-- Sentence "Akhenaten is 30L-big"
-- Prediction : true -> "at least" semantics for degrees

-- helper denotation
akh :: Context E
akh = pure "Akhenaten" -- lift the individual to a contextual type
l30 :: Context D
l30 = pure 30 



{-LF : 

[ Akhenaten
    [ 30L big 
-}

sentence1 = akh <^>
                (
                l30  <^>
                big
                )


-- SENTENCE 2
-- Sentence "Akhenaten is the biggest tomb"
-- Prediction : false -> "Sargon" is bigger

-- helper denotation
estT = est (listToPred _tomb) -- a superlative restricted to tombs

{-LF : 

[ Akhenaten
    [ est(tombs)
        [ lambda_d
            [ d big ]
                tomb

-}

sentence2 = akh <^>
                (
                    estT
                    <^>
                    (
                        (bind_d "deg")
                        <^>
                        (
                            ((varDeg $ Index "deg") <^> big)
                            <^>
                            tomb
                        )
                    )
                )

-- SENTENCE 3
-- Sentence "Sargon is the biggest tomb"
-- Prediction : true 

-- helper denotation
sarg :: Context E
sarg = pure "Sargon"

{-LF : 

[ Sargon
    [ est(tombs)
        [ lambda_d
            [ d big ]
                tomb

-}

sentence3 = sarg <^>
                (
                    estT
                    <^>
                    (
                        (bind_d "deg")
                        <^>
                        (
                            ((varDeg $ Index "deg") <^> big)
                            <^>
                            tomb
                        )
                    )
                )
