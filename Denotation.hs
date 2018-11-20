{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeFamilies, TypeOperators, FunctionalDependencies #-}

module Denotation where

import qualified Data.Map as Map
import Control.Applicative
import Grammar
import NonFunctional

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
    domain = filter (\x -> x `mod` 10 == 0) [0 .. 200]




-- PREDICATES

--et
ind :: Context (E -> T)
ind = pure $ listToPred _ind

tomb :: Context (E -> T)
tomb = pure $ listToPred _tomb

domainE = _tomb ++ _ind

instance Domain E where
    domain = domainE

-- edt
big :: Context (D -> E -> T)
big = pure $ mapToDeg _big

-- edet
-- Here, I simplify somewhat and assume that "excavate" take the time degree as an argument directly ; that avoids having to deal with yet another indefinite

excavate :: Context (E -> D -> E -> T)
excavate = pure $ \obj time subj -> any (\(s,ob,tm2) -> (s == subj) && (obj == ob) && (time >= tm2)) _excavate


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
an :: Context ((E -> T) -> (E -> T) -> T)
an = exists


-- SUPERLATIVE

-- superlative takes scope below the subject ; has a covert domain restriction 
{-_est :: (E -> T) -> (D -> E -> T) -> (E -> T)
_est covert degP x = _exists  (inDom) (best)
                where best d = (degP d x) && _forall (\x1 -> x1/= x && (covert x1)) (\x1 -> not (degP d x1))
est :: (E -> T) -> Context ((D -> E -> T) -> (E -> T))
est = pure <$> _est-}

-- comment the above and uncomment the below for the inclusion superlative semantics:
-- -est_C p asserts all other alternatives are included in the prejacent.
_est :: (E -> T) -> (D -> E -> T) -> (E -> T)
_est covert degP x = _forall (/= x) included
                where included y = _forall (\d -> degP d y) (\d -> degP d x)
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

-- SENTENCE 4
-- Sentence "Lara excavated the biggest tomb in the shortest time"
-- Prediction : true 

{-LF : 

[ Lara
    [ est(inds)
        [ lambda_d
            [ est(inds)
                [ lambda_d'
                    [ lambda_x 
                        [.alpha
                            [.gamma a 
                                [ [d big] tomb]
                            ]
                            
                            [ lambda y
                               [.beta x
                                    [
                                        [ excavated y
                                        d'
-}

beta :: Context T
beta = (varInd $ Index "x")
            <^>
            (
                (excavate <^> (varInd $ Index "y"))
                <^>
                (varDeg $ Index "d2")
            )

gamma :: Context ((E -> T) -> T)   
gamma = an <^>
            (
                ((varDeg $ Index "d1") <^> big)
                <^>
                tomb
            )

alpha :: Context T
alpha = gamma
        <^>
            (
                (bind_e "y")
                <^>
                beta
            )
sentence4 :: Context T
sentence4 = lara
            <^>
                (
                estInds
                <^>
                    (
                    (bind_d "d1")
                    <^>
                        (
                        estInds
                        <^>
                            (
                            (bind_d "d2")
                            <^>
                                (
                                (bind_e "x")
                                <^>
                                alpha
                                )
                            )
                        )
                    )
                )
{-sentence3 = sarg <^>
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
                )-}

