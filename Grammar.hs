-- *TODO*
-- 1) Rework assignment functions to avoid duplicate codes
-- 2) Rework rules of composition to avoid lifting all non-contextual predicates

{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeFamilies, TypeOperators, FunctionalDependencies #-}

module Grammar where

import qualified Data.Map as Map
import Control.Applicative

-- #############################################
-- GRAMMAR
-- #############################################
-- define the types, the rules of composition

-- BASIC TYPES

type E = String
type D = Int
type T = Bool

data Index = Index {varName :: String} deriving (Eq, Ord)

-- ASSIGNMENT
class MultiTypeMap o g where
    at ::  g -> Index -> Maybe o
    update :: g -> Index -> o -> g

type Assignment = (Map.Map Index E, Map.Map Index D)

instance MultiTypeMap D Assignment where
    at g = (flip Map.lookup) g1 where g1 = snd g
    update (mapE, mapD) idx val = g1 where g1 = (mapE, Map.insert idx val mapD)

instance MultiTypeMap E Assignment where
    at g = (flip Map.lookup) g1 where g1 = fst g
    update (mapE, mapD) idx val = g1 where g1 = (Map.insert idx val mapE, mapD)

-- ASSIGNMENT-DEPENDENT DENOTATION

type Context a = Assignment -> a

-- if var is not in the map, we let the interpreter crash
varDeg :: Index -> (Context D)
varDeg idx g = toUndef (g `at` idx)
    where toUndef (Just s) = s
          toUndef Nothing = undefined

varInd :: Index -> (Context E)
varInd idx g = toUndef (g `at` idx)
    where toUndef (Just s) = s
          toUndef Nothing = undefined

-- CONJOINABLE TYPE

class Conjoinable a where
    con :: a -> a -> a 

instance Conjoinable T where
    con = (&&)

instance (Conjoinable a) => Conjoinable (b -> a) where
    con f g = \x -> (f x) `con` (g x)

-- RULES OF COMPOSITION

class Combine t1 t2 r | t1 t2 -> r where
    (<^>) :: t1 -> t2 -> r

-- a) regular fa
-- forward
instance Combine (a->b) a b where
    f <^> x = f x

-- backward
instance Combine a (a->b) b where
    x <^> f = f x

-- A) Functional Application
-- forward
instance Combine (Context (a->b)) (Context a) (Context b) where
    f <^> x = f <*> x

-- backward
instance Combine (Context a) (Context (a->b)) (Context b) where
    x <^> f = f <*> x

-- B) Predicate Modification
instance (Conjoinable a) => Combine a a a where
    (<^>) =  con

-- C) Abstraction
-- forward over degree and individuals
instance Combine (Index, E) (Context a) (Context (E -> a)) where
    ((idx,_) <^> meaning) g x = meaning (update g idx x)  

instance Combine (Index, D) (Context a) (Context (D -> a)) where
    ((idx,_) <^> meaning) g x = meaning (update g idx x)  

--backward
instance Combine (Context a) (Index, E) (Context (E -> a)) where
    (meaning <^> (idx,_)) g x = meaning (update g idx x)  

instance Combine (Context a) (Index, D) (Context (D -> a)) where
    (meaning <^> (idx,_)) g x = meaning (update g idx x)  

-- To make abstraction easier, we define a couple of functions:

bind_e :: String -> (Index, E)
bind_e s = (Index s, "")

bind_d :: String -> (Index, D)
bind_d s = (Index s, 0)
