{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeFamilies, TypeOperators, FunctionalDependencies #-}


module Grammar where

import Data.Tree
import Control.Monad

-- #############################################
-- GRAMMAR
-- #############################################
-- define the types, the rules of composition

-- BASIC TYPES

newtype E = E {ind :: String} deriving (Eq)
newtype D = D {deg :: String} deriving (Eq)
type T = Tree String

-- T-ENDING TYPES

class TEnding a where
    apply :: (String -> String) -> a -> a
    con :: a -> a -> a

instance TEnding T where
    apply = id
    con f g = Node { rootLabel = "and", subForest = [f, g] }

instance (TEnding a) => TEnding (b -> a)  where
    apply f = (apply f) .
    con f g  x = (f x) `con` (g x)



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

(<|>) :: (TEnding a, Eq b) => b -> a -> (b -> a)
binder <|> sister = \x -> apply (replace binder x) sister
                    where replace s1 s2 x = 
                            | s1 == x = s2
                            | Otherwise = x
