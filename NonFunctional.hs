module NonFunctional where

import qualified Data.Map as Map
import Grammar

_big :: Map.Map E D
_big = Map.fromList [("Xerxes", 50), ("Akhenaten", 40), ("Sargon", 60)]

_ind = ["Lara", "Indiana", "Drake"]

_tomb = ["Xerxes", "Akhenaten", "Sargon"]

_excavate :: [(E, E, D)]
_excavate = [ ("Lara", "Sargon", 170), ("Lara", "Xerxes", 140), ("Indiana", "Xerxes", 160), ("Drake", "Xerxes", 190)]


-- helper denotation
akh :: Context E
akh = pure "Akhenaten" -- lift the individual to a contextual type
l30 :: Context D
l30 = pure 30 
sarg :: Context E
sarg = pure "Sargon"
lara :: Context E
lara = pure "Lara"
