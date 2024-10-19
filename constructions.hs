----------------------------------------------------------------------------
--Kripke model
----------------------------------------------------------------------------
--kripke frame represented by adjacency list
-- -> for example turnstile state machine
          __  _______<_______  __
         /  \/               \/  \  
        v   1                2    v 
         \__/\_______>_______/\__/

frame = [(1, [1,2]),(2, [2,1])]

--labeling function
labeling node 
  | node == 1 = "locked"
  | node == 2 = "unlocked"
----------------------------------------------------------------------------
--Object of first-order types
----------------------------------------------------------------------------
myfind predicate [] = (3, [4,5])
myfind predicate (x:xs) 
  | predicate x = x
  | otherwise = myfind predicate xs 

-- possible worlds implementation
worlds frame initial_state = [initial_state] : next (worlds frame initial_state)
  where
  next (a:r@(_)) = (map (\n -> a ++ [n]) neigbours) ++ next r
    where
    looked_for = last a
    node = myfind (\node -> fst node == looked_for) frame
    neigbours = snd node

next :: Int -> Int
next = \t -> (+) t 1

----------------------------------------------------------------------------
--Constructions--
----------------------------------------------------------------------------
--variable
-- -> implemented by haskell variable

--trivialiaztion
triv :: a -> d -> a
triv = \x dummy -> x

--closure
-- -> parameter x of the function precedes a dummy parameter
-- -> after the function body, I need to apply the dummy parameter
-- -> every occurrence of parameter x in the function body is replaced by the function \dummy -> x
-- example: (\dummy -> \x -> (comp (triv next) (\dummy -> x)) dummy)
-- implementation
clos = \f -> \dummy -> \x -> f (\dummy -> x) dummy

--composition
comp :: (d -> a -> b) -> (d -> a) -> d -> b
comp = \c1 -> \c2 -> \dummy -> (c1 dummy) (c2 dummy)

----------------------------------------------------------------------------
--Examples
----------------------------------------------------------------------------
--(comp (\dummy -> \x -> (comp (triv next) x) dummy) (triv 1))
--(\dummy -> \x -> (comp (triv next) x)) True (triv 1) True
--(clos (\x -> (comp (triv next) x))) True