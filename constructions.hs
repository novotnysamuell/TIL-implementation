----------------------------------------------------------------------------
--Object of first-order types
----------------------------------------------------------------------------
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