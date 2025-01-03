import Data.Typeable
----------------------------------------------------------------------------
--Constructions--
----------------------------------------------------------------------------
type Tau = Integer

instance (Typeable a, Typeable b) => Show (a -> b) where
    show f = "Function: " ++ (show $ typeOf f)

data Star = Star { 
  x :: Tau
-- others variables and their respective types  
}deriving (Show)

--variable

-- -> implemented as function of type star -> alpha, defined by valuation record.

--trivialiaztion
triv :: alpha -> Star -> alpha
triv = \x -> \dummy -> x


--closure
-- -> parameter x of the function precedes a dummy parameter
-- -> after the function body, I need to apply the dummy parameter
-- -> every occurrence of parameter x in the function body is replaced by the function \dummy -> x

--clos :: (a -> Star -> b) -> Star -> a -> b
clos = \f -> \dummy -> \x -> f (\dummy -> x) dummy
--                      ⬑                 ⬏
--                      ⬑ exchange of ordinary haskell variable 
--                        in f by TIL variable (construction)
--composition
comp :: (Star -> a -> b) -> (Star -> a) -> Star -> b
comp = \c1 c2 -> \dummy -> (c1 dummy) (c2 dummy)
--             execution of c0 ⬏          ⬑ execution c1

comp2 :: (Star -> a -> b -> c) -> (Star -> a) -> (Star -> b) -> Star -> c
comp2 = \c1 c2 c3 -> \dummy -> (c1 dummy) (c2 dummy) (c3 dummy)

--execution
exec1 :: (Star -> alpha) -> Star -> alpha
exec1 = \c -> \dummy -> c dummy
--                        ⬑ execution c

--double execution
exec2 :: (Star -> Star -> alpha) -> Star -> alpha
exec2 = \c -> \dummy -> c dummy dummy 
--        first execution ⬏     ⬑ second execution


--Examples
--(\dummy -> \x -> (comp (triv next) x)) True (triv 1) True
--(clos (\x -> (comp (triv next) x))) True
-- Propagation of improperness
--(comp2 (triv (-)) (comp2 (triv (div)) (triv 2) (triv 0)) x) Star {x = 8} -extensional context
--(clos (\x -> (comp2 (triv (-)) (comp2 (triv (div)) (triv 2) (triv 0)) x))) Star {x = 8} -intensional contex
--(triv (comp2 (triv (-)) (comp2 (triv (div)) (triv 2) (triv 0)) x)) Star {x = 8} -hyperintensional context