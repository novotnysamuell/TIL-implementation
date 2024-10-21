import Data.List
----------------------------------------------------------------------------
--Kripke model
----------------------------------------------------------------------------
--kripke frame represented by adjacency list
-- -> for example turnstile state machine
--        __  _______<_______  __
--       /  \/               \/  \  
--      v   1                2    v 
--       \__/\_______>_______/\__/

frame = [(1, [1,2]),(2, [2,1])]
initial_state = 1

--labeling functions
-- ->labeling of nodes
labeling_nodes node 
  | node == 1 = ["locked"]
  | node == 2 = ["unlocked"]

--labeling of edges
labeling_edges 1 1 = ["push"]
labeling_edges 1 2 = ["insertCoin"]
labeling_edges 2 2 = ["insertCoin"]
labeling_edges 2 1 = ["push"]
----------------------------------------------------------------------------
--Object of first-order types
----------------------------------------------------------------------------
--object base B_o
-- ->time implementation
time_moments = 0 : next time_moments
  where
  next (a:r@(_)) = (a+1) : next r

-- ->possible worlds implementation
possible_worlds = possible_worlds_from_frame frame initial_state
possible_worlds_from_frame frame initial_state = [initial_state] : next (possible_worlds_from_frame frame initial_state)
  where
  next (a:r@(_)) = (map (\n -> a ++ [n]) neigbours) ++ next r
    where
    looked_for = last a
    node = myfind (\node -> fst node == looked_for) frame
    neigbours = snd node

myfind predicate [] = (3, [4,5])
myfind predicate (x:xs) 
  | predicate x = x
  | otherwise = myfind predicate xs 


--functional object over the object base B_o  
w_moment = \w -> \t -> w !! t

-- ->next function returning next time moment
next :: Int -> Int
next = \t -> (+) t 1

-- ->prev function returning previous time moment
prev :: Int -> Int
prev = \t -> (-) t 1

-- ->implies function implementation of logical connective =>
implies :: Bool -> Bool -> Bool
implies = \o1 -> \o2 -> not o1 || o2

-- ->forAll function implementation of logical universal quantifier 
forAll :: (a -> Bool) -> [a] -> Bool -> Bool
forAll f domain False = False -- initial value for aggregation True
forAll f [] aggregation = aggregation
forAll f (x:xs) aggregation = forAll f xs ((&&) aggregation (f x))

forAll_t :: (Int -> Bool) -> Bool
forAll_t = \f -> forAll f time_moments True
--forAll_w :: ([] -> Bool) -> Bool
forAll_w = \f -> forAll f possible_worlds True

-- ->exists function implementation of logical existential quantifier 
exists :: (a -> Bool) -> [a] -> Bool -> Bool
exists f domain True = True -- initial value for aggregation False
exists f [] aggregation = aggregation
exists f (x:xs) aggregation = exists f xs ((||) aggregation (f x))

exists_t :: (Int -> Bool) -> Bool
exists_t = \f -> exists f time_moments False
--exists_w :: ([] -> Bool) -> Bool
exists_w = \f -> exists f possible_worlds False

-- ->intensional base
locked = \w -> \t -> elem "locked" (labeling_nodes (w !! t))
unlocked = \w -> \t -> elem "unlocked" (labeling_nodes (w !! t))
push = \w -> \t -> elem "push" (labeling_edges (w !! (prev t)) (w !! t))
insertCoin = \w -> \t -> elem "insertCoin" (labeling_edges (w !! (prev t)) (w !! t))
----------------------------------------------------------------------------
--Object of higher-order types
----------------------------------------------------------------------------
exists_path = (clos 
                (\p -> (clos 
                          (\w1 -> (clos 
                                    (\t -> (comp1 
                                              (triv exists_w) 
                                              (clos (\w2 -> (comp2 
                                                              (triv (&&)) 
                                                              (comp2 (triv (==)) 
                                                                (comp1 (comp1 (triv w_moment) (w1)) (t)) 
                                                                (comp1 (comp1 (triv w_moment) (w2)) (t))
                                                              ) 
                                                              (comp1 (comp1 (p) (w2)) (t))
                                                            )
                                                    )
                                              )
                                            ) 
                                    )
                                  )
                          )
                        )
                )
              )

forall_path = (clos 
                (\p -> (clos 
                          (\w1 -> (clos 
                                    (\t -> (comp1 
                                              (triv forAll_w) 
                                              (clos (\w2 -> (comp2 
                                                              (triv implies) 
                                                              (comp2 (triv (==)) 
                                                                (comp1 (comp1 (triv w_moment) (w1)) (t)) 
                                                                (comp1 (comp1 (triv w_moment) (w2)) (t))
                                                              ) 
                                                              (comp1 (comp1 (p) (w2)) (t))
                                                            )
                                                    )
                                              )
                                            ) 
                                    )
                                  )
                          )
                        )
                )
              )

next_time = (clos 
              (\p -> (clos 
                        (\w -> (clos
                                  (\t -> (comp1
                                            (comp1 (p) (w))
                                            (comp1 (triv next) (t))
                                         )
                                  )
                               )
                        )
                     )
              )
            )

future = (clos 
            (\p -> (clos 
                      (\w -> (clos 
                                (\t1 -> (comp1 
                                          (triv exists_t) 
                                          (clos (\t2 -> (comp2 
                                                          (triv (&&)) 
                                                          (comp2 (triv (<=)) (t1) (t2)) 
                                                          (comp1 (comp1 (p) (w)) (t2))
                                                        )
                                                )
                                          )
                                        ) 
                                )
                              )
                      )
                    )
            )
         )

globally = (clos 
              (\p -> (clos 
                        (\w -> (clos 
                                  (\t1 -> (comp1 
                                            (triv forAll_t) 
                                            (clos (\t2 -> (comp2 
                                                            (triv implies) 
                                                            (comp2 (triv (<=)) (t1) (t2)) 
                                                            (comp1 (comp1 (p) (w)) (t2))
                                                          )
                                                  )
                                            )
                                          ) 
                                  )
                                )
                        )
                      )
              )
           )

until = (clos 
          (\p1 -> (clos 
                    (\p2 -> (clos 
                              (\w -> (clos 
                                        (\t1 -> (comp1 
                                                  (triv exists_t) 
                                                  (clos (\t2 -> (comp2
                                                                  (triv (&&))
                                                                  (comp2 
                                                                    (triv (&&)) 
                                                                    (comp2 (triv (<=)) (t1) (t2)) 
                                                                    (comp1 (comp1 (p2) (w)) (t2))
                                                                  )
                                                                  (comp1
                                                                    (triv forAll_t)
                                                                    (clos (\t3 -> (comp2
                                                                                    (triv implies)
                                                                                    (comp2 (triv (<)) (t3) (t2))
                                                                                    (comp1 (comp1 (p1) (w)) (t3))
                                                                                  )
                                                                          )
                                                                    )
                                                                  )
                                                                )
                                                        )
                                                  )
                                                ) 
                                        )
                                      )
                              )
                            )
                    )
                  )
          )
        )
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
comp1 :: (d -> a -> b) -> (d -> a) -> d -> b
comp1 = \c1 -> \c2 -> \dummy -> (c1 dummy) (c2 dummy)

comp2 :: (d -> a -> b -> c) -> (d -> a) -> (d -> b) -> d -> c
comp2 = \c1 -> \c2 -> \c3 -> \dummy -> (c1 dummy) (c2 dummy) (c3 dummy)

--execution
exec1 = \c -> c

--double execution
exec2 = \c -> c True 


--Examples
--(comp (\dummy -> \x -> (comp (triv next) x) dummy) (triv 1))
--(\dummy -> \x -> (comp (triv next) x)) True (triv 1) True
--(clos (\x -> (comp (triv next) x))) True
--e = (clos (\p -> (clos (\w1 -> (clos (\t -> (comp1 (triv exists_w) (clos (\w2 -> (comp2 (triv (&&)) (comp2 (triv (==)) (comp1 (comp1 (triv w_moment) (w1)) (t)) (comp1 (comp1 (triv w_moment) (w2)) (t))) (comp1 (comp1 (p) (w2)) (t))))))))))))