module LinearDiophantine (solveLinearDiophantine) where

import Data.Function
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Vector.Unboxed (Vector)
import Data.Vector.Unboxed qualified as V

-- Breadth-first search and fold combined
bfsFold :: (s -> a -> (s, [a])) -> s -> [a] -> s
bfsFold step ini roots = go ini (Seq.fromList roots)
  where
    go = \cases
      s Seq.Empty -> s
      s (x Seq.:<| q) -> case step s x of
        (s', ys) -> go s' (q Seq.>< Seq.fromList ys)

dot :: Vector Int -> Vector Int -> Int
xs `dot` ys = V.sum $ V.zipWith (*) xs ys

leq :: Vector Int -> Vector Int -> Bool
xs `leq` ys = V.and $ V.zipWith (<=) xs ys

standardUnit :: Int -> Int -> Vector Int
standardUnit n i = V.generate n (\j -> if j == i then 1 else 0)

standardBasis :: Int -> [Vector Int]
standardBasis n = map (standardUnit n) [0 .. n - 1]

-- Solve a homogeneous linear diophantine equation
--   a1 * x1 + a2 * x2 + ... + an * xn = 0.
-- Takes the coefficients as a list and returns the basis of the solution space.
solveLinearDiophantine :: [Int] -> [[Int]]
solveLinearDiophantine as =
  bfsFold step Set.empty (standardBasis n)
    & Set.toList
    & map V.toList
  where
    as' = V.fromList as
    n = V.length as'

    step basis xs = (basis', children)
      where
        basis' =
          if as' `dot` xs == 0 && xs `Set.notMember` basis
            then Set.insert xs basis
            else basis
        children = do
          if any (`leq` xs) basis'
            then []
            else
              [ xs V.// [(k, xs V.! k + 1)]
                | k <- [0 .. n - 1],
                  (as' `dot` xs) * (as' V.! k) < 0
              ]
