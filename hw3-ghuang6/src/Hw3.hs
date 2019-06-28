--------------------------
-- | Geoff Huang      | --
-- | ghuang6@ucsc.edu | --
--------------------------

{- | CMPS 112: All about fold.

     For this assignment, you may use the following library functions:

     length
     append (++)
     map
     foldl'
     foldr
     unzip
     zip
     reverse

  Use www.haskell.org/hoogle to learn more about the above.

  Do not change the skeleton code! The point of this assignment
  is to figure out how the functions can be written this way
  (using fold). You may only replace the `error "TBD:..."` terms.

-}

module Hw3 where

import Prelude hiding (replicate, sum)
import Data.List (foldl')

foldLeft :: (a -> b -> a) -> a -> [b] -> a
foldLeft = foldl'

--------------------------------------------------------------------------------
-- | sqSum [x1, ... , xn] should return (x1^2 + ... + xn^2)
--
-- >>> sqSum []
-- 0
--
-- >>> sqSum [1,2,3,4]
-- 30
--
-- >>> sqSum [(-1), (-2), (-3), (-4)]
-- 30

sqSum :: [Int] -> Int
sqSum xs = foldLeft f base xs
  where
   f a x = a + x^2
   base  = 0

--------------------------------------------------------------------------------
-- | `pipe [f1,...,fn] x` should return `f1(f2(...(fn x)))`
--
-- >>> pipe [] 3
-- 3
--
-- >>> pipe [(\x -> x+x), (\x -> x + 3)] 3
-- 12
--
-- >>> pipe [(\x -> x * 4), (\x -> x + x)] 3
-- 24

pipe :: [(a -> a)] -> (a -> a)
pipe fs   = foldLeft f base fs
  where
    f a x = a . x   -- f = (.)
    base  = \x -> x -- base = id

-- note: pipe is essentially the built in Haskell function "compose", but without reversing the list of functions
-- pipe fs = foldLeft (.) id fs
-- compose fs = foldLeft (flip (.)) id fs

-- note: for students confused about the type signature, pipe takes in a list of functions, and returns a FUNCTION
-- you could also define pipe like below, but it is literally the same thing:
-- pipe fs v = (foldLeft (.) id fs) v  
-- pipe fs v = foldLeft (.) id fs $ v 

--------------------------------------------------------------------------------
-- | `sepConcat sep [s1,...,sn]` returns `s1 ++ sep ++ s2 ++ ... ++ sep ++ sn`
--
-- >>> sepConcat "---" []
-- ""
--
-- >>> sepConcat ", " ["foo", "bar", "baz"]
-- "foo, bar, baz"
--
-- >>> sepConcat "#" ["a","b","c","d","e"]
-- "a#b#c#d#e"

sepConcat :: String -> [String] -> String
sepConcat sep []     = ""
sepConcat sep (x:xs) = foldLeft f base l
  where
    f a x            = a ++ sep ++ x    
    base             = x
    l                = xs

-- Alternate way to write sepConcat
-- sepConcat :: String -> [String] -> String
-- sepConcat sep l = foldLeft f base l
--   where
--     f a x            = if a == "" then x else a ++ sep ++ x    
--     base             = "" 

intString :: Int -> String
intString = show

--------------------------------------------------------------------------------
-- | `stringOfList pp [x1,...,xn]` uses the element-wise printer `pp` to
--   convert the element-list into a string:
--
-- >>> stringOfList intString [1, 2, 3, 4, 5, 6]
-- "[1, 2, 3, 4, 5, 6]"
--
-- >>> stringOfList (\x -> x) ["foo"]
-- "[foo]"
--
-- >>> stringOfList (stringOfList show) [[1, 2, 3], [4, 5], [6], []]
-- "[[1, 2, 3], [4, 5], [6], []]"

stringOfList :: (a -> String) -> [a] -> String
stringOfList f xs = "[" ++ sepConcat ", " (map f xs) ++ "]"

--------------------------------------------------------------------------------
-- | `clone x n` returns a `[x,x,...,x]` containing `n` copies of `x`
--
-- >>> clone 3 5
-- [3,3,3,3,3]
--
-- >>> clone "foo" 2
-- ["foo", "foo"]

clone :: a -> Int -> [a]
clone x n
  | n <= 0      = []
  | otherwise   = x:(clone x (n-1))

type BigInt = [Int]

--------------------------------------------------------------------------------
-- | `padZero l1 l2` returns a pair (l1', l2') which are just the input lists,
--   padded with extra `0` on the left such that the lengths of `l1'` and `l2'`
--   are equal.
--
-- >>> padZero [9,9] [1,0,0,2]
-- [0,0,9,9] [1,0,0,2]
--
-- >>> padZero [1,0,0,2] [9,9]
-- [1,0,0,2] [0,0,9,9]

-- my first working attempt:
-- padZero :: BigInt -> BigInt -> (BigInt, BigInt)
-- padZero l1 l2
--   | length l1 < length l2   = (clone 0 (length l2 - length l1) ++ l1, l2)
--   | otherwise               = (l1, clone 0 (length l1 - length l2) ++ l2)

-- minor optimization (only compute length2 - length 1 once)
padZero :: BigInt -> BigInt -> (BigInt, BigInt)
padZero l1 l2
  | difference > 0 = (clone 0 difference ++ l1, l2)
  | otherwise      = (l1, clone 0 (-difference) ++ l2)
  where difference = length l2 - length l1

-- this looks cleaner but I'm not sure if we can use the abs function
-- padZero :: BigInt -> BigInt -> (BigInt, BigInt)
-- padZero l1 l2
--   | length l1 < length l2   = (clone 0 difference ++ l1, l2)
--   | otherwise               = (l1, clone 0 difference ++ l2)
--   where difference = abs (length l2 - length l1)

--------------------------------------------------------------------------------
-- | `removeZero ds` strips out all leading `0` from the left-side of `ds`.
--
-- >>> removeZero [0,0,0,1,0,0,2]
-- [1,0,0,2]
--
-- >>> removeZero [9,9]
-- [9,9]
--
-- >>> removeZero [0,0,0,0]
-- []

removeZero :: BigInt -> BigInt
removeZero [] = []
removeZero (d:ds)
  | d == 0    = removeZero ds
  | otherwise = (d:ds)

--------------------------------------------------------------------------------
-- | `bigAdd n1 n2` returns the `BigInt` representing the sum of `n1` and `n2`.
--
-- >>> bigAdd [9, 9] [1, 0, 0, 2]
-- [1, 1, 0, 1]
--
-- >>> bigAdd [9, 9, 9, 9] [9, 9, 9]
-- [1, 0, 9, 9, 8]

bigAdd :: BigInt -> BigInt -> BigInt
bigAdd l1 l2     = removeZero res
  where
    (l1', l2')   = padZero l1 l2
    res          = foldLeft f base args
    f (a:as) (d1, d2) = d:m:as 
      where
        (d, m) = (a+d1+d2) `divMod` 10
    base         = [0]
    args         = reverse (zip l1' l2')

-- note: one line code for f, but I think it's less readable
-- f (a:as) (d1, d2) = let (d, m) = (a+d1+d2) `divMod` 10 in d:m:as     

-- note: my helper function f doesn't need to have a case for when the accumulator
-- is [], because the base is [0]; it will never be passed in an empty list

-- note: there are many other "creative" ways to store the carry bit that I have seen

--------------------------------------------------------------------------------
-- | `mulByDigit i n` returns the result of multiplying
--   the digit `i` (between 0..9) with `BigInt` `n`.
--
-- >>> mulByDigit 9 [9,9,9,9]
-- [8,9,9,9,1]

mulByDigit :: Int -> BigInt -> BigInt
mulByDigit i n = foldLeft bigAdd [0] (clone n i)

-- here is another way to do it (bad runtime and space complexity again):
-- mulByDigit :: Int -> BigInt -> BigInt
-- mulByDigit i n = pipe (clone (bigAdd n) i) [0]

-- below is a way more time and space efficient way to do mulByDigit:
-- mulByDigit :: Int -> BigInt -> BigInt
-- mulByDigit i n = removeZero (foldLeft f [0] (reverse n))
--   where
--     f (a:as) x = d:m:as 
--       where
--         (d, m) = (a+i*x) `divMod` 10

--------------------------------------------------------------------------------
-- | `bigMul n1 n2` returns the `BigInt` representing the product of `n1` and `n2`.
--
-- >>> bigMul [9,9,9,9] [9,9,9,9]
-- [9,9,9,8,0,0,0,1]
--
-- >>> bigMul [9,9,9,9,9] [9,9,9,9,9]
-- [9,9,9,9,8,0,0,0,0,1]

-- here is the "obvious" way to do bigMul that follows the elementary school way to do multiplication
-- the first part of the pair stores the number of zeroes to add to the "line"
-- bigMul :: BigInt -> BigInt -> BigInt
-- bigMul l1 l2   = res
--   where
--     (_, res)   = foldLeft f base args
--     f (n, a) x = (n + 1, bigAdd a ((mulByDigit x l1) ++ clone 0 n))
--     base       = (0, [])
--     args       = reverse l2

-- here is a "better" way to do bigMul where you don't need to store the number of zeroes to append to each line
-- we take advantage of the fact that addition is commutative and add the lines in reverse order 
-- while appending the proper number of zeroes along the way
bigMul :: BigInt -> BigInt -> BigInt
bigMul l1 l2 = res
  where
    res      = foldLeft f base args
    f a x    = bigAdd (a ++ [0]) (mulByDigit x l1)
    base     = []
    args     = l2
