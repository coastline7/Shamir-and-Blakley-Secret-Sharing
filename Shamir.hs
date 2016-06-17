module Shamir where

import Data.List
import System.Random
import System.IO
import Control.Monad
import Control.Monad.Fix

takeN :: Integer -> [a] -> [a]
takeN n l = take (fromIntegral n) l

-- given set A, return set of all subsets of A having length = k
getSubsets :: Integer -> [a] -> [[a]]
getSubsets k = filterSubsets k . getSubsets'
 where 
	getSubsets' [] = [[]]
	getSubsets' (x:xs) = s ++ map (x:) s where s = getSubsets' xs

	filterSubsets :: Integer -> [[a]]-> [[a]]
	filterSubsets k [] = []
	filterSubsets k (x:xs)= if (fromIntegral (length x) == k) then (x:filterSubsets k xs) else filterSubsets k xs

-- return all prime numbers using Sieve of Eratosthenes
allPrimes :: [Integer]
allPrimes = sieve [2..]
 where
	sieve (x:xs) = x:sieve (filter ((/=0).(`mod` x)) xs)
	
-- return random prime p from 100 prime numbers (all > max (n, M))
getPrime :: Integer -> Integer -> IO Integer
getPrime n m = do 
	xs <- return $ take 100 [x | x <- allPrimes, x > max n m]
	n <- randomRIO (0, length xs - 1)
	p <- return $ xs !! n
	return $ p
	
-- given k and p, return list of k-1 numbers from finite field p
randomList :: Integer -> Integer -> IO [Integer]
randomList k p = do 
    listZp <- generate 0 (p-1)
    return $ takeN (k-1) listZp
 where 
	generate :: Random a => a -> a -> IO [a]
	generate a b = fmap (randomRs (a,b)) newStdGen

type Polynomial = [Integer] --Polynomials are represented in ascending degree order

returnPoly :: [Integer] -> Integer -> Polynomial
returnPoly xs m = m:xs

deg :: Polynomial -> Int
deg poly = (length poly) - 1

evalPoly :: Polynomial -> Integer -> Integer -> Integer
evalPoly poly x p = mod (sum [snd a * x ^ (fst a) | a <- temp]) p
  where
	temp = zip [0..] poly

-- given polynomial, points and prime p, return each secret share tuple (index and value) in a list
evalShares :: Polynomial -> [Integer] -> Integer -> [(Integer,Integer)]
evalShares poly points p = zip [1..] [evalPoly poly x p | x <- points]

-- given prime p and shares, evaluate the Lagrange polynomial 
calcLagrange :: Integer -> [(Integer, Integer)] -> Integer
calcLagrange p terms = (sum $ map g terms) `mod` p
  where
    g (c, y) = y * l c
    l i	= product [f x | (x, _) <- terms, x /= i]
      where
        f x	= (-x) * inverse (i - x) p
    inverse a = fst . eGCD a
    eGCD a b
      | b == 0	= (1, 0)
      | otherwise = (t, s - q * t)
        where
          (q, r) = divMod a b
          (s, t) = eGCD b r

test m k n k' = do 
--encrypt section
	p <- getPrime n m
	coeff <- randomList k p 
	polynomial <- return $ returnPoly coeff m 
	shares <- return $ evalShares polynomial [1..n] p
	
	putStr $ "secret = "
	print $ m
	
	putStr $ "p = "
	print $ p
	
	putStr $ "polynomial = "
	print $ polynomial
	
	putStr $ "shares = "
	print $ shares
	
	x <- decrypt k' p shares 
	return $ x 

-- decrypt section
decrypt k' p shares = do
	sharesSubset <- return $ (getSubsets k' shares)
	index <- randomRIO (0, length sharesSubset - 1)
	shares' <- return $ sharesSubset !! index
	secret <- return $ calcLagrange p shares'
	
	putStr $ "k shares = "
	print $ shares'
	
	putStr $ "secret = "
	print $ secret
	
	return $ secret 
