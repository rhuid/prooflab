-- LambdaCalculus.hs
module LambdaCalculus where

-- Import necessary modules
import Data.List (elemIndex)    -- For finding variable indices
import Data.Maybe (fromMaybe)   -- For handling Maybe results safely

-- ======================
-- 1. Data Type Definition
-- ======================

-- Define the lambda calculus term structure
data Term
  = Var String    -- Variable (e.g., "x")
  | Lam String Term  -- Abstraction (e.g., λx.M)
  | App Term Term    -- Application (e.g., M N)
  deriving (Eq)      -- Allow equality comparison

-- Show instance for pretty printing
instance Show Term where
  show (Var x) = x
  show (Lam x t) = "λ" ++ x ++ "." ++ show t
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"

-- ======================
-- 2. Core Reduction Logic
-- ======================

-- Main reduction function (implements normal-order reduction)
reduce :: Term -> Term
reduce (App (Lam x body) arg) = substitute body x arg  -- β-reduction step
reduce (App t1 t2) = App (reduce t1) (reduce t2)      -- Reduce leftmost first
reduce (Lam x t) = Lam x (reduce t)                   -- Reduce under lambda
reduce t = t                                          -- Variables are irreducible

-- ======================
-- 3. Substitution System
-- ======================

-- Capture-avoiding substitution
substitute :: Term -> String -> Term -> Term
substitute (Var y) x arg
  | y == x    = arg              -- Replace matched variable
  | otherwise = Var y            -- Leave other variables unchanged

substitute (Lam y t) x arg
  | y == x    = Lam y t          -- Shadowed binding, don't substitute
  | y `notElem` freeVars arg = Lam y (substitute t x arg)  -- Safe to substitute
  | otherwise =                  -- Need α-conversion to avoid capture
      let z = freshName (freeVars arg ++ freeVars t)
      in Lam z (substitute (substitute t y (Var z)) x arg

substitute (App t1 t2) x arg = 
  App (substitute t1 x arg) (substitute t2 x arg)  -- Recurse into subterms

-- ======================
-- 4. Helper Functions
-- ======================

-- Get all free variables in a term
freeVars :: Term -> [String]
freeVars (Var x) = [x]
freeVars (Lam x t) = filter (/= x) (freeVars t)
freeVars (App t1 t2) = freeVars t1 ++ freeVars t2

-- Generate a fresh variable name not in the used set
freshName :: [String] -> String
freshName used = head $ filter (`notElem` used) $ map (("v" ++) . show) [0..]

-- ======================
-- 5. Example Usage
-- ======================

-- Identity function applied to itself
example1 :: Term
example1 = App (Lam "x" (Var "x")) (Lam "y" (Var "y"))

-- (λx.λy.x) (λz.z) → λy.λz.z
example2 :: Term
example2 = App (Lam "x" (Lam "y" (Var "x"))) (Lam "z" (Var "z"))

-- Test reduction
main :: IO ()
main = do
  putStrLn "Original:"
  print example1
  putStrLn "Reduced:"
  print (reduce example1)
  
  putStrLn "\nOriginal:"
  print example2
  putStrLn "Reduced:"
  print (reduce example2)
