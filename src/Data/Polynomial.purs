module Data.Polynomial
  ( Polynomial
  , fromCoefficients
  , coefficients
  , pretty
  ) where

import Prelude
import Data.Array as Array
import Data.String as String
import Data.Foldable (foldr, sum)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (class Newtype, unwrap)
import Data.String (Pattern(..))
import Data.Tuple (Tuple(..))
import Data.Unfoldable (unfoldr)
import Partial.Unsafe (unsafePartial)

-- Invariant: There are no trailing zeroes in a Polynomial. This ensures that
-- the degree can be accurately computed.

-- | Finite-degree polynomials, with coefficients given by the type argument.
-- | So for example, a `Polynomial Int` is a polynomial with integer
-- | coefficients.
-- |
-- | The representation is an array, where the
-- | element at the index n is the coefficient of x^n. So e.g. x^2 + 1 is
-- | represented as `Polynomial [1, 0, 1]` and x^2 + 3x + 2 is represented as
-- | `Polynomial [2, 3, 1]`.
newtype Polynomial a = Polynomial (Array a)

derive newtype instance functorPolynomial :: Functor Polynomial
derive newtype instance eqPolynomial :: Eq a => Eq (Polynomial a)
-- derive instance genericPolynomial :: Generic a => Generic (Polynomial a) _

-- Drop trailing zeroes.
normalise :: forall a. (Eq a, Semiring a) => Array a -> Array a
normalise xs =
  Array.reverse xs
  # Array.dropWhile (_ == zero)
  # Array.reverse

fromCoefficients :: forall a. (Eq a, Semiring a) => Array a -> Polynomial a
fromCoefficients = Polynomial <<< normalise

coefficients :: forall a. Polynomial a -> Array a
coefficients (Polynomial xs) = xs

-- | Create a polynomial with a single (given) term and no dependence in x:
-- | that is, a constant polynomial; one of degree 0.
constant :: forall a. (Eq a, Semiring a) => a -> Polynomial a
constant = fromCoefficients <<< pure

instance semiringPolynomial :: (Eq a, Semiring a) => Semiring (Polynomial a) where
  one =
    Polynomial [one]
  add (Polynomial xs) (Polynomial ys) =
    Polynomial (normalise (preservingZipWith (+) zero xs ys))
  zero =
    Polynomial []
  mul (Polynomial xs) (Polynomial ys) =
    Polynomial (normalise (foldr (preservingZipWith (+) zero) [] zs))
    where
      zs = Array.mapWithIndex (\i a -> map (_ * a) (shiftBy i zero ys)) xs

instance ringPolynomial :: (Eq a, Ring a) => Ring (Polynomial a) where
  sub (Polynomial xs) (Polynomial ys) =
    Polynomial (normalise (preservingZipWith (-) zero xs ys))

instance commutativeRingPolynomial :: (Eq a, CommutativeRing a) => CommutativeRing (Polynomial a)

instance euclideanRingPolynomial :: (Eq a, EuclideanRing a) => EuclideanRing (Polynomial a) where
  degree = polynomialDegree
  div n d = (polynomialDivMod n d).div
  mod n d = (polynomialDivMod n d).mod

polynomialDegree :: forall a. Polynomial a -> Int
polynomialDegree = coefficients >>> Array.length >>> (_ - 1)

-- See https://en.wikipedia.org/wiki/Polynomial_long_division.
polynomialDivMod :: forall a.
  (Eq a, EuclideanRing a) =>
  Polynomial a ->
  Polynomial a ->
  { div :: Polynomial a, mod :: Polynomial a }
polynomialDivMod n d = go zero n
  where
    -- Get the leading term of a nonzero polynomial
    lead = unsafePartial (fromJust <<< Array.last <<< coefficients)
    go q r =
      if r == zero || polynomialDegree r < polynomialDegree d
        then
          { div: q, mod: r }
        else
          let
            t = lead r / lead d
          in
            go (q + constant t) (r - (constant t * d))

-- | Insert the given number of copies of the given value at the start of an
-- | array.
shiftBy :: forall a. Int -> a -> Array a -> Array a
shiftBy n x xs = Array.replicate n x <> xs

-- | A version of zipWith which uses a default value in cases where the arrays
-- | have different lengths to continue zipping elements with instead of
-- | discarding extra elements from the longer array.
preservingZipWith :: forall a. (a -> a -> a) -> a -> Array a -> Array a -> Array a
preservingZipWith f def xs ys = unfoldr go 0
  where
    go i =
      case Array.index xs i, Array.index ys i of
        Just x, Just y  -> Just (Tuple (f x y) (i+1))
        Just x, Nothing -> Just (Tuple (f x def) (i+1))
        Nothing, Just y -> Just (Tuple (f def y) (i+1))
        _, _ -> Nothing

pretty :: forall a. (Show a, Semiring a, Eq a) => Polynomial a -> String
pretty p@(Polynomial xs) =
  let
    deg = Array.length xs - 1
    xPow =
      case _ of
        0 -> ""
        1 -> "x"
        i -> "x^" <> show i
    term i coeff
      | coeff == zero = Nothing
      | coeff == one = Just $ if i == 0 then show (one :: a) else (xPow i)
      | otherwise = Just (parenthesise (show coeff) <> xPow i)
  in
    Array.mapWithIndex term xs
    # Array.catMaybes
    # String.joinWith " + "

parenthesise :: String -> String
parenthesise str =
  if String.contains (Pattern " ") str
    then "(" <> str <> ")"
    else str
