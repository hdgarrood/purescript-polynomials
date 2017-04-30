module Data.Polynomial
  ( Polynomial
  , fromCoefficients
  , coefficients
  , constant
  , identity
  , compose
  , evaluate
  , innerProduct
  , antiderivative
  , pretty
  , VPolynomial(..)
  ) where

import Prelude
import Data.Newtype (class Newtype)
import Data.Array as Array
import Data.String as String
import Data.Group (class Group, class CommutativeGroup)
import Data.VectorSpace (class VectorSpace)
import Data.Foldable (foldl, foldr)
import Data.Maybe (Maybe(..), fromJust)
import Data.Monoid (class Monoid)
import Data.Int as Int
import Data.String (Pattern(..))
import Data.Tuple (Tuple(..))
import Data.Unfoldable (unfoldr)
import Partial.Unsafe (unsafePartial)
import Test.QuickCheck (class Arbitrary, arbitrary)

-- Invariant: There are no trailing zeroes in a Polynomial. This ensures that
-- the degree can be accurately computed.

-- | Finite-degree polynomials, with coefficients given by the type argument.
-- | So for example, a `Polynomial Int` is a polynomial with integer
-- | coefficients.
-- |
-- | The `Monoid` instance works by considering polynomials as functions, where
-- | `<>` corresponds to function composition and the identity polynomial
-- | `mempty` is nothing more than the identity function `P(x) = x`.
newtype Polynomial a = Polynomial (Array a)

derive newtype instance functorPolynomial :: Functor Polynomial
derive newtype instance eqPolynomial :: Eq a => Eq (Polynomial a)

-- Drop trailing zeroes.
normalise :: forall a. (Eq a, Semiring a) => Array a -> Array a
normalise = Array.reverse <<< Array.dropWhile (_ == zero) <<< Array.reverse

instance arbitraryPolynomial :: (Eq a, Semiring a, Arbitrary a) => Arbitrary (Polynomial a) where
  arbitrary = map (Polynomial <<< normalise) arbitrary

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

instance euclideanRingPolynomial :: (Eq a, Field a) => EuclideanRing (Polynomial a) where
  degree = polynomialDegree
  div x y = (polynomialDivMod x y).div
  mod x y = (polynomialDivMod x y).mod

--   (a_0 + a_1 x + a_2 x^2) . (b_0 + b_1 x + b_2 x^2)
-- =
--   a_0 + a_1 (b_0 + b_1 x + b_2 x^2) + a_2 (b_0 + b_1 x + b_2 x^2)^2
-- =
--   a_0 + a_1*b_0 + a_2*b_0^2
--   + a_1*b_1 x + a_2*(2*b_0*b_1) x
--   + a_1*b_2 x^2 + a_2*(b_1^2 + 2*b_0*b_2) x^2
--   + a_2*(2*b_1*b_2) x^3
--   + a_2*b_2^2 x^4
--
instance semigroupPolynomial :: (Eq a, Semiring a) => Semigroup (Polynomial a) where
  append = compose

instance monoidPolynomial :: (Eq a, Semiring a) => Monoid (Polynomial a) where
  mempty = identity

-- | The identity polynomial; `P(x) = x`.
identity :: forall a. Semiring a => Polynomial a
identity = Polynomial [zero, one]

-- | Compose two polynomials, by treating them as functions. Composing with
-- | `identity` yields the same polynomial.
compose :: forall a. (Eq a, Semiring a) => Polynomial a -> Polynomial a -> Polynomial a
compose (Polynomial coeffs) =
  evaluate (Polynomial (map constant coeffs))

polynomialDegree :: forall a. Polynomial a -> Int
polynomialDegree = coefficients >>> Array.length >>> (_ - 1)

-- See https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor#Euclidean_division
polynomialDivMod :: forall a.
  (Eq a, Field a) =>
  Polynomial a ->
  Polynomial a ->
  { div :: Polynomial a, mod :: Polynomial a }
polynomialDivMod a b = go zero a
  where
    -- Get the leading term of a nonzero polynomial
    lc = unsafePartial (fromJust <<< Array.last <<< coefficients)
    d = polynomialDegree b
    c = lc b
    go q r =
      let
        degreeDiff = polynomialDegree r - d
      in
        if degreeDiff < 0
          then
            { div: q, mod: r }
          else
            let
              s = Polynomial (shiftBy degreeDiff zero [lc r / c])
            in
              go (q + s) (r - (s * b))

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

-- | Evaluate a polynomial by supplying a value for x.
evaluate :: forall a. Semiring a => Polynomial a -> a -> a
evaluate (Polynomial coeffs) x =
  (foldl go { acc: zero, val: one } coeffs).acc
  where
    go { acc, val } coeff =
      let
        newVal = val * x
        term = coeff * val
      in
        { acc: acc + term, val: newVal }

pretty :: forall a. (Show a, Semiring a, Eq a) => Polynomial a -> String
pretty (Polynomial []) = show (zero :: a)
pretty (Polynomial coeffs) =
  let
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
    Array.mapWithIndex term coeffs
    # Array.catMaybes
    # String.joinWith " + "

instance showPolynomial :: (Show a, Semiring a, Eq a) => Show (Polynomial a) where
  show = pretty

parenthesise :: String -> String
parenthesise str =
  if String.contains (Pattern " ") str
    then "(" <> str <> ")"
    else str

-- | We can consider the set of polynomials with real coefficients as a real vector
-- | space. In this case, this function defines an inner product given by the
-- | integral of the product of the arguments between 0 and 1.
innerProduct :: Polynomial Number -> Polynomial Number -> Number
innerProduct p q = evaluate (antiderivative (p*q)) 1.0

-- | Gives the antiderivative of a particular polynomial having a constant
-- | term of 0. For example, an antiderivative of `2x + 1` is `x^2 + x`.
-- |
-- | ```purescript
-- | antiderivative (fromCoefficients [1.0,2.0])
-- |   == fromCoefficients [0.0,1.0,1.0]
-- | ```
antiderivative :: Polynomial Number -> Polynomial Number
antiderivative (Polynomial coeffs) =
  Polynomial ([0.0] <> Array.mapWithIndex shift coeffs)
  where
  shift i a = a / (Int.toNumber i + 1.0)

-- | A newtype wrapper of polynomials which provides a `VectorSpace` instance.
-- | We use a `newtype` because the `Polynomial` type already has a `Semigroup`
-- | instance corresponding to polynomial composition; this `newtype` instead
-- | uses addition for its `Semigroup` instance.
newtype VPolynomial a = VPolynomial (Polynomial a)

derive newtype instance eqVPolynomial :: Eq a => Eq (VPolynomial a)
derive newtype instance functorVPolynomial :: Functor VPolynomial
derive newtype instance semiringVPolynomial :: (Eq a, Semiring a) => Semiring (VPolynomial a)
derive newtype instance ringVPolynomial :: (Eq a, Ring a) => Ring (VPolynomial a)
derive newtype instance commutativeringVPolynomial :: (Eq a, CommutativeRing a) => CommutativeRing (VPolynomial a)
derive newtype instance euclideanRingVPolynomial :: (Eq a, Field a) => EuclideanRing (VPolynomial a)

derive instance newtypeVPolynomial :: Newtype (VPolynomial a) _

instance semigroupVPolynomial :: (Eq a, Semiring a) => Semigroup (VPolynomial a) where
  append = (+)

instance monoidVPolynomial :: (Eq a, Semiring a) => Monoid (VPolynomial a) where
  mempty = zero

instance groupVPolynomial :: (Eq a, Ring a) => Group (VPolynomial a) where
  ginverse = negate

instance commutativeGroupVPolynomial :: (Eq a, Ring a) => CommutativeGroup (VPolynomial a)

instance vectorSpaceVPolynomial :: (Eq a, Field a) => VectorSpace (VPolynomial a) a where
  scalarMul x p = map (_ * x) p
