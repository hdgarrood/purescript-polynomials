module Test.Main where

import Prelude
import Control.Monad.Eff.Console (log)
import Data.ModularArithmetic (Z)
import Data.Polynomial (Polynomial, evaluate, pretty)
import Data.Typelevel.Num (D11)
import Test.QuickCheck (Result(..), quickCheck, quickCheck', (<?>), (===))
import Test.QuickCheck.Laws.Data (checkCommutativeRing, checkEq, checkEuclideanRing, checkMonoid, checkRing, checkSemigroup, checkSemiring)
import Type.Proxy (Proxy(..))

main = do
  let p11 = Proxy :: Proxy (Polynomial (Z D11))

  checkEq p11
  checkSemiring p11
  checkRing p11
  checkCommutativeRing p11
  checkEuclideanRing p11

  -- This takes too long
  -- checkSemigroup p11
  checkMonoid p11

  log "Checking that evaluate is a homomorphism with respect to addition"
  quickCheck \(p :: Polynomial (Z D11)) q x ->
    evaluate (p + q) x === evaluate p x + evaluate q x

  log "Checking that evaluate is a homomorphism with respect to subtraction"
  quickCheck \(p :: Polynomial (Z D11)) q x ->
    evaluate (p - q) x === evaluate p x - evaluate q x

  log "Checking that evaluate is a homomorphism with respect to multiplication"
  quickCheck \(p :: Polynomial (Z D11)) q x ->
    evaluate (p * q) x === evaluate p x * evaluate q x

  log "Behaviour of degree with respect to addition"
  quickCheck' 1000 \(p :: Polynomial (Z D11)) q ->
    degree (p + q) <= max (degree p) (degree q)

  log "Behaviour of degree with respect to multiplication"
  quickCheck' 1000 \(p :: Polynomial (Z D11)) q ->
    (p /= zero && q /= zero) `implies`
      (degree (p * q) === degree p + degree q)

  log "Behaviour of degree with respect to composition"
  quickCheck' 1000 \(p :: Polynomial (Z D11)) q ->
    (p /= zero && q /= zero) `implies`
      (degree (p <> q) == degree p * degree q
        <?> "p: " <> pretty p <> ", q: " <> pretty q <> ", p<>q: " <> pretty (p <> q))

implies :: Boolean -> Result -> Result
implies true x = x
implies false _ = Success
