{-# OPTIONS --safe --without-K #-}
module UnderstatedBound where
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import EpistemicTypes.EchoBridge
import EpistemicTypes.ContinuityExamples as Examples
open Examples.Residues using (identityRetention; constantCost; boundedTrue)
forged : BoundedEcho identityRetention constantCost (finite zero) true
forged = boundedTrue
