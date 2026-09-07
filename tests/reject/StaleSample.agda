{-# OPTIONS --safe --without-K #-}
module StaleSample where
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import EpistemicTypes.ReadConsistency
import EpistemicTypes.ContinuityExamples as Examples
open Examples.Reads using (after)
forged : ReadView after
forged = readView false refl
