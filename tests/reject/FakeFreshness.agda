{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
module FakeFreshness where
open import Agda.Builtin.Equality
open import EpistemicTypes.ReadConsistency
import EpistemicTypes.ContinuityExamples as Examples
open Examples.Reads using (historical)
forged : Fresh historical
forged = refl
