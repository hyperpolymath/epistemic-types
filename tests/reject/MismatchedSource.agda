{-# OPTIONS --safe --without-K #-}
module MismatchedSource where
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import EpistemicTypes.EchoBridge
import EpistemicTypes.ContinuityExamples as Examples
open Examples.Residues using (identityRetention; identityTrue)
forged : MatchesSource identityRetention false identityTrue
forged = matchesSource refl refl
