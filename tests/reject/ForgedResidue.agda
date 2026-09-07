{-# OPTIONS --safe --without-K #-}
module ForgedResidue where
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import EpistemicTypes.EchoBridge
import EpistemicTypes.ContinuityExamples as Examples
open Examples.Residues using (identityRetention)
forged : Echo identityRetention true
forged = echo false refl
