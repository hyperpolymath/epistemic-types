{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
module FinalStateProvesNoTouch where
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import EpistemicTypes.Applications.ApprovalSeal

forged : broken restored ≡ false
forged = refl
