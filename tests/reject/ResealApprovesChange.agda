{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
module ResealApprovesChange where
open import Agda.Builtin.Equality using (_≡_; refl)
open import EpistemicTypes.Applications.ApprovalSeal

forged : gate resealed ≡ accepted
forged = refl
