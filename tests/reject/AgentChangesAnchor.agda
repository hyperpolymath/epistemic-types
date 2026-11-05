{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
module AgentChangesAnchor where
open import Agda.Builtin.Equality using (_≡_; refl)
open import EpistemicTypes.Applications.ApprovalSeal

forged : anchor resealed ≡ 1
forged = refl
