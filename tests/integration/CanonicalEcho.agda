{-# OPTIONS --safe --without-K #-}

module CanonicalEcho where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
import Echo as Core
import EchoResidue as Canonical
open import EpistemicTypes.EchoBridge

-- This file imports the actual sibling sources, not a copied approximation.
-- Keep it separate from the dependency-free core build.
toCanonical : {A B R : Set} {C : Retention A B R} {y : B} ->
  Echo C y -> Canonical.EchoR R (Retention.Cert C) y
toCanonical (echo r p) = r , p

fromCanonical : {A B R : Set} {C : Retention A B R} {y : B} ->
  Canonical.EchoR R (Retention.Cert C) y -> Echo C y
fromCanonical (r , p) = echo r p

fromTo : {A B R : Set} {C : Retention A B R} {y : B} (e : Echo C y) ->
  fromCanonical {C = C} (toCanonical e) ≡ e
fromTo (echo r p) = refl

toFrom : {A B R : Set} {C : Retention A B R} {y : B}
  (e : Canonical.EchoR R (Retention.Cert C) y) ->
  toCanonical (fromCanonical {C = C} e) ≡ e
toFrom (r , p) = refl

lowerAgreesWithCanonical : {A B R : Set} (C : Retention A B R) (x : A) ->
  toCanonical (lower C x) ≡ Canonical.echo-to-residue
    (Retention.observe C) (Retention.retain C) (Retention.Cert C) (Retention.sound C)
    (Core.echo-intro (Retention.observe C) x)
lowerAgreesWithCanonical C x = refl
