{-# OPTIONS --safe --without-K #-}

module EpistemicTypes.EchoBridge where

open import Agda.Primitive using (lzero; lsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import EpistemicTypes.Base

-- This module is only a bridge scaffold.
-- Echo grades are min-plus-like loss/residue grades, while epistemic indices
-- are standpoints.  They compose, but they are not the same modality.
data Grade : Set where
  finite   : Nat -> Grade
  infinity : Grade

minNat : Nat -> Nat -> Nat
minNat zero n = zero
minNat (suc m) zero = zero
minNat (suc m) (suc n) = suc (minNat m n)

-- Tropical "addition": choose the smaller grade.
gradeMin : Grade -> Grade -> Grade
gradeMin (finite m) (finite n) = finite (minNat m n)
gradeMin (finite m) infinity = finite m
gradeMin infinity (finite n) = finite n
gradeMin infinity infinity = infinity

-- Tropical "multiplication": compose costs by ordinary addition.
gradePlus : Grade -> Grade -> Grade
gradePlus (finite m) (finite n) = finite (m + n)
gradePlus (finite m) infinity = infinity
gradePlus infinity (finite n) = infinity
gradePlus infinity infinity = infinity

-- Echo is represented abstractly here.  A value of Echo r A contains a
-- residue token, not an exposed value of A.
record Echo (r : Grade) (A : Set) : Set₁ where
  constructor echo
  field
    Residue : Set
    residue : Residue

-- E κ (Echo r A): standpoint κ has epistemic access to an echo of A at
-- irrecoverability grade r.
EpistemicEcho :
  {K : Set} ->
  Modality K (lsuc lzero) ->
  K ->
  Grade ->
  Set ->
  Set₁
EpistemicEcho M κ r A = Modality.E M κ (Echo r A)
