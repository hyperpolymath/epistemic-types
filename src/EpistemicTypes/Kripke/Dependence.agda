{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- DECISION-002 test 1, run in a faithful mirror of residual-evidence-types'
-- Dependent (support ⊆ Γ, claim over the thinned context): dependence is
-- NOT a function of the candidate set.  Two contexts with the same worlds
-- differ in what a claim can be made to rest on — the duplicated
-- assumption can be dropped in one and not the other.  A box sees worlds;
-- dependence sees assumptions.  That is structure the frame forgets, and
-- the family half of the test passes here; it remains to re-prove it
-- against residual-evidence's own record (same kernel, same shape).
module EpistemicTypes.Kripke.Dependence where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)
open import EpistemicTypes.Kripke.Frame using (⊥)

infixr 5 _∷_
data Ctx (W : Set) : Set₁ where
  []  : Ctx W
  _∷_ : (W → Set) → Ctx W → Ctx W

⟦_⟧ : ∀ {W} → Ctx W → W → Set
⟦ [] ⟧    w = ⊤
⟦ P ∷ Γ ⟧ w = Σ (P w) (λ _ → ⟦ Γ ⟧ w)

infix 4 _⊆_
data _⊆_ {W : Set} : Ctx W → Ctx W → Set₁ where
  done : [] ⊆ []
  keep : ∀ {P Γ Δ} → Γ ⊆ Δ → (P ∷ Γ) ⊆ (P ∷ Δ)
  drop : ∀ {P Γ Δ} → Γ ⊆ Δ → Γ ⊆ (P ∷ Δ)

-- A claim under Γ: P at every world satisfying Γ (the candidates).
HoldsUnder : ∀ {W} → Ctx W → (W → Set) → Set
HoldsUnder Γ P = ∀ w → ⟦ Γ ⟧ w → P w

record Dependent {W : Set} (Γ : Ctx W) (P : W → Set) : Set₁ where
  constructor rests-on
  field
    support : Ctx W
    thin    : support ⊆ Γ
    claim   : HoldsUnder support P

-- A support is proper when it drops at least one assumption of Γ.
Proper : ∀ {W} {Γ Δ : Ctx W} → Δ ⊆ Γ → Set
Proper done     = ⊥
Proper (keep t) = Proper t
Proper (drop t) = ⊤

ProperlyDependent : ∀ {W} → Ctx W → (W → Set) → Set₁
ProperlyDependent Γ P = Σ (Dependent Γ P) (λ d → Proper (Dependent.thin d))

----------------------------------------------------------------------
-- The witness.
data W : Set where u v : W

P : W → Set
P u = ⊤
P v = ⊥

Γ₁ Γ₂ : Ctx W
Γ₁ = P ∷ []
Γ₂ = P ∷ P ∷ []

-- Same candidates, pointwise.
same-candidates : ∀ w → Σ (⟦ Γ₁ ⟧ w → ⟦ Γ₂ ⟧ w) (λ _ → ⟦ Γ₂ ⟧ w → ⟦ Γ₁ ⟧ w)
same-candidates w = (λ { (p , tt) → p , p , tt }) , (λ { (p , _ , tt) → p , tt })

-- Under Γ₂ the claim can rest on strictly less than Γ₂ ...
properly-in-Γ₂ : ProperlyDependent Γ₂ P
properly-in-Γ₂ = rests-on (P ∷ []) (drop (keep done)) (λ { w (p , tt) → p }) , tt

-- ... under Γ₁ it cannot: the only proper support is empty, and P fails at v.
not-properly-in-Γ₁ : ProperlyDependent Γ₁ P → ⊥
not-properly-in-Γ₁ (rests-on _ (keep done) _     , ())
not-properly-in-Γ₁ (rests-on _ (drop done) claim , _) = claim v tt
