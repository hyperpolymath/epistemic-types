{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- residual-evidence-types' Holds, read as a Kripke box.
--
-- There, a Case is an observation `observe : W → O`, a reading `r`, and
-- evidence `E : W → Set`; a Candidate is a world with that reading that
-- satisfies the evidence; `Holds c P` says P at every candidate.  That is
-- Box over the accessibility "w' is a candidate" — the Echo fibre over the
-- reading, cut down by the evidence.  So the four verdicts (entailed,
-- refuted, unresolved, inconsistent) are the four joint cases of
-- Box P and Box (¬ P), and "presence without identification" is de dicto
-- without de re: Box (∃ a. P a) with no Box (P a).  Witnessed below.
module EpistemicTypes.Kripke.Residual where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)
open import EpistemicTypes.Kripke.Frame

-- The residual frame: one standpoint; w' accessible iff it is a candidate.
residualFrame : {W O : Set} (observe : W → O) (r : O) (E : W → Set) → Frame ⊤ W
residualFrame observe r E = record { _∼[_]_ = λ _ _ w' → Σ (observe w' ≡ r) (λ _ → E w') }

-- Holds c P, by definition, is Box at any world (the base world is inert).
Holds : {W O : Set} (observe : W → O) (r : O) (E : W → Set) → (W → Set) → W → Set
Holds observe r E = Box (residualFrame observe r E) tt

----------------------------------------------------------------------
-- Presence without identification.  Three worlds; the observation cannot
-- tell a from b; the evidence excludes c.  Something is present (de dicto),
-- but no particular thing is (de re).
data W : Set where a b c : W
data O : Set where seen unseen : O

observe : W → O
observe a = seen
observe b = seen
observe c = unseen

E : W → Set
E _ = ⊤

-- "Thing x is here": true only at world x.
Is : W → W → Set
Is a a = ⊤
Is a b = ⊥
Is a c = ⊥
Is b a = ⊥
Is b b = ⊤
Is b c = ⊥
Is c a = ⊥
Is c b = ⊥
Is c c = ⊥

Present : W → Set
Present w = Σ W (λ x → Is x w)

presence : ∀ w → Holds observe seen E Present w
presence _ a (refl , _) = a , tt
presence _ b (refl , _) = b , tt

no-identification : ∀ x w → ¬ Holds observe seen E (Is x) w
no-identification a w h = h b (refl , tt)
no-identification b w h = h a (refl , tt)
no-identification c w h = h a (refl , tt)
