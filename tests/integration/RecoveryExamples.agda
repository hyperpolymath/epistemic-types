{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module RecoveryExamples where

open import Data.Bool.Base using (Bool; false; true)
open import Agda.Builtin.Maybe using (just; nothing)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import CanonicalEcho as Residues
import CanonicalRecovery as Adapter
import CanonicalPartialRecovery as PartialAdapter
import EchoFiniteResidue as Exact
import EpistemicTypes.EchoBridge as Epistemic
import EpistemicTypes.PartialRecovery as Partial
import EpistemicTypes.PartialRecoveryExamples as PartialExamples

-- Two distinct sources occupy one visible fibre. Identity retention supplies
-- enough residue; the certificate restricts the visible index to that fibre.
twoRetention : Epistemic.Retention (Fin 2) (Fin 2) (Fin 2)
Epistemic.Retention.observe twoRetention _ = zero
Epistemic.Retention.retain twoRetention x = x
Epistemic.Retention.Cert twoRetention _ y = y ≡ zero
Epistemic.Retention.sound twoRetention _ = refl

twoRecovery : Epistemic.Recovery twoRetention
Epistemic.Recovery.recover twoRecovery _ r = r
Epistemic.Recovery.roundtrip twoRecovery _ = refl

twoExactRecovery :
  Exact.ExactRecovery (Epistemic.Retention.observe twoRetention)
    (Epistemic.Retention.retain twoRetention)
twoExactRecovery = Adapter.toExactRecovery twoRecovery

twoAdapterRoundtrip : (x : Fin 2) ->
  Epistemic.Recovery.recover
    (Adapter.fromExactRecovery {C = twoRetention} twoExactRecovery) zero x ≡ x
twoAdapterRoundtrip x = refl

-- This is the actual two-source single-fibre bound, not a claim about bits,
-- entropy, security or the cardinality of every source fibre.
twoSymbolBound : 2 ≤ 2
twoSymbolBound = Adapter.recoveryFiniteFibreBound twoRecovery
  (λ x -> x) (λ p -> p) zero (λ _ -> refl)

-- Existing canonical residue conversion copies the original proof, rather
-- than proving all certificates equal or recovering an equality witness.
twoCertificatePreserved : {y : Fin 2} (e : Epistemic.Echo twoRetention y) ->
  Epistemic.Echo.certified
    (Residues.fromCanonical {C = twoRetention} (Residues.toCanonical e)) ≡
  Epistemic.Echo.certified e
twoCertificatePreserved (Epistemic.echo r cert) = refl

twoOtherFibreUncertified : Epistemic.Echo twoRetention (suc zero) -> ⊥
twoOtherFibreUncertified (Epistemic.echo r ())

-- A certificate may be valid while the retained pair loses a source
-- distinction. The transferred collision theorem forbids any total recovery.
oneSymbolRetention : Epistemic.Retention (Fin 2) ⊤ (Fin 1)
Epistemic.Retention.observe oneSymbolRetention _ = tt
Epistemic.Retention.retain oneSymbolRetention _ = zero
Epistemic.Retention.Cert oneSymbolRetention _ _ = ⊤
Epistemic.Retention.sound oneSymbolRetention _ = tt

first≢second : (zero {1}) ≢ suc zero
first≢second ()

noOneSymbolRecovery : Epistemic.Recovery oneSymbolRetention -> ⊥
noOneSymbolRecovery recovery =
  Adapter.recoveryForbidsResidueCollision recovery first≢second refl refl

-- Certificate-restricted decoding can be vacuous on an empty source. Both
-- actual recovery interfaces demand a total decoder even off the image.
emptyRetention : Epistemic.Retention ⊥ ⊤ ⊤
Epistemic.Retention.observe emptyRetention ()
Epistemic.Retention.retain emptyRetention ()
Epistemic.Retention.Cert emptyRetention _ _ = ⊥
Epistemic.Retention.sound emptyRetention ()

emptyCertifiedDecoder : (y : ⊤) -> Epistemic.Echo emptyRetention y -> ⊥
emptyCertifiedDecoder y (Epistemic.echo r ())

emptyCertifiedRoundtrip : (x : ⊥) ->
  emptyCertifiedDecoder (Epistemic.Retention.observe emptyRetention x)
    (Epistemic.lower emptyRetention x) ≡ x
emptyCertifiedRoundtrip ()

noEmptyRecovery : Epistemic.Recovery emptyRetention -> ⊥
noEmptyRecovery recovery = Epistemic.Recovery.recover recovery tt tt

noEmptyExactRecovery :
  Exact.ExactRecovery (Epistemic.Retention.observe emptyRetention)
    (Epistemic.Retention.retain emptyRetention) -> ⊥
noEmptyExactRecovery recovery =
  noEmptyRecovery (Adapter.fromExactRecovery {C = emptyRetention} recovery)

-- On-image equality alone does not identify total decoders: these two valid
-- recoveries differ at an unreachable, uncertified visible/residue pair.
offImageRetention : Epistemic.Retention Bool (Bool × Bool) ⊤
Epistemic.Retention.observe offImageRetention b = b , false
Epistemic.Retention.retain offImageRetention _ = tt
Epistemic.Retention.Cert offImageRetention _ y = proj₂ y ≡ false
Epistemic.Retention.sound offImageRetention _ = refl

projectRecovery : Epistemic.Recovery offImageRetention
Epistemic.Recovery.recover projectRecovery y _ = proj₁ y
Epistemic.Recovery.roundtrip projectRecovery _ = refl

private
  flip : Bool -> Bool
  flip false = true
  flip true = false

flipOffImageRecovery : Epistemic.Recovery offImageRetention
Epistemic.Recovery.recover flipOffImageRecovery (b , false) _ = b
Epistemic.Recovery.recover flipOffImageRecovery (b , true) _ = flip b
Epistemic.Recovery.roundtrip flipOffImageRecovery _ = refl

decodersAgreeOnImage : (b : Bool) ->
  Epistemic.Recovery.recover projectRecovery (b , false) tt ≡
  Epistemic.Recovery.recover flipOffImageRecovery (b , false) tt
decodersAgreeOnImage b = refl

decodersDisagreeOffImage :
  Epistemic.Recovery.recover projectRecovery (false , true) tt ≢
  Epistemic.Recovery.recover flipOffImageRecovery (false , true) tt
decodersDisagreeOffImage ()

offImageUncertified : Epistemic.Echo offImageRetention (false , true) -> ⊥
offImageUncertified (Epistemic.echo r ())

adapterPreservesOffImage :
  Epistemic.Recovery.recover
    (Adapter.fromExactRecovery {C = offImageRetention}
      (Adapter.toExactRecovery flipOffImageRecovery)) (false , true) tt ≡ true
adapterPreservesOffImage = refl

-- This decision returns actual canonical Echo fibres of the joint pair
-- function. The adapter checks the owning definition at the reviewed pin.
canonicalPartial : Partial.PartialRecovery PartialExamples.finiteRetention
canonicalPartial = PartialAdapter.fromCanonicalDecision
  {C = PartialExamples.finiteRetention}
  PartialExamples.finiteSeparates PartialExamples.finiteImageDecision

canonicalPartialGenerated : (b : Bool) ->
  Partial.PartialRecovery.decode canonicalPartial (b , false) tt ≡ just b
canonicalPartialGenerated b = refl

canonicalPartialUnreachable : (b : Bool) ->
  Partial.PartialRecovery.decode canonicalPartial (b , true) tt ≡ nothing
canonicalPartialUnreachable b = refl
