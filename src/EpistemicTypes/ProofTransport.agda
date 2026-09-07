{-# OPTIONS --safe --without-K #-}

-- Proof statuses carry a successful check and entail a caller-supplied meaning.
-- Soundness is relative to Meaning and the verifier's explicit soundness proof.
-- This module does not establish cryptography, physical facts, or runtime timing.
module EpistemicTypes.ProofTransport
  (Agent : Set)
  (Claim : Set)
  (Artifact : Set)
  (Meaning : Agent -> Artifact -> Claim -> Set)
  (Payload : Artifact -> Claim -> Set)
  where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)

data ⊥ : Set where
¬_ : {ℓ : Level} -> Set ℓ -> Set ℓ
¬ A = A -> ⊥

infixr 4 _,_
infixr 2 _×_
data Either {ℓ ℓ' : Level} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  left : A -> Either A B
  right : B -> Either A B

record Σ {ℓ ℓ' : Level} (A : Set ℓ) (B : A -> Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst

_×_ : {ℓ ℓ' : Level} -> Set ℓ -> Set ℓ' -> Set (ℓ ⊔ ℓ')
A × B = Σ A (λ _ -> B)

data Maybe {ℓ : Level} (A : Set ℓ) : Set ℓ where
  nothing : Maybe A
  just : A -> Maybe A

data Mode : Set where
  Public : Mode
  Designated : Agent -> Mode
  IssuerMediated EnvironmentMediated OpaqueReceipt : Mode

data Status : Set where
  Data Code Claimed Receipt Proof : Status
  ProofUnder : Mode -> Status

data Gap : Set where
  TrivialGap DesignatedGap EnvironmentGap IssuerTrustGap OpaqueGap : Gap
  MissingChecker MissingEvidence MissingContext InvalidEvidence : Gap

-- Evidence carries a payload, but the payload's existence never proves Meaning.
data Evidence : Mode -> Artifact -> Claim -> Set where
  publicEv : {a : Artifact} {c : Claim} -> Payload a c -> Evidence Public a c
  designatedEv : {a : Artifact} {c : Claim} (d : Agent) ->
    Payload a c -> Evidence (Designated d) a c
  issuerEv : {a : Artifact} {c : Claim} -> Payload a c -> Evidence IssuerMediated a c
  envEv : {a : Artifact} {c : Claim} -> Payload a c -> Evidence EnvironmentMediated a c
  receiptEv : {a : Artifact} {c : Claim} -> Payload a c -> Evidence OpaqueReceipt a c

evidencePayload : {m : Mode} {a : Artifact} {c : Claim} -> Evidence m a c -> Payload a c
evidencePayload (publicEv p) = p
evidencePayload (designatedEv _ p) = p
evidencePayload (issuerEv p) = p
evidencePayload (envEv p) = p
evidencePayload (receiptEv p) = p

-- A real checking function plus a proof that acceptance entails the exact claim
-- for this holder and artifact. Completeness is deliberately not required.
record CertificateCheck (holder : Agent) (a : Artifact) (c : Claim) : Set where
  constructor certificateCheck
  field
    check : Payload a c -> Bool
    sound : (p : Payload a c) -> check p ≡ true -> Meaning holder a c

data Checker (holder : Agent) : Mode -> Artifact -> Claim -> Set where
  publicCheck : {a : Artifact} {c : Claim} ->
    CertificateCheck holder a c -> Checker holder Public a c
  designatedCheck : {a : Artifact} {c : Claim} ->
    CertificateCheck holder a c -> Checker holder (Designated holder) a c
  issuerCheck : {a : Artifact} {c : Claim} ->
    CertificateCheck holder a c -> Checker holder IssuerMediated a c
  envCheck : {a : Artifact} {c : Claim} ->
    CertificateCheck holder a c -> Checker holder EnvironmentMediated a c
  receiptCheck : {a : Artifact} {c : Claim} -> Checker holder OpaqueReceipt a c

data Certifying : Mode -> Set where
  certPublic : Certifying Public
  certDesignated : {d : Agent} -> Certifying (Designated d)
  certIssuer : Certifying IssuerMediated
  certEnv : Certifying EnvironmentMediated

runChecker :
  {holder : Agent} {a : Artifact} {m : Mode} {c : Claim} ->
  Checker holder m a c -> Evidence m a c -> Bool
runChecker (publicCheck v) ev = CertificateCheck.check v (evidencePayload ev)
runChecker (designatedCheck v) ev = CertificateCheck.check v (evidencePayload ev)
runChecker (issuerCheck v) ev = CertificateCheck.check v (evidencePayload ev)
runChecker (envCheck v) ev = CertificateCheck.check v (evidencePayload ev)
runChecker receiptCheck _ = false

checkerSound :
  {holder : Agent} {a : Artifact} {m : Mode} {c : Claim} ->
  Certifying m -> (ck : Checker holder m a c) -> (ev : Evidence m a c) ->
  runChecker ck ev ≡ true -> Meaning holder a c
checkerSound certPublic (publicCheck v) ev ok = CertificateCheck.sound v (evidencePayload ev) ok
checkerSound certDesignated (designatedCheck v) ev ok = CertificateCheck.sound v (evidencePayload ev) ok
checkerSound certIssuer (issuerCheck v) ev ok = CertificateCheck.sound v (evidencePayload ev) ok
checkerSound certEnv (envCheck v) ev ok = CertificateCheck.sound v (evidencePayload ev) ok

data View (holder : Agent) : Artifact -> Status -> Claim -> Set where
  asData : {a : Artifact} {c : Claim} -> View holder a Data c
  asCode : {a : Artifact} {c : Claim} -> View holder a Code c
  asClaimed : {a : Artifact} {c : Claim} -> View holder a Claimed c
  asReceipt : {a : Artifact} {c : Claim} -> View holder a Receipt c
  asProofUnder :
    {a : Artifact} {m : Mode} {c : Claim} ->
    Certifying m -> (ck : Checker holder m a c) -> (ev : Evidence m a c) ->
    runChecker ck ev ≡ true -> View holder a (ProofUnder m) c
  forgetMode :
    {a : Artifact} {m : Mode} {c : Claim} ->
    View holder a (ProofUnder m) c -> View holder a Proof c

-- The semantic guarantee holds even for clients using the constructors directly.
proofSound :
  {holder : Agent} {a : Artifact} {c : Claim} ->
  View holder a Proof c -> Meaning holder a c
proofSound (forgetMode (asProofUnder cert ck ev ok)) = checkerSound cert ck ev ok

proofCannotSupportFalse :
  {holder : Agent} {a : Artifact} {c : Claim} ->
  ¬ Meaning holder a c -> ¬ View holder a Proof c
proofCannotSupportFalse notMeaning proof = notMeaning (proofSound proof)

infix 4 _⇒_
record Boundary : Set where
  constructor _⇒_
  field
    from to : Agent
open Boundary public

transmit :
  {a : Artifact} {c : Claim} -> (b : Boundary) ->
  View (from b) a Proof c -> View (to b) a Receipt c
transmit b _ = asReceipt

verifyCertifying :
  {holder : Agent} {a : Artifact} {m : Mode} {c : Claim} ->
  Certifying m -> (ck : Checker holder m a c) -> Evidence m a c ->
  Either Gap (View holder a Proof c)
verifyCertifying cert ck ev with runChecker ck ev in accepted
... | true = right (forgetMode (asProofUnder cert ck ev accepted))
... | false = left InvalidEvidence

verify :
  {holder : Agent} {a : Artifact} {m : Mode} {c : Claim} ->
  Checker holder m a c -> Evidence m a c -> View holder a Data c ->
  Either Gap (View holder a Proof c)
verify (publicCheck v) ev _ = verifyCertifying certPublic (publicCheck v) ev
verify (designatedCheck v) ev _ = verifyCertifying certDesignated (designatedCheck v) ev
verify (issuerCheck v) ev _ = verifyCertifying certIssuer (issuerCheck v) ev
verify (envCheck v) ev _ = verifyCertifying certEnv (envCheck v) ev
verify receiptCheck _ _ = left OpaqueGap

-- This returns a checked result, not a promise that arbitrary evidence succeeds.
checkableTransportUpgrades :
  {a : Artifact} {m : Mode} {c : Claim} ->
  (b : Boundary) -> View (from b) a Proof c -> View (to b) a Data c ->
  Checker (to b) m a c -> Evidence m a c ->
  Either Gap (View (to b) a Proof c)
checkableTransportUpgrades b _ dv ck ev = verify ck ev dv

publicTransfer :
  {receiver : Agent} {a : Artifact} {c : Claim} ->
  Checker receiver Public a c -> Evidence Public a c ->
  View receiver a Data c -> Either Gap (View receiver a Proof c)
publicTransfer = verify

-- Holder-dependent meanings cannot be silently transported. A caller supplies
-- the semantic implication, while the executable payload check is preserved.
publicIsPortable :
  {r q : Agent} {a : Artifact} {c : Claim} ->
  (Meaning r a c -> Meaning q a c) ->
  Checker r Public a c -> Checker q Public a c
publicIsPortable transport (publicCheck v) = publicCheck
  (certificateCheck (CertificateCheck.check v)
    (λ p ok -> transport (CertificateCheck.sound v p ok)))

designatedTransfer :
  {receiver : Agent} {a : Artifact} {c : Claim} ->
  Checker receiver (Designated receiver) a c ->
  Evidence (Designated receiver) a c -> View receiver a Data c ->
  Either Gap (View receiver a Proof c)
designatedTransfer = verify

designatedBindsHolder :
  {holder d : Agent} {a : Artifact} {c : Claim} ->
  Checker holder (Designated d) a c -> d ≡ holder
designatedBindsHolder (designatedCheck _) = refl

opaqueNotCertifying : ¬ Certifying OpaqueReceipt
opaqueNotCertifying ()

verifyReceiptIsGap :
  {holder : Agent} {a : Artifact} {c : Claim} ->
  (ev : Evidence OpaqueReceipt a c) -> (v : View holder a Data c) ->
  verify {holder} receiptCheck ev v ≡ left OpaqueGap
verifyReceiptIsGap ev v = refl

tryUpgrade :
  {holder : Agent} {a : Artifact} {m : Mode} {c : Claim} ->
  Maybe (Checker holder m a c) -> Maybe (Evidence m a c) ->
  View holder a Data c -> Either Gap (View holder a Proof c)
tryUpgrade nothing _ _ = left MissingChecker
tryUpgrade (just _) nothing _ = left MissingEvidence
tryUpgrade (just ck) (just ev) v = verify ck ev v

proofNeedsChecker :
  {holder : Agent} {a : Artifact} {c : Claim} ->
  View holder a Proof c ->
  Σ Mode (λ m -> Certifying m × Checker holder m a c × Evidence m a c)
proofNeedsChecker (forgetMode (asProofUnder cert ck ev ok)) = _ , cert , ck , ev

proofHasSuccessfulCheck :
  {holder : Agent} {a : Artifact} {c : Claim} ->
  View holder a Proof c ->
  Σ Mode (λ m -> Σ (Checker holder m a c)
    (λ ck -> Σ (Evidence m a c) (λ ev -> runChecker ck ev ≡ true)))
proofHasSuccessfulCheck (forgetMode (asProofUnder cert ck ev ok)) = _ , ck , ev , ok
