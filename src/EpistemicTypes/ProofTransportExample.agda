{-# OPTIONS --safe --without-K #-}

-- Executable Boolean certificate checks, semantic soundness, and countercases.
-- ArtifactIsTrue means a Boolean equality, not that a physical action occurred.
module EpistemicTypes.ProofTransportExample where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

data Agent : Set where
  K9SVC Alice Bob : Agent

data Claim : Set where
  ArtifactIsTrue ImpossibleClaim : Claim

Artifact : Set
Artifact = Bool

data NoMeaning : Set where

Meaning : Agent -> Artifact -> Claim -> Set
Meaning _ a ArtifactIsTrue = a ≡ true
Meaning _ _ ImpossibleClaim = NoMeaning

Payload : Artifact -> Claim -> Set
Payload _ _ = Bool

open import EpistemicTypes.ProofTransport Agent Claim Artifact Meaning Payload

checkPayload : (a : Artifact) -> (c : Claim) -> Payload a c -> Bool
checkPayload true ArtifactIsTrue p = p
checkPayload false ArtifactIsTrue _ = false
checkPayload _ ImpossibleClaim _ = false

checkPayloadSound :
  (holder : Agent) (a : Artifact) (c : Claim) (p : Payload a c) ->
  checkPayload a c p ≡ true -> Meaning holder a c
checkPayloadSound _ true ArtifactIsTrue true _ = refl
checkPayloadSound _ true ArtifactIsTrue false ()
checkPayloadSound _ false ArtifactIsTrue p ()
checkPayloadSound _ true ImpossibleClaim p ()
checkPayloadSound _ false ImpossibleClaim p ()

verifier : (holder : Agent) (a : Artifact) (c : Claim) -> CertificateCheck holder a c
verifier holder a c = certificateCheck (checkPayload a c) (checkPayloadSound holder a c)

aliceRaw : View Alice true Data ArtifactIsTrue
aliceRaw = asData

aliceChecker : Checker Alice (Designated Alice) true ArtifactIsTrue
aliceChecker = designatedCheck (verifier Alice true ArtifactIsTrue)

aliceEvidence : Evidence (Designated Alice) true ArtifactIsTrue
aliceEvidence = designatedEv Alice true

aliceProof : View Alice true Proof ArtifactIsTrue
aliceProof = forgetMode (asProofUnder certDesignated aliceChecker aliceEvidence refl)

aliceUpgrade : Either Gap (View Alice true Proof ArtifactIsTrue)
aliceUpgrade = designatedTransfer aliceChecker aliceEvidence aliceRaw

aliceUpgradeSucceeds : aliceUpgrade ≡ right aliceProof
aliceUpgradeSucceeds = refl

aliceProofHasMeaning : Meaning Alice true ArtifactIsTrue
aliceProofHasMeaning = proofSound aliceProof

aliceToBob : Boundary
aliceToBob = Alice ⇒ Bob

bobReceipt : View Bob true Receipt ArtifactIsTrue
bobReceipt = transmit aliceToBob aliceProof

Alice≢Bob : ¬ (Alice ≡ Bob)
Alice≢Bob ()

bobHasNoDesignatedChecker : ¬ Checker Bob (Designated Alice) true ArtifactIsTrue
bobHasNoDesignatedChecker ck = Alice≢Bob (designatedBindsHolder ck)

-- This concrete meaning is holder-independent, so the required implication is id.
bobPublicChecker : Checker Bob Public true ArtifactIsTrue
bobPublicChecker = publicIsPortable {r = Alice} {q = Bob} (λ p -> p)
  (publicCheck (verifier Alice true ArtifactIsTrue))

bobPublicProof : View Bob true Proof ArtifactIsTrue
bobPublicProof = forgetMode
  (asProofUnder certPublic bobPublicChecker (publicEv true) refl)

bobPublicUpgradeSucceeds :
  publicTransfer bobPublicChecker (publicEv true) asData ≡ right bobPublicProof
bobPublicUpgradeSucceeds = refl

-- Negative data cases are successful proofs ABOUT actual rejection computations.
badPayloadRejected :
  publicTransfer bobPublicChecker (publicEv false) asData ≡ left InvalidEvidence
badPayloadRejected = refl

tamperedArtifactRejected :
  verify (publicCheck (verifier Bob false ArtifactIsTrue))
    (publicEv true) asData ≡ left InvalidEvidence
tamperedArtifactRejected = refl

falseClaimRejected :
  verify (publicCheck (verifier Bob true ImpossibleClaim))
    (publicEv true) asData ≡ left InvalidEvidence
falseClaimRejected = refl

falseClaimHasNoProof : ¬ View Bob true Proof ImpossibleClaim
falseClaimHasNoProof = proofCannotSupportFalse (λ ())

-- Any attempted generic fabrication function is refuted by the false instance.
noArbitraryProofStatuses :
  ¬ ((c : Claim) -> View Bob true Proof c)
noArbitraryProofStatuses manufacture = falseClaimHasNoProof (manufacture ImpossibleClaim)

receiptModeRejected :
  verify {holder = Bob} {a = true} {c = ArtifactIsTrue}
    receiptCheck (receiptEv true) asData ≡ left OpaqueGap
receiptModeRejected = refl

missingCheckerRejected :
  tryUpgrade {holder = Bob} {a = true} {m = Public} {c = ArtifactIsTrue}
    nothing (just (publicEv true)) asData ≡ left MissingChecker
missingCheckerRejected = refl

missingEvidenceRejected :
  tryUpgrade (just bobPublicChecker) nothing asData ≡ left MissingEvidence
missingEvidenceRejected = refl

-- Issuer/environment modes use the SAME semantic soundness obligation.
issuerProof : View Alice true Proof ArtifactIsTrue
issuerProof = forgetMode (asProofUnder certIssuer
  (issuerCheck (verifier Alice true ArtifactIsTrue)) (issuerEv true) refl)

issuerAccepts :
  verify (issuerCheck (verifier Alice true ArtifactIsTrue)) (issuerEv true) asData
  ≡ right issuerProof
issuerAccepts = refl

issuerRejectsFalse :
  verify (issuerCheck (verifier Alice true ImpossibleClaim)) (issuerEv true) asData
  ≡ left InvalidEvidence
issuerRejectsFalse = refl

environmentProof : View Alice true Proof ArtifactIsTrue
environmentProof = forgetMode (asProofUnder certEnv
  (envCheck (verifier Alice true ArtifactIsTrue)) (envEv true) refl)

environmentAccepts :
  verify (envCheck (verifier Alice true ArtifactIsTrue)) (envEv true) asData
  ≡ right environmentProof
environmentAccepts = refl

environmentRejectsFalse :
  verify (envCheck (verifier Alice true ImpossibleClaim)) (envEv true) asData
  ≡ left InvalidEvidence
environmentRejectsFalse = refl

designatedRejectsFalse :
  verify (designatedCheck (verifier Alice true ImpossibleClaim))
    (designatedEv Alice true) asData ≡ left InvalidEvidence
designatedRejectsFalse = refl

-- A holder-sensitive interpretation demonstrates why portability needs a proof.
-- Alice knows her own identity; that fact cannot be relabelled as Bob = Alice.
module HolderBoundary where
  LocalMeaning : Agent -> Artifact -> Claim -> Set
  LocalMeaning holder _ _ = holder ≡ Alice

  import EpistemicTypes.ProofTransport as Core
  module Local = Core Agent Claim Artifact LocalMeaning Payload

  aliceCheck : Local.CertificateCheck Alice true ArtifactIsTrue
  aliceCheck = Local.certificateCheck (λ _ -> true) (λ _ _ -> refl)

  aliceLocalProof : Local.View Alice true Local.Proof ArtifactIsTrue
  aliceLocalProof = Local.forgetMode (Local.asProofUnder Local.certPublic
    (Local.publicCheck aliceCheck) (Local.publicEv true) refl)

  noBobProof : Local.¬ Local.View Bob true Local.Proof ArtifactIsTrue
  noBobProof = Local.proofCannotSupportFalse (λ ())

  noSilentHolderTransport :
    Local.¬ (Local.View Alice true Local.Proof ArtifactIsTrue ->
      Local.View Bob true Local.Proof ArtifactIsTrue)
  noSilentHolderTransport move = noBobProof (move aliceLocalProof)
