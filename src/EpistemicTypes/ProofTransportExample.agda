{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- A K9-SVC / A2ML-style attestation, modelled with proof transport.
--
--   issuer        K9SVC
--   receiver      Alice
--   third party   Bob
--   claim         ActionWasPerformed
--   artifact      AttestationBlob
--
-- Three cases are exhibited:
--   (1) the blob is raw Data for Alice;
--   (2) Alice upgrades it to Proof with her designated checker + evidence;
--   (3) Bob, across the boundary, holds only a Receipt — and *cannot* hold the
--       designated capability that was issued to Alice — UNLESS the attestation
--       is public, which is portable to any agent.
------------------------------------------------------------------------

module EpistemicTypes.ProofTransportExample where

open import Agda.Builtin.Equality using (_≡_; refl)

data Agent : Set where
  K9SVC : Agent
  Alice : Agent
  Bob   : Agent

data Claim : Set where
  ActionWasPerformed : Claim

data Artifact : Set where
  AttestationBlob : Artifact

-- Instantiate the proof-transport core at these concrete carriers.
open import EpistemicTypes.ProofTransport Agent Claim Artifact

----------------------------------------------------------------------
-- Case 1: the attestation blob is just data for Alice.
----------------------------------------------------------------------

aliceRaw : View Alice AttestationBlob Data ActionWasPerformed
aliceRaw = asData

----------------------------------------------------------------------
-- Case 2: Alice has the designated checker and the matching evidence, so she
-- upgrades the blob to a proof of ActionWasPerformed.
----------------------------------------------------------------------

aliceChecker : Checker Alice (Designated Alice) AttestationBlob ActionWasPerformed
aliceChecker = designatedCheck

aliceEvidence : Evidence (Designated Alice) AttestationBlob ActionWasPerformed
aliceEvidence = designatedEv Alice

aliceUpgrade : Either Gap (View Alice AttestationBlob Proof ActionWasPerformed)
aliceUpgrade = designatedTransfer aliceChecker aliceEvidence aliceRaw

aliceProof : View Alice AttestationBlob Proof ActionWasPerformed
aliceProof = forgetMode (asProofUnder certDesignated aliceChecker aliceEvidence)

-- The upgrade really does succeed (it computes to `right aliceProof`).
aliceUpgradeSucceeds : aliceUpgrade ≡ right aliceProof
aliceUpgradeSucceeds = refl

----------------------------------------------------------------------
-- Case 3a: across the Alice ⇒ Bob boundary, Bob's view of the proof degrades
-- to a mere receipt.  The bytes crossed; the proofhood did not.
----------------------------------------------------------------------

aliceToBob : Boundary
aliceToBob = Alice ⇒ Bob

bobReceipt : View Bob AttestationBlob Receipt ActionWasPerformed
bobReceipt = transmit aliceToBob aliceProof

----------------------------------------------------------------------
-- Case 3b: Bob cannot manufacture the *designated* proof.  The designated
-- capability is bound to Alice, and Alice ≢ Bob, so the type
--   Checker Bob (Designated Alice) AttestationBlob ActionWasPerformed
-- is uninhabited.  This is the deniability of a designated attestation.
----------------------------------------------------------------------

Alice≢Bob : ¬ (Alice ≡ Bob)
Alice≢Bob ()

bobHasNoDesignatedChecker :
  ¬ Checker Bob (Designated Alice) AttestationBlob ActionWasPerformed
bobHasNoDesignatedChecker ck = Alice≢Bob (designatedBindsHolder ck)

----------------------------------------------------------------------
-- Case 3c: but if the attestation is *public*, Bob upgrades like anyone else,
-- because public checking is portable from Alice to Bob.
----------------------------------------------------------------------

bobPublicChecker : Checker Bob Public AttestationBlob ActionWasPerformed
bobPublicChecker = publicIsPortable {Alice} {Bob} publicCheck

bobPublicUpgrade :
  Evidence Public AttestationBlob ActionWasPerformed ->
  Either Gap (View Bob AttestationBlob Proof ActionWasPerformed)
bobPublicUpgrade ev = publicTransfer bobPublicChecker ev asData

----------------------------------------------------------------------
-- A receipt-only attestation never upgrades to proof of the claim, for anyone.
----------------------------------------------------------------------

bobBlob : View Bob AttestationBlob Data ActionWasPerformed
bobBlob = asData

bobReceiptStuck :
  (ev : Evidence OpaqueReceipt AttestationBlob ActionWasPerformed) ->
  verify receiptCheck ev bobBlob ≡ left OpaqueGap
bobReceiptStuck ev = verifyReceiptIsGap ev bobBlob
