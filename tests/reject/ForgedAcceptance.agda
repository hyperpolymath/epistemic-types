{-# OPTIONS --safe --without-K #-}
module ForgedAcceptance where
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (refl)
open import EpistemicTypes.ProofTransportExample using (Agent; Claim; Artifact; Meaning; Payload; Bob; ArtifactIsTrue; bobPublicChecker)
open import EpistemicTypes.ProofTransport Agent Claim Artifact Meaning Payload

-- The public constructor cannot bypass a sound check rejecting this payload.
forge : View Bob true Proof ArtifactIsTrue
forge = forgetMode (asProofUnder certPublic bobPublicChecker (publicEv false) refl)
