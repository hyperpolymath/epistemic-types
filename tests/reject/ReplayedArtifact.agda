{-# OPTIONS --safe --without-K #-}
module ReplayedArtifact where
open import Agda.Builtin.Bool using (false)
open import EpistemicTypes.ProofTransportExample using (Agent; Claim; Artifact; Meaning; Payload; Alice; ArtifactIsTrue; aliceProof)
open import EpistemicTypes.ProofTransport Agent Claim Artifact Meaning Payload

-- A proof bound to the original artifact cannot be reused for an altered one.
replay : View Alice false Proof ArtifactIsTrue
replay = aliceProof
