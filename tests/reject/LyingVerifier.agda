{-# OPTIONS --safe --without-K #-}
module LyingVerifier where
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (refl)
open import EpistemicTypes.ProofTransportExample using (Agent; Claim; Artifact; Meaning; Payload; Alice; ArtifactIsTrue)
open import EpistemicTypes.ProofTransport Agent Claim Artifact Meaning Payload

-- An always-accepting checker cannot supply soundness for a false artifact.
lie : CertificateCheck Alice false ArtifactIsTrue
lie = certificateCheck (λ _ -> true) (λ _ _ -> refl)
