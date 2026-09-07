{-# OPTIONS --safe --without-K #-}
module ReplayedHolder where
open import Agda.Builtin.Bool using (true)
open import EpistemicTypes.ProofTransportExample using (Bob; ArtifactIsTrue; module HolderBoundary)
open HolderBoundary using (module Local; aliceLocalProof)

-- Holder-sensitive evidence cannot silently acquire a different holder.
replay : Local.View Bob true Local.Proof ArtifactIsTrue
replay = aliceLocalProof
