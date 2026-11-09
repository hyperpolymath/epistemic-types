{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
module ReplayedHolder where
open import Agda.Builtin.Bool using (true)
open import EpistemicTypes.ProofTransportExample using (Bob; ArtifactIsTrue; module HolderBoundary)
open HolderBoundary using (module Local; aliceLocalProof)

-- Holder-sensitive evidence cannot silently acquire a different holder.
-- Audit 2026-11-09: this is rejected because `View` is indexed by holder,
-- which would also reject it under a holder-independent `Meaning`; the
-- holder-sensitivity evidence is the positive `noSilentHolderTransport`.
replay : Local.View Bob true Local.Proof ArtifactIsTrue
replay = aliceLocalProof
