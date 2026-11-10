{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
module ReplayedHolder where
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (refl)
open import EpistemicTypes.ProofTransportExample using (Bob; ArtifactIsTrue; module HolderBoundary)
open HolderBoundary using (module Local)

-- Holder-sensitive evidence cannot be re-certified for a different holder.
-- `LocalMeaning holder _ _` is `holder ≡ Alice`.  The forgery below
-- replays Alice's accepting checker with Bob as the holder; it fails
-- exactly at the checker's soundness obligation, `Bob ≡ Alice`.  Under a
-- holder-independent meaning the same term would type-check, so the
-- rejection is evidence about the meaning, not about the `View` index.
-- (Rewritten 2026-11-09; the earlier fixture failed on the index alone.)

-- EXPECTED-REJECTION
bobCheck : Local.CertificateCheck Bob true ArtifactIsTrue
bobCheck = Local.certificateCheck (λ _ -> true) (λ _ _ -> refl)
