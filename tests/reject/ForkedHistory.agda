{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
module ForkedHistory where
open import EpistemicTypes.ReadConsistency
import EpistemicTypes.ContinuityExamples as Examples
open Examples.Reads using (after; otherBranch)
forged : CachedRead after
forged = cached otherBranch here (readCurrent otherBranch)
