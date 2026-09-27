{-# OPTIONS --safe --without-K #-}

-- Applications / RapidNJSkip
--
-- The epistemic reading of the RapidNJ quadrant skip.  This module is the
-- answer to the question "how does a `FactiveModality` map onto the
-- Q-criterion bound, and how does skipping a quadrant generate a *valid*
-- warrant?"
--
-- The mapping is one line long: `FactiveModality.reflect` for the RapidNJ
-- frame *is* the soundness map of the skip warrant, whose proof is the
-- Q-criterion bound lemma `QCriterion.Criterion.qBound-≤-Q`.  Concretely,
-- the chain is
--
--     run data (numbers, cursor, sorted suffix, accepted check)
--       --(skipWarrant)-->  Warrant κ "nothing skipped beats the incumbent"
--       --(skip-sound, the bound lemma)-->  SoundWarrant κ (same claim)
--       --(sound-epi = FactiveModality.reflect)-->  the claim itself
--
-- Nothing about soundness is assumed: the warrant is *generated* from the
-- run, the check must be accepted by a `Checkable` instance, and the only
-- arithmetic fact consumed is the order-monotonicity budget of
-- `OrderedGroup` (no ring identities, hence no ℚ-specific law).  The
-- resulting knowledge is therefore valid in any exact model, and an
-- implementation whose arithmetic is not exact fails at exactly one place:
-- supplying `Checkable` (see the Float64 seam in
-- link:docs/applications/rapidnj-q-criterion.adoc[]).
--
-- The same run, held without a soundness map, is belief: `Epi` packages a
-- warrant with a token and `no-receipt-reflection` shows that a token alone
-- is never the claim.
--
-- Universe note.  A warrant is a *type of evidence*, so a record packaging
-- one sits one universe above its claim.  The modalities below are
-- therefore instantiated at `lsuc lzero`: claims enter through `Lift₁`,
-- and `lower` takes the reflected claim back down.  This is the same
-- universe bookkeeping the core uses for `Warrant` and `Epi`; it is not an
-- extra assumption.

module EpistemicTypes.Applications.RapidNJSkip where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Primitive using (Level; lzero; lsuc)

open import EpistemicTypes.Base
open import EpistemicTypes.Warrant
open import EpistemicTypes.EchoBridge using (Impossible)
open import EpistemicTypes.Applications.OrderedGroup
import EpistemicTypes.Applications.SortedRow as SortedRow
import EpistemicTypes.Applications.QCriterion as QCriterion

-- A claim carried one universe up, so that a modality at `lsuc lzero` can
-- take it as an argument.
record Lift₁ (A : Set) : Set₁ where
  constructor lift
  field
    lower : A

-- The skip layer, parameterised by the exact arithmetic it reasons about.
module Skip (G : OrderedGroup) where
  open OrderedGroup G
  open Laws G
  open SortedRow.Row G
  open QCriterion.Criterion G

  -- ── the obligation an executable implementation must meet ────────────────

  -- A decision procedure whose `true` verdicts *reflect* the order.  This is
  -- the single seam between the proof and a running program: an
  -- implementation with exact arithmetic (integers, or rationals with
  -- cross-multiplied comparisons) can supply it; one with rounding cannot,
  -- because rounding is not monotone for every pair of operands.
  record Checkable : Set₁ where
    field
      decide      : (x y : Carrier) -> Bool
      decide-true : {x y : Carrier} -> decide x y ≡ true -> x ≤ y

  -- ── the scan state, as data ─────────────────────────────────────────────

  -- Exactly the line a logger would record for a bounded row scan: the
  -- numbers, the stop cursor, and the suffix that was not looked at.
  record ScanState : Set where
    constructor scanning
    field
      run     : Numbers
      cursor  : Entry
      suffix  : List Entry

  -- The check the run performs: the incumbent is at most the bound.  In
  -- RapidNJ terms: "q(min) ≤ q(bound), so stop scanning this row".
  --
  -- Stated as a *type* with a plain body rather than as a pattern-matching
  -- function: a matching definition would not unfold on a variable state,
  -- and the evidence type below must be syntactically the conclusion of
  -- `Checkable.decide-true`.
  CheckStatement : (C : Checkable) (s : ScanState) -> Set
  CheckStatement C s =
    Checkable.decide C (Numbers.incumbent (ScanState.run s))
      (qBound (Numbers.coefficient (ScanState.run s))
              (Numbers.row-sum-i (ScanState.run s))
              (Numbers.row-sum-max (ScanState.run s))
              (Entry.dist (ScanState.cursor s))) ≡ true

  -- The claim a skip carries: no entry of the skipped suffix beats the
  -- incumbent, in the same units as the bound.
  RowClaim : (s : ScanState) (es : List Entry) -> Set
  RowClaim s es = (e : Entry) -> e ∈E es ->
    Numbers.incumbent (ScanState.run s) ≤
    Q (Numbers.coefficient (ScanState.run s))
      (Numbers.row-sum-i (ScanState.run s))
      (Entry.rowSum e) (Entry.dist e)

  SkipClaimAt : (s : ScanState) -> Set
  SkipClaimAt s = RowClaim s (ScanState.suffix s)

  -- The evidence a skipper holds: the sorted-row invariant, the
  -- running-maximum invariant, and an accepted check.  Holding this is what
  -- it means to have skipped the quadrant.
  SkipEvidence : (C : Checkable) (s : ScanState) -> Set
  SkipEvidence C s =
    Σ (AllDistAtLeast (Entry.dist (ScanState.cursor s)) (ScanState.suffix s))
      (λ _ → Σ (AllRowSumAtMost (Numbers.row-sum-max (ScanState.run s))
                                (ScanState.suffix s))
        (λ _ → CheckStatement C s))

  -- ── warrant generation ──────────────────────────────────────────────────

  -- The warrant is *computed* from the run.  Its type of evidence is the
  -- skipper's evidence type; no soundness is asserted here.
  skipWarrant : (K : Set) (κ : K) (C : Checkable) (s : ScanState) ->
    Warrant {wℓ = lzero} K κ (SkipClaimAt s)
  Warrant.Evidence (skipWarrant K κ C s) = SkipEvidence C s

  -- Soundness of the generated warrant: the accepted check, routed through
  -- the Q-criterion bound lemma, is the claim.
  skip-sound : (C : Checkable) (s : ScanState) ->
    SkipEvidence C s -> SkipClaimAt s
  -- The implicit arguments are supplied explicitly: the coefficient sits
  -- under `scale`, which is a defined function, so it cannot be recovered by
  -- unification.  Naming the numbers is also what a log line does.
  skip-sound C s (ordered , maximal , accepted) =
    qBound-≤-suffix {k = Numbers.coefficient (ScanState.run s)}
                    {ti = Numbers.row-sum-i (ScanState.run s)}
                    {tmax = Numbers.row-sum-max (ScanState.run s)}
                    {q₀ = Numbers.incumbent (ScanState.run s)}
                    {cursor = ScanState.cursor s}
                    ordered maximal (Checkable.decide-true C accepted)

  skipSoundWarrant : (K : Set) (κ : K) (C : Checkable) (s : ScanState) ->
    SoundWarrant {wℓ = lzero} K κ (SkipClaimAt s)
  SoundWarrant.warrant (skipSoundWarrant K κ C s) = skipWarrant K κ C s
  SoundWarrant.sound (skipSoundWarrant K κ C s) = skip-sound C s

  -- ── the factive layer ───────────────────────────────────────────────────

  -- A warrant whose evidence type is fixed by the caller.  This is how the
  -- modality below re-uses an existing evidence type under a new claim.
  warrantOn : {ℓ : Level} {K : Set} (κ : K) (A : Set ℓ) (E : Set) ->
    Warrant {wℓ = lzero} K κ A
  Warrant.Evidence (warrantOn κ A E) = E

  -- Knowledge at a standpoint: a sound warrant *and* a token of its
  -- evidence.  The projection is the soundness map, not the token.
  Knowledge : (K : Set) (κ : K) (A : Set₁) -> Set₁
  Knowledge K κ A = Σ (SoundWarrant {ℓ = lsuc lzero} {wℓ = lzero} K κ A)
                      (λ sw → Warrant.Evidence (SoundWarrant.warrant sw))

  sound-map : {K : Set} {κ : K} {A B : Set₁} (f : A -> B) ->
    SoundWarrant {ℓ = lsuc lzero} {wℓ = lzero} K κ A ->
    SoundWarrant {ℓ = lsuc lzero} {wℓ = lzero} K κ B
  SoundWarrant.warrant (sound-map {κ = κ} f sw) =
    warrantOn κ _ (Warrant.Evidence (SoundWarrant.warrant sw))
  SoundWarrant.sound (sound-map f sw) e = f (SoundWarrant.sound sw e)

  -- The modality: `map` rewrites the soundness map and keeps the evidence.
  knowledgeModality : (K : Set) -> Modality K (lsuc lzero)
  Modality.E (knowledgeModality K) κ A = Knowledge K κ A
  Modality.map (knowledgeModality K) f (sw , e) = (sound-map f sw , e)

  -- The mapping that answers the question: `reflect` *is* the soundness map
  -- of the generated skip warrant.
  rapidKnowledge : (K : Set) -> FactiveModality K (lsuc lzero)
  FactiveModality.modality (rapidKnowledge K) = knowledgeModality K
  FactiveModality.reflect (rapidKnowledge K) (sw , e) = sound-epi sw e

  -- ── the theorems ────────────────────────────────────────────────────────

  -- The same warrant, its soundness map delivering the lifted claim, which
  -- is the shape the modality at `lsuc lzero` consumes.
  liftedSoundWarrant : (K : Set) (κ : K) (C : Checkable) (s : ScanState) ->
    SoundWarrant {ℓ = lsuc lzero} {wℓ = lzero} K κ (Lift₁ (SkipClaimAt s))
  SoundWarrant.warrant (liftedSoundWarrant K κ C s) =
    warrantOn κ (Lift₁ (SkipClaimAt s)) (SkipEvidence C s)
  SoundWarrant.sound (liftedSoundWarrant K κ C s) e = lift (skip-sound C s e)

  -- Skipping a quadrant, with a run recorded as evidence, yields knowledge
  -- of the claim (at the lifted universe).
  skip-generates-knowledge : (K : Set) (κ : K) (C : Checkable)
    (s : ScanState) -> SkipEvidence C s -> Knowledge K κ (Lift₁ (SkipClaimAt s))
  skip-generates-knowledge K κ C s ev = (liftedSoundWarrant K κ C s , ev)

  -- Reflecting it gives the claim itself.  This is the theorem the pipeline
  -- consumes: a checked bound, not a trusted one.
  skip-known : (K : Set) (κ : K) (C : Checkable) (s : ScanState) ->
    SkipEvidence C s -> SkipClaimAt s
  skip-known K κ C s ev =
    Lift₁.lower (FactiveModality.reflect (rapidKnowledge K)
      (skip-generates-knowledge K κ C s ev))

  -- The examined prefix (checked by the scanner) and the skipped suffix
  -- (certified by the generated warrant) cover the whole row: the skip
  -- composes back into a whole-row guarantee.
  whole-row-known : (K : Set) (κ : K) (C : Checkable) (s : ScanState)
    (pre : List Entry) ->
    ((e : Entry) -> e ∈E pre -> Numbers.incumbent (ScanState.run s) ≤
      Q (Numbers.coefficient (ScanState.run s))
        (Numbers.row-sum-i (ScanState.run s)) (Entry.rowSum e) (Entry.dist e)) ->
    SkipEvidence C s ->
    (e : Entry) -> e ∈E (pre ++ ScanState.suffix s) ->
      Numbers.incumbent (ScanState.run s) ≤
      Q (Numbers.coefficient (ScanState.run s))
        (Numbers.row-sum-i (ScanState.run s)) (Entry.rowSum e) (Entry.dist e)
  whole-row-known K κ C s pre scanned ev =
    noBetter-append {k = Numbers.coefficient (ScanState.run s)}
                    {ti = Numbers.row-sum-i (ScanState.run s)}
                    {q₀ = Numbers.incumbent (ScanState.run s)}
                    {pre = pre} {suf = ScanState.suffix s}
                    scanned (skip-known K κ C s ev)

  -- ── the non-factive layer, for contrast ─────────────────────────────────

  EpiAt : (K : Set) (κ : K) (A : Set₁) -> Set₁
  EpiAt K κ A = Epi {ℓ = lsuc lzero} {wℓ = lzero} K κ A

  receipt-map : {K : Set} {κ : K} {A B : Set₁} (f : A -> B) ->
    EpiAt K κ A -> EpiAt K κ B
  receipt-map {κ = κ} f (epi w e) = epi (warrantOn κ _ (Warrant.Evidence w)) e

  receipts : (K : Set) -> Modality K (lsuc lzero)
  Modality.E (receipts K) κ A = EpiAt K κ A
  Modality.map (receipts K) f x = receipt-map f x

  -- Belief: the same run, the same token, no soundness map.
  rapidBelief : (K : Set) -> BeliefModality K (lsuc lzero)
  BeliefModality.modality (rapidBelief K) = receipts K

  skip-belief-only : (K : Set) (κ : K) (C : Checkable) (s : ScanState) ->
    SkipEvidence C s -> EpiAt K κ (Lift₁ (SkipClaimAt s))
  skip-belief-only K κ C s ev =
    epi (warrantOn κ (Lift₁ (SkipClaimAt s)) (SkipEvidence C s)) ev

  -- A one-element type, used to exhibit a token whose claim is empty.
  data Point : Set where
    point : Point

  -- A warrant plus a token is not knowledge: there is no reflection out of
  -- `Epi`, for the skip warrants or for any others.
  no-receipt-reflection : {K : Set} (κ : K) ->
    ((A : Set₁) -> EpiAt K κ A -> A) -> Impossible
  no-receipt-reflection {K} κ reflectEpi =
    Lift₁.lower (reflectEpi (Lift₁ Impossible)
      (epi (warrantOn κ (Lift₁ Impossible) Point) point))

  -- ── the standpoint frame, for the worked example and the documentation ──

  data Standpoint : Set where
    full-scan  : Standpoint   -- every entry of the row was examined
    pruned     : Standpoint   -- a prefix was examined, the rest is certified
    unverified : Standpoint   -- the same numbers, no accepted check

  rapidNJKnowledge : FactiveModality Standpoint (lsuc lzero)
  rapidNJKnowledge = rapidKnowledge Standpoint

  rapidNJBelief : BeliefModality Standpoint (lsuc lzero)
  rapidNJBelief = rapidBelief Standpoint

  -- ── the open obligation, stated and not assumed ─────────────────────────

  -- The "dynamic" RapidNJ variant re-uses a bound across iterations by the
  -- argument that q-values only weaken when a cluster is joined.  That
  -- transport is NOT proved here.  The obligation is declared so it can be
  -- attacked explicitly, and nothing in this module depends on it: there is
  -- no instance and no result that consumes one.
  record WeakeningObligation : Set₁ where
    field
      continues : ScanState -> ScanState -> Set
      carries   : {s s' : ScanState} -> continues s s' ->
        RowClaim s (ScanState.suffix s) -> RowClaim s (ScanState.suffix s')
