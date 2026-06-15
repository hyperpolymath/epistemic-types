{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Standpoint-indexed proof transport across trust boundaries.
--
-- This module distinguishes three readings of one artefact:
--
--   1. von Neumann      : the artefact is data/code — bytes that can cross
--                         any wall.  Here this is `Artifact`, and the cheap
--                         statuses `Data` / `Code`.
--   2. Curry–Howard     : a *checked* artefact can be a proof of a
--                         proposition.  Here `Proof` / `ProofUnder m` are the
--                         statuses reached only by running a `Checker` over
--                         `Evidence` (a `verify`).
--   3. proof-carrying    : code-plus-certificate can be re-checked by the
--      code (PCC)          consumer.  Here `Evidence` is the certificate (it
--                          travels as data), and the consumer's `Checker` is
--                          the local verifier that re-establishes proofhood.
--
-- The epistemic-types contribution is that *proofhood is standpoint-indexed*.
-- A sender may hold an artefact as `View sender artifact Proof claim`, while
-- the receiver initially holds the same bytes only as `Data`, `Claimed`, or
-- `Receipt`.  Transmission moves bytes, not proofhood: `transmit` downgrades a
-- sender's proof to a receiver's `Receipt`.  Proofhood is *recovered* on the
-- receiver's side only when the receiver has an appropriate verification
-- capability (`Checker`) and certificate (`Evidence`).
--
-- The honesty discipline of this repository (see EpistemicTypes.Base) is kept:
-- the only constructor of `View` that reaches a proof status demands a
-- certifying mode, a checker, and evidence.  No checker-free transport
-- function `View sender a Proof c -> View receiver a Proof c` is exported.
-- See `proofNeedsChecker` for the structural statement of this.
------------------------------------------------------------------------

module EpistemicTypes.ProofTransport
  (Agent    : Set)   -- who holds a standpoint / view
  (Claim    : Set)   -- what is asserted
  (Artifact : Set)   -- the von Neumann object: bytes, code, certificate
  where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Tiny prelude.  This library does not depend on a standard library
-- (`agda --no-libraries`), so the few structural types are defined locally,
-- mirroring the local ⊥/¬ pattern in EpistemicTypes.Examples.
------------------------------------------------------------------------

data ⊥ : Set where

¬_ : {ℓ : Level} -> Set ℓ -> Set ℓ
¬ A = A -> ⊥

infixr 4 _,_
infixr 2 _×_

data Either {ℓ ℓ' : Level} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  left  : A -> Either A B
  right : B -> Either A B

record Σ {ℓ ℓ' : Level} (A : Set ℓ) (B : A -> Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst

_×_ : {ℓ ℓ' : Level} -> Set ℓ -> Set ℓ' -> Set (ℓ ⊔ ℓ')
A × B = Σ A (λ _ -> B)

data Maybe {ℓ : Level} (A : Set ℓ) : Set ℓ where
  nothing : Maybe A
  just    : A -> Maybe A

------------------------------------------------------------------------
-- Verification / attestation modes.
------------------------------------------------------------------------

data Mode : Set where
  Public              : Mode            -- publicly checkable; transferable
  Designated          : Agent -> Mode   -- "Designated Agent": bound to one party
  IssuerMediated      : Mode            -- needs trust in the issuer
  EnvironmentMediated : Mode            -- needs a runtime / environment context
  OpaqueReceipt       : Mode            -- only acknowledges receipt; never certifies

------------------------------------------------------------------------
-- Epistemic status of an artefact, relative to a holder, w.r.t. a claim.
------------------------------------------------------------------------

data Status : Set where
  Data       : Status           -- von Neumann bytes; asserts nothing
  Code       : Status           -- executable bytes; still just data to a receiver
  Claimed    : Status           -- a claim is asserted, but unverified
  Receipt    : Status           -- an acknowledgement; not proof of the claim
  Proof      : Status           -- a checked proof of the claim (mode forgotten)
  ProofUnder : Mode -> Status   -- a checked proof under a specific mode/standpoint

------------------------------------------------------------------------
-- Gaps: reasons an upgrade to Proof fails.
------------------------------------------------------------------------

data Gap : Set where
  TrivialGap      : Gap   -- nothing else to do, but a checker is still required
  DesignatedGap   : Gap   -- the designation does not match this holder
  EnvironmentGap  : Gap   -- environment / context absent
  IssuerTrustGap  : Gap   -- issuer not trusted by this holder
  OpaqueGap       : Gap   -- receipt-only; the underlying claim is not certified
  MissingChecker  : Gap   -- the holder lacks the checking capability
  MissingEvidence : Gap   -- the holder lacks the certificate / evidence
  MissingContext  : Gap   -- the holder lacks the ambient context

------------------------------------------------------------------------
-- A Checker is a holder's *capability* to verify, in a given mode, that an
-- artefact certifies a claim.  Capabilities — not certificates — are the part
-- that does not automatically cross a trust boundary.
------------------------------------------------------------------------

data Checker (holder : Agent) : Mode -> Artifact -> Claim -> Set where
  -- Public verification is agent-agnostic: any holder can run it.
  publicCheck     : {a : Artifact} {c : Claim} -> Checker holder Public a c
  -- Designated verification binds the designated party to the holder itself.
  -- There is deliberately NO constructor designated to another agent.
  designatedCheck : {a : Artifact} {c : Claim} -> Checker holder (Designated holder) a c
  -- Issuer-mediated and environment-mediated capabilities for the holder.
  issuerCheck     : {a : Artifact} {c : Claim} -> Checker holder IssuerMediated a c
  envCheck        : {a : Artifact} {c : Claim} -> Checker holder EnvironmentMediated a c
  -- An opaque receipt is the capability only to acknowledge receipt — never to
  -- certify the underlying claim.  (Note: `Certifying OpaqueReceipt` is empty.)
  receiptCheck    : {a : Artifact} {c : Claim} -> Checker holder OpaqueReceipt a c

-- Which modes actually *certify* a claim, i.e. may yield `Proof`.
-- `OpaqueReceipt` is deliberately excluded — see `opaqueNotCertifying`.
data Certifying : Mode -> Set where
  certPublic     : Certifying Public
  certDesignated : {d : Agent} -> Certifying (Designated d)
  certIssuer     : Certifying IssuerMediated
  certEnv        : Certifying EnvironmentMediated

-- Evidence is the certificate payload.  It is plain data and may cross the
-- boundary freely (von Neumann).  Possessing evidence is not possessing proof;
-- proof additionally requires the holder's own certifying `Checker`.
data Evidence : Mode -> Artifact -> Claim -> Set where
  publicEv     : {a : Artifact} {c : Claim} -> Evidence Public a c
  designatedEv : {a : Artifact} {c : Claim} (d : Agent) -> Evidence (Designated d) a c
  issuerEv     : {a : Artifact} {c : Claim} -> Evidence IssuerMediated a c
  envEv        : {a : Artifact} {c : Claim} -> Evidence EnvironmentMediated a c
  receiptEv    : {a : Artifact} {c : Claim} -> Evidence OpaqueReceipt a c

------------------------------------------------------------------------
-- The standpoint-indexed judgement.
--
--   View holder artifact status claim
--     "the holder regards `artifact` at epistemic `status` w.r.t. `claim`."
--
-- The cheap statuses (Data/Code/Claimed/Receipt) are freely introducible.
-- A proof status is NOT: the only route to `ProofUnder m` is `asProofUnder`,
-- which demands `Certifying m`, a `Checker`, and `Evidence`; and `Proof`
-- is reached only by forgetting the mode of a `ProofUnder`.
------------------------------------------------------------------------

data View (holder : Agent) : Artifact -> Status -> Claim -> Set where
  asData    : {a : Artifact} {c : Claim} -> View holder a Data c
  asCode    : {a : Artifact} {c : Claim} -> View holder a Code c
  asClaimed : {a : Artifact} {c : Claim} -> View holder a Claimed c
  asReceipt : {a : Artifact} {c : Claim} -> View holder a Receipt c
  asProofUnder :
    {a : Artifact} {m : Mode} {c : Claim} ->
    Certifying m -> Checker holder m a c -> Evidence m a c ->
    View holder a (ProofUnder m) c
  forgetMode :
    {a : Artifact} {m : Mode} {c : Claim} ->
    View holder a (ProofUnder m) c -> View holder a Proof c

------------------------------------------------------------------------
-- A trust boundary, directed from a sender to a receiver.
------------------------------------------------------------------------

infix 4 _⇒_

record Boundary : Set where
  constructor _⇒_
  field
    from : Agent
    to   : Agent
open Boundary public

-- Transmission across a boundary.  A sender's *proof* arrives at the receiver
-- only as a *receipt*: the bytes cross the wall, the proofhood does not.
-- This is the conservative half of the story — transport alone never upgrades.
transmit :
  {a : Artifact} {c : Claim} ->
  (b : Boundary) ->
  View (from b) a Proof c ->
  View (to b) a Receipt c
transmit b _ = asReceipt

------------------------------------------------------------------------
-- verify: with a matching checker and evidence, upgrade Data to Proof.
-- The opaque-receipt capability yields a Gap, never a proof of the claim.
------------------------------------------------------------------------

verify :
  {holder : Agent} {a : Artifact} {m : Mode} {c : Claim} ->
  Checker holder m a c ->
  Evidence m a c ->
  View holder a Data c ->
  Either Gap (View holder a Proof c)
verify publicCheck     ev _ = right (forgetMode (asProofUnder certPublic     publicCheck     ev))
verify designatedCheck ev _ = right (forgetMode (asProofUnder certDesignated designatedCheck ev))
verify issuerCheck     ev _ = right (forgetMode (asProofUnder certIssuer     issuerCheck     ev))
verify envCheck        ev _ = right (forgetMode (asProofUnder certEnv        envCheck        ev))
verify receiptCheck    _  _ = left OpaqueGap

------------------------------------------------------------------------
-- The central positive theorem.
--
-- A receiver holding the artefact as Data, *and* a checker and evidence, can
-- upgrade to Proof.  The sender's proof and the boundary are present but
-- deliberately unused (`_`): transmission alone does not justify the upgrade —
-- only the receiver's own checker and evidence do.
------------------------------------------------------------------------

checkableTransportUpgrades :
  {sender receiver : Agent} {a : Artifact} {m : Mode} {c : Claim} ->
  View sender a Proof c ->     -- the sender already had a proof ...
  Boundary ->                  -- ... it crossed a boundary ...
  View receiver a Data c ->    -- ... and the receiver holds the bytes,
  Checker receiver m a c ->    -- but proofhood is recovered only via the
  Evidence m a c ->            -- receiver's own checker and evidence.
  Either Gap (View receiver a Proof c)
checkableTransportUpgrades _ _ dv ck ev = verify ck ev dv

------------------------------------------------------------------------
-- Public (transferable) attestation.
------------------------------------------------------------------------

-- A public certificate plus a public checker upgrades data to proof.
publicTransfer :
  {receiver : Agent} {a : Artifact} {c : Claim} ->
  Checker receiver Public a c ->
  Evidence Public a c ->
  View receiver a Data c ->
  Either Gap (View receiver a Proof c)
publicTransfer = verify

-- Public verification is not bound to one designated receiver: a public
-- checker held by `r` is reconstructible by any other agent `q`.
publicIsPortable :
  {r q : Agent} {a : Artifact} {c : Claim} ->
  Checker r Public a c -> Checker q Public a c
publicIsPortable publicCheck = publicCheck

------------------------------------------------------------------------
-- Designated (deniable) attestation.
------------------------------------------------------------------------

-- The designated receiver can verify a designated attestation addressed to it.
designatedTransfer :
  {receiver : Agent} {a : Artifact} {c : Claim} ->
  Checker receiver (Designated receiver) a c ->
  Evidence (Designated receiver) a c ->
  View receiver a Data c ->
  Either Gap (View receiver a Proof c)
designatedTransfer = verify

-- But a designated checker pins the designated party to its own holder.  Thus
-- no third party can hold the checker for someone else's designation: that
-- gives the deniability of a designated-verifier attestation by construction.
-- (See EpistemicTypes.ProofTransportExample for the concrete Bob case.)
designatedBindsHolder :
  {holder d : Agent} {a : Artifact} {c : Claim} ->
  Checker holder (Designated d) a c -> d ≡ holder
designatedBindsHolder designatedCheck = refl

------------------------------------------------------------------------
-- Receipt-only (opaque) attestation never certifies the underlying claim.
------------------------------------------------------------------------

opaqueNotCertifying : ¬ Certifying OpaqueReceipt
opaqueNotCertifying ()

verifyReceiptIsGap :
  {holder : Agent} {a : Artifact} {c : Claim} ->
  (ev : Evidence OpaqueReceipt a c) ->
  (v  : View holder a Data c) ->
  verify {holder} receiptCheck ev v ≡ left OpaqueGap
verifyReceiptIsGap ev v = refl

------------------------------------------------------------------------
-- A resource-gathering entry point that names the missing-resource gaps.
-- This is the partial / discovery layer above `verify`: before you can run a
-- check you must actually possess the capability and the certificate.
------------------------------------------------------------------------

tryUpgrade :
  {holder : Agent} {a : Artifact} {m : Mode} {c : Claim} ->
  Maybe (Checker holder m a c) ->
  Maybe (Evidence m a c) ->
  View holder a Data c ->
  Either Gap (View holder a Proof c)
tryUpgrade nothing   _         _ = left MissingChecker
tryUpgrade (just _)  nothing   _ = left MissingEvidence
tryUpgrade (just ck) (just ev) v = verify ck ev v

------------------------------------------------------------------------
-- No smuggling.
--
-- Every proof a holder possesses is backed by *that holder's* own certifying
-- mode, checker, and evidence.  Equivalently: a `View holder a Proof c` can
-- never be obtained witness-free, so in particular there is no exported
--   View sender a Proof c -> View receiver a Proof c
-- (such a function would have to fabricate the receiver's checker+evidence).
------------------------------------------------------------------------

proofNeedsChecker :
  {holder : Agent} {a : Artifact} {c : Claim} ->
  View holder a Proof c ->
  Σ Mode (λ m -> Certifying m × Checker holder m a c × Evidence m a c)
proofNeedsChecker (forgetMode (asProofUnder cert ck ev)) = _ , cert , ck , ev
