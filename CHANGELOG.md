# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Dates are ISO 8601 (`YYYY-MM-DD`). This is a small, deliberately honest Agda
formalization that favours mathematical honesty over a large API; the changelog
records what is actually proved, not what is aspired to.

## [Unreleased]

### Added

- `EpistemicTypes.ProofTransport`: standpoint-indexed proof transport across
  trust boundaries.
  - `View : Agent -> Artifact -> Status -> Claim -> Set`, with statuses
    `Data` / `Code` / `Claimed` / `Receipt` / `Proof` / `ProofUnder`.
  - Transport modes `Public` / `Designated` / `IssuerMediated` /
    `EnvironmentMediated` / `OpaqueReceipt`.
  - `transmit` downgrades a sender's `Proof` to a receiver's `Receipt`;
    `verify` upgrades `Data -> Proof` only with the receiver's OWN checker and
    evidence. Public views are portable, designated views are receiver-bound,
    and receipt-only views never certify.
  - `proofNeedsChecker`: the structural no-smuggling guarantee.
- `EpistemicTypes.ProofTransportExample`: a worked K9-SVC / A2ML attestation
  scenario — issuer `K9SVC`, receiver `Alice`, third party `Bob`, claim
  `ActionWasPerformed`, artifact `AttestationBlob` — exercising transmit,
  receipt non-certification, and receiver-local verification.
- Engineering rendering of proof transport for `a2ml` / `k9` consumers under
  `.machine_readable/proof-transport/` (`ProofTransport.a2ml`,
  `proof-transport.k9.ncl`, `README.adoc`), targeting the estate `a2ml` + `k9`
  contractile tooling.
- `EpistemicTypes.SurrealBridge`: graded upgrade of surreal-numbered access.
  - `SurrealAccess` carrier and `GradedSurrealModality`.
  - `daySurrealAccess`, a finite birthday-tower account of standpoint access.

### Changed

- `EpistemicTypes.All` re-export aggregator extended to include
  `ProofTransport`, `ProofTransportExample`, and the upgraded `SurrealBridge`.
- RSR-compliance and documentation pass: machine-readable `6a2` descriptors
  (`0-AI-MANIFEST.a2ml`, `STATE.a2ml`) and AsciiDoc docs (`readme.adoc`,
  `explainme.adoc`) brought into line with the current module set. Existing
  lowercase doc filenames are preserved deliberately.

### Notes

- Continuous integration is not enabled for this repository (see `AUDIT.adoc`).
  Verification is local-only via `just check`.

## [0.1.0] - 2026-06-15

Prototype baseline: the first honest formalization of standpoint-indexed
modal / epistemic / echo-like type formers.

### Added

- `EpistemicTypes.Base`: the core interface. `E : K -> Set ℓ -> Set ℓ`, where
  `E κ A` reads "`A` is epistemically available at standpoint `κ`". This is a
  plain indexed endofunctor (`map` only) — deliberately NOT a monad or comonad,
  with no generic `return` / `reflect`. Provides `Modality`, `LawfulModality`,
  `FactiveModality`, `BeliefModality`, and `ReturnModality`.
- `EpistemicTypes.Warrant`: `Warrant`, `Epi`, and `SoundWarrant`.
- `EpistemicTypes.Access`: a `Preorder` on standpoints and an
  `AccessibleModality` whose `increase` transports availability along the
  preorder.
- `EpistemicTypes.EchoBridge`: min-plus graded loss / residue `Echo r A`, kept
  deliberately distinct from `E κ A`. Composes with the sibling `echo-types`
  loss-with-residue formalism.
- `EpistemicTypes.SurrealBridge`: initial `SurrealAccess` carrier and graded
  surreal modality.
- `EpistemicTypes.Examples`: small worked instances of the above.
- `EpistemicTypes.All`: re-export aggregator over the public modules.
- Build tooling: a `Justfile` with `just check`, defined as
  `agda --no-libraries -i src src/EpistemicTypes/All.agda` (Agda 2.8.0), plus
  the `epistemic-types.agda-lib` library descriptor.

### Project conventions

- Compiles under `{-# OPTIONS --safe --without-K #-}`.
- No postulates.
- No Agda standard library: built with `agda --no-libraries`, using only
  `Agda.Builtin.*` and `Agda.Primitive`.

[Unreleased]: https://github.com/hyperpolymath/epistemic-types/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/hyperpolymath/epistemic-types/releases/tag/v0.1.0
