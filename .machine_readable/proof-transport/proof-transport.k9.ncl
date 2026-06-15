# proof-transport.k9.ncl
# K9 Contractile: Kennel Level (Pure Data)
#
# Engineering rendering of the research module EpistemicTypes.ProofTransport
# (src/EpistemicTypes/ProofTransport.agda).  Kennel level = data only, no eval:
# this file states the standpoint-indexed proof-transport policy as a datum that
# K9 tooling can read.  The Agda module is the authority; this mirrors it.
#
# Thesis: proofhood is standpoint-indexed.  Transmission across a trust boundary
# moves bytes (von Neumann), not proofhood (Curry-Howard).  A receiver recovers
# proofhood only with its own checker (verifier) + evidence (certificate) — the
# proof-carrying-code pattern, made standpoint-relative.

let Leash = [| 'Kennel, 'Yard, 'Hunt |] in
let Mode = [| 'Public, 'Designated, 'IssuerMediated, 'EnvironmentMediated, 'OpaqueReceipt |] in
let Gap = [|
  'TrivialGap, 'DesignatedGap, 'EnvironmentGap, 'IssuerTrustGap,
  'OpaqueGap, 'MissingChecker, 'MissingEvidence, 'MissingContext
|] in

# Per-mode transport semantics.
let ModeRule = {
  certifies | Bool,            # can a matching checker + evidence yield Proof?
  portable | Bool,             # is the checker reconstructible by any agent?
  receiver_bound | Bool,       # is the checker pinned to one designated holder?
  gap_on_fail | Gap,           # RESERVED: the gap a future refinement would report
                               # for this mode. The core does NOT yet emit these per
                               # mode — see law.gaps_realized_today for what it emits.
} in

{
  leash | Leash = 'Kennel,

  contractile = {
    name = "proof-transport",
    version = "0.1.0",
    research_counterpart = "src/EpistemicTypes/ProofTransport.agda",
    example_counterpart = "src/EpistemicTypes/ProofTransportExample.agda",
    summary = "Proofhood is standpoint-indexed; transmission moves bytes, not proofhood.",
  },

  # The transport law, as data (cf. `transmit`, `checkableTransportUpgrades`,
  # `proofNeedsChecker` in the Agda module).
  law = {
    transmit_yields = "Receipt",                  # sender Proof crosses as Receipt
    upgrade_requires = ["Certifying", "Checker", "Evidence"],
    no_free_proof_transfer = true,                # no Proof -> Proof without a checker
    # The research core currently CONSTRUCTS only these gaps: `verify` emits
    # OpaqueGap (receipt-only); `tryUpgrade` emits MissingChecker / MissingEvidence.
    # All other gaps (including modes.*.gap_on_fail) are reserved vocabulary.
    gaps_realized_today = ["OpaqueGap", "MissingChecker", "MissingEvidence"],
  },

  # Statuses an artefact can hold relative to a holder (data `Status`).
  statuses = ["Data", "Code", "Claimed", "Receipt", "Proof", "ProofUnder"],

  # Verification / attestation modes and how each transports.
  modes = {
    Public | ModeRule = {
      certifies = true, portable = true, receiver_bound = false,
      gap_on_fail = 'MissingEvidence,
    },
    Designated | ModeRule = {
      certifies = true, portable = false, receiver_bound = true,
      gap_on_fail = 'DesignatedGap,
    },
    IssuerMediated | ModeRule = {
      certifies = true, portable = false, receiver_bound = false,
      gap_on_fail = 'IssuerTrustGap,
    },
    EnvironmentMediated | ModeRule = {
      certifies = true, portable = false, receiver_bound = false,
      gap_on_fail = 'EnvironmentGap,
    },
    OpaqueReceipt | ModeRule = {
      certifies = false, portable = false, receiver_bound = false,
      gap_on_fail = 'OpaqueGap,
    },
  },

  # All gaps in the vocabulary (data `Gap`).
  gaps = [
    "TrivialGap", "DesignatedGap", "EnvironmentGap", "IssuerTrustGap",
    "OpaqueGap", "MissingChecker", "MissingEvidence", "MissingContext",
  ],

  # The worked K9-SVC attestation scenario (mirrors ProofTransportExample.agda).
  scenario = {
    issuer = "K9SVC",
    receiver = "Alice",
    third_party = "Bob",
    claim = "ActionWasPerformed",
    artifact = "AttestationBlob",
    cases = [
      { who = "Alice", mode = 'Data, holds = ["blob"],
        result = "raw data; no claim certified" },
      { who = "Alice", mode = 'Designated, holds = ["blob", "designated_checker", "designated_evidence"],
        result = "Proof ActionWasPerformed" },
      { who = "Bob", mode = 'Receipt, holds = ["blob_via_transmit"],
        result = "Receipt only — designated checker is Alice-bound, so Bob cannot upgrade" },
      { who = "Bob", mode = 'Public, holds = ["blob", "public_checker", "public_evidence"],
        result = "Proof ActionWasPerformed — public checking is portable" },
    ],
  },

  # Conceptual mapping carried for agents that consume this datum.
  mapping = {
    von_neumann = "Artifact + statuses Data/Code: bytes/code cross any wall.",
    curry_howard = "Statuses Proof/ProofUnder: a checked artefact is a proof.",
    proof_carrying_code = "Evidence = certificate (travels); Checker = consumer-side verifier.",
    epistemic_types = "Proofhood is standpoint-indexed and must be re-established per receiver.",
  },
}
