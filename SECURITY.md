# Security Policy

_Last updated: 2026-06-15 — version 0.1.0 (prototype)_

## Scope and threat model

`epistemic-types` (`hyperpolymath/epistemic-types`) is a small Agda
formalization of standpoint-indexed modal / epistemic / echo-like type
formers. It is a single-tool, library-only project:

- **No runtime.** There is no executable, server, daemon, or service. The
  only "execution" is Agda type-checking the source.
- **No network, no secrets, no I/O.** The library reads no input and writes
  no output beyond what the type-checker reports.
- **No dependencies.** It compiles under `{-# OPTIONS --safe --without-K #-}`
  with **no postulates** and **no Agda standard library** (built with
  `agda --no-libraries`, using only `Agda.Builtin.*` / `Agda.Primitive`).

Because there is no runtime surface, the meaningful "attack surface" is the
**proofs and machine-readable specifications themselves**. A security-relevant
defect here is essentially a *soundness* defect — for example:

- a proof that type-checks but encodes a false or misleading claim;
- an unintended use of a postulate, `--type-in-type`, an `unsafe` pragma, or
  some other escape hatch that would weaken the `--safe --without-K`
  guarantee;
- a flaw in the `ProofTransport` discipline that lets an attestation claim
  more than it should — e.g. something that lets a receiver-bound (designated)
  proof be treated as portable, or a receipt-only artifact be treated as a
  certifying proof, contrary to the `proofNeedsChecker` "no-smuggling"
  invariant. The same applies to the `EchoBridge` graded loss/residue
  accounting and the `SurrealBridge` birthday-tower carriers.
- a divergence between the Agda formalization and its engineering rendering in
  `.machine_readable/proof-transport/` (a2ml / Nickel-k9) that would let the
  machine-readable spec be read as guaranteeing something the proofs do not.

Plain typos, broken imports, or build breakage are ordinary bugs, not security
issues — please raise those as normal issues rather than via this policy.

## Reporting a vulnerability

If you believe you have found a soundness or attestation-discipline defect of
the kind above, please report it **privately first**:

- **Preferred:** open a [GitHub security advisory](https://github.com/hyperpolymath/epistemic-types/security/advisories/new)
  (private) on `hyperpolymath/epistemic-types`.
- **Alternatively:** email **Jonathan D.A. Jewell (hyperpolymath)** at
  **j.d.a.jewell@open.ac.uk** with `[epistemic-types security]` in the
  subject.

Please include the affected module(s) and a minimal Agda snippet (or a
machine-readable excerpt) that demonstrates the issue, if you can.

## Response expectations

This is a prototype maintained by a single author, so timelines are
best-effort rather than contractual:

- **Acknowledgement:** within 7 days.
- **Initial assessment:** within 30 days.
- **Fix or documented decision:** as soon as practicable thereafter. Because
  the remedy for a soundness defect is usually to *correct or withdraw a
  claim* rather than ship a patch to running software, the resolution may take
  the form of a documentation correction, a proof revision, or an honest
  note that a stated property does not hold.

There is no automated CI on this repository (see `AUDIT.adoc`), so
verification is manual: the canonical check is

```
just check   # == agda --no-libraries -i src src/EpistemicTypes/All.agda
```

with **Agda 2.8.0**.

## Supported versions

| Version    | Status    | Supported            |
| ---------- | --------- | -------------------- |
| `main`     | active    | yes                  |
| `0.1.0`    | prototype | yes (current)        |

Only the latest state of `main` and the current `0.1.0` prototype are
maintained. There are no prior released versions to back-port to.

## Coordinated disclosure

Please give a reasonable opportunity to assess and correct an issue before
disclosing it publicly. Good-faith research that follows this policy is
welcome; there will be no legal action against researchers who report
responsibly and avoid privacy violations or destructive testing.

## Related projects

Findings here may also be relevant to sibling formal-methods work in the
estate — in particular `echo-types` (the loss-with-residue formalism that
`EchoBridge` composes with), `ephapax` (sibling formal language with echo
obligations), and the `standards` / `a2ml` / `k9` tooling that
`ProofTransport`'s machine-readable rendering targets. Where appropriate, a
report against one may be cross-referenced to the others.
