# Contributing to epistemic-types

`epistemic-types` is a small, deliberately honest Agda formalization of
standpoint-indexed modal / epistemic / echo-like type formers. It favours
mathematical honesty over a large API. Contributions are welcome, but the bar
is **everything still type-checks under `--safe --without-K`, with no shortcuts**.

- **Author:** Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
- **Version:** 0.1.0 (status: prototype)
- **Last updated:** 2026-06-15

---

## Build and check

There is exactly one thing to run, and it must stay green:

```
just check
```

which is:

```
agda --no-libraries -i src src/EpistemicTypes/All.agda
```

Requirements:

- **Agda 2.8.0**.
- **No Agda standard library.** The build runs with `--no-libraries`; the only
  imports allowed are from `Agda.Builtin.*` and `Agda.Primitive`. Do not add a
  dependency on `agda-stdlib` or any other library.

`All.agda` re-exports every module, so `just check` checks the whole library.
A change is not done until `just check` passes with no errors and no warnings.

There is no CI (see `AUDIT.adoc` / repo notes — CI is not enabled). The
type-checker run above is the gate. Run it locally before opening a PR.

---

## The honesty rules

These are non-negotiable. A PR that breaks any of them will not be merged.

- **No `postulate`.** Nothing is asserted without proof. If a law holds, prove
  it; if it does not, it is not stated as if it did. Where a law is not
  derivable but is needed, it appears as an explicit *field* the caller must
  supply (see `LawfulModality`, `FactiveModality`, `BeliefModality`), so the
  assumption is visible at the type level rather than smuggled in.
- **No standard library.** As above: `Agda.Builtin.*` and `Agda.Primitive` only.
- **`--safe --without-K`.** Every module compiles under
  `{-# OPTIONS --safe --without-K #-}`. This rules out `postulate`, unsafe
  pragmas, axiom K, and `--type-in-type`. Do not weaken these options.
- **No too-strong rules.** Keep the interfaces as weak as the proofs allow. The
  base form `E : K → Set ℓ → Set ℓ` is a plain indexed endofunctor (`map` only)
  — it is **not** a monad or comonad, and there is no generic `return`/`reflect`.
  Do not promote it to one. If something needs more structure, add a *named*
  stronger interface (e.g. `ReturnModality`) that callers opt into, and keep the
  base interface untouched.
- **Add lemmas with proofs, not admits.** New results land as complete proofs
  closed with normal Agda terms. No holes (`?`), no admit-shaped escapes, no
  `TERMINATING`/`NON_COVERING` pragmas to paper over gaps.

### Keep the bridges distinct

The library is careful about what is and is not the same thing. Preserve these
separations when extending:

- `Echo r A` (the min-plus graded loss/residue in `EchoBridge`) is **not**
  `E κ A`. Keep the echo bridge separate; do not collapse it into the modality,
  and do not import a full graded comonad to get it.
- In `ProofTransport`, the no-smuggling discipline is the point: `transmit`
  downgrades a sender's `Proof` to a receiver's `Receipt`; `verify` upgrades
  `Data → Proof` only with the receiver's **own** checker and evidence; public
  proofs are portable, designated ones are receiver-bound, and a receipt alone
  never certifies (`proofNeedsChecker`). Any new transport rule must respect
  these — no rule that lets one agent's `Proof` become another's without the
  receiver's own checker.

---

## Adding a module or lemma

1. Put Agda source under `src/EpistemicTypes/` and add the new module to the
   `import`/re-export list in `src/EpistemicTypes/All.agda` so `just check`
   covers it.
2. Open each module with `{-# OPTIONS --safe --without-K #-}`.
3. Keep modules small and single-purpose, mirroring the existing layout:
   `Base`, `Warrant`, `Access`, `EchoBridge`, `SurrealBridge`, `ProofTransport`,
   `ProofTransportExample`, `Examples`.
4. State assumptions as interface fields, not postulates. Add lawful instances
   only after the laws are proved or explicitly required as fields.
5. Run `just check`.

If a change touches the ProofTransport engineering rendering (the a2ml/k9
attestation target under `.machine_readable/proof-transport/`), keep the Agda
model and the machine-readable description in step.

---

## Documentation

- **AsciiDoc (`.adoc`) is the default** for documentation. Update the relevant
  `.adoc` file alongside any behavioural or interface change.
- Existing docs keep their current lowercase names: `readme.adoc` and
  `explainme.adoc`. Do **not** rename or duplicate them.
- Machine-readable descriptions live under `.machine_readable/` (a2ml +
  Nickel/k9). a2ml files use the canonical TOML-like dialect: `[section]`
  headers, `key = "value"`, arrays `[ "a", "b" ]`, inline tables
  `{ k = "v", j = "w" }`.
- Only these files may be Markdown (GitHub community-health special-casing):
  `CONTRIBUTING.md`, `CODE_OF_CONDUCT.md`, `SECURITY.md`, `CHANGELOG.md`.
  Everything else is `.adoc`.

---

## Commits and pull requests

### Branch naming

```
feat/short-description    # new module, interface, or lemma
fix/short-description     # corrected proof or definition
docs/short-description    # .adoc / machine-readable docs
refactor/short-description
```

### Conventional Commits

Commit messages follow [Conventional Commits](https://www.conventionalcommits.org/):

```
<type>(<scope>): <description>

[optional body]

[optional footer]
```

Typical scopes match the modules: `base`, `warrant`, `access`, `echo`,
`surreal`, `proof-transport`, `docs`.

### Signed commits

All commits must be **signed**. Use the existing SSH/GPG signing key; do not
create new keys. Verify with:

```
git log --show-signature
```

Unsigned commits will be asked to be re-signed before merge.

### Before you open a PR

1. `just check` passes — no errors, no warnings.
2. No `postulate`, no library imports, no `?`/admits, no weakened pragmas.
3. The honesty rules above still hold (weak base interface, distinct bridges,
   no proof-smuggling in transport).
4. Relevant `.adoc` and `.machine_readable/` files updated.
5. Commits are conventional and signed.

Keep PRs small and focused — one idea, one proof obligation, easy to check.

---

## Licence note

The licence is owner-managed. Do **not** add `LICENSE`,
`SPDX-License-Identifier` headers, or copyright header lines in a PR. The repo
is currently SPDX-free and stays consistent; licensing is handled separately by
the owner.

---

## Ecosystem siblings

`epistemic-types` sits alongside (and should stay coherent with) these estate
repos:

- **echo-types** — Agda loss-with-residue formalism; `EchoBridge` composes with
  it. Audit it before duplicating echo machinery here.
- **ephapax** — sibling formal language (four-layer redesign with echo
  obligations).
- **standards** — estate RSR/standards, k9-svc, and a2ml tooling.
- **a2ml / k9** — machine-readable + contractile tooling; the engineering target
  for `ProofTransport`.

When a contribution overlaps a sibling (especially echo-types), prefer reusing
or extending it upstream over re-deriving it locally.
