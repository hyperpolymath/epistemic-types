# Contributing to epistemic-types

`epistemic-types` is a small, deliberately honest Agda formalization of
standpoint-indexed modal / epistemic / echo-like type formers. It
favours mathematical honesty over a large API. Contributions are
welcome, but the bar is **everything still passes the canonical
`--safe --without-K --cubical-compatible` profile, with no shortcuts**.

- **Author:** Jonathan D.A. Jewell (hyperpolymath)
  [j.d.a.jewell@open.ac.uk](mailto:j.d.a.jewell@open.ac.uk)

- **Version:** 0.1.0 (status: prototype)

- **Last updated:** 2026-11-01

’’’’’

## Contribution model — Tri-Perimeter Contribution Framework (TPCF)

epistemic-types follows the estate-wide **Tri-Perimeter Contribution
Framework (TPCF)** — graduated trust without gatekeeping:

- **Perimeter 1 — Core Systems (maintainers only).** The proof kernel:
  all 22 modules recursively under `src/EpistemicTypes/` (core,
  applications, and Kripke semantics), the `All.agda` wiring, and proof
  tooling.

- **Perimeter 2 — Expert Extensions (trusted contributors).** New
  epistemic/standpoint modules, examples, and bridges. Apply via issue →
  review → merge, with `just` `check` green.

- **Perimeter 3 — Community Sandbox (open to all).** Docs (`.adoc`),
  `.well-known/`, AI manifests, spec proposals.

### Fork workflow

External contributors use the standard **fork**-and-pull-request
workflow: fork the repository, branch from `main`, run `just check`
(the policy gate, all positive modules, and all expected rejections) locally,
and open a PR. Proofs are load-bearing — a red `agda` check blocks merge, and no
`postulate` / `believe_me` shortcuts are accepted.

## Build and check

The combined proof and rejection gate must stay green:

    just check

This runs `tests/check-policy.sh`, checks all 22 source modules recursively,
and validates all 13 expected-rejection fixtures. Deliberate rejection
fixtures stay outside the positive `All.agda` import graph; coverage does not
depend on `All.agda` alone.

Requirements:

- **Agda 2.6.4.3**.

- **No Agda standard library.** The build runs with `--no-libraries`;
  the only external core imports allowed are from `Agda.Builtin.*` and
  `Agda.Primitive`. The optional `tests/integration/CanonicalEcho.agda`
  checks correspondence with actual sibling sources through `just`
  `check-canonical`; its dependencies stay outside the default core
  gate.

`All.agda` imports the full graph, but the gate also checks every source file
independently so an omitted aggregate import cannot hide a module. A change is
not done until `just check` passes with no errors and no warnings.

CI checks every source module, semantic rejection controls and pinned
canonical Echo correspondence. Proof and security gates must pass before
merge; see [docs/ci-safety.adoc](../docs/ci-safety.adoc). Run the local
checks before opening a PR.

’’’’’

## The honesty rules

These are non-negotiable. A PR that breaks any of them will not be
merged.

- **No `postulate`.** Nothing is asserted without proof. If a law holds,
  prove it; if it does not, it is not stated as if it did. Where a law
  is not derivable but is needed, it appears as an explicit *field* the
  caller must supply (see `LawfulModality`, `FactiveModality`,
  `BeliefModality`), so the assumption is visible at the type level
  rather than smuggled in.

- **No standard library in core source.** As above: `Agda.Builtin.*`,
  `Agda.Primitive`, and local modules only. The optional pinned integration is
  a separate boundary.

- **Complete strict profile.** Every first-party module starts with
  `{-# OPTIONS --safe --without-K --cubical-compatible --exact-split
  --no-sized-types --no-guardedness #-}`. The command line repeats the first
  three canonical flags. Do not weaken or partially restate this profile.

- **No too-strong rules.** Keep the interfaces as weak as the proofs
  allow. The base form `E` `:` `K` `→` `Set` `ℓ` `→` `Set` `ℓ` is a
  plain indexed endofunctor (`map` only) — it is **not** a monad or
  comonad, and there is no generic `return`/`reflect`. Do not promote it
  to one. If something needs more structure, add a *named* stronger
  interface (e.g. `ReturnModality`) that callers opt into, and keep the
  base interface untouched.

- **Add lemmas with proofs, not admits.** New results land as complete
  proofs closed with normal Agda terms. No holes (`?`), no admit-shaped
  escapes, no `TERMINATING`/`NON_COVERING` pragmas to paper over gaps.

### Keep the bridges distinct

The library is careful about what is and is not the same thing. Preserve
these separations when extending:

- `Echo` `C` `y` carries a specified residue certificate.
  `MatchesSource` is compatibility, not unique historical provenance.
  `BoundedEcho` measures a residue separately; it is not a retention
  index or an epistemic standpoint.

- A `ReadView` `s` must entail its contents equality. Writes must not
  silently refresh cached values; evidence transport needs its stability
  proof.

- In `ProofTransport`, every proof status must entail its explicit
  `Meaning` via `proofSound`. Preserve the successful-check witness and
  the verifier’s soundness obligation. Public transport needs an
  explicit implication between holder meanings; evidence tokens alone
  never suffice. `just` `check` must pass both the positive library and
  the deliberate type-error regression controls.

’’’’’

## Adding a module or lemma

1.  Put Agda source under `src/EpistemicTypes/` and wire it into
    `src/EpistemicTypes/All.agda` where the full graph requires it. The
    recursive gate will detect the new module; update the explicit 22-module
    policy/metadata inventory in the same change rather than bypassing it.

2.  Open each module with the exact complete strict `OPTIONS` line shown above.

3.  Keep modules small and single-purpose, following the existing core,
    `Applications/`, and `Kripke/` layout.

4.  State assumptions as interface fields, not postulates. Add lawful
    instances only after the laws are proved or explicitly required as
    fields.

5.  Run `just` `check`.

If a change touches the ProofTransport engineering rendering (the
a2ml/k9 attestation target under `.machine_readable/proof-transport/`),
keep the Agda model and the machine-readable description in step.

’’’’’

## Documentation

- **AsciiDoc (`.adoc`) is the default** for documentation. Update the
  relevant `.adoc` file alongside any behavioural or interface change.

- Preserve exact current names and roles: `README.adoc` is the overview,
  `explainme.adoc` the concise narrative, and `EXPLAINME.adoc` the detailed
  claims/evidence ledger.

- Machine-readable descriptions live under `.machine_readable/` (a2ml +
  Nickel/k9). a2ml files use the canonical TOML-like dialect:
  `[section]` headers, `key` `=` `"value"`, arrays `[` `"a",` `"b"` `]`,
  inline tables `{` `k` `=` `"v",` `j` `=` `"w"` `}`.

- Root contribution, conduct, security and changelog documents use
  AsciiDoc. Preserve their existing `.adoc` filenames.

’’’’’

## Commits and pull requests

### Branch naming

    feat/short-description    # new module, interface, or lemma
    fix/short-description     # corrected proof or definition
    docs/short-description    # .adoc / machine-readable docs
    refactor/short-description

### Conventional Commits

Commit messages follow [Conventional
Commits](https://www.conventionalcommits.org/):

    <type>(<scope>): <description>

    [optional body]

    [optional footer]

Typical scopes match the modules: `base`, `warrant`, `access`, `echo`,
`surreal`, `proof-transport`, `docs`.

### Signed commits

Every commit that reaches the default branch must be signed; a ruleset refuses
unsigned pushes. Estate policy:
[SIGNING-POLICY](https://github.com/hyperpolymath/standards/blob/main/docs/SIGNING-POLICY.adoc).

- **People and interactive agents** sign with an SSH key registered on GitHub
  as a *signing* key (`gpg.format=ssh`, `user.signingkey=<key>.pub`,
  `commit.gpgsign=true`). The committer email must be verified on that account.
- **Apps, bots and workflows** never `git push` local commits. They write
  through the API (`createCommitOnBranch` or the estate `signed-push` action)
  so that GitHub signs each commit.
- Merge PRs with **squash**. The ruleset checks every commit on the PR branch,
  not just the result, so one unsigned commit blocks the merge. Re-create such a
  branch with signed commits (`git cherry-pick -S`) and open a new PR.
  Rebase-merge replays commits unsigned and is disabled.

### Before you open a PR

1.  `just` `check` passes — no errors, no warnings.

2.  No `postulate`, no library imports, no `?`/admits, no weakened
    pragmas.

3.  The honesty rules above still hold (weak base interface, distinct
    bridges, no proof-smuggling in transport).

4.  Relevant `.adoc` and `.machine_readable/` files updated.

5.  Commits are conventional and signed.

Keep PRs small and focused — one idea, one proof obligation, easy to
check.

’’’’’

## Licence note

The licence and existing SPDX declarations are owner-managed. Do **not** add,
remove, or alter licence files, SPDX identifiers, or copyright lines without
explicit owner instruction.

’’’’’

## Ecosystem siblings

`epistemic-types` sits alongside (and should stay coherent with) these
estate repos:

- **echo-types** — canonical proof-relevant Echo sibling. The optional pin
  checks representation and one-way lowering; Echo is not a resource instance.
  Audit it before duplicating Echo machinery here.

- **ephapax** — sibling formal language (four-layer redesign with echo
  obligations).

- **standards** — estate RSR/standards, k9-svc, and a2ml tooling.

- **a2ml / k9** — machine-readable + contractile tooling; the
  engineering target for `ProofTransport`.

When a contribution overlaps a sibling (especially echo-types), prefer
reusing or extending it upstream over re-deriving it locally.
