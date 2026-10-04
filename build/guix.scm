;; SPDX-License-Identifier: MPL-2.0
;; Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
;;
;; Guix development environment for epistemic-types. Replaces flake.nix (Guix-only policy).
;; Usage: guix shell -D -f build/guix.scm

(use-modules (guix packages)
             (guix build-system gnu)
             (gnu packages agda)
             (gnu packages haskell)
             (gnu packages base)
             (gnu packages bash)
             (gnu packages rust-apps))

;; Development environment for the proof gates.
;;
;; Entry point:  guix shell -D -f build/guix.scm -- bash scripts/check.sh
;;
;; `scripts/check.sh` falls back to this environment when no Agda is on PATH.
;; The Agda in Guix may differ from the version CI pins (2.6.4.3); the script
;; reports the version it uses. ripgrep and findutils are required by
;; tests/check-rejections.sh and tests/check-proofs.sh.
(package
  (name "epistemic-types")
  (version "0.1.0")
  (source #f)
  (build-system gnu-build-system)
  (inputs (list agda ghc coreutils findutils ripgrep bash make))
  (synopsis "epistemic-types")
  (description "epistemic-types — part of the hyperpolymath ecosystem.")
  (home-page "https://github.com/hyperpolymath/epistemic-types")
  (license ((@@ (guix licenses) license) "MPL-2.0" "https://github.com/hyperpolymath/palimpsest-license")))
