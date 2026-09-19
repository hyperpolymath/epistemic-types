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
             (gnu packages bash))

(package
  (name "epistemic-types")
  (version "0.1.0")
  (source #f)
  (build-system gnu-build-system)
  (inputs (list agda ghc coreutils bash make))
  (synopsis "epistemic-types")
  (description "epistemic-types — part of the hyperpolymath ecosystem.")
  (home-page "https://github.com/hyperpolymath/epistemic-types")
  (license ((@@ (guix licenses) license) "MPL-2.0" "https://github.com/hyperpolymath/palimpsest-license")))
