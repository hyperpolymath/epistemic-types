{-# OPTIONS --safe --without-K #-}
module InventedMigration where
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import EpistemicTypes.EchoBridge
import EpistemicTypes.ContinuityExamples as Examples
open Examples.Residues using (firstRetention)
forged : Migration firstRetention snd
Migration.migrate forged _ residue = residue
Migration.adequate forged (true , false) = refl
Migration.adequate forged (true , true) = refl
Migration.adequate forged (false , false) = refl
Migration.adequate forged (false , true) = refl
