{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}

-- A small authority/history model, not cryptographic or filesystem verification.
-- Nat represents exact model artifact identity, NOT a collision-free hash.
module EpistemicTypes.Applications.ApprovalSeal where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

data Impossible : Set where

private
  cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
  cong f refl = refl

  trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
  trans refl q = q

  sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
  sym refl = refl

  false-not-true : false ≡ true -> Impossible
  false-not-true ()

same : Nat -> Nat -> Bool
same zero zero = true
same zero (suc _) = false
same (suc _) zero = false
same (suc x) (suc y) = same x y

same-reflexive : (x : Nat) -> same x x ≡ true
same-reflexive zero = refl
same-reflexive (suc x) = same-reflexive x

same-sound : (x y : Nat) -> same x y ≡ true -> x ≡ y
same-sound zero zero _ = refl
same-sound zero (suc _) ()
same-sound (suc _) zero ()
same-sound (suc x) (suc y) p = cong suc (same-sound x y p)

record State : Set where
  constructor state
  field
    anchor : Nat
    artifact : Nat
    localReference : Nat
    broken : Bool
open State public

-- These are ALL agent actions in this model. There is no reset or reanchor.
-- Record constructors are public: the theorem concerns traces from a fixed
-- initial state, not arbitrary records supplied by an untrusted caller.
data AgentAction : Set where
  writeArtifact : Nat -> AgentAction
  writeLocalReference : Nat -> AgentAction

step : AgentAction -> State -> State
step (writeArtifact x) s = state (anchor s) x (localReference s) true
step (writeLocalReference x) s = state (anchor s) (artifact s) x (broken s)

run : List AgentAction -> State -> State
run [] s = s
run (a ∷ rest) s = run rest (step a s)

initial : Nat -> State
initial x = state x x x false

data Verdict : Set where
  accepted mismatch sealBroken : Verdict

matchVerdict : Bool -> Verdict
matchVerdict true = accepted
matchVerdict false = mismatch

gate : State -> Verdict
gate (state a x _ false) = matchVerdict (same x a)
gate (state _ _ _ true) = sealBroken

-- A deliberately inadequate comparator: both arguments are agent-writable.
localGate : State -> Bool
localGate s = same (artifact s) (localReference s)

-- A protected endpoint comparator still cannot detect intermediate writes.
endpointGate : State -> Bool
endpointGate s = same (artifact s) (anchor s)

private
  match-accepted : (b : Bool) -> matchVerdict b ≡ accepted -> b ≡ true
  match-accepted true _ = refl
  match-accepted false ()

-- AS-1: acceptance binds the exact model artifact to the protected anchor.
accepted-matches-anchor : (s : State) -> gate s ≡ accepted -> artifact s ≡ anchor s
accepted-matches-anchor (state a x _ false) p = same-sound x a (match-accepted (same x a) p)
accepted-matches-anchor (state _ _ _ true) ()

-- AS-2: an accepted state has an intact seal.
accepted-is-unbroken : (s : State) -> gate s ≡ accepted -> broken s ≡ false
accepted-is-unbroken (state _ _ _ false) _ = refl
accepted-is-unbroken (state _ _ _ true) ()

step-preserves-anchor : (a : AgentAction) (s : State) -> anchor (step a s) ≡ anchor s
step-preserves-anchor (writeArtifact _) _ = refl
step-preserves-anchor (writeLocalReference _) _ = refl

-- AS-3: no finite agent trace changes the protected authority.
run-preserves-anchor : (actions : List AgentAction) (s : State) -> anchor (run actions s) ≡ anchor s
run-preserves-anchor [] _ = refl
run-preserves-anchor (a ∷ rest) s = trans (run-preserves-anchor rest (step a s)) (step-preserves-anchor a s)

-- AS-4: the accepted endpoint of any trace is bound to its ORIGINAL anchor.
accepted-trace-matches-original : (actions : List AgentAction) (s : State) ->
  gate (run actions s) ≡ accepted -> artifact (run actions s) ≡ anchor s
accepted-trace-matches-original actions s p =
  trans (accepted-matches-anchor (run actions s) p) (run-preserves-anchor actions s)

step-keeps-broken : (a : AgentAction) (s : State) -> broken s ≡ true -> broken (step a s) ≡ true
step-keeps-broken (writeArtifact _) _ _ = refl
step-keeps-broken (writeLocalReference _) _ p = p

-- AS-5: once broken, all subsequent agent traces leave the seal broken.
run-keeps-broken : (actions : List AgentAction) (s : State) -> broken s ≡ true -> broken (run actions s) ≡ true
run-keeps-broken [] _ p = p
run-keeps-broken (a ∷ rest) s p = run-keeps-broken rest (step a s) (step-keeps-broken a s p)

-- AS-6: any observed artifact write prevents acceptance after ANY continuation.
write-prevents-acceptance : (x : Nat) (rest : List AgentAction) (s : State) ->
  gate (run rest (step (writeArtifact x) s)) ≡ accepted -> Impossible
write-prevents-acceptance x rest s p = false-not-true
  (trans (sym (accepted-is-unbroken (run rest (step (writeArtifact x) s)) p))
    (run-keeps-broken rest (step (writeArtifact x) s) refl))

-- AS-7: regenerating the local reference cannot affect the protected verdict.
local-reseal-irrelevant : (x : Nat) (s : State) -> gate (step (writeLocalReference x) s) ≡ gate s
local-reseal-irrelevant _ (state _ _ _ false) = refl
local-reseal-irrelevant _ (state _ _ _ true) = refl

-- AS-8: positive control; the gate does not achieve safety by rejecting all.
initial-accepted : (x : Nat) -> gate (initial x) ≡ accepted
initial-accepted x = cong matchVerdict (same-reflexive x)

-- Concrete attacks and limits. These are checked reductions, not crypto tests.
resealed : State
resealed = run (writeArtifact 1 ∷ writeLocalReference 1 ∷ []) (initial 0)

local-reseal-fools-local-gate : localGate resealed ≡ true
local-reseal-fools-local-gate = refl

local-reseal-breaks-protected-seal : gate resealed ≡ sealBroken
local-reseal-breaks-protected-seal = refl

restored : State
restored = run (writeArtifact 1 ∷ writeArtifact 0 ∷ []) (initial 0)

restoration-fools-endpoint-gate : endpointGate restored ≡ true
restoration-fools-endpoint-gate = refl

restoration-does-not-repair-seal : gate restored ≡ sealBroken
restoration-does-not-repair-seal = refl

-- An actor allowed to replace the root AND the history can manufacture a new
-- accepted state. This is outside AgentAction, and an explicit trust boundary.
replacement-root-is-accepted : gate (state 1 1 1 false) ≡ accepted
replacement-root-is-accepted = refl
