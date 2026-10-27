import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor

/-!
# Scalar costs in finite-key security

Key-length costs are measured in bits. The postselection prefactor is the symmetric-subspace
dimension `Math.Combinatorics.deFinettiPrefactor`, also denoted `g_{n,d}` in the literature.
-/

noncomputable section

namespace InfoTheory.Security

/-- Collision error of an independently seeded two-universal verification tag of `bits` bits. -/
def verificationError (bits : ℕ) : ℝ := (2 : ℝ) ^ (-(bits : ℝ))

/-- Purification cost `2 log₂ g_{n,d}` in bits for a postselection reference of dimension `g`. -/
def postselectionCost (d n : ℕ) : ℝ :=
  2 * Real.logb 2 (Math.Combinatorics.deFinettiPrefactor d n : ℝ)

/-- Leftover-hashing cost in bits when the trace-distance error is at most `εPA`.
The subtraction of two comes from the factor `1/2` in trace distance. -/
def privacyAmplificationCost (εPA : ℝ) : ℝ := 2 * Real.logb 2 (1 / εPA) - 2

/-- Trace-distance contribution of a rejected-state weight bounded by `εAT`. -/
def acceptanceError (εAT : ℝ) : ℝ := 2 * Real.sqrt (2 * εAT)

/-- Trace-distance contribution of smoothing with purified-distance radius `ε`. -/
def smoothingError (ε : ℝ) : ℝ := 2 * ε

end InfoTheory.Security
