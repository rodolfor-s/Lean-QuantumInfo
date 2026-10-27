import QCryptLean.Math.CodingTheory.LinearCodes

/-!
# Binary Pauli error patterns

Pairs of binary patterns and their Hamming weights.
-/

open Math.CodingTheory

namespace Math.CodingTheory.CSS

/-- Specification of a Pauli error on n qubits.
    xPattern i = 1 means qubit i has an X error.
    zPattern i = 1 means qubit i has a Z error. -/
structure PauliError (n : ℕ) where
  /-- Binary support pattern of the Pauli X (bit-flip) component. -/
  xPattern : Fin n → ZMod 2
  /-- Binary support pattern of the Pauli Z (phase-flip) component. -/
  zPattern : Fin n → ZMod 2

/-- Number of X (bit flip) errors -/
def PauliError.xWeight {n : ℕ} (e : PauliError n) : ℕ :=
  hammingWeight e.xPattern

/-- Number of Z (phase flip) errors -/
def PauliError.zWeight {n : ℕ} (e : PauliError n) : ℕ :=
  hammingWeight e.zPattern

/-- The identity (no error) -/
def PauliError.identity (n : ℕ) : PauliError n :=
  ⟨fun _ => 0, fun _ => 0⟩

/-- Identity error has zero weight -/
theorem PauliError.identity_xWeight (n : ℕ) : (PauliError.identity n).xWeight = 0 := by
  simp [identity, xWeight, hammingWeight]

theorem PauliError.identity_zWeight (n : ℕ) : (PauliError.identity n).zWeight = 0 := by
  simp [identity, zWeight, hammingWeight]

end Math.CodingTheory.CSS
