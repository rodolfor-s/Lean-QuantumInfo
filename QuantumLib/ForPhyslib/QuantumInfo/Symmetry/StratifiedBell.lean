import QuantumLib.ForMathlib.LinearAlgebra.Matrix.PiTensorProduct
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.BellMixture
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.Stratified

/-!
# Bell diagonality on a stratified register

The quantum register is a dependent family of Boolean-pair function registers.
Its Bell labels form a separate dependent family with `Fin 4` as classical labels.
-/

namespace Quantum.Symmetry

open Matrix Quantum.Operators

/-- Independent Bell-basis rotations in each stratum, with distinct row and column types. -/
noncomputable def stratifiedBellRotation {k : ℕ} (n : Fin k → ℕ) :
    Matrix ((j : Fin k) → Fin (n j) → Fin 4) ((j : Fin k) → Fin (n j) → Bool × Bool) ℂ :=
  piTensorProduct (fun j => bellRotation (n j))

/-- Diagonality in the actual product of the stratum Bell bases. -/
def IsStratifiedBellDiagonal {k : ℕ} (n : Fin k → ℕ)
    (A : Op ((j : Fin k) → Fin (n j) → Bool × Bool)) : Prop :=
  ∀ i j, i ≠ j → (stratifiedBellRotation n * A * (stratifiedBellRotation n)ᴴ) i j = 0

end Quantum.Symmetry
