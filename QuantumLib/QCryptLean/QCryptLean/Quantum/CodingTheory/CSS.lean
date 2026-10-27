import QCryptLean.Math.CodingTheory.CSS.Codes
import QCryptLean.Math.CodingTheory.CSS.ErrorModel
import QCryptLean.Math.CodingTheory.LinearCodes
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Symmetry.Bell

/-!
# CSS errors and stabilized code spaces on Boolean words

The classical binary code retains its ordered positions. Quantum operators act
on Boolean functions of those positions, without encoding a word as a number.
-/

noncomputable section

namespace Quantum.CodingTheory

open Matrix Quantum.Operators Quantum.Symmetry Math.CodingTheory.CSS

/-- The single-qubit operator `X^a Z^b`, in computational Boolean coordinates. -/
def singleQubitPauli (a b : ZMod 2) : Op Bool :=
  (if a = 0 then 1 else pauliX) * (if b = 0 then 1 else pauliZ)

/-- Single-qubit Pauli errors preserve inner products. -/
theorem singleQubitPauli_unitary (a b : ZMod 2) :
    (singleQubitPauli a b)ᴴ * singleQubitPauli a b = 1 := by
  have hx : (if a = 0 then (1 : Op Bool) else pauliX)ᴴ *
      (if a = 0 then 1 else pauliX) = 1 := by
    split_ifs
    · simp
    · exact pauli_unitary 1
  have hz : (if b = 0 then (1 : Op Bool) else pauliZ)ᴴ *
      (if b = 0 then 1 else pauliZ) = 1 := by
    split_ifs
    · simp
    · exact pauli_unitary 3
  unfold singleQubitPauli
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (if b = 0 then 1 else pauliZ),
    hx, Matrix.one_mul, hz]

/-- A Pauli error acts independently at each ordered position. -/
def pauliErrorOp {n : ℕ} (e : PauliError n) : Op (Fin n → Bool) :=
  piTensorProduct (fun i => singleQubitPauli (e.xPattern i) (e.zPattern i))

/-- Tensor products of Pauli errors are unitary, also for zero qubits. -/
theorem pauliErrorOp_unitary {n : ℕ} (e : PauliError n) :
    (pauliErrorOp e)ᴴ * pauliErrorOp e = 1 := by
  rw [pauliErrorOp, conjTranspose_piTensorProduct, piTensorProduct_mul]
  simp only [singleQubitPauli_unitary, piTensorProduct_one]

/-- The CSS code space is the common fixed space of its X and Z stabilizers. -/
def InCodeSpace {n : ℕ} (code : CSSCode n) (ψ : Ket (Fin n → Bool)) : Prop :=
  (∀ w, w ∈ code.C2.codewords → pauliErrorOp ⟨w, fun _ => 0⟩ * ψ = ψ) ∧
  (∀ v, v ∈ code.C1.dual → pauliErrorOp ⟨fun _ => 0, v⟩ * ψ = ψ)

end Quantum.CodingTheory
