import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Twirl

/-!
# Pauli and Bell constructions on Boolean qubits

A qubit has basis `Bool`, a pair has basis `Bool × Bool`, and a repeated pair
register has basis `Fin k → Bool × Bool`. The four-valued Pauli label is a
classical finite label, not an encoding of the quantum register.
-/

noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators Quantum.Channels
open scoped Kronecker ComplexOrder

/-- The bit-flip Pauli matrix in the Boolean basis. -/
def pauliX : Op Bool := of fun a b => if a = !b then 1 else 0

/-- The phase-flip Pauli matrix in the Boolean basis. -/
def pauliZ : Op Bool := diagonal fun a => if a then -1 else 1

/-- The imaginary Pauli matrix in the Boolean basis. -/
def pauliY : Op Bool := of fun a b => if a = b then 0 else if a then Complex.I else -Complex.I

/-- The four Pauli matrices, labelled in the order `I, X, Y, Z`. -/
def pauli : Fin 4 → Op Bool := ![1, pauliX, pauliY, pauliZ]

/-- Pauli matrices are unitary, by their Boolean entries. -/
theorem pauli_unitary (a : Fin 4) : (pauli a)ᴴ * pauli a = 1 := by
  ext i j
  fin_cases a <;> cases i <;> cases j <;>
    norm_num [pauli, pauliX, pauliY, pauliZ, mul_apply, Fintype.sum_bool,
      conjTranspose_apply, diagonal_apply, one_apply]

/-- The paired action of the same Pauli on both qubits. -/
def bilateralPauli (a : Fin 4) : Op (Bool × Bool) := pauli a ⊗ₖ pauli a

/-- Bilateral Pauli matrices are unitary. -/
theorem bilateralPauli_unitary (a : Fin 4) : (bilateralPauli a)ᴴ * bilateralPauli a = 1 := by
  rw [bilateralPauli, conjTranspose_kronecker, ← mul_kronecker_mul,
    pauli_unitary, one_kronecker_one]

/-- The independent per-site bilateral Pauli action. -/
def bellTwirlUnitary {k : ℕ} (g : Fin k → Fin 4) : UnitaryOp (Fin k → Bool × Bool) :=
  ⟨piTensorProduct (fun i => bilateralPauli (g i)), mem_unitaryGroup_iff'.mpr (by
    change (piTensorProduct (fun i => bilateralPauli (g i)))ᴴ * _ = _
    rw [conjTranspose_piTensorProduct, piTensorProduct_mul]
    simp only [bilateralPauli_unitary, piTensorProduct_one])⟩

/-- The independent bilateral-Pauli twirl is a linear channel. -/
def bellTwirl (k : ℕ) : Operation (Fin k → Bool × Bool) (Fin k → Bool × Bool) :=
  twirl bellTwirlUnitary

/-- Bell twirling is completely positive and trace preserving. -/
theorem isChannel_bellTwirl (k : ℕ) : IsChannel (bellTwirl k) := isChannel_twirl _

/-- Bell twirling preserves trace on every matrix. -/
theorem trace_bellTwirl {k : ℕ} (A : Op (Fin k → Bool × Bool)) :
    (bellTwirl k A).trace = A.trace := (isChannel_bellTwirl k).2 A

/-- Bell twirling preserves positivity. -/
theorem posSemidef_bellTwirl {k : ℕ} {A : Op (Fin k → Bool × Bool)} (h : A.PosSemidef) :
    (bellTwirl k A).PosSemidef := (isChannel_bellTwirl k).1.posSemidef h

/-- Joint Bell diagonality as the fixed-point condition for independent Pauli twirling. -/
def IsIIDBellDiagonal {k : ℕ} (A : Op (Fin k → Bool × Bool)) : Prop := bellTwirl k A = A

/-- The Bell ket with labels `(phase, bit)`, with the phase label as the first component. -/
def bellKet (phase bit : Bool) : Ket (Bool × Bool) :=
  ⟨fun p => if p.2 = xor p.1 bit then
    (1 / Real.sqrt 2 : ℂ) * (if phase && p.1 then -1 else 1) else 0⟩

/-- Permuting the sites relabels the Pauli string. -/
theorem bellTwirlUnitary_perm_conj {k : ℕ} (σ : Equiv.Perm (Fin k)) (g : Fin k → Fin 4) :
    permutationRepresentation σ * (bellTwirlUnitary g).val * (permutationRepresentation σ)ᴴ =
      (bellTwirlUnitary (g ∘ σ.symm)).val :=
  tensorPermutation_conj_piTensorProduct σ (fun i => bilateralPauli (g i))

/-- Bell twirling commutes with a permutation of the sites on every operator. -/
theorem bellTwirl_perm_conj {k : ℕ} (σ : Equiv.Perm (Fin k))
    (M : Op (Fin k → Bool × Bool)) :
    bellTwirl k (permutationRepresentation σ * M * (permutationRepresentation σ)ᴴ) =
      permutationRepresentation σ * bellTwirl k M * (permutationRepresentation σ)ᴴ := by
  let U := permutationRepresentation (X := Bool × Bool) σ
  have hs (g : Fin k → Fin 4) :
      (bellTwirlUnitary g).val * U = U * (bellTwirlUnitary (g ∘ σ)).val := by
    have h := bellTwirlUnitary_perm_conj σ (g ∘ σ)
    have he : (g ∘ σ) ∘ σ.symm = g := by ext i; simp
    rw [he] at h
    calc _ = (U * (bellTwirlUnitary (g ∘ σ)).val * Uᴴ) * U := by rw [h]
         _ = _ := by rw [Matrix.mul_assoc, (tensorPermutation_unitary σ).1, Matrix.mul_one]
  simp only [bellTwirl, twirl_apply, Matrix.mul_smul, Matrix.smul_mul]
  apply congrArg ((Fintype.card (Fin k → Fin 4) : ℂ)⁻¹ • ·)
  rw [Matrix.mul_sum, Matrix.sum_mul]
  rw [← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin 4)))
    (fun g => U * ((bellTwirlUnitary g).val * M * (bellTwirlUnitary g).valᴴ) * Uᴴ)]
  apply Finset.sum_congr rfl
  intro g _
  have he : (Equiv.arrowCongr σ.symm (Equiv.refl (Fin 4))) g = g ∘ σ := rfl
  rw [he]
  have hh : Uᴴ * (bellTwirlUnitary g).valᴴ =
      (bellTwirlUnitary (g ∘ σ)).valᴴ * Uᴴ := by
    simpa only [conjTranspose_mul] using congrArg Matrix.conjTranspose (hs g)
  calc _ = ((bellTwirlUnitary g).val * U) * M * (Uᴴ * (bellTwirlUnitary g).valᴴ) := by
             simp only [U, Matrix.mul_assoc]
       _ = (U * (bellTwirlUnitary (g ∘ σ)).val) * M *
           ((bellTwirlUnitary (g ∘ σ)).valᴴ * Uᴴ) := by rw [hs, hh]
       _ = _ := by simp only [Matrix.mul_assoc]

end Quantum.Symmetry
