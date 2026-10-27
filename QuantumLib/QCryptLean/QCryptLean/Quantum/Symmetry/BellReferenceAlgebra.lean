import QCryptLean.Math.LinearAlgebra.Matrix.DiagonalFiber
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.BellDickeCore
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Bell
import QCryptLean.Quantum.Symmetry.BellBasis
import QCryptLean.Quantum.Symmetry.BellDephasing
import QCryptLean.Quantum.Symmetry.BellDicke
import QCryptLean.Quantum.Symmetry.BellMixture
import QCryptLean.Quantum.Symmetry.BellReference
import QCryptLean.Quantum.Symmetry.BellSpectrum
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.PairedAlgebra

/-! # Bell Reference Algebra -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped ComplexOrder
open private exists_perm_comp_of_map_eq
  from QCryptLean.Quantum.Symmetry.BellDickeCore

/-- The Bell-sector reference is fixed by Bell twirling. -/
theorem isIIDBellDiagonal_bellDeFinettiDensity (k : ℕ) :
    IsIIDBellDiagonal (bellDeFinettiDensity k).toOp :=
  bellTwirl_idempotent (deFinettiState (Bool × Bool) k).toOp

/-- The Bell reference dominates every permutation-invariant Bell-diagonal sub-density matrix.
The proof uses the native Bell-sector decomposition and reference spectrum. -/
theorem bellSym_subnormalized_marginal_dominated (k : ℕ)
    (A : Op (Fin k → Bool × Bool)) (hA : A.PosSemidef) (htr : A.trace.re ≤ 1)
    (hperm : ∀ σ : Equiv.Perm (Fin k),
      permutationRepresentation σ * A = A * permutationRepresentation σ)
    (hbell : IsIIDBellDiagonal A) :
    ((Nat.choose (k + 3) 3 : ℂ) • (bellDeFinettiState k).toOp - A).PosSemidef := by
  classical
  let V := bellRotation k
  let M := V * A * Vᴴ
  have hM : M.PosSemidef := hA.mul_mul_conjTranspose_same V
  have ht : M.trace.re ≤ 1 := by
    dsimp [M]
    rw [trace_mul_cycle, show Vᴴ * V = 1 from bellRotation_unitary k, Matrix.one_mul]
    exact htr
  have hc (σ : Equiv.Perm (Fin k)) :
      permutationRepresentation (X := Fin 4) σ * V =
        V * permutationRepresentation (X := Bool × Bool) σ :=
    tensorPermutation_mul_piTensorProduct_const σ bellSinglePairRotation
  have hmc (σ : Equiv.Perm (Fin k)) :
      permutationRepresentation (X := Fin 4) σ * M *
        (permutationRepresentation (X := Fin 4) σ)ᴴ = M := by
    let B := permutationRepresentation (X := Fin 4) σ
    let C := permutationRepresentation (X := Bool × Bool) σ
    have hl : B * V = V * C := hc σ
    have hr : Vᴴ * Bᴴ = Cᴴ * Vᴴ := by
      simpa only [conjTranspose_mul] using congrArg Matrix.conjTranspose hl
    change B * (V * A * Vᴴ) * Bᴴ = M
    calc _ = (B * V) * A * (Vᴴ * Bᴴ) := by simp only [Matrix.mul_assoc]
         _ = (V * C) * A * (Cᴴ * Vᴴ) := by rw [hl, hr]
         _ = V * (C * A * Cᴴ) * Vᴴ := by simp only [Matrix.mul_assoc]
         _ = M := by
           rw [show C * A = A * C from hperm σ, Matrix.mul_assoc A C Cᴴ,
             show C * Cᴴ = 1 from (tensorPermutation_unitary σ).2, Matrix.mul_one]
  have horbit (i j : Fin k → Fin 4) (hij : bellTypeOfIndex i = bellTypeOfIndex j) :
      M i i = M j j := by
    obtain ⟨σ, hσ⟩ := exists_perm_comp_of_map_eq (congrArg Subtype.val hij)
    have h := congrFun (congrFun (hmc σ) j) j
    simpa only [tensorPermutation_conj_apply, hσ] using h
  have hd (i : Fin k → Fin 4) :
      0 ≤ symmetricProjector (Fin 4) k i i - M i i := by
    rw [symmetricProjector_apply_eq_typeIndicator, ite_eq_left rfl, sub_nonneg]
    exact hM.diag_le_inv_card_fiber ht bellTypeOfIndex horbit i
  have hdiag : V * A * Vᴴ = diagonal (fun i => M i i) := by
    change bellRotation k * A * (bellRotation k)ᴴ = _
    rw [← hbell, bellRotation_bellTwirl_eq_diagonal]
  let D := ((Nat.choose (k + 3) 3 : ℂ) • (bellDeFinettiState k).toOp - A)
  have he : V * D * Vᴴ = diagonal (fun i => symmetricProjector (Fin 4) k i i - M i i) := by
    change bellRotation k * (((Nat.choose (k + 3) 3 : ℂ) •
      (bellDeFinettiDensity k).toOp) - A) * (bellRotation k)ᴴ = _
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      bellRotation_conj_bellDeFinettiDensity_eq_diagonal, hdiag, ← diagonal_smul,
      ← diagonal_sub]
    congr 2
    funext i
    change (Nat.choose (k + 3) 3 : ℂ) * (_ * _) = _
    rw [← mul_assoc, mul_inv_cancel₀
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega)))), one_mul]
  have hp : (V * D * Vᴴ).PosSemidef := by
    rw [he]
    exact PosSemidef.diagonal hd
  have hh := hp.mul_mul_conjTranspose_same Vᴴ
  rw [conjTranspose_conjTranspose] at hh
  have hs : Vᴴ * (V * D * Vᴴ) * V = D := by
    calc _ = (Vᴴ * V) * D * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
         _ = D := by rw [show Vᴴ * V = 1 from bellRotation_unitary k,
           Matrix.one_mul, Matrix.mul_one]
  rwa [hs] at hh

end Quantum.Symmetry
