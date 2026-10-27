import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Bell
import QCryptLean.Quantum.Symmetry.BellDephasing
import QCryptLean.Quantum.Symmetry.BellDicke
import QCryptLean.Quantum.Symmetry.BellDoubling
import QCryptLean.Quantum.Symmetry.BellMixture
import QCryptLean.Quantum.Symmetry.BellReference
import QCryptLean.Quantum.Symmetry.Dimension

/-! # Bell Spectrum -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder

/-- The Bell reference is diagonal in Bell coordinates. -/
theorem bellRotation_conj_bellDeFinettiDensity_eq_diagonal (k : ℕ) :
    bellRotation k * (bellDeFinettiDensity k).toOp * (bellRotation k)ᴴ =
      diagonal (fun i => ((k + 3).choose 3 : ℂ)⁻¹ * symmetricProjector (Fin 4) k i i) := by
  let P := symmetricProjector (Bool × Bool) k
  have ht : P.trace = ((k + 3).choose 3 : ℂ) := by
    apply Complex.ext
    · change (symmetricProjector (Bool × Bool) k).trace.re = _
      rw [Quantum.Symmetry.symmetricSubspace_dim]
      norm_num [Fintype.card_prod, Nat.add_sub_assoc]
    · simpa using (Complex.nonneg_iff.mp
        (symmetricProjector_posSemidef (X := Bool × Bool) (k := k)).trace_nonneg).2.symm
  have hp : bellRotation k * P * (bellRotation k)ᴴ = symmetricProjector (Fin 4) k := by
    rw [show P = (bellRotation k)ᴴ * symmetricProjector (Fin 4) k * bellRotation k from
      (bellRotation_conjTranspose_symmetricProjector k).symm]
    calc
      _ = (bellRotation k * (bellRotation k)ᴴ) * symmetricProjector (Fin 4) k *
          (bellRotation k * (bellRotation k)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [bellRotation_mul_conjTranspose, Matrix.one_mul, Matrix.mul_one]
  change bellRotation k * bellTwirl k (P.trace⁻¹ • P) * (bellRotation k)ᴴ = _
  rw [ht, map_smul, Matrix.mul_smul, Matrix.smul_mul, bellRotation_bellTwirl_eq_diagonal]
  change ((k + 3).choose 3 : ℂ)⁻¹ • diagonal (fun i => (bellRotation k * P *
    (bellRotation k)ᴴ) i i) = _
  rw [hp]
  exact (diagonal_smul _ _).symm

/-- The square root of the Bell reference has the explicit occupation-multiplicity spectrum. -/
theorem sqrt_bellDeFinettiDensity_eq_conj_diagonal (k : ℕ) :
    CFC.sqrt (bellDeFinettiDensity k).toOp =
      (bellRotation k)ᴴ * diagonal (fun i =>
        (Real.sqrt (((k + 3).choose 3 : ℝ)⁻¹ *
          (bellTypeMult k (bellTypeOfIndex i) : ℝ)⁻¹) : ℂ)) * bellRotation k := by
  set sDg : (Fin k → Fin 4) → ℂ := fun i => (Real.sqrt (((k + 3).choose 3 : ℝ)⁻¹ *
    (bellTypeMult k (bellTypeOfIndex i) : ℝ)⁻¹) : ℂ) with hsDgdef
  set S : Op (Fin k → Bool × Bool) :=
    (bellRotation k)ᴴ * Matrix.diagonal sDg * bellRotation k with hSdef
  have hnn : (0 : (Fin k → Fin 4) → ℂ) ≤ sDg := by
    intro i; exact Complex.zero_le_real.mpr (Real.sqrt_nonneg _)
  have hSpsd : S.PosSemidef := by
    have h := (Matrix.PosSemidef.diagonal hnn).mul_mul_conjTranspose_same (bellRotation k)ᴴ
    rwa [Matrix.conjTranspose_conjTranspose] at h
  have hDD : Matrix.diagonal sDg * Matrix.diagonal sDg
      = Matrix.diagonal (fun i => ((k + 3).choose 3 : ℂ)⁻¹ * symmetricProjector (Fin 4) k i i) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [symmetricProjector_apply_eq_typeIndicator, ite_eq_left rfl, hsDgdef]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  have hSS : S * S = (bellDeFinettiDensity k).toOp := by
    have hRRc : bellRotation k * (bellRotation k)ᴴ = 1 := bellRotation_mul_conjTranspose k
    have hcalc : S * S = (bellRotation k)ᴴ *
        (Matrix.diagonal sDg * Matrix.diagonal sDg) * bellRotation k := by
      rw [hSdef]
      rw [show (bellRotation k)ᴴ * Matrix.diagonal sDg * bellRotation k *
            ((bellRotation k)ᴴ * Matrix.diagonal sDg * bellRotation k)
          = (bellRotation k)ᴴ * Matrix.diagonal sDg * (bellRotation k * (bellRotation k)ᴴ) *
              Matrix.diagonal sDg * bellRotation k from by simp only [Matrix.mul_assoc],
        hRRc, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    rw [hcalc, hDD]
    have hdiag := bellRotation_conj_bellDeFinettiDensity_eq_diagonal k
    rw [show (bellRotation k)ᴴ *
          Matrix.diagonal (fun i => ((k + 3).choose 3 : ℂ)⁻¹ * symmetricProjector (Fin 4) k i i) *
          bellRotation k
        = (bellRotation k)ᴴ * (bellRotation k * (bellDeFinettiDensity k).toOp *
            (bellRotation k)ᴴ) * bellRotation k from by rw [hdiag]]
    rw [show (bellRotation k)ᴴ * (bellRotation k * (bellDeFinettiDensity k).toOp *
            (bellRotation k)ᴴ) * bellRotation k
          = ((bellRotation k)ᴴ * bellRotation k) * (bellDeFinettiDensity k).toOp *
              ((bellRotation k)ᴴ * bellRotation k) from by simp only [Matrix.mul_assoc],
      bellRotation_unitary, Matrix.one_mul, Matrix.mul_one]
  exact CFC.sqrt_unique hSS hSpsd.nonneg

/-- Each type-coherent Kraus operator is its type projector times the scalar square root. -/
theorem bellPairedKraus_eq_smul (k : ℕ) (T : Sym (Fin 4) k) :
    bellPairedKraus k T
      = (Real.sqrt (((k + 3).choose 3 : ℝ)⁻¹ * (bellTypeMult k T : ℝ)⁻¹) : ℂ) •
          bellTypeProjector k T := by
  rw [bellPairedKraus, sqrt_bellDeFinettiDensity_eq_conj_diagonal, bellTypeProjector]
  set sDg : (Fin k → Fin 4) → ℂ := fun i => (Real.sqrt (((k + 3).choose 3 : ℝ)⁻¹ *
    (bellTypeMult k (bellTypeOfIndex i) : ℝ)⁻¹) : ℂ) with hsDgdef
  have hRRc : bellRotation k * (bellRotation k)ᴴ = 1 := bellRotation_mul_conjTranspose k
  have hDP : Matrix.diagonal sDg * bellTypeDiagProjector k T
      = (Real.sqrt (((k + 3).choose 3 : ℝ)⁻¹ * (bellTypeMult k T : ℝ)⁻¹) : ℂ) •
          bellTypeDiagProjector k T := by
    ext i j
    simp only [bellTypeDiagProjector, Matrix.diagonal_mul_diagonal, Matrix.smul_apply,
      Matrix.diagonal_apply, smul_eq_mul]
    split_ifs with hij hT
    · simp only [hsDgdef, hT, mul_one]
    · simp only [mul_zero]
    · simp only [mul_zero]
  calc (bellRotation k)ᴴ * Matrix.diagonal sDg * bellRotation k *
          ((bellRotation k)ᴴ * bellTypeDiagProjector k T * bellRotation k)
         = (bellRotation k)ᴴ * Matrix.diagonal sDg * (bellRotation k * (bellRotation k)ᴴ) *
          bellTypeDiagProjector k T * bellRotation k := by simp only [Matrix.mul_assoc]
    _ = (bellRotation k)ᴴ * (Matrix.diagonal sDg * bellTypeDiagProjector k T) *
          bellRotation k := by rw [hRRc, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (bellRotation k)ᴴ * ((Real.sqrt (((k + 3).choose 3 : ℝ)⁻¹ *
            (bellTypeMult k T : ℝ)⁻¹) : ℂ) • bellTypeDiagProjector k T) * bellRotation k := by
          rw [hDP]
    _ = (Real.sqrt (((k + 3).choose 3 : ℝ)⁻¹ * (bellTypeMult k T : ℝ)⁻¹) : ℂ) •
          ((bellRotation k)ᴴ * bellTypeDiagProjector k T * bellRotation k) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]


end Quantum.Symmetry
