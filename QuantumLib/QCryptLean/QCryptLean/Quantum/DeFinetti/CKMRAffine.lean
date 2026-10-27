import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.Probability.UnitaryHaar
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKMRMeasure
import QCryptLean.Quantum.DeFinetti.CKMRReduction
import QCryptLean.Quantum.DeFinetti.CKMRSchur
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.Basic

/-! # The positive affine remainder in the CKMR estimate -/
noncomputable section
namespace Quantum.DeFinetti
open Matrix Quantum.Operators Quantum.Symmetry MeasureTheory
open scoped ComplexOrder
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n k : ℕ}

/-- The CKMR affine remainder is an average of positive complementary sandwiches. -/
theorem coherent_affine_posSemidef (x : X) (ρ : DensityOp (Fin n → X))
    (hρ : symmetricProjector X n * ρ.toOp * symmetricProjector X n = ρ.toOp) (hk : k ≤ n)
    (r : ℝ) (hr : (r : ℂ) * (symmetricProjector X n).trace =
      (symmetricProjector X (n - k)).trace) :
    (((1 - 2 * r : ℂ) • (partialTraceLast hk ρ).toOp) +
      (r : ℂ) • integralTensorPower k (coherentMeasure x ρ hρ)).PosSemidef := by
  let P (U : unitaryGroup X ℂ) : Matrix (Fin k → X) (Fin k → X) ℂ :=
    ((pureStateMap x U).tensorPow k).toOp
  let R : unitaryGroup X ℂ → Matrix (Fin k → X) (Fin k → X) ℂ :=
    coherentReduction x ρ hk
  let J (F : unitaryGroup X ℂ → Matrix (Fin k → X) (Fin k → X) ℂ) :=
    of fun i j => ∫ U, F U i j ∂UnitaryGroup.haarProbUnitary X
  let W (U : unitaryGroup X ℂ) := (1 - P U) * R U * (1 - P U)
  have hP : Continuous P := continuous_pi fun i => continuous_pi fun j =>
    (DensityOp.continuous_tensorPow_entry k i j).comp (continuous_pureStateMap x)
  have hR : Continuous R := continuous_coherentReduction x ρ hk
  have hint {F : unitaryGroup X ℂ → Matrix (Fin k → X) (Fin k → X) ℂ} (hF : Continuous F) (i j) :
      Integrable (fun U => F U i j) (UnitaryGroup.haarProbUnitary X) :=
    ((continuous_apply j).comp ((continuous_apply i).comp hF)).integrable_of_compactSpace
  have hs : symmetricProjector X n * ρ.toOp = ρ.toOp := by
    calc
      _ = symmetricProjector X n * (symmetricProjector X n * ρ.toOp *
          symmetricProjector X n) := congrArg (symmetricProjector X n * ·) hρ.symm
      _ = symmetricProjector X n * ρ.toOp * symmetricProjector X n := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, symmetricProjector_mul_self]
      _ = ρ.toOp := hρ
  have h00 : (symmetricProjector X (n - k)).trace • J R = (partialTraceLast hk ρ).toOp :=
    integral_coherentReduction x ρ hk hs
  have h10 : (symmetricProjector X (n - k)).trace • J (fun U => P U * R U) =
      (r : ℂ) • (partialTraceLast hk ρ).toOp := by
    rw [← hr, ← smul_smul]
    exact congrArg ((r : ℂ) • ·) (integral_pureStateMap_mul_coherentReduction x ρ hk hs)
  have h11 : (symmetricProjector X (n - k)).trace • J (fun U => P U * R U * P U) =
      (r : ℂ) • integralTensorPower k (coherentMeasure x ρ hρ) := by
    rw [← hr, ← smul_smul]
    exact congrArg ((r : ℂ) • ·)
      (integral_pureStateMap_sandwich_coherentReduction x ρ hρ hk)
  have hJ : (J (fun U => P U * R U))ᴴ = J (fun U => R U * P U) := by
    ext i j
    change starRingEnd ℂ (∫ U, (P U * R U) j i ∂_) = ∫ U, (R U * P U) i j ∂_
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with U
    change ((P U * R U)ᴴ) i j = _
    rw [conjTranspose_mul, (coherentReduction_posSemidef x ρ hk U).isHermitian.eq,
      ((pureStateMap x U).tensorPow k).posSemidef.isHermitian.eq]
  have h01 : (symmetricProjector X (n - k)).trace • J (fun U => R U * P U) =
      (r : ℂ) • (partialTraceLast hk ρ).toOp := by
    have h := congrArg Matrix.conjTranspose h10
    rw [conjTranspose_smul, conjTranspose_smul,
      (symmetricProjector_posSemidef (X := X) (k := n - k)).trace_nonneg.star_eq,
      Complex.star_def, Complex.conj_ofReal,
      (partialTraceLast hk ρ).posSemidef.isHermitian.eq, hJ] at h
    exact h
  have hW (U : unitaryGroup X ℂ) : W U =
      R U - P U * R U - R U * P U + P U * R U * P U := by
    dsimp only [W]
    noncomm_ring
  have hJW : J W = J R - J (fun U => P U * R U) - J (fun U => R U * P U) +
      J (fun U => P U * R U * P U) := by
    ext i j
    change (∫ U, W U i j ∂_) = _
    simp_rw [hW, Matrix.add_apply, Matrix.sub_apply]
    have h00i := hint hR i j
    have h10i := hint (F := fun U => P U * R U) (hP.mul hR) i j
    have h01i := hint (F := fun U => R U * P U) (hR.mul hP) i j
    have h11i := hint (F := fun U => P U * R U * P U) ((hP.mul hR).mul hP) i j
    exact (integral_add ((h00i.sub h10i).sub h01i) h11i).trans
      (congrArg (· + _) ((integral_sub (h00i.sub h10i) h01i).trans
        (congrArg (· - _) (integral_sub h00i h10i))))
  have hpos : ((symmetricProjector X (n - k)).trace • J W).PosSemidef := by
    apply PosSemidef.smul _ (symmetricProjector_posSemidef (X := X) (k := n - k)).trace_nonneg
    apply Matrix.posSemidef_entryIntegral
    · intro U
      have h := (coherentReduction_posSemidef x ρ hk U).mul_mul_conjTranspose_same (1 - P U)
      rwa [(isHermitian_one.sub ((pureStateMap x U).tensorPow k).posSemidef.isHermitian).eq] at h
    · exact hint (((continuous_const.sub hP).mul hR).mul (continuous_const.sub hP))
  rw [hJW, smul_add, smul_sub, smul_sub, h00, h10, h01, h11] at hpos
  convert hpos using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Quantum.DeFinetti
