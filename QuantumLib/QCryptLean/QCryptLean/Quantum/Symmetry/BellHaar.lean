import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.DeFinetti.HaarAlgebra
import QCryptLean.Quantum.DeFinetti.Integral
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.BellDoubling
import QCryptLean.Quantum.Symmetry.BellDoublingAlgebra
import QCryptLean.Quantum.Symmetry.BellMixture
import QCryptLean.Quantum.Symmetry.Dimension
import QCryptLean.Quantum.Symmetry.Paired

/-! # Bell Haar -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators Quantum.DeFinetti MeasureTheory
open scoped ComplexOrder

/-- The joint Bell mixture is the Haar mixture of grouped Bell-doubled pure tensor powers. -/
theorem bellPairedDeFinettiState_eq_haar_integral (k : ℕ) :
    (bellPairedDeFinettiState k).toOp =
      Matrix.of fun i j => ∫ φ : DensityOp (Bool × Bool),
        (reindex (pairFunctions (Bool × Bool) (Bool × Bool) k)
          (pairFunctions (Bool × Bool) (Bool × Bool) k)
          ((bellWembed φ).tensorPow k).toOp) i j
            ∂(haarDensityMeasure (false, false)).measure := by
  have ht : (symmetricProjector (Bool × Bool) k).trace = ((k + 3).choose 3 : ℂ) := by
    apply Complex.ext
    · simpa using (symmetricSubspace_dim (X := Bool × Bool) (k := k))
    · simpa using (Complex.nonneg_iff.mp
        (symmetricProjector_posSemidef (X := Bool × Bool) (k := k)).trace_nonneg).2.symm
  have hn : (deFinettiState (Bool × Bool) k).toOp =
      (((k + 3).choose 3 : ℂ)⁻¹ • symmetricProjector (Bool × Bool) k) := by
    change (symmetricProjector (Bool × Bool) k).trace⁻¹ • _ = _
    rw [ht]
  change bellPairedDeFinettiStateOp k = _
  rw [bellPairedDeFinettiStateOp_eq_conj_symmetricProjector, ← hn,
    Quantum.DeFinetti.deFinettiState_eq_haar_integral (false, false)]
  have h := Matrix.sandwich_entryIntegral (bellDoublingIsometryPow k)
    (integrable_tensorPow_entry (haarDensityMeasure (false, false)) k)
  change reindex _ _ (bellDoublingIsometryPow k * integralTensorPower k _ *
    (bellDoublingIsometryPow k)ᴴ) = _
  rw [show bellDoublingIsometryPow k * integralTensorPower k _ *
    (bellDoublingIsometryPow k)ᴴ = _ from h]
  ext i j
  apply integral_congr_ae
  filter_upwards [] with φ
  exact congrFun (congrFun (bellWembed_tensorPow_toOp_eq_conj k φ).symm
    ((pairFunctions (Bool × Bool) (Bool × Bool) k).symm i))
    ((pairFunctions (Bool × Bool) (Bool × Bool) k).symm j)

end Quantum.Symmetry
