import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.RankOne
import QCryptLean.Math.Probability.UnitaryHaar
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKMRCoherent
import QCryptLean.Quantum.DeFinetti.CKMRMeasure
import QCryptLean.Quantum.DeFinetti.CKMRReduction
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.Basic

/-! # The three coherent-state Schur identities on finite function registers -/
noncomputable section
namespace Quantum.DeFinetti
open Matrix Quantum.Operators Quantum.Symmetry MeasureTheory
open scoped Kronecker
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n k : ℕ}

/-- Averaging the conditional contractions recovers the retained marginal. -/
theorem integral_coherentReduction (x : X) (ρ : DensityOp (Fin n → X)) (hk : k ≤ n)
    (hρ : symmetricProjector X n * ρ.toOp = ρ.toOp) :
    (symmetricProjector X (n-k)).trace •
      (of fun i j => ∫ U, coherentReduction x ρ hk U i j ∂UnitaryGroup.haarProbUnitary X) =
      (partialTraceLast hk ρ).toOp := by
  let T := (ρ.reindex (splitLast hk)).toOp
  let Q (U : unitaryGroup X ℂ) : Op ((Fin k → X) × (Fin (n-k) → X)) :=
    1 ⊗ₖ ((pureStateMap x U).tensorPow (n-k)).toOp
  have hc : Continuous Q := continuous_pi fun i => continuous_pi fun j => continuous_const.mul
    ((DensityOp.continuous_tensorPow_entry (n-k) i.2 j.2).comp (continuous_pureStateMap x))
  have hint (i j) : Integrable (fun U => Q U i j) (UnitaryGroup.haarProbUnitary X) :=
    ((continuous_apply j).comp ((continuous_apply i).comp hc)).integrable_of_compactSpace
  have hintT (i j) : Integrable (fun U => (Q U * T) i j) (UnitaryGroup.haarProbUnitary X) :=
    ((continuous_apply j).comp ((continuous_apply i).comp
      (hc.mul (continuous_const (y := T))))).integrable_of_compactSpace
  have hQ : (symmetricProjector X (n-k)).trace •
      (of fun i j => ∫ U, Q U i j ∂UnitaryGroup.haarProbUnitary X) =
      (1 : Op (Fin k → X)) ⊗ₖ symmetricProjector X (n-k) := by
    conv_rhs => rw [symmetricProjector_eq_scaled_haar x (n-k)]
    ext i j
    change _ * (∫ U, (1 : Op (Fin k → X)) i.1 j.1 *
      ((pureStateMap x U).tensorPow (n-k)).toOp i.2 j.2 ∂_) = _
    rw [integral_const_mul]
    change (symmetricProjector X (n-k)).trace * ((1 : Op (Fin k → X)) i.1 j.1 * _) =
      (1 : Op (Fin k → X)) i.1 j.1 * ((symmetricProjector X (n-k)).trace * _)
    simp only [of_apply]
    ring
  have hT : reindex (splitLast hk) (splitLast hk) (symmetricProjector X n) * T = T := by
    change (reindexAlgEquiv ℂ ℂ (splitLast hk)) _ *
      (reindexAlgEquiv ℂ ℂ (splitLast hk)) _ = (reindexAlgEquiv ℂ ℂ (splitLast hk)) _
    rw [← map_mul, hρ]
  have hBT : ((1 : Op (Fin k → X)) ⊗ₖ symmetricProjector X (n-k)) * T = T := by
    calc
      _ = ((1 : Op (Fin k → X)) ⊗ₖ symmetricProjector X (n-k)) *
          (reindex (splitLast hk) (splitLast hk) (symmetricProjector X n) * T) := by rw [hT]
      _ = T := by rw [← Matrix.mul_assoc, kronecker_symmetricProjector_mul_reindex x hk, hT]
  change _ • (of fun i j => ∫ U, partialTraceRight (Q U * T) i j ∂_) = _
  rw [← partialTraceRight_entryIntegral hintT, ← partialTraceRight_smul,
    ← entryIntegral_mul T hint, ← Matrix.smul_mul, hQ, hBT]
  rfl

/-- Inserting the retained coherent projector changes the averaging dimension to all sites. -/
theorem integral_pureStateMap_mul_coherentReduction (x : X) (ρ : DensityOp (Fin n → X))
    (hk : k ≤ n) (hρ : symmetricProjector X n * ρ.toOp = ρ.toOp) :
    (symmetricProjector X n).trace •
      (of fun i j => ∫ U, (((pureStateMap x U).tensorPow k).toOp *
        coherentReduction x ρ hk U) i j ∂UnitaryGroup.haarProbUnitary X) =
      (partialTraceLast hk ρ).toOp := by
  let T := (ρ.reindex (splitLast hk)).toOp
  let Q (U : unitaryGroup X ℂ) := reindex (splitLast hk) (splitLast hk)
    ((pureStateMap x U).tensorPow n).toOp
  have hc : Continuous Q := continuous_pi fun i => continuous_pi fun j =>
    (DensityOp.continuous_tensorPow_entry n _ _).comp (continuous_pureStateMap x)
  have hint (i j) : Integrable (fun U => Q U i j) (UnitaryGroup.haarProbUnitary X) :=
    ((continuous_apply j).comp ((continuous_apply i).comp hc)).integrable_of_compactSpace
  have hintT (i j) : Integrable (fun U => (Q U * T) i j) (UnitaryGroup.haarProbUnitary X) :=
    ((continuous_apply j).comp ((continuous_apply i).comp
      (hc.mul (continuous_const (y := T))))).integrable_of_compactSpace
  have hQ : (symmetricProjector X n).trace •
      (of fun i j => ∫ U, Q U i j ∂UnitaryGroup.haarProbUnitary X) =
      reindex (splitLast hk) (splitLast hk) (symmetricProjector X n) := by
    conv_rhs => rw [symmetricProjector_eq_scaled_haar x n]
    rfl
  have he (U : unitaryGroup X ℂ) : ((pureStateMap x U).tensorPow k).toOp *
      coherentReduction x ρ hk U = partialTraceRight (Q U * T) := by
    rw [pureStateMap_mul_coherentReduction]
    congr 1
    exact (reindexAlgEquiv ℂ ℂ (splitLast hk)).map_mul _ _
  simp_rw [he]
  rw [← partialTraceRight_entryIntegral hintT, ← partialTraceRight_smul,
    ← entryIntegral_mul T hint, ← Matrix.smul_mul, hQ]
  have hT : reindex (splitLast hk) (splitLast hk) (symmetricProjector X n) * T = T := by
    change (reindexAlgEquiv ℂ ℂ (splitLast hk)) _ *
      (reindexAlgEquiv ℂ ℂ (splitLast hk)) _ = (reindexAlgEquiv ℂ ℂ (splitLast hk)) _
    rw [← map_mul, hρ]
  rw [hT]
  rfl

/-- Sandwiching conditional contractions yields the coherent-measure mixture. -/
theorem integral_pureStateMap_sandwich_coherentReduction (x : X)
    (ρ : DensityOp (Fin n → X))
    (hρ : symmetricProjector X n * ρ.toOp * symmetricProjector X n = ρ.toOp) (hk : k ≤ n) :
    (symmetricProjector X n).trace •
      (of fun i j => ∫ U, (((pureStateMap x U).tensorPow k).toOp *
        coherentReduction x ρ hk U * ((pureStateMap x U).tensorPow k).toOp) i j
        ∂UnitaryGroup.haarProbUnitary X) = integralTensorPower k (coherentMeasure x ρ hρ) := by
  rw [integralTensorPower_coherentMeasure]
  ext i j
  change (symmetricProjector X n).trace * _ = _
  simp only [of_apply]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [pureStateMap_sandwich_coherentReduction, Matrix.smul_apply, smul_eq_mul,
    ofReal_coherentWeight]
  exact (mul_assoc _ _ _).symm

end Quantum.DeFinetti
