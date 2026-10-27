import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementAlgebra
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.PartialTrace
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.SubDensityMonotonicity
import QCryptLean.Quantum.Operators.Basic

/-! # Measurement Channel -/


noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators Quantum.Channels Quantum.Metrics
open scoped ComplexOrder MatrixOrder Kronecker
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- The partial isometry in output/environment versus input/conditioning layouts. -/
def measTransportMatrix (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) :
    Matrix ((A × B) × (A × A)) (A × ((A × A) × B)) ℂ :=
  reindex measTraceEquiv measEntropyEquiv
    (RankOneProjectiveBasis.partialIsometryW P Q ⊗ₖ (1 : Op B))

/-- The measurement transport is conjugation followed by an explicit discard. -/
def measTransportMap (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) :
    Operation (A × ((A × A) × B)) (A × B) :=
  partialTraceRightLinearMap.comp (krausMap (fun _ : Unit => measTransportMatrix P Q))

/-- The transport has the expected conjugation-and-discard formula. -/
theorem measTransportMap_apply (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (M : Op (A × ((A × A) × B))) :
    measTransportMap P Q M = partialTraceRight
      (measTransportMatrix P Q * M * (measTransportMatrix P Q)ᴴ) := by
  simp [measTransportMap, krausMap]

/-- The transport matrix is a contraction. -/
theorem measTransportMatrix_contraction [DecidableEq A]
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) :
    ((1 : Op (A × ((A × A) × B))) -
      (measTransportMatrix (B := B) P Q)ᴴ * measTransportMatrix P Q).PosSemidef := by
  have hk : (measTransportMatrix (B := B) P Q)ᴴ * measTransportMatrix P Q =
      reindex measEntropyEquiv measEntropyEquiv
        ((RankOneProjectiveBasis.dilationIso Q * (RankOneProjectiveBasis.dilationIso Q)ᴴ) ⊗ₖ
          (1 : Op B)) := by
    simp only [measTransportMatrix, reindex_apply, conjTranspose_submatrix,
      submatrix_mul_equiv, conjTranspose_kronecker, conjTranspose_one,
      ← mul_kronecker_mul, Matrix.one_mul,
      RankOneProjectiveBasis.partialIsometryW_dagger_mul_self_eq]
  rw [hk]
  have h := (RankOneProjectiveBasis.dilationCoprojector_posSemidef Q).kronecker
    (PosSemidef.one (n := B) (R := ℂ))
  have he : (1 - RankOneProjectiveBasis.dilationIso Q *
      (RankOneProjectiveBasis.dilationIso Q)ᴴ) ⊗ₖ (1 : Op B) =
      1 - (RankOneProjectiveBasis.dilationIso Q *
        (RankOneProjectiveBasis.dilationIso Q)ᴴ) ⊗ₖ (1 : Op B) := by
    conv_rhs => lhs; rw [← one_kronecker_one (α := ℂ)]
    ext p q
    simp only [kroneckerMap_apply, Matrix.sub_apply, sub_mul]
  rw [he] at h
  have hh := h.submatrix (measEntropyEquiv (A := A) (B := B)).symm
  change ((reindexAddEquiv ℂ measEntropyEquiv measEntropyEquiv) _).PosSemidef at hh
  rw [map_sub] at hh
  change PosSemidef (reindex measEntropyEquiv measEntropyEquiv
    (1 : Op (((A × A) × A) × B)) - reindex measEntropyEquiv measEntropyEquiv
      ((RankOneProjectiveBasis.dilationIso Q * (RankOneProjectiveBasis.dilationIso Q)ᴴ) ⊗ₖ
        (1 : Op B))) at hh
  rw [reindex_apply, submatrix_one_equiv] at hh
  exact hh

/-- Complete positivity follows from the one-Kraus conjugation and partial-trace channel. -/
theorem isCompletelyPositive_measTransportMap
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) :
    IsCompletelyPositive (measTransportMap (B := B) P Q) :=
  isChannel_partialTraceRight.1.comp (isCompletelyPositive_krausMap _)

/-- The transport does not increase positive input weight. -/
theorem trace_measTransportMap_le (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (M : Op (A × ((A × A) × B))) (hM : M.PosSemidef) :
    (measTransportMap P Q M).trace.re ≤ M.trace.re := by
  classical
  rw [measTransportMap_apply, trace_partialTraceRight, trace_mul_cycle]
  have h := (measTransportMatrix_contraction (B := B) P Q).trace_mul_nonneg hM
  rw [Matrix.sub_mul, Matrix.one_mul, trace_sub] at h
  exact sub_nonneg.mp (Complex.nonneg_iff.mp h).1

/-- Push a subnormalized state through the measurement subchannel. -/
def measDilateTransport (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (τ : SubDensityOp (A × ((A × A) × B))) : SubDensityOp (A × B) where
  toOp := measTransportMap P Q τ.toOp
  posSemidef := (isCompletelyPositive_measTransportMap P Q).posSemidef τ.posSemidef
  trace_le_one := (trace_measTransportMap_le P Q τ.toOp τ.posSemidef).trans τ.trace_le_one

/-- The transport recovers the measured marginal of a coherently dilated state. -/
theorem measDilateTransport_zDilatedState_eq_xMeasuredMarginal [DecidableEq A]
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (ρ : SubDensityOp (A × B)) :
    measDilateTransport P Q (zDilatedState Q ρ) = xMeasuredMarginal P ρ := by
  apply SubDensityOp.ext
  change measTransportMap P Q _ = _
  rw [measTransportMap_apply]
  have hw : (RankOneProjectiveBasis.partialIsometryW P Q ⊗ₖ (1 : Op B)) *
      (RankOneProjectiveBasis.dilationIso Q ⊗ₖ (1 : Op B)) =
      RankOneProjectiveBasis.dilationIso P ⊗ₖ (1 : Op B) := by
    rw [← mul_kronecker_mul, RankOneProjectiveBasis.partialIsometryW_mul_dilationIso,
      Matrix.one_mul]
  have he (W : Op (((A × A) × A) × B)) (M : Op (((A × A) × A) × B)) :
      reindex measTraceEquiv measEntropyEquiv W * reindex measEntropyEquiv measEntropyEquiv M *
        (reindex measTraceEquiv measEntropyEquiv W)ᴴ =
      reindex measTraceEquiv measTraceEquiv (W * M * Wᴴ) := by
    simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  change partialTraceRight (reindex measTraceEquiv measEntropyEquiv _ *
    reindex measEntropyEquiv measEntropyEquiv
      ((RankOneProjectiveBasis.dilationIso Q ⊗ₖ (1 : Op B)) * ρ.toOp *
        (RankOneProjectiveBasis.dilationIso Q ⊗ₖ (1 : Op B))ᴴ) *
      (reindex measTraceEquiv measEntropyEquiv _)ᴴ) = _
  rw [he]
  have ha (W : Op (((A × A) × A) × B)) (V : Matrix (((A × A) × A) × B) (A × B) ℂ) :
      W * (V * ρ.toOp * Vᴴ) * Wᴴ = (W * V) * ρ.toOp * (W * V)ᴴ := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [ha, hw]
  rfl

/-- Purified distance contracts at the same radius under measurement transport. -/
theorem measDilateTransport_purifiedDistance_le [Nonempty A] [Nonempty B]
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (ρ τ : SubDensityOp (A × ((A × A) × B))) :
    purifiedDistance (measDilateTransport P Q ρ) (measDilateTransport P Q τ) ≤
      purifiedDistance ρ τ :=
  purifiedDistance_le_of_isCompletelyPositive_of_trace_le (measTransportMap P Q)
    (isCompletelyPositive_measTransportMap P Q) (trace_measTransportMap_le P Q)
    ρ τ _ _ rfl rfl

end InfoTheory.SmoothMinEntropy
