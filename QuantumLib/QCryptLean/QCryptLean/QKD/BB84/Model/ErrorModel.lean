import QCryptLean.Math.ClassicalEntropy.BinaryEntropy
import QCryptLean.Math.Concentration.SamplingBounds
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Projector
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.BellMixture

/-!
# BB84 error observables on the signal pair

Bit and phase errors are the corresponding two Bell sectors on Alice's and Bob's
actual bit registers. The Bell label order remains `(phase, bit) = 00, 01, 10, 11`.
The only basis identification is the componentwise Boolean-to-bit equivalence.
-/

open Quantum.Operators Quantum.Symmetry Matrix
open scoped ComplexOrder BigOperators

noncomputable section

namespace QKD.BB84.Model

open Measurement

/-- The sum of the Bell sectors with a bit error. -/
def bitFlipProjector : Op Signal :=
  Matrix.reindex (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)
    (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)
    ((bellLabelKet 1).projector + (bellLabelKet 3).projector)

/-- The sum of the Bell sectors with a phase error. -/
def phaseFlipProjector : Op Signal :=
  Matrix.reindex (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)
    (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)
    ((bellLabelKet 2).projector + (bellLabelKet 3).projector)

/-- The phase-error observable is a Hermitian idempotent. -/
theorem phaseFlipProjector_is_projector :
    phaseFlipProjector * phaseFlipProjector = phaseFlipProjector ∧
      phaseFlipProjectorᴴ = phaseFlipProjector := by
  have hh (i j : Fin 4) : (bellLabelKet i).projector * (bellLabelKet j).projector =
      if i = j then (bellLabelKet i).projector else 0 := by
    change vecMulVec _ _ * vecMulVec _ _ = _
    rw [Matrix.vecMulVec_mul_vecMulVec]
    change vecMulVec _ (((bellLabelKet i).dag * bellLabelKet j : ℂ) • _) = _
    rw [bellLabelKet_orthonormal]
    split_ifs with h
    · subst j
      simp only [one_smul, Ket.projector]
      rfl
    · simp
  have hP : ((bellLabelKet 2).projector + (bellLabelKet 3).projector) *
      ((bellLabelKet 2).projector + (bellLabelKet 3).projector) =
        (bellLabelKet 2).projector + (bellLabelKet 3).projector := by
    rw [add_mul, mul_add, mul_add, hh, hh, hh, hh]
    simp
  refine ⟨?_, ?_⟩
  · unfold phaseFlipProjector
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hP]
  · exact (((bellLabelKet 2).posSemidef_projector.add
      (bellLabelKet 3).posSemidef_projector).submatrix
        (finTwoEquiv.prodCongr finTwoEquiv)).isHermitian.eq

/-- The probability of a bit error in a single signal pair. -/
def bitFlipErrorRate (ρ : DensityOp Signal) : ℝ :=
  (bitFlipProjector * ρ.toOp).trace.re

/-- The probability of a phase error in a single signal pair. -/
def phaseFlipErrorRate (ρ : DensityOp Signal) : ℝ :=
  (phaseFlipProjector * ρ.toOp).trace.re

/-- Pairing a density operator with a fixed matrix via `Tr(Aρ)` is continuous. -/
lemma continuous_trace_mul_densityOp_toOp {X : Type*} [Fintype X] (A : Op X) :
    Continuous (fun ρ : DensityOp X => (A * ρ.toOp).trace) := by
  unfold Matrix.trace Matrix.diag
  apply continuous_finsetSum
  intro i _
  simp only [Matrix.mul_apply]
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul (((continuous_apply i).comp
    ((continuous_apply k).comp DensityOp.continuous_toOp)))

/-- The single-round phase-error probability is continuous. -/
lemma continuous_phaseFlipErrorRate : Continuous phaseFlipErrorRate :=
  Complex.continuous_re.comp (continuous_trace_mul_densityOp_toOp phaseFlipProjector)

/-- The single-round phase-error probability is measurable. -/
lemma phaseFlipErrorRate_measurable : Measurable phaseFlipErrorRate :=
  continuous_phaseFlipErrorRate.measurable

/-- The phase-error probability lies between zero and one. -/
theorem phaseFlipErrorRate_bounds (ρ : DensityOp Signal) :
    0 ≤ phaseFlipErrorRate ρ ∧ phaseFlipErrorRate ρ ≤ 1 := by
  have hP : IsOrthogonalProjector phaseFlipProjector :=
    ⟨phaseFlipProjector_is_projector.2, phaseFlipProjector_is_projector.1⟩
  refine ⟨(Complex.nonneg_iff.mp (hP.posSemidef.trace_mul_nonneg ρ.posSemidef)).1, ?_⟩
  have h := hP.re_trace_sandwich_le ρ.posSemidef
  rw [Matrix.trace_mul_cycle, hP.idempotent, ρ.trace_one, Complex.one_re] at h
  exact h

end QKD.BB84.Model
