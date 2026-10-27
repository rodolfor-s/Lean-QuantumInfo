import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.InfoTheory.VonNeumannEntropy.Bounds
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.BellBasis
import QCryptLean.Quantum.Symmetry.BellMixture

/-! # Entropy -/


noncomputable section

namespace InfoTheory.BellDiagonal

open Quantum.Operators Quantum.Symmetry Quantum.Metrics
  InfoTheory.VonNeumannEntropy Matrix
open scoped ComplexOrder

/-- Bell probabilities indexed by their phase and bit labels. -/
def bellProbability (σ : DensityOp (Fin 2 × Fin 2)) (b : Fin 2 × Fin 2) : ℝ :=
  fidelitySq σ.toPosSemidefOp
    (((bellDensity (finProdFinEquiv b)).reindex
      (qubitEquiv.prodCongr qubitEquiv)).toPosSemidefOp)

/-- A Bell probability is the trace against its rank-one projector. -/
theorem bellProbability_eq_trace (σ : DensityOp (Fin 2 × Fin 2)) (b : Fin 2 × Fin 2) :
    bellProbability σ b =
      ((((bellDensity (finProdFinEquiv b)).reindex
        (qubitEquiv.prodCongr qubitEquiv)).toOp) * σ.toOp).trace.re := by
  exact fidelitySq_pure_right σ.toPosSemidefOp
    ((bellNormKet (finProdFinEquiv b)).reindex (qubitEquiv.prodCongr qubitEquiv))

/-- The Bell probabilities sum to one. -/
theorem sum_bellProbability (σ : DensityOp (Fin 2 × Fin 2)) :
    ∑ b, bellProbability σ b = 1 := by
  have hp : (∑ b : Fin 2 × Fin 2,
      ((bellDensity (finProdFinEquiv b)).reindex
        (qubitEquiv.prodCongr qubitEquiv)).toOp) = 1 := by
    rw [Equiv.sum_comp (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) (fun k =>
      ((bellDensity k).reindex (qubitEquiv.prodCongr qubitEquiv)).toOp)]
    change (∑ k, (reindexLinearEquiv ℂ ℂ
      (qubitEquiv.prodCongr qubitEquiv) (qubitEquiv.prodCongr qubitEquiv))
      (bellLabelKet k).projector) = _
    rw [← map_sum, bellLabelKet_projectors_sum]
    exact submatrix_one_equiv _
  simp_rw [bellProbability_eq_trace]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hp,
    Matrix.one_mul, σ.trace_one]
  rfl


/-- Bell pinching is the probability-weighted sum of the existing Bell projectors. -/
def bellDephasingOp (σ : DensityOp (Fin 2 × Fin 2)) : Op (Fin 2 × Fin 2) :=
  ∑ b : Fin 2 × Fin 2, (bellProbability σ b : ℂ) •
    ((bellDensity (finProdFinEquiv b)).reindex (qubitEquiv.prodCongr qubitEquiv)).toOp

/-- Bell pinching preserves the trace of a density operator. -/
theorem trace_bellDephasingOp (σ : DensityOp (Fin 2 × Fin 2)) :
    (bellDephasingOp σ).trace = 1 := by
  simp only [bellDephasingOp, Matrix.trace_sum, Matrix.trace_smul,
    DensityOp.trace_one, smul_eq_mul, mul_one]
  rw [← Complex.ofReal_sum, sum_bellProbability]
  rfl

/-- Bell pinching as a density operator on the natural bit-pair register. -/
def bellDephasingDensity (σ : DensityOp (Fin 2 × Fin 2)) : DensityOp (Fin 2 × Fin 2) where
  toOp := bellDephasingOp σ
  posSemidef := Matrix.posSemidef_sum _ fun b _ =>
    (((bellDensity (finProdFinEquiv b)).reindex
      (qubitEquiv.prodCongr qubitEquiv)).posSemidef).smul
        (Complex.zero_le_real.mpr (sq_nonneg _))
  trace_one := by
    exact trace_bellDephasingOp σ

/-- Bell basis with phase and bit as separate labels. -/
def bellBasis : Op (Fin 2 × Fin 2) := fun x b =>
  (bellLabelKet (finProdFinEquiv b)).vec (finTwoEquiv x.1, finTwoEquiv x.2)

/-- The phase/bit-labelled Bell basis is unitary. -/
lemma bellBasis_conjTranspose_mul : bellBasisᴴ * bellBasis = 1 := by
  ext b c
  change (∑ x : Fin 2 × Fin 2,
    star ((bellLabelKet (finProdFinEquiv b)).vec (finTwoEquiv x.1, finTwoEquiv x.2)) *
      (bellLabelKet (finProdFinEquiv c)).vec (finTwoEquiv x.1, finTwoEquiv x.2)) =
      if b = c then 1 else 0
  refine (Equiv.sum_comp (finTwoEquiv.prodCongr finTwoEquiv)
    (fun x => star ((bellLabelKet (finProdFinEquiv b)).vec x) *
      (bellLabelKet (finProdFinEquiv c)).vec x)).trans ?_
  change ((bellLabelKet (finProdFinEquiv b)).dag *
    bellLabelKet (finProdFinEquiv c) : ℂ) = _
  simp only [bellLabelKet_orthonormal, EmbeddingLike.apply_eq_iff_eq]

/-- The Bell probabilities are the diagonal in the Bell basis. -/
lemma bellProbability_eq_bellBasis_diagonal (ρ : DensityOp (Fin 2 × Fin 2))
    (b : Fin 2 × Fin 2) :
    bellProbability ρ b = ((bellBasisᴴ * ρ.toOp * bellBasis) b b).re := by
  rw [bellProbability_eq_trace]
  congr 1
  change (∑ x, ∑ y, (bellBasis x b * star (bellBasis y b)) * ρ.toOp y x) = _
  simp only [Matrix.mul_apply, conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  ring


/-- Bell-dephasing entropy is the entropy of its phase/bit distribution. -/
theorem vonNeumannEntropy_bellDephasingDensity (σ : DensityOp (Fin 2 × Fin 2)) :
    vonNeumannEntropy (bellDephasingDensity σ) =
      ∑ b : Fin 2 × Fin 2, Math.ClassicalEntropy.entropyTerm (bellProbability σ b) := by
  let U := bellBasis
  have hU : Uᴴ * U = 1 := bellBasis_conjTranspose_mul
  apply vonNeumannEntropy_eq_sum_entropyTerm_of_diagonalization _ U hU (bellProbability σ)
  ext x y
  change (∑ b : Fin 2 × Fin 2, (bellProbability σ b : ℂ) *
    ((bellLabelKet (finProdFinEquiv b)).vec (finTwoEquiv x.1, finTwoEquiv x.2) *
      star ((bellLabelKet (finProdFinEquiv b)).vec (finTwoEquiv y.1, finTwoEquiv y.2)))) = _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro b _
  change _ = (U x b * (bellProbability σ b : ℂ)) * star (U y b)
  dsimp only [U, bellBasis]
  ring
end InfoTheory.BellDiagonal
