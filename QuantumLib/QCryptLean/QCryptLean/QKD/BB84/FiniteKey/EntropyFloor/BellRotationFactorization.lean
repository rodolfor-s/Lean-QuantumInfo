import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Weighted
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PhaseErrorUncertainty
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Projector
import QCryptLean.Quantum.Operators.StateOperations

/-! # Single-round reference blocks for the virtual Bell sift

The signal and its purifying reference are both natural bit-pair registers.
Computational conditioning uses matrix units; no numbering of outcomes is needed.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators InfoTheory.SmoothMinEntropy
open QKD.BB84.Model QKD.BB84.Measurement Matrix
open scoped Kronecker

/-- Pull the computational outcome projector back through the virtual Bell sift. -/
def siftedConditionOp (b : Bool) (k : Signal) : Op Signal :=
  (siftedPairOp b)ᴴ * Matrix.single k k 1 * siftedPairOp b

/-- The pulled-back outcome projector is Hermitian. -/
lemma conjTranspose_siftedConditionOp (b : Bool) (k : Signal) :
    (siftedConditionOp b k)ᴴ = siftedConditionOp b k := by
  simp [siftedConditionOp, conjTranspose_mul, Matrix.mul_assoc]

/-- Each virtual Bell sift also satisfies the other unitary identity. -/
lemma siftedPairOp_mul_conjTranspose (b : Bool) :
    siftedPairOp b * (siftedPairOp b)ᴴ = (1 : Op Signal) :=
  mul_eq_one_comm.mp (conjTranspose_mul_siftedPairOp b)

/-- Pulling back by the sift preserves idempotence of an outcome projector. -/
lemma siftedConditionOp_mul_self (b : Bool) (k : Signal) :
    siftedConditionOp b k * siftedConditionOp b k = siftedConditionOp b k := by
  unfold siftedConditionOp
  calc (siftedPairOp b)ᴴ * single k k 1 * siftedPairOp b *
      ((siftedPairOp b)ᴴ * single k k 1 * siftedPairOp b) =
      (siftedPairOp b)ᴴ * single k k 1 *
        (siftedPairOp b * (siftedPairOp b)ᴴ) * (single k k 1 * siftedPairOp b) := by
          simp only [mul_assoc]
    _ = _ := by
      rw [siftedPairOp_mul_conjTranspose, Matrix.mul_one,
        mul_assoc (siftedPairOp b)ᴴ, ← mul_assoc (single k k (1 : ℂ)),
        single_mul_single_same, one_mul, ← mul_assoc]

/-- The reference block conditioned on a single outcome of the virtual sift. -/
def siftedRoundRefBlock (ψ : DensityOp (Signal × Signal)) (b : Bool) (k : Signal) :
    SubDensityOp Signal :=
  (ψ.toSubDensityOp.projectorSandwich (siftedConditionOp b k ⊗ₖ (1 : Op Signal))
    ⟨by simp [Matrix.IsHermitian, conjTranspose_kronecker, conjTranspose_siftedConditionOp],
      by rw [← mul_kronecker_mul, siftedConditionOp_mul_self, one_mul]⟩).partialTraceLeft

/-- The conditioned block is the signal trace of its projector sandwich. -/
@[simp] lemma siftedRoundRefBlock_toOp
    (ψ : DensityOp (Signal × Signal)) (b : Bool) (k : Signal) :
    (siftedRoundRefBlock ψ b k).toOp =
      partialTraceLeft ((siftedConditionOp b k ⊗ₖ (1 : Op Signal)) * ψ.toOp *
        (siftedConditionOp b k ⊗ₖ (1 : Op Signal))) := rfl

/-- The projector-weighted entry formula for a conditioned reference block. -/
lemma siftedRoundRefBlock_toOp_apply
    (ψ : DensityOp (Signal × Signal)) (b : Bool) (k r r' : Signal) :
    (siftedRoundRefBlock ψ b k).toOp r r' =
      ∑ t : Signal, ∑ t' : Signal,
        siftedConditionOp b k t' t * ψ.toOp (t, r) (t', r') := by
  rw [siftedRoundRefBlock_toOp, partialTraceLeft_kronecker_sandwich_cycle,
    siftedConditionOp_mul_self]
  simp [partialTraceLeft, mul_apply, kroneckerMap_apply, Fintype.sum_prod_type,
    one_apply, mul_comm]

/-- Key rounds use the computational outcome projector without a rotation. -/
lemma siftedConditionOp_false (k : Signal) :
    siftedConditionOp false k = Matrix.single k k 1 := by
  simp [siftedConditionOp, siftedPairOp]

/-- A key-round block is the principal reference block at its signal outcome. -/
lemma siftedRoundRefBlock_false_toOp_apply
    (ψ : DensityOp (Signal × Signal)) (k r r' : Signal) :
    (siftedRoundRefBlock ψ false k).toOp r r' = ψ.toOp (k, r) (k, r') := by
  simp [siftedRoundRefBlock_toOp_apply, siftedConditionOp_false, single_apply, ite_and]

/-- All sifted outcome projectors exhaust the signal identity. -/
lemma sum_siftedConditionOp (b : Bool) :
    ∑ k : Signal, siftedConditionOp b k = (1 : Op Signal) := by
  simp only [siftedConditionOp]
  rw [← Finset.sum_mul, ← Finset.mul_sum, Matrix.sum_single_one,
    Matrix.mul_one, conjTranspose_mul_siftedPairOp]

/-- Summing the sifted outcome blocks keeps the full reference marginal. -/
lemma sum_siftedRoundRefBlock_toOp_eq_partialTraceA
    (ψ : DensityOp (Signal × Signal)) (b : Bool) :
    ∑ k : Signal, (siftedRoundRefBlock ψ b k).toOp = partialTraceLeft ψ.toOp := by
  simp only [siftedRoundRefBlock_toOp, partialTraceLeft_kronecker_sandwich_cycle,
    siftedConditionOp_mul_self]
  change (∑ k, partialTraceLeftLinearMap (S := ℂ)
    (ψ.toOp * (siftedConditionOp b k ⊗ₖ (1 : Op Signal)))) = _
  rw [← _root_.map_sum, ← Matrix.mul_sum]
  have hk : (∑ k : Signal, siftedConditionOp b k ⊗ₖ (1 : Op Signal)) =
      (∑ k : Signal, siftedConditionOp b k) ⊗ₖ (1 : Op Signal) := by
    ext p q
    simp only [Matrix.sum_apply, kroneckerMap_apply, Finset.sum_mul]
  rw [hk, sum_siftedConditionOp, one_kronecker_one, Matrix.mul_one]
  rfl

/-- All conditioned reference blocks together have total weight one. -/
lemma sum_trace_siftedRoundRefBlock (ψ : DensityOp (Signal × Signal)) (b : Bool) :
    ∑ k : Signal, (siftedRoundRefBlock ψ b k).trace = 1 := by
  simp only [SubDensityOp.trace, ← Complex.re_sum, ← Matrix.trace_sum,
    sum_siftedRoundRefBlock_toOp_eq_partialTraceA, trace_partialTraceLeft,
    ψ.trace_one, Complex.one_re]

end QKD.BB84.FiniteKey
