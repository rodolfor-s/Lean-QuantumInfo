import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Regularized
import QCryptLean.Quantum.Operators.StateOperations

/-! # Regularization of natural block-reference families

The assembled reference is exactly ordinary reference regularization. Its positive
definiteness and smooth-entropy charge therefore reuse the general reference API.
-/

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Matrix
open scoped ComplexOrder

variable {T Q : Type*} [Fintype T] [Fintype Q]
  [DecidableEq T] [DecidableEq Q] [Nonempty T] [Nonempty Q]

/-- Regularize each block with its share of a uniformly distributed maximally mixed state. -/
def blockFamilyRegularized (ν : T → SubDensityOp Q) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (t : T) : SubDensityOp Q where
  toOp := ((1 - γ : ℝ) : ℂ) • (ν t).toOp +
    (↑(γ / (Fintype.card T : ℝ)) : ℂ) • (DensityOp.maxMixed (X := Q)).toOp
  posSemidef := ((ν t).posSemidef.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hγ1))).add
    (DensityOp.maxMixed.posSemidef.smul
      (Complex.zero_le_real.mpr (div_nonneg hγ0 (Nat.cast_nonneg _))))
  trace_le_one := by
    have hc : (1 : ℝ) ≤ Fintype.card T := by exact_mod_cast Fintype.card_pos (α := T)
    have hd : γ / (Fintype.card T : ℝ) ≤ γ := div_le_self hγ0 hc
    simp only [trace_add, trace_smul, DensityOp.trace_one, smul_eq_mul, mul_one,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    nlinarith [(ν t).trace_le_one]

omit [DecidableEq T] in
/-- The regularized family retains its exact total mass, including subnormalized input families. -/
theorem sum_blockFamilyRegularized_trace (ν : T → SubDensityOp Q) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∑ t, (blockFamilyRegularized ν γ hγ0 hγ1 t).trace =
      (1 - γ) * (∑ t, (ν t).trace) + γ := by
  simp [blockFamilyRegularized, SubDensityOp.trace, trace_add, trace_smul,
    Complex.mul_re, DensityOp.trace_one, Finset.sum_add_distrib, ← Finset.sum_mul,
    div_eq_mul_inv, mul_comm, mul_left_comm, Fintype.card_ne_zero]

/-- Block-family regularization agrees exactly with regularization of the assembled reference.
Consequently the general positive-definite and entropy-floor theorems apply without a new charge. -/
theorem blockDiagRef_blockFamilyRegularized (ν : T → SubDensityOp Q)
    (hν : ∑ t, (ν t).trace ≤ 1) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    blockDiagRef (blockFamilyRegularized ν γ hγ0 hγ1)
      (by rw [sum_blockFamilyRegularized_trace]; nlinarith) =
      (blockDiagRef ν hν).regularized γ hγ0 hγ1 := by
  ext ⟨t,i⟩ ⟨u,j⟩
  by_cases htu : t = u <;> by_cases hij : i = j <;>
    simp [blockDiagRef, CQState.toJointDensity, CQState.toJointOp,
      SubDensityOp.reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
      blockDiagonal_apply, blockFamilyRegularized, SubDensityOp.regularized,
      DensityOp.maxMixed, Fintype.card_prod, htu, hij,
      div_eq_mul_inv, mul_comm, mul_assoc]

end InfoTheory.SmoothMinEntropy
