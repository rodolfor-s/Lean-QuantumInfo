import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Regularization of a subnormalized reference -/

noncomputable section

namespace Quantum.Operators

open scoped ComplexOrder

variable {Q : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]

/-- Mix a subnormalized reference with the maximally mixed state without increasing
its trace above one. -/
def SubDensityOp.regularized (σ : SubDensityOp Q) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) : SubDensityOp Q where
  toOp := ((1 - γ : ℝ) : ℂ) • σ.toOp + (γ : ℂ) • (DensityOp.maxMixed (X := Q)).toOp
  posSemidef := (σ.posSemidef.smul (Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr hγ1, rfl⟩)).add
    (DensityOp.maxMixed.posSemidef.smul (Complex.nonneg_iff.mpr ⟨hγ0, rfl⟩))
  trace_le_one := by
    simp only [Matrix.trace_add, Matrix.trace_smul, DensityOp.trace_one,
      smul_eq_mul, mul_one, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [σ.trace_le_one]

/-- Zero mixing weight preserves every subnormalized reference. -/
@[simp] theorem SubDensityOp.regularized_zero (σ : SubDensityOp Q) :
    σ.regularized 0 le_rfl zero_le_one = σ := by
  apply SubDensityOp.ext
  simp [SubDensityOp.regularized]

/-- Every positive mixing weight makes the reference positive definite. -/
theorem SubDensityOp.posDef_regularized (σ : SubDensityOp Q) (γ : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    (σ.regularized γ hγ0.le hγ1).toOp.PosDef := by
  change (((1 - γ : ℝ) : ℂ) • σ.toOp +
    (γ : ℂ) • (((Fintype.card Q : ℝ)⁻¹ : ℂ) • (1 : Op Q))).PosDef
  rw [smul_smul]
  exact Matrix.PosDef.posSemidef_add
    (σ.posSemidef.smul (Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr hγ1, rfl⟩))
    (Matrix.PosDef.one.smul (mul_pos (Complex.zero_lt_real.mpr hγ0)
      (inv_pos.mpr (Complex.zero_lt_real.mpr (Nat.cast_pos.mpr Fintype.card_pos)))))

end Quantum.Operators
