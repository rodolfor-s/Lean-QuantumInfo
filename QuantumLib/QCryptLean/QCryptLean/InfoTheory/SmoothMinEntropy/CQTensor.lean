import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Math.LinearAlgebra.Matrix.TensorOrder
import QCryptLean.Math.LinearAlgebra.Matrix.TensorRpow
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.Tensor

/-! # Feasibility and collision moments on function-indexed CQ tensor powers -/
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder
variable {C Q : Type*} [Fintype C] [Fintype Q]

/-- Tensoring a feasible reference raises its coefficient to the number of copies. -/
theorem IsFeasible.tensorPower {ρ : CQState C Q} {σ : SubDensityOp Q} {t : ℝ}
    (ht : IsFeasible ρ σ t) (k : ℕ) :
    IsFeasible (ρ.tensorPower k) (σ.tensorPow k) (t ^ k) := by
  classical
  refine ⟨pow_nonneg ht.1 k, fun cs => opLe_of_posSemidef_sub ?_⟩
  have hi := Matrix.piTensorProduct_mono (fun i : Fin k => (ρ.stateMap (cs i)).posSemidef)
    (B := fun _ : Fin k => (t : ℂ) • σ.toOp) (fun i => Matrix.le_iff.mpr
      ((opLe_iff_posSemidef_sub (ρ.stateMap (cs i)).isHermitian
        (σ.posSemidef.smul (Complex.zero_le_real.mpr ht.1)).isHermitian).mp (ht.2 (cs i))))
  have he : piTensorProduct (fun _ : Fin k => (t : ℂ) • σ.toOp) =
      ((t ^ k : ℝ) : ℂ) • piTensorProduct (fun _ : Fin k => σ.toOp) := by
    ext x y
    simp only [piTensorProduct_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Complex.ofReal_pow]
  rw [he] at hi
  exact Matrix.le_iff.mp hi

/-- CQ tensor powers factor every two-exponent collision moment, including the empty power. -/
theorem CQState.sum_trace_rpow_tensorPower [DecidableEq Q]
    (ρ : CQState C Q) (σ : SubDensityOp Q) (a b : ℝ) (k : ℕ) :
    (∑ cs, (((ρ.tensorPower k).stateMap cs).toOp ^ a * (σ.tensorPow k).toOp ^ b).trace.re) =
      (∑ c, ((ρ.stateMap c).toOp ^ a * σ.toOp ^ b).trace.re) ^ k := by
  classical
  let f : C → ℝ := fun c => ((ρ.stateMap c).toOp ^ a * σ.toOp ^ b).trace.re
  have hr (c : C) : ((ρ.stateMap c).toOp ^ a * σ.toOp ^ b).trace =
      (f c : ℂ) := by
    have h := (Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := (ρ.stateMap c).toOp) (y := a))).trace_mul_nonneg
      (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := σ.toOp) (y := b)))
    exact Complex.ext rfl (Complex.nonneg_iff.mp h).2.symm
  have he (cs : Fin k → C) :
      (((ρ.tensorPower k).stateMap cs).toOp ^ a * (σ.tensorPow k).toOp ^ b).trace.re =
        ∏ i, ((ρ.stateMap (cs i)).toOp ^ a * σ.toOp ^ b).trace.re := by
    change ((piTensorProduct (fun i => (ρ.stateMap (cs i)).toOp) ^ a) *
      (piTensorProduct (fun _ : Fin k => σ.toOp) ^ b)).trace.re = _
    rw [PosSemidef.rpow_piTensorProduct _ (fun i => (ρ.stateMap (cs i)).posSemidef),
      PosSemidef.rpow_piTensorProduct _ (fun _ => σ.posSemidef),
      piTensorProduct_mul, trace_piTensorProduct]
    simp only [hr, ← Complex.ofReal_prod, Complex.ofReal_re]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun (_ : Fin k) c =>
    ((ρ.stateMap c).toOp ^ a * σ.toOp ^ b).trace.re)]
  simp

end InfoTheory.SmoothMinEntropy
