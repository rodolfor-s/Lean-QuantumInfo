import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import QCryptLean.Math.Analysis.ImaginaryIdentityTheorem
import QCryptLean.Math.SpectralTheory.HermitianCpowAnalytic

/-! # Unitary Centralizer Tensor Powers -/


open Matrix   Math.SpectralTheory
open scoped BigOperators ComplexOrder MatrixOrder Topology

noncomputable section

namespace Quantum.Symmetry

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- Applying a scalar function to a diagonal matrix preserves its commutant. -/
lemma commute_diagonal_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℂ) (f : ℂ → ℂ) {T : Matrix ι ι ℂ}
    (h : Commute (Matrix.diagonal lam) T) : Commute (Matrix.diagonal (f ∘ lam)) T := by
  ext i j
  have hij := congrFun (congrFun h.eq i) j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij ⊢
  by_cases heq : lam i = lam j
  · simp only [Function.comp_apply, heq, mul_comm]
  · have hzero : T i j = 0 := by
      apply (mul_eq_zero.mp (show (lam i - lam j) * T i j = 0 by
        rw [sub_mul, hij, mul_comm (T i j), sub_self])).resolve_left (sub_ne_zero.mpr heq)
    simp only [hzero, mul_zero, zero_mul]

end Quantum.Symmetry
