import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Bell De Finetti Domination -/


noncomputable section

open scoped BigOperators

namespace Quantum.Symmetry

/-- The `ℤ₂×ℤ₂` character table `χ_k(p)` (rows `k = I,XX,YY,ZZ`; columns `p = β₀₀,β₀₁,β₁₀,β₁₁`),
each `±1`: the eigenvalue of the bilateral Pauli `G k` on Bell state `p`. -/
private def bellCharE : Fin 4 → Fin 4 → ℂ :=
  ![![1,1,1,1], ![1,1,-1,-1], ![-1,1,1,-1], ![1,-1,1,-1]]

/-- Single-pair character orthogonality (the `ℤ₂×ℤ₂` column orthogonality of the Bell table). -/
private theorem bellCharOrtho (p q : Fin 4) :
    (4:ℂ)⁻¹ * ∑ k : Fin 4, bellCharE k p * star (bellCharE k q) = if p = q then 1 else 0 := by
  simp only [Fin.sum_univ_four, bellCharE, Matrix.cons_val]
  fin_cases p <;> fin_cases q <;> norm_num


end Quantum.Symmetry
