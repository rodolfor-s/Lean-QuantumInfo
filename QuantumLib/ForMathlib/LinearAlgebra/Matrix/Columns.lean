import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Matrix columns and multiplication by matrix units

Matrix columns and multiplication by matrix units.
-/

open scoped Matrix BigOperators

noncomputable section

/-- A matrix with a specified column sends a matrix unit to that column's matrix unit. -/
theorem _root_.Matrix.mul_single_eq_single_of_apply_eq_ite
    {X Y Z R : Type*} [Fintype X] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [Semiring R] (A : Matrix Y X R) (P : X) (P' : Y) (w : Z) (μ : R)
    (h : ∀ i, A i P = if P' = i then μ else 0) :
    A * Matrix.single P w (1 : R) = Matrix.single P' w μ := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.single_apply, ite_and, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ P), h i]
  by_cases hj : w = j <;> by_cases hi : P' = i <;> simp [hj, hi]

/-- Scalar multiplication preserves a column supported at one row. -/
theorem _root_.Matrix.smul_apply_eq_ite_of_apply_eq_ite
    {X Y R : Type*} [DecidableEq Y] [Semiring R] (c : R) (A : Matrix Y X R)
    (x : X) (x' : Y) (μ : R)
    (h : ∀ i, A i x = if x' = i then μ else 0) (i : Y) :
    (c • A) i x = if x' = i then c * μ else 0 := by
  rw [Matrix.smul_apply, smul_eq_mul, h i]
  by_cases hh : x' = i <;> simp [hh]

end
