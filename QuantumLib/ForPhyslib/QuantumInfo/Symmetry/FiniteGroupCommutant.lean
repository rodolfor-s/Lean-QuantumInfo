import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Finite Group Commutant -/


open Matrix 
open scoped BigOperators

noncomputable section

namespace Quantum.Symmetry

/-- Conjugation averaging for a finite-group matrix representation. -/
def finiteGroupMatrixAverage {G ι : Type*} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ) (X : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g * X * ρ g⁻¹

/-- A finite-group conjugation average commutes with its representation. -/
lemma finiteGroupMatrixAverage_commute {G ι : Type*} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ) (X : Matrix ι ι ℂ) (g : G) :
    Commute (ρ g) (finiteGroupMatrixAverage ρ X) := by
  change ρ g * _ = _ * ρ g
  unfold finiteGroupMatrixAverage
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  change ρ g * (ρ h * X * ρ h⁻¹) = ρ (g * h) * X * ρ (g * h)⁻¹ * ρ g
  rw [_root_.mul_inv_rev, map_mul, map_mul]
  simp only [mul_assoc, ← map_mul, inv_mul_cancel, mul_one]
  rw [map_mul, mul_assoc]

/-- Finite-group conjugation averaging is complex linear. -/
def finiteGroupMatrixAverageLinear {G ι : Type*} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun := finiteGroupMatrixAverage ρ
  map_add' A B := by
    simp only [finiteGroupMatrixAverage, mul_add, add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' c A := by
    change finiteGroupMatrixAverage ρ (c • A) = c • finiteGroupMatrixAverage ρ A
    simp only [finiteGroupMatrixAverage, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]
    exact smul_comm _ _ _

/-- A matrix already in the commutant is fixed by conjugation averaging. -/
lemma finiteGroupMatrixAverage_eq_self {G ι : Type*} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ) (X : Matrix ι ι ℂ)
    (hX : ∀ g, Commute (ρ g) X) : finiteGroupMatrixAverage ρ X = X := by
  have hterm (g : G) : ρ g * X * ρ g⁻¹ = X := by
    rw [(hX g).eq, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [finiteGroupMatrixAverage, hterm, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

end Quantum.Symmetry
