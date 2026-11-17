import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Conjugating matrix units

A single supported Kraus column determines the conjugate of its diagonal matrix unit.
-/

open Matrix

namespace Matrix

/-- Conjugating a diagonal matrix unit by a Kraus operator whose column at the unit's index is a
single scaled basis vector. -/
theorem conj_single_of_mul_single {P Q R : Type*} [Fintype P] [DecidableEq P]
    [DecidableEq Q] [Semiring R] [StarRing R] (K : Matrix Q P R) (i : P)
    (i' : Q) (μ : R) (h : K * Matrix.single i i (1 : R) = Matrix.single i' i μ) :
    K * Matrix.single i i (1 : R) * Kᴴ = Matrix.single i' i' (μ * star μ) := by
  have hS : Matrix.single i i (1 : R) * (Matrix.single i i (1 : R))ᴴ =
      Matrix.single i i (1 : R) := by
    rw [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, mul_one]
  calc K * Matrix.single i i (1 : R) * Kᴴ
         = K * (Matrix.single i i (1 : R) * (Matrix.single i i (1 : R))ᴴ) * Kᴴ := by rw [hS]
    _ = (K * Matrix.single i i (1 : R)) * (K * Matrix.single i i (1 : R))ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = Matrix.single i' i' (μ * star μ) := by
        rw [h, Matrix.conjTranspose_single, Matrix.single_mul_single_same]

/-- Right multiplication by a matrix permuting coordinate projectors relabels a matrix-unit
column and scales it by the corresponding matrix entry. -/
theorem single_mul_of_conj_single {X Y R : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq Y] [Semiring R] [StarRing R] [NoZeroDivisors R] [Nontrivial R]
    (U : Matrix X X R) (π : Equiv.Perm (X))
    (hperm : ∀ ν, U * (Matrix.single ν ν 1 : Matrix X X R) * Uᴴ = Matrix.single (π ν) (π ν) 1)
    (a : Y) (c : X) :
    (Matrix.single a c 1 : Matrix (Y) (X) R) * U =
      (U c (π.symm c)) • (Matrix.single a (π.symm c) 1 : Matrix (Y) (X) R) := by
  -- entry of the conjugated projector: `(U |ν⟩⟨ν| U†)_{ij} = U_{iν} · conj U_{jν}`
  have hconj : ∀ ν i j,
      (U * (Matrix.single ν ν 1 : Matrix X X R) * Uᴴ) i j = U i ν * star (U j ν) := by
    intro ν i j
    rw [Matrix.mul_apply, Finset.sum_eq_single ν]
    · rw [Matrix.mul_single_apply_same, mul_one, Matrix.conjTranspose_apply]
    · intro l _ hl; rw [Matrix.mul_single_apply_of_ne (hbj := hl), zero_mul]
    · intro hcon; exact (hcon (Finset.mem_univ _)).elim
  have hkey : ∀ ν i j, U i ν * star (U j ν) =
      (if i = π ν then (1 : R) else 0) * (if j = π ν then 1 else 0) := by
    intro ν i j
    rw [← hconj ν i j, hperm ν, Matrix.single_apply]
    rcases eq_or_ne i (π ν) with hi | hi <;> rcases eq_or_ne j (π ν) with hj | hj <;>
      simp [hi, hj, eq_comm]
  have hdiag : ∀ ν, U (π ν) ν * star (U (π ν) ν) = 1 := by
    intro ν; rw [hkey ν (π ν) (π ν), ite_eq_left rfl, mul_one]
  have hoff : ∀ ν i, i ≠ π ν → U i ν = 0 := by
    intro ν i hi
    have h := hkey ν i (π ν)
    rw [ite_eq_right hi, ite_eq_left rfl, zero_mul] at h
    have hne : star (U (π ν) ν) ≠ 0 := fun hz => by
      simpa [hz] using hdiag ν
    exact (mul_eq_zero.mp h).resolve_right hne
  ext p q
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
  by_cases hp : p = a
  · subst hp
    rw [Matrix.single_mul_apply_same, one_mul]
    by_cases hq : q = π.symm c
    · subst hq; rw [ite_eq_left ⟨rfl, rfl⟩, mul_one]
    · rw [ite_eq_right (fun h => hq h.2.symm), mul_zero]
      exact hoff q c (fun hcon => hq (by rw [hcon, Equiv.symm_apply_apply]))
  · rw [Matrix.single_mul_apply_of_ne (h := hp), ite_eq_right (fun h => hp h.1.symm), mul_zero]

/-- The nonzero entry in a column of a projector-permuting matrix has unit squared modulus. -/
theorem mul_star_eq_one_of_conj_single {X R : Type*} [Fintype X] [DecidableEq X]
    [Semiring R] [StarRing R]
    (U : Matrix X X R) (π : Equiv.Perm (X))
    (hperm : ∀ ν, U * (Matrix.single ν ν 1 : Matrix X X R) * Uᴴ = Matrix.single (π ν) (π ν) 1)
    (ν : X) :
    U (π ν) ν * star (U (π ν) ν) = 1 := by
  have hconj : (U * (Matrix.single ν ν 1 : Matrix X X R) * Uᴴ) (π ν) (π ν) =
      U (π ν) ν * star (U (π ν) ν) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single ν]
    · rw [Matrix.mul_single_apply_same, mul_one, Matrix.conjTranspose_apply]
    · intro l _ hl; rw [Matrix.mul_single_apply_of_ne (hbj := hl), zero_mul]
    · intro hc; exact (hc (Finset.mem_univ _)).elim
  rw [← hconj, hperm ν, Matrix.single_apply, ite_eq_left ⟨rfl, rfl⟩]

end Matrix
