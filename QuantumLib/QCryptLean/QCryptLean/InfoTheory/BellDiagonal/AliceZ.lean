import QCryptLean.Math.LinearAlgebra.Matrix.KroneckerSandwich
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic

/-! # Alice's computational-basis pinching on a pair of bits -/

noncomputable section

namespace InfoTheory.BellDiagonal

open Quantum.Operators Quantum.Channels Matrix
open scoped Kronecker

/-- Project onto Alice's value, retaining Bob's bit as the second coordinate. -/
def aliceZProj (z : Fin 2) : Op (Fin 2 × Fin 2) :=
  diagonal fun p => if p.1 = z then 1 else 0

/-- Alice's pinching is a channel on the natural pair register. -/
theorem isChannel_aliceZDephase : IsChannel (krausMap aliceZProj) := by
  refine ⟨isCompletelyPositive_krausMap _, (isTracePreserving_krausMap_iff _).mpr ?_⟩
  ext p q
  simp [aliceZProj, diagonal_mul_diagonal,
    Matrix.sum_apply, diagonal_apply, one_apply]

/-- Alice's computational-basis dephasing, without enumerating the pair register. -/
def aliceZDephase (σ : DensityOp (Fin 2 × Fin 2)) : DensityOp (Fin 2 × Fin 2) :=
  isChannel_aliceZDephase.applyDensity σ

/-- Alice pinching retains precisely the matrix entries with the same Alice index. -/
theorem aliceZDephase_apply (σ : DensityOp (Fin 2 × Fin 2)) (p q : Fin 2 × Fin 2) :
    (aliceZDephase σ).toOp p q = if p.1 = q.1 then σ.toOp p q else 0 := by
  change (∑ z, aliceZProj z * σ.toOp * (aliceZProj z)ᴴ) p q = _
  simp only [Matrix.sum_apply, aliceZProj, diagonal_conjTranspose, diagonal_mul,
    mul_diagonal, Pi.star_apply, apply_ite (Star.star : ℂ → ℂ), star_one, star_zero]
  by_cases hpq : p.1 = q.1
  · simp [hpq]
  · simp [hpq]

/-- Measuring Alice retains the matching row and column of her register. -/
theorem aliceZProj_kronecker_one_sandwich_apply {R : Type*} [Fintype R] [DecidableEq R]
    (M : Op ((Fin 2 × Fin 2) × R)) (z : Fin 2)
    (a b : Fin 2 × Fin 2) (e f : R) :
    ((aliceZProj z ⊗ₖ (1 : Op R)) * M * (aliceZProj z ⊗ₖ (1 : Op R))) (a,e) (b,f) =
      if a.1 = z ∧ b.1 = z then M (a,e) (b,f) else 0 := by
  rw [kronecker_one_sandwich_apply]
  simp only [aliceZProj, diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.mem_univ, ↓reduceIte, Finset.sum_ite_eq', one_mul, mul_one]
  by_cases ha : a.1 = z <;> by_cases hb : b.1 = z <;> simp [ha, hb]


end InfoTheory.BellDiagonal
