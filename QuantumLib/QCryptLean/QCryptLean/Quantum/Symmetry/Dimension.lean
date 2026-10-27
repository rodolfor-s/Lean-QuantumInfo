import QCryptLean.Math.Combinatorics.PermutationAction
import QCryptLean.Math.LinearAlgebra.Matrix.IdempotentTrace
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.TensorAlgebra
import QCryptLean.Quantum.Symmetry.Basic

/-! # Dimension -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators

variable {X : Type*} [Fintype X] [DecidableEq X] {d k : ℕ}

/-- The symmetric dimension formula follows from fixed-word counting. -/
theorem symmetricSubspace_dim [Nonempty X] :
    (symmetricProjector X k).trace.re =
      Nat.choose (k + Fintype.card X - 1) (Fintype.card X - 1) := by
  classical
  let : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have ht (σ : Equiv.Perm (Fin k)) :
      (permutationRepresentation (X := X) σ).trace =
        ((Finset.univ.filter fun f : Fin k → X => f ∘ σ = f).card : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, permutationRepresentation, tensorPermutation,
      Matrix.of_apply, Matrix.eq_comp_symm_iff]
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hc := Math.RepresentationTheory.sum_card_fixedBy_permFun_eq_of_fintype (β := X) k
  have he : (symmetricProjector X k).trace =
      (Nat.choose (k + Fintype.card X - 1) (Fintype.card X - 1) : ℂ) := by
    rw [symmetricProjector, Matrix.trace_smul, Matrix.trace_sum]
    simp_rw [ht]
    rw [← Nat.cast_sum, hc, Nat.cast_mul, smul_eq_mul]
    have hn : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp
  rw [he, Complex.natCast_re]

/-- The symmetric projector has rank equal to the number of occupation types. -/
theorem rank_symmetricProjector [Nonempty X] :
    (symmetricProjector X k).rank =
      Nat.choose (k + Fintype.card X - 1) (Fintype.card X - 1) := by
  have h := symmetricSubspace_dim (X := X) (k := k)
  rw [Matrix.trace_eq_rank_of_mul_self_eq _ symmetricProjector_mul_self] at h
  exact_mod_cast h

end Quantum.Symmetry
