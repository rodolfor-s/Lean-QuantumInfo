import Batteries.Tactic.OpenPrivate
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.TensorPowerPolarization
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Commutant
import QCryptLean.Quantum.Symmetry.Projected

/-!
# Tensor powers span the permutation commutant

The inclusion–exclusion identity is scalar and is reused unchanged. Matrix units
and permutation orbits live directly on function registers.
-/

noncomputable section
namespace Quantum.Symmetry
open Matrix Quantum.Operators
open scoped BigOperators
open private scalar_polarization
  from QCryptLean.Quantum.Symmetry.TensorPowerPolarization
variable {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ}

omit [Fintype X] [DecidableEq X] in
/-- Polarization expresses symmetrized tensor families as combinations of tensor powers. -/
theorem tensorFamily_polarization (A : Fin k → Op X) :
    (∑ S : Finset (Fin k), (-1 : ℂ) ^ (k - S.card) • Op.tensorPow (∑ i ∈ S, A i) k) =
      ∑ σ : Equiv.Perm (Fin k), piTensorProduct (fun i => A (σ i)) := by
  classical
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Op.tensorPow_apply,
    piTensorProduct_apply]
  exact scalar_polarization (fun i j => A i (x j) (y j))

/-- Tensor powers span the commutant of the site-permutation representation. -/
theorem span_tensorPow_eq_permCommutant :
    Submodule.span ℂ (Set.range fun A : Op X => Op.tensorPow A k) =
      commutant (Set.range fun σ : Equiv.Perm (Fin k) => permutationRepresentation (X := X) σ) := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨A, rfl⟩ _ ⟨σ, rfl⟩
    exact (tensorPow_commute_permutationRepresentation A σ).eq.symm
  · intro M hM
    have hEntry (σ : Equiv.Perm (Fin k)) (a b : Fin k → X) :
        M (a ∘ σ) (b ∘ σ) = M a b := by
      have h := hM _ ⟨σ, rfl⟩
      have he := congrArg (fun B => B * (permutationRepresentation (X := X) σ)ᴴ) h
      rw [Matrix.mul_assoc M, (tensorPermutation_unitary σ).2, Matrix.mul_one] at he
      simpa only [tensorPermutation_conj_apply] using congrFun (congrFun he a) b
    have horbit (a b : Fin k → X) :
        (∑ σ : Equiv.Perm (Fin k), Matrix.single (a ∘ σ) (b ∘ σ) (1 : ℂ)) ∈
          Submodule.span ℂ (Set.range fun A : Op X => Op.tensorPow A k) := by
      have hs (σ : Equiv.Perm (Fin k)) :
          piTensorProduct (fun i => Matrix.single (a (σ i)) (b (σ i)) (1 : ℂ)) =
            Matrix.single (a ∘ σ) (b ∘ σ) (1 : ℂ) := by
        ext x y
        simp only [piTensorProduct_apply, Matrix.single_apply]
        simp only [ite_and, Finset.prod_ite_zero, Finset.mem_univ, forall_const,
          Finset.prod_const_one, ← funext_iff]
        rfl
      have hp := tensorFamily_polarization (fun i => Matrix.single (a i) (b i) (1 : ℂ))
      simp_rw [hs] at hp
      rw [← hp]
      exact Submodule.sum_mem _ fun S _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    have hterm (σ : Equiv.Perm (Fin k)) :
        (∑ a : Fin k → X, ∑ b : Fin k → X,
          M a b • Matrix.single (a ∘ σ) (b ∘ σ) (1 : ℂ)) = M := by
      let e := Equiv.arrowCongr σ.symm (Equiv.refl X)
      have he (a : Fin k → X) : e a = a ∘ σ := rfl
      have hcoeff (a b : Fin k → X) : M a b = M (e a) (e b) := (hEntry σ a b).symm
      conv_lhs =>
        arg 2; ext a; arg 2; ext b; rw [hcoeff a b]
      simp only [← he, smul_single, smul_eq_mul, mul_one]
      rw [Equiv.sum_comp e (fun a => ∑ b, Matrix.single a (e b) (M a (e b)))]
      calc
        _ = ∑ a : Fin k → X, ∑ b : Fin k → X, Matrix.single a b (M a b) := by
          apply Finset.sum_congr rfl
          intro a _
          exact Equiv.sum_comp e (fun b => Matrix.single a b (M a b))
        _ = M := (Matrix.matrix_eq_sum_single M).symm
    have hc : (Fintype.card (Equiv.Perm (Fin k)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hsum : (∑ a : Fin k → X, ∑ b : Fin k → X,
        M a b • (∑ σ : Equiv.Perm (Fin k), Matrix.single (a ∘ σ) (b ∘ σ) (1 : ℂ))) =
          (Fintype.card (Equiv.Perm (Fin k)) : ℂ) • M := by
      simp only [Finset.smul_sum]
      rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_comm), Finset.sum_comm]
      simp only [hterm, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    have hm : (∑ a : Fin k → X, ∑ b : Fin k → X,
        M a b • (∑ σ : Equiv.Perm (Fin k), Matrix.single (a ∘ σ) (b ∘ σ) (1 : ℂ))) ∈
          Submodule.span ℂ (Set.range fun A : Op X => Op.tensorPow A k) :=
      Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
        Submodule.smul_mem _ _ (horbit a b)
    rw [hsum] at hm
    have h := Submodule.smul_mem _ (Fintype.card (Equiv.Perm (Fin k)) : ℂ)⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h

end Quantum.Symmetry
