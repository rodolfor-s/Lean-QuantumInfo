import QCryptLean.Math.Combinatorics.PermutationAction
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.ProjectionDiagonal
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Projector
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Dimension
import QCryptLean.Quantum.Symmetry.Projected

/-! # Projected Algebra -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators

variable {X : Type*} [Fintype X] [DecidableEq X] {d k : ℕ}

/-- The projected dimension follows by diagonalization and fixed-word counting. -/
theorem trace_tensorPow_projection_mul_symmetricProjector {r : ℕ} [NeZero r]
    (P : Op X) (hP : P.IsHermitian) (hPP : P * P = P) (ht : P.trace = (r : ℂ)) :
    (Op.tensorPow P k * symmetricProjector X k).trace =
      ((k + r - 1).choose (r - 1) : ℂ) := by
  classical
  obtain ⟨U, s, hdiag⟩ := hP.exists_unitary_diagonal_indicator P hPP
  have hU : U.valᴴ * U.val = 1 := Unitary.coe_star_mul_self U
  have hs : s.card = r := by
    rw [hdiag, Matrix.trace_mul_cycle, hU, one_mul, Matrix.trace_diagonal,
      Finset.sum_boole] at ht
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
      (Nat.cast_inj.mp ht : (Finset.univ.filter (fun x => x ∈ s)).card = r)
  have hsne : s.Nonempty := Finset.card_pos.mp (hs ▸ NeZero.pos r)
  let : Nonempty s := hsne.coe_sort
  let D : Op X := diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)
  have hconj : (Op.tensorPow (U.val * D * U.valᴴ) k * symmetricProjector X k).trace =
      (Op.tensorPow D k * symmetricProjector X k).trace := by
    rw [Op.tensorPow_mul, Op.tensorPow_mul]
    rw [mul_assoc (Op.tensorPow U.val k * Op.tensorPow D k),
      (tensorPow_commute_symmetricProjector U.valᴴ).eq,
      ← mul_assoc, Matrix.trace_mul_cycle,
      ← mul_assoc, ← Op.tensorPow_mul U.valᴴ U.val, hU]
    simp only [Op.tensorPow, piTensorProduct_one, one_mul]
  rw [hdiag, hconj]
  have htr (σ : Equiv.Perm (Fin k)) :
      (Op.tensorPow D k * permutationRepresentation σ).trace =
        ((Finset.univ.filter fun f : Fin k → s => f ∘ σ = f).card : ℂ) := by
    have hcount : (Finset.univ.filter (fun f : Fin k → X =>
        (∀ i, f i ∈ s) ∧ f ∘ σ = f)).card =
        (Finset.univ.filter (fun f : Fin k → s => f ∘ σ = f)).card := by
      symm
      refine Finset.card_bij (fun f _ => fun i => (f i).val) ?_ ?_ ?_
      · intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
        exact ⟨fun i => (f i).property, congrArg (fun f => fun i => (f i).val) hf⟩
      · intro f _ g _ h
        funext i
        exact Subtype.ext (congrFun h i)
      · intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
        refine ⟨fun i => ⟨f i, hf.1 i⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        funext i
        exact Subtype.ext (congrFun hf.2 i)
    have hD : Op.tensorPow D k = diagonal (fun f => if ∀ i, f i ∈ s then 1 else 0) := by
      ext f g
      simp only [Op.tensorPow_apply, D, diagonal_apply]
      simp only [Finset.prod_ite_zero, Finset.mem_univ, forall_const,
        Finset.prod_const_one, ← funext_iff]
    rw [hD, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.diagonal_mul]
    simp only [permutationRepresentation, tensorPermutation, Matrix.of_apply,
      Matrix.eq_comp_symm_iff]
    have he (f : Fin k → X) :
        (if ∀ i, f i ∈ s then (1 : ℂ) else 0) * (if f ∘ σ = f then 1 else 0) =
          if (∀ i, f i ∈ s) ∧ f ∘ σ = f then 1 else 0 := by
      split_ifs <;> simp_all
    simp only [he, Finset.sum_boole, hcount]
  rw [symmetricProjector, Matrix.mul_smul, Finset.mul_sum, Matrix.trace_smul, Matrix.trace_sum]
  simp_rw [htr]
  rw [← Nat.cast_sum,
    Math.RepresentationTheory.sum_card_fixedBy_permFun_eq_of_fintype (β := s) k,
    Fintype.card_coe, hs, Nat.cast_mul, smul_eq_mul]
  have hn : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

/-- The native compression has the same dimension as the original commuting product. -/
theorem trace_projectedSymmetricProjector {r : ℕ} [NeZero r]
    (P : Op X) (hP : IsOrthogonalProjector P) (ht : P.trace = (r : ℂ)) :
    (projectedSymmetricProjector P k).trace = ((k + r - 1).choose (r - 1) : ℂ) := by
  rw [projectedSymmetricProjector_eq P hP]
  exact trace_tensorPow_projection_mul_symmetricProjector P hP.1 hP.2 ht

end Quantum.Symmetry
