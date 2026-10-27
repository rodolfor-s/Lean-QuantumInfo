import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.Probability.MatrixHaarAverage
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Commutant
import QCryptLean.Quantum.Symmetry.CommutantAlgebra
import QCryptLean.Quantum.Symmetry.UnitaryCentralizer

/-! # Tensor-power unitary representations with an arbitrary untouched register -/
noncomputable section
namespace Quantum.Symmetry
open Matrix Quantum.Operators
open scoped Kronecker
variable (A Y : Type*) [Fintype A] [Fintype Y] [DecidableEq A] [DecidableEq Y] (k : ℕ)

/-- A unitary acts identically at every site and leaves the first register untouched. -/
def tensorUnitaryRepresentation : unitaryGroup Y ℂ →* unitaryGroup (A × (Fin k → Y)) ℂ where
  toFun U := ⟨(1 : Op A) ⊗ₖ Op.tensorPow U.val k, kronecker_mem_unitary (one_mem _) (by
    apply mem_unitaryGroup_iff'.mpr
    change (piTensorProduct (fun _ : Fin k => U.val))ᴴ * piTensorProduct (fun _ => U.val) = 1
    rw [conjTranspose_piTensorProduct, piTensorProduct_mul]
    simp only [← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, piTensorProduct_one])⟩
  map_one' := by
    apply Subtype.ext
    change (1 : Op A) ⊗ₖ piTensorProduct (fun _ : Fin k => (1 : Op Y)) = 1
    rw [piTensorProduct_one, one_kronecker_one]
  map_mul' U V := by
    apply Subtype.ext
    change (1 : Op A) ⊗ₖ Op.tensorPow (U.val * V.val) k =
      ((1 : Op A) ⊗ₖ Op.tensorPow U.val k) * ((1 : Op A) ⊗ₖ Op.tensorPow V.val k)
    rw [← mul_kronecker_mul, Matrix.one_mul, Op.tensorPow_mul]

/-- Tensor-power unitary representations are continuous in the entrywise topology. -/
theorem continuous_tensorUnitaryRepresentation :
    Continuous (tensorUnitaryRepresentation A Y k) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun U : unitaryGroup Y ℂ =>
    (1 : Op A) i.1 j.1 * ∏ t : Fin k, U.val (i.2 t) (j.2 t))
  exact continuous_const.mul (continuous_finsetProd _ fun t _ =>
    (continuous_apply (j.2 t)).comp ((continuous_apply (i.2 t)).comp continuous_subtype_val))

variable {A Y k}

/-- The commutant with an untouched register is spanned by matrices tensored with permutations. -/
theorem mem_tensorPermSpan_of_commute_unitary (M : Op (A × (Fin k → Y)))
    (hM : ∀ U : unitaryGroup Y ℂ, Commute (tensorUnitaryRepresentation A Y k U).val M) :
    M ∈ Submodule.span ℂ {T | ∃ (D : Op A) (σ : Equiv.Perm (Fin k)),
      T = D ⊗ₖ permutationRepresentation (X := Y) σ} := by
  let B (a b : A) : Op (Fin k → Y) := M.submatrix (fun i => (a,i)) (fun j => (b,j))
  have hB (a b : A) : B a b ∈ permSpan (X := Y) k := by
    rw [← commutant_matrixTensorPow_eq_permSpan]
    rintro _ ⟨D, rfl⟩
    apply (commute_tensorPow_of_unitaryCentralizer ∅ (by simp) (B a b) _ D (by simp)).eq
    intro U _
    ext i j
    have h := congrFun (congrFun (hM U).eq (a,i)) (b,j)
    change (((1 : Op A) ⊗ₖ Op.tensorPow U.val k) * M) (a,i) (b,j) =
      (M * ((1 : Op A) ⊗ₖ Op.tensorPow U.val k)) (a,i) (b,j) at h
    simpa [Matrix.mul_apply, kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
      apply_ite, B] using h
  have he : M = ∑ a : A, ∑ b : A, (single a b (1 : ℂ)) ⊗ₖ B a b := by
    ext ⟨a,i⟩ ⟨b,j⟩
    simp [Matrix.sum_apply, kroneckerMap_apply, Matrix.single_apply, B, ite_and]
  rw [he]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  have hb := hB a b
  change B a b ∈ Submodule.span ℂ (Set.range fun σ : Equiv.Perm (Fin k) =>
    permutationRepresentation (X := Y) σ) at hb
  generalize B a b = D at hb ⊢
  induction hb using Submodule.span_induction with
  | mem D hD =>
      obtain ⟨σ, rfl⟩ := hD
      exact Submodule.subset_span ⟨single a b 1, σ, rfl⟩
  | zero => simpa only [kronecker_zero] using (Submodule.zero_mem _)
  | add D E _ _ hD hE => simpa only [kronecker_add] using Submodule.add_mem _ hD hE
  | smul c D _ hD => simpa only [kronecker_smul] using Submodule.smul_mem _ c hD

end Quantum.Symmetry
