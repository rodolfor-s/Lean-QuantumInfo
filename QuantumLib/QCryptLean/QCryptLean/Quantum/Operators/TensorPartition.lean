import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor

/-! # Partitioning and permuting tensor families of sub-density states -/

namespace Quantum.Operators

open Matrix
open scoped Kronecker

variable {X Y Z I J : Type*} [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Relabelling the sites relabels the tensor factors by the inverse equivalence. -/
theorem SubDensityOp.tensorFamily_reindex (e : I ≃ J) (ρ : I → SubDensityOp X) :
    (tensorFamily ρ).reindex (Equiv.arrowCongr e (Equiv.refl X)) =
      tensorFamily (fun j => ρ (e.symm j)) := by
  apply SubDensityOp.ext
  ext x y
  change (∏ i, (ρ i).toOp (x (e i)) (y (e i))) =
    ∏ j, (ρ (e.symm j)).toOp (x j) (y j)
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.prod_comp e (fun j => (ρ (e.symm j)).toOp (x j) (y j)))

/-- Tensor associativity is register associativity, without a dimension cast. -/
theorem SubDensityOp.kronecker_assoc (ρ : SubDensityOp X) (σ : SubDensityOp Y)
    (τ : SubDensityOp Z) :
    ((ρ.kronecker σ).kronecker τ).reindex (Equiv.prodAssoc X Y Z) =
      ρ.kronecker (σ.kronecker τ) := by
  apply SubDensityOp.ext
  ext ⟨x,y,z⟩ ⟨x',y',z'⟩
  exact mul_assoc _ _ _

/-- Split a function on a sum of site types into its two restrictions. -/
theorem SubDensityOp.tensorFamily_sum (ρ : I ⊕ J → SubDensityOp X) :
    (tensorFamily ρ).reindex (Equiv.sumArrowEquivProdArrow I J X) =
      (tensorFamily (fun i => ρ (Sum.inl i))).kronecker
        (tensorFamily (fun j => ρ (Sum.inr j))) := by
  apply SubDensityOp.ext
  ext x y
  exact Fintype.prod_sum_type _

/-- Splitting any finite site partition is a permutation followed by the sum split. -/
theorem SubDensityOp.tensorFamily_partition {K : Type*} [Fintype K] [DecidableEq K]
    (e : K ≃ I ⊕ J) (ρ : K → SubDensityOp X) :
    (tensorFamily ρ).reindex
      ((Equiv.arrowCongr e (Equiv.refl X)).trans (Equiv.sumArrowEquivProdArrow I J X)) =
      (tensorFamily (fun i => ρ (e.symm (Sum.inl i)))).kronecker
        (tensorFamily (fun j => ρ (e.symm (Sum.inr j)))) := by
  have h := (tensorFamily_reindex e ρ)
  have hs := congrArg (SubDensityOp.reindex (Equiv.sumArrowEquivProdArrow I J X)) h
  rw [tensorFamily_sum] at hs
  exact hs

/-- Splitting a finite sequence gives its prefix and suffix as product registers. -/
theorem SubDensityOp.tensorFamily_split {a b : ℕ} (ρ : Fin (a + b) → SubDensityOp X) :
    (tensorFamily ρ).reindex (Fin.appendEquiv a b).symm =
      (tensorFamily (fun i => ρ (Fin.castAdd b i))).kronecker
        (tensorFamily (fun j => ρ (Fin.natAdd a j))) := by
  apply SubDensityOp.ext
  ext x y
  change (∏ i, (ρ i).toOp (Fin.append x.1 x.2 i) (Fin.append y.1 y.2 i)) = _
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rfl

end Quantum.Operators
