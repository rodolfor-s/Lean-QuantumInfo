import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Gates
import QCryptLean.Quantum.Symmetry.Bell
import QCryptLean.Quantum.Symmetry.BellBasis
import QCryptLean.Quantum.Symmetry.BellMixture

/-! # Bell Covariance -/


noncomputable section

namespace Quantum.Gates

open Quantum.Operators Quantum.Symmetry Matrix
open scoped Kronecker

/-- Bob's bit flip changes the Bell bit label and preserves the phase label. -/
theorem one_kronecker_pauliX_mul_bellKet (p b : Fin 2) :
    ((1 : Op (Fin 2)) ⊗ₖ reindex qubitEquiv qubitEquiv Quantum.Symmetry.pauliX) *
      ((bellLabelKet (finProdFinEquiv (p,b))).reindex (qubitEquiv.prodCongr qubitEquiv)) =
      (bellLabelKet (finProdFinEquiv (p,b + 1))).reindex
        (qubitEquiv.prodCongr qubitEquiv) := by
  ext ⟨i,j⟩
  change ((_ : Op (Fin 2 × Fin 2)) *ᵥ (_ : (Fin 2 × Fin 2) → ℂ)) (i,j) = _
  fin_cases p <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [Ket.reindex, bellLabelKet, bellKet, qubitEquiv, finTwoEquiv,
      Quantum.Symmetry.pauliX, Matrix.mulVec, dotProduct, kroneckerMap_apply,
      Fintype.sum_prod_type,
      Fin.sum_univ_two, reindex_apply, submatrix_apply, finProdFinEquiv]

/-- Bob's phase flip changes the phase label, with the exact bit-dependent sign. -/
theorem one_kronecker_pauliZ_mul_bellKet (p b : Fin 2) :
    ((1 : Op (Fin 2)) ⊗ₖ reindex qubitEquiv qubitEquiv Quantum.Symmetry.pauliZ) *
      ((bellLabelKet (finProdFinEquiv (p,b))).reindex (qubitEquiv.prodCongr qubitEquiv)) =
      (if b = 0 then (1 : ℂ) else -1) •
        (bellLabelKet (finProdFinEquiv (p + 1,b))).reindex
          (qubitEquiv.prodCongr qubitEquiv) := by
  ext ⟨i,j⟩
  change ((_ : Op (Fin 2 × Fin 2)) *ᵥ (_ : (Fin 2 × Fin 2) → ℂ)) (i,j) =
    (if b = 0 then (1 : ℂ) else -1) *
      ((bellLabelKet (finProdFinEquiv (p + 1,b))).reindex
        (qubitEquiv.prodCongr qubitEquiv)).vec (i,j)
  fin_cases p <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [Ket.reindex, bellLabelKet, bellKet, qubitEquiv, finTwoEquiv,
      Quantum.Symmetry.pauliZ, Matrix.mulVec, dotProduct, kroneckerMap_apply,
      Fintype.sum_prod_type,
      Fin.sum_univ_two, reindex_apply, submatrix_apply, finProdFinEquiv]

/-- Bob's Y gate flips both Bell labels, retaining its exact imaginary phase. -/
theorem one_kronecker_pauliY_mul_bellKet (p b : Fin 2) :
    ((1 : Op (Fin 2)) ⊗ₖ reindex qubitEquiv qubitEquiv Quantum.Symmetry.pauliY) *
      ((bellLabelKet (finProdFinEquiv (p,b))).reindex (qubitEquiv.prodCongr qubitEquiv)) =
      (if b = 0 then Complex.I else -Complex.I) •
        (bellLabelKet (finProdFinEquiv (p + 1,b + 1))).reindex
          (qubitEquiv.prodCongr qubitEquiv) := by
  ext ⟨i,j⟩
  change ((_ : Op (Fin 2 × Fin 2)) *ᵥ (_ : (Fin 2 × Fin 2) → ℂ)) (i,j) =
    (if b = 0 then Complex.I else -Complex.I) *
      ((bellLabelKet (finProdFinEquiv (p + 1,b + 1))).reindex
        (qubitEquiv.prodCongr qubitEquiv)).vec (i,j)
  fin_cases p <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [Ket.reindex, bellLabelKet, bellKet, qubitEquiv, finTwoEquiv,
      Quantum.Symmetry.pauliY, Matrix.mulVec, dotProduct, kroneckerMap_apply,
      Fintype.sum_prod_type,
      Fin.sum_univ_two, reindex_apply, submatrix_apply, finProdFinEquiv]

/-- Bilateral Hadamards exchange the phase and bit labels, including the singlet sign. -/
theorem hadamard_kronecker_mul_bellKet (p b : Fin 2) :
    (reindex qubitEquiv qubitEquiv hadamard ⊗ₖ reindex qubitEquiv qubitEquiv hadamard) *
      ((bellLabelKet (finProdFinEquiv (p,b))).reindex (qubitEquiv.prodCongr qubitEquiv)) =
      (if p = 1 ∧ b = 1 then (-1 : ℂ) else 1) •
        (bellLabelKet (finProdFinEquiv (b,p))).reindex
          (qubitEquiv.prodCongr qubitEquiv) := by
  have hs : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  ext ⟨i,j⟩
  change ((_ : Op (Fin 2 × Fin 2)) *ᵥ (_ : (Fin 2 × Fin 2) → ℂ)) (i,j) =
    (if p = 1 ∧ b = 1 then (-1 : ℂ) else 1) *
      ((bellLabelKet (finProdFinEquiv (b,p))).reindex
        (qubitEquiv.prodCongr qubitEquiv)).vec (i,j)
  fin_cases p <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [Ket.reindex, bellLabelKet, bellKet, qubitEquiv, finTwoEquiv,
      hadamard, Matrix.mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, reindex_apply, submatrix_apply, finProdFinEquiv] <;>
    field_simp <;> first | linear_combination -hs | linear_combination hs

end Quantum.Gates
