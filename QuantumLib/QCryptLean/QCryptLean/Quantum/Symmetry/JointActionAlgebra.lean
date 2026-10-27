import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.FiniteGroupCommutant
import QCryptLean.Quantum.Symmetry.FiniteGroupTensorCommutant
import QCryptLean.Quantum.Symmetry.Commutant
import QCryptLean.Quantum.Symmetry.JointAction
import QCryptLean.Quantum.Symmetry.JointHelpers
import QCryptLean.Quantum.Symmetry.Projected
import QCryptLean.Quantum.Symmetry.TensorPowerSpan

/-! # Joint Action Algebra -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators

variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G] {d k : ℕ}

/-- The constrained powers span the commutant of independent actions and permutations. -/
theorem span_centralizer_tensorPow_eq [Finite G] (ρ : G →* Op X) (k : ℕ) :
    Submodule.span ℂ (centralizerTensorPowers ρ k) = commutant (Set.range (jointAction ρ k)) := by
  classical
  let := Fintype.ofFinite G
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨A, rfl⟩
    apply (mem_jointAction_commutant_iff ρ k _).mpr
    constructor
    · intro v
      change piTensorProduct (fun i => ρ (v i)) * Op.tensorPow A.val k =
        Op.tensorPow A.val k * piTensorProduct (fun i => ρ (v i))
      simp only [Op.tensorPow, piTensorProduct_mul]
      congr 1
      funext i
      exact A.property _ ⟨v i, rfl⟩
    · intro σ
      exact (tensorPow_commute_permutationRepresentation A.val σ).symm
  · intro T hT
    obtain ⟨hG, hP⟩ := (mem_jointAction_commutant_iff ρ k T).mp hT
    have hp : T ∈ Submodule.span ℂ (Set.range fun A : Op X => Op.tensorPow A k) := by
      rw [span_tensorPow_eq_permCommutant]
      rintro _ ⟨σ, rfl⟩
      exact (hP σ).eq
    let L := finiteGroupMatrixAverageLinear (tensorFamilyRep ρ k)
    have hLT : L T = T := finiteGroupMatrixAverage_eq_self _ _ hG
    rw [← hLT]
    clear hT hG hP hLT
    induction hp using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨A, rfl⟩ := hM
      change finiteGroupMatrixAverage _ _ ∈ _
      rw [finiteGroupMatrixAverage_tensorPow]
      apply Submodule.subset_span
      refine ⟨⟨finiteGroupMatrixAverage ρ A, ?_⟩, rfl⟩
      rintro M ⟨g, rfl⟩
      exact (finiteGroupMatrixAverage_commute ρ A g).eq
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add A B _ _ hA hB => rw [map_add]; exact Submodule.add_mem _ hA hB
    | smul c A _ hA => rw [map_smul]; exact Submodule.smul_mem _ c hA

/-- The commutant of constrained powers is the span of independent actions and permutations. -/
theorem commutant_centralizer_tensorPow_eq [Finite G] (ρ : G →* Op X) (k : ℕ) :
    commutant (centralizerTensorPowers ρ k) = Submodule.span ℂ (Set.range (jointAction ρ k)) := by
  have : Finite (SemidirectProduct (Fin k → G) (Equiv.Perm (Fin k))
      (wordPermutationAction G k)) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  rw [commutant_span, span_centralizer_tensorPow_eq, ← range_tensorWreathRep,
    finiteGroup_bicommutant]

end Quantum.Symmetry
