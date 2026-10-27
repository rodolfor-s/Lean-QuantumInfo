import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.Probability.UnitaryHaar
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.DeFinetti.HaarAlgebra
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-! # Coherent tensor powers on split registers -/
noncomputable section
namespace Quantum.DeFinetti
open Matrix Quantum.Operators Quantum.Symmetry MeasureTheory
open scoped Kronecker
variable {X : Type*} [Fintype X] [DecidableEq X] {n k : ℕ}

omit [Fintype X] [DecidableEq X] in
/-- Restricting a tensor power to final and initial sites gives its two tensor factors. -/
theorem tensorPow_reindex_splitLast (A : Op X) (hk : k ≤ n) :
    reindex (splitLast hk) (splitLast hk) (Op.tensorPow A n) =
      Op.tensorPow A k ⊗ₖ Op.tensorPow A (n-k) := by
  let e : Fin (n-k) ⊕ Fin k ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hk))
  ext x y
  have h := e.prod_comp (fun i => A ((splitLast hk).symm x i) ((splitLast hk).symm y i))
  rw [Fintype.prod_sum_type] at h
  change (∏ i, A ((splitLast hk).symm x i) ((splitLast hk).symm y i)) =
    (∏ i, A (x.1 i) (y.1 i)) * ∏ i, A (x.2 i) (y.2 i)
  rw [← h]
  have hl (i : Fin (n-k)) : e (Sum.inl i) = ⟨i, by omega⟩ := rfl
  have hr (i : Fin k) : e (Sum.inr i) = ⟨n-k+i, by omega⟩ := rfl
  simp only [hl, hr]
  change (∏ i, A (((splitLast hk) ((splitLast hk).symm x)).2 i)
      (((splitLast hk) ((splitLast hk).symm y)).2 i)) *
    (∏ i, A (((splitLast hk) ((splitLast hk).symm x)).1 i)
      (((splitLast hk) ((splitLast hk).symm y)).1 i)) = _
  rw [(splitLast hk).apply_symm_apply, (splitLast hk).apply_symm_apply]
  exact mul_comm _ _

/-- A coherent tensor power is supported on the symmetric subspace, including zero sites. -/
theorem symmetricProjector_mul_pureStateMap_tensorPow (x : X)
    (U : unitaryGroup X ℂ) (k : ℕ) :
    symmetricProjector X k * ((pureStateMap x U).tensorPow k).toOp =
      ((pureStateMap x U).tensorPow k).toOp := by
  let v := Ket.tensorFamily (fun _ : Fin k => (unitaryColumn x U).toKet)
  have hp : ((pureStateMap x U).tensorPow k).toOp = v.projector :=
    (Ket.projector_tensorFamily _).symm
  have hv : symmetricProjector X k *ᵥ v.vec = v.vec := by
    apply (symmetricProjector_mulVec_eq_iff _).mpr
    intro σ a
    exact Equiv.prod_comp σ (fun t => U.val (a t) x)
  rw [hp]
  change symmetricProjector X k * vecMulVec v.vec (star v.vec) = _
  rw [Matrix.mul_vecMulVec, hv]
  rfl

/-- The Haar average of coherent powers, scaled by the symmetric dimension, is the projector. -/
theorem symmetricProjector_eq_scaled_haar [Nonempty X] (x : X) (k : ℕ) :
    symmetricProjector X k = (symmetricProjector X k).trace •
      (of fun i j => ∫ U : unitaryGroup X ℂ,
        ((pureStateMap x U).tensorPow k).toOp i j ∂UnitaryGroup.haarProbUnitary X) := by
  have hm : (of fun i j => ∫ U : unitaryGroup X ℂ,
      ((pureStateMap x U).tensorPow k).toOp i j ∂UnitaryGroup.haarProbUnitary X) =
      integralTensorPower k (haarDensityMeasure x) := by
    ext i j
    symm
    exact integral_map (continuous_pureStateMap x).measurable.aemeasurable
      (DensityOp.continuous_tensorPow_entry k i j).measurable.aestronglyMeasurable
  rw [hm, ← deFinettiState_eq_haar_integral]
  change _ = _ • ((symmetricProjector X k).trace⁻¹ • symmetricProjector X k)
  rw [smul_smul, mul_inv_cancel₀
    (Quantum.Symmetry.symmetricProjector_trace_ne_zero (X := X)), one_smul]

/-- A globally symmetric register is symmetric on its discarded sites. -/
theorem kronecker_symmetricProjector_mul_reindex [Nonempty X] (x : X) (hk : k ≤ n) :
    (1 ⊗ₖ symmetricProjector X (n-k)) *
      reindex (splitLast hk) (splitLast hk) (symmetricProjector X n) =
      reindex (splitLast hk) (splitLast hk) (symmetricProjector X n) := by
  let B (U : unitaryGroup X ℂ) := reindex (splitLast hk) (splitLast hk)
    ((pureStateMap x U).tensorPow n).toOp
  have hint (i j) : Integrable (fun U => B U i j) (UnitaryGroup.haarProbUnitary X) :=
    ((DensityOp.continuous_tensorPow_entry n _ _).comp
      (continuous_pureStateMap x)).integrable_of_compactSpace
  have hB (U : unitaryGroup X ℂ) : (1 ⊗ₖ symmetricProjector X (n-k)) * B U = B U := by
    change _ * reindex _ _ (Op.tensorPow _ n) = reindex _ _ (Op.tensorPow _ n)
    rw [tensorPow_reindex_splitLast _ hk, ← mul_kronecker_mul, Matrix.one_mul]
    rw [show symmetricProjector X (n-k) * Op.tensorPow (pureStateMap x U).toOp (n-k) =
      Op.tensorPow (pureStateMap x U).toOp (n-k) from
      symmetricProjector_mul_pureStateMap_tensorPow x U (n-k)]
  have he : reindex (splitLast hk) (splitLast hk) (symmetricProjector X n) =
      (symmetricProjector X n).trace •
      (of fun i j => ∫ U, B U i j ∂UnitaryGroup.haarProbUnitary X) := by
    conv_lhs => rw [symmetricProjector_eq_scaled_haar x n]
    rfl
  rw [he, Matrix.mul_smul, Matrix.mul_entryIntegral _ hint]
  congr 1
  ext i j
  exact integral_congr_ae (Filter.Eventually.of_forall fun U => congrFun (congrFun (hB U) i) j)

end Quantum.DeFinetti
