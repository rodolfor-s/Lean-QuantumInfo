import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.Matrix
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveEntries
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor

/-! # Topology -/


noncomputable section

namespace Quantum.Operators

open Matrix
open scoped ComplexOrder

variable {X : Type*} [Fintype X]

/-- The entrywise topology induced by the underlying matrix. -/
instance : TopologicalSpace (DensityOp X) := TopologicalSpace.induced DensityOp.toOp inferInstance

/-- The underlying-matrix map embeds the state space. -/
theorem DensityOp.isEmbedding_toOp : Topology.IsEmbedding (fun ρ : DensityOp X => ρ.toOp) :=
  ⟨⟨rfl⟩, fun _ _ h => DensityOp.ext h⟩

/-- The state topology makes its matrix embedding continuous. -/
theorem DensityOp.continuous_toOp : Continuous (fun ρ : DensityOp X => ρ.toOp) :=
  continuous_induced_dom

/-- Relabelling a density operator is continuous in its matrix entries. -/
theorem DensityOp.continuous_reindex {Y : Type*} [Fintype Y] (e : X ≃ Y) :
    Continuous (DensityOp.reindex e : DensityOp X → DensityOp Y) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  exact (continuous_apply (e.symm j)).comp
    ((continuous_apply (e.symm i)).comp DensityOp.continuous_toOp)

/-- Distinct states have disjoint neighborhoods. -/
instance : T2Space (DensityOp X) := DensityOp.isEmbedding_toOp.t2Space

/-- The measurable sets of states are their Borel sets. -/
instance : MeasurableSpace (DensityOp X) := borel _

/-- The state measurable space is Borel. -/
instance : BorelSpace (DensityOp X) := ⟨rfl⟩

/-- The image consists exactly of positive matrices of unit trace. -/
theorem DensityOp.range_toOp : Set.range (fun ρ : DensityOp X => ρ.toOp) =
    {M : Op X | M.PosSemidef ∧ M.trace = 1} := by
  ext M
  exact ⟨fun ⟨ρ, h⟩ => h ▸ ⟨ρ.posSemidef, ρ.trace_one⟩,
    fun ⟨hp, ht⟩ => ⟨⟨M, hp, ht⟩, rfl⟩⟩

/-- Every state entry has norm at most one. -/
theorem DensityOp.entry_norm_le_one (ρ : DensityOp X) (i j : X) : ‖ρ.toOp i j‖ ≤ 1 :=
  ρ.posSemidef.norm_apply_le_one_of_trace_re_le_one (by simp [ρ.trace_one]) i j

/-- The state space is a closed subset of the compact product of complex unit balls. -/
instance : CompactSpace (DensityOp X) := by
  refine ⟨DensityOp.isEmbedding_toOp.isInducing.isCompact_iff.2 ?_⟩
  rw [Set.image_univ, DensityOp.range_toOp]
  have hc : IsClosed {A : Op X | A.PosSemidef} := by
    have he : {A : Op X | A.PosSemidef} =
        {A : Op X | A.IsHermitian} ∩ ⋂ v : X → ℂ, {A | 0 ≤ star v ⬝ᵥ A *ᵥ v} := by
      ext A
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
        Matrix.posSemidef_iff_dotProduct_mulVec]
    rw [he]
    exact (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
      (isClosed_iInter fun _ => isClosed_Ici.preimage
        (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)))
  have hb : IsCompact (Set.univ.pi fun _ : X =>
      Set.univ.pi fun _ : X => Metric.closedBall (0 : ℂ) 1 : Set (Op X)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1
  refine hb.of_isClosed_subset
    (hc.inter (isClosed_eq continuous_id.matrix_trace continuous_const)) fun M hM => ?_
  simp only [Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  exact hM.1.norm_apply_le_one_of_trace_re_le_one (by simp [hM.2])

/-- Each tensor-power entry varies continuously with the state. -/
theorem DensityOp.continuous_tensorPow_entry (k : ℕ) (x y : Fin k → X) :
    Continuous (fun ρ : DensityOp X => (ρ.tensorPow k).toOp x y) := by
  change Continuous (fun ρ : DensityOp X => ∏ i : Fin k, ρ.toOp (x i) (y i))
  exact continuous_finsetProd _ fun i _ => (continuous_apply (y i)).comp
    ((continuous_apply (x i)).comp DensityOp.continuous_toOp)

end Quantum.Operators
