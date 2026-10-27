import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.TensorFamilyTrace
import QCryptLean.Math.LinearAlgebra.Matrix.UnitaryGram
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.Probability.UnitaryHaar
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.DeFinetti.HaarAlgebra
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.RankPurification
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.Paired

/-! # CKRMixture -/


noncomputable section
namespace Quantum.DeFinetti
open Matrix Quantum.Operators Quantum.Symmetry MeasureTheory
open scoped ComplexOrder
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Every normalized vector is a specified column of a unitary matrix. -/
theorem exists_unitaryColumn_eq (x : X) (v : NormKet X) :
    ∃ U : unitaryGroup X ℂ, unitaryColumn x U = v := by
  let A : Matrix X Unit ℂ := fun i _ => if i = x then 1 else 0
  let B : Matrix X Unit ℂ := fun i _ => v.vec i
  have hg : Aᴴ * A = Bᴴ * B := by
    ext i j
    cases i; cases j
    change (∑ i, star (A i ()) * A i ()) = ∑ i, star (v.vec i) * v.vec i
    have hv := v.normalized
    change (∑ i, star (v.vec i) * v.vec i) = 1 at hv
    rw [hv]
    simp [A, apply_ite]
  obtain ⟨U, hU, hU', he⟩ := exists_unitary_of_columnGram_eq A B hg
  refine ⟨⟨U, hU, hU'⟩, ?_⟩
  have hv : (unitaryColumn x ⟨U, hU, hU'⟩).vec = v.vec := by
    funext i
    change U i x = v.vec i
    have hi := congrFun (congrFun he i) ()
    change (∑ j, U i j * A j ()) = v.vec i at hi
    simpa [A, mul_ite] using hi
  have hext (v w : NormKet X) (h : v.vec = w.vec) : v = w := by
    rcases v with ⟨⟨v⟩, hv⟩
    rcases w with ⟨⟨w⟩, hw⟩
    cases h
    rfl
  exact hext _ _ hv

omit [DecidableEq X] in
/-- Partial trace is continuous for entrywise state topologies. -/
theorem continuous_partialTraceRight {Y : Type*} [Fintype Y] :
    Continuous (DensityOp.partialTraceRight : DensityOp (X × Y) → DensityOp X) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_finsetSum _ fun r _ =>
    (continuous_apply (j, r)).comp ((continuous_apply (i, r)).comp DensityOp.continuous_toOp)

/-- The marginal of a bipartite Haar column reaches every density operator. -/
theorem partialTraceRight_pureStateMap_surjective (x : X) :
    Function.Surjective (fun U : unitaryGroup (X × X) ℂ =>
      (pureStateMap (x, x) U).partialTraceRight) := by
  intro ρ
  obtain ⟨U, hU⟩ := exists_unitaryColumn_eq (x, x) ρ.purificationKet
  refine ⟨U, ?_⟩
  change (unitaryColumn (x, x) U).toDensityOp.partialTraceRight = ρ
  rw [hU]
  exact ρ.partialTraceRight_purification

/-- The CKR reference measure is the marginal of a bipartite Haar column. -/
def ckrMixtureMeasure (x : X) : DensityMeasure X where
  measure := Measure.map (fun U : unitaryGroup (X × X) ℂ =>
    (pureStateMap (x, x) U).partialTraceRight) (UnitaryGroup.haarProbUnitary (X × X))
  isProbability := by
    have := UnitaryGroup.isProbabilityMeasure_haarProbUnitary (X × X)
    constructor
    change (Measure.map (DensityOp.partialTraceRight ∘ pureStateMap (x, x))
      (UnitaryGroup.haarProbUnitary (X × X))) Set.univ = 1
    rw [Measure.map_apply (continuous_partialTraceRight.comp
      (continuous_pureStateMap (x, x))).measurable MeasurableSet.univ]
    simp

/-- Every nonempty open set of density operators has positive CKR mixture measure. -/
theorem isOpenPosMeasure_ckrMixtureMeasure (x : X) :
    (ckrMixtureMeasure x).measure.IsOpenPosMeasure := by
  have : (UnitaryGroup.haarProbUnitary (X × X)).IsOpenPosMeasure := by
    unfold UnitaryGroup.haarProbUnitary
    have : (UnitaryGroup.haarOnUnitary (X × X)).IsOpenPosMeasure := by
      unfold UnitaryGroup.haarOnUnitary
      infer_instance
    apply Measure.isOpenPosMeasure_smul
    exact ENNReal.inv_ne_zero.mpr
      (ne_of_lt (UnitaryGroup.haarOnUnitary_finite (X × X)))
  exact Continuous.isOpenPosMeasure_map
    (continuous_partialTraceRight.comp (continuous_pureStateMap (x, x)))
    (partialTraceRight_pureStateMap_surjective x)

/-- The CKR mixture recovers the marginal of the paired symmetric reference at every size. -/
theorem integralTensorPower_ckrMixtureMeasure [Nonempty X] (x : X) (k : ℕ) :
    integralTensorPower k (ckrMixtureMeasure x) = (ckrDeFinettiState X k).toOp := by
  let : Nonempty X := ⟨x⟩
  have hp := deFinettiState_eq_haar_integral (x, x) k
  have he : (ckrDeFinettiState X k).toOp =
      partialTraceRight (reindex (pairFunctions X X k) (pairFunctions X X k)
        (integralTensorPower k (haarDensityMeasure (x, x)))) := by
    rw [← hp]
    rfl
  rw [he]
  ext i j
  have hi (r : Fin k → X) : Integrable
      (fun U : unitaryGroup (X × X) ℂ =>
        ((pureStateMap (x, x) U).tensorPow k).toOp
          (fun t => (i t, r t)) (fun t => (j t, r t)))
      (UnitaryGroup.haarProbUnitary (X × X)) :=
    ((DensityOp.continuous_tensorPow_entry k _ _).comp
      (continuous_pureStateMap (x, x))).integrable_of_compactSpace
  have hm (a b : Fin k → X × X) :
      integralTensorPower k (haarDensityMeasure (x, x)) a b =
        ∫ U, ((pureStateMap (x, x) U).tensorPow k).toOp a b
          ∂UnitaryGroup.haarProbUnitary (X × X) :=
    integral_map (continuous_pureStateMap (x, x)).measurable.aemeasurable
      (DensityOp.continuous_tensorPow_entry k a b).measurable.aestronglyMeasurable
  change (∫ ρ, (ρ.tensorPow k).toOp i j ∂(ckrMixtureMeasure x).measure) = _
  change (∫ ρ, (ρ.tensorPow k).toOp i j ∂Measure.map
    (DensityOp.partialTraceRight ∘ pureStateMap (x, x))
      (UnitaryGroup.haarProbUnitary (X × X))) = _
  rw [integral_map (continuous_partialTraceRight.comp
    (continuous_pureStateMap (x, x))).measurable.aemeasurable
      (DensityOp.continuous_tensorPow_entry k i j).measurable.aestronglyMeasurable]
  change _ = ∑ r : Fin k → X, integralTensorPower k (haarDensityMeasure (x, x))
    (fun t => (i t, r t)) (fun t => (j t, r t))
  simp_rw [hm]
  rw [← integral_finsetSum _ (fun r _ => hi r)]
  apply integral_congr_ae
  filter_upwards [] with U
  simpa only [Function.comp_apply, DensityOp.tensorPow, DensityOp.tensorFamily,
    DensityOp.partialTraceRight,
    Matrix.partialTraceRight, Matrix.reindex_apply, pairFunctions,
    Equiv.arrowProdEquivProdArrow, Matrix.of_apply,
    Matrix.submatrix_apply,
    Equiv.coe_fn_symm_mk]
    using (congrFun (congrFun (partialTraceRight_reindex_piTensorProduct
    (fun _ : Fin k => (pureStateMap (x, x) U).toOp)) i) j).symm

end Quantum.DeFinetti
