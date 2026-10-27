import QCryptLean.Math.LinearAlgebra.Matrix.TensorFamilyTrace
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKRMixture
import QCryptLean.Quantum.DeFinetti.Integral
import QCryptLean.Quantum.Metrics.PartialTrace
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.Paired

/-! # Marginal Mixture -/


noncomputable section
namespace Quantum.DeFinetti
open Matrix Quantum.Operators Quantum.Symmetry MeasureTheory
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Push forward a density-state distribution by its system marginal. -/
def DensityMeasure.partialTraceRight (μ : DensityMeasure (X × Y)) : DensityMeasure X where
  measure := Measure.map DensityOp.partialTraceRight μ.measure
  isProbability := by
    have := μ.isProbability
    infer_instance

/-- The mixture of marginal tensor powers equals the marginal of the joint mixture. -/
theorem integralTensorPower_partialTraceRight (μ : DensityMeasure (X × Y)) (k : ℕ) :
    integralTensorPower k μ.partialTraceRight =
      partialTraceRight (reindex (pairFunctions X Y k) (pairFunctions X Y k)
        (integralTensorPower k μ)) := by
  ext i j
  change (∫ ρ, (ρ.tensorPow k).toOp i j ∂Measure.map DensityOp.partialTraceRight μ.measure) = _
  rw [integral_map continuous_partialTraceRight.measurable.aemeasurable
    (DensityOp.continuous_tensorPow_entry k i j).measurable.aestronglyMeasurable]
  change _ = ∑ r : Fin k → Y, ∫ ρ, (ρ.tensorPow k).toOp
    (fun t => (i t, r t)) (fun t => (j t, r t)) ∂μ.measure
  rw [← integral_finsetSum _ (fun r _ => integrable_tensorPow_entry μ k _ _)]
  apply integral_congr_ae
  filter_upwards [] with ρ
  simpa only [DensityOp.tensorPow, DensityOp.tensorFamily, DensityOp.partialTraceRight,
    Matrix.partialTraceRight, Matrix.reindex_apply, pairFunctions,
    Equiv.arrowProdEquivProdArrow, Matrix.of_apply, Matrix.submatrix_apply,
    Equiv.coe_fn_symm_mk] using
    (congrFun (congrFun (partialTraceRight_reindex_piTensorProduct
      (fun _ : Fin k => ρ.toOp)) i) j).symm

/-- Discarding sites and discarding one component of every site commute. -/
theorem partialTraceLast_partialTraceRight {n k : ℕ} (hk : k ≤ n)
    (ρ : DensityOp (Fin n → X × Y)) :
    partialTraceLast hk (ρ.reindex (pairFunctions X Y n)).partialTraceRight =
      ((partialTraceLast hk ρ).reindex (pairFunctions X Y k)).partialTraceRight := by
  classical
  apply DensityOp.ext
  ext i j
  let e : (Fin (n - k) → X) × (Fin n → Y) ≃
      (Fin k → Y) × (Fin (n - k) → X × Y) :=
    ((Equiv.refl _).prodCongr (splitLast (X := Y) hk)) |>.trans
      ((Equiv.prodAssoc _ _ _).symm.trans
        (((Equiv.prodComm _ _).prodCongr (Equiv.refl _)).trans
          ((Equiv.prodAssoc _ _ _).trans
            ((Equiv.refl _).prodCongr (pairFunctions X Y (n - k)).symm))))
  have he (a : Fin k → X) (p : (Fin (n - k) → X) × (Fin n → Y)) :
      (pairFunctions X Y n).symm ((splitLast hk).symm (a, p.1), p.2) =
        (splitLast hk).symm ((pairFunctions X Y k).symm (a, (e p).1), (e p).2) := by
    apply (splitLast hk).injective
    rw [Equiv.apply_symm_apply]
    change ((fun t : Fin k => (((splitLast hk).symm (a, p.1)) ⟨n-k+t, by omega⟩,
        p.2 ⟨n-k+t, by omega⟩)),
      fun t : Fin (n-k) => (((splitLast hk).symm (a, p.1)) ⟨t, by omega⟩, p.2 ⟨t, by omega⟩)) = _
    have ha := (splitLast (X := X) hk).apply_symm_apply (a, p.1)
    have h1 := congrArg Prod.fst ha
    have h2 := congrArg Prod.snd ha
    apply Prod.ext <;> funext t
    · exact Prod.ext (congrFun h1 t) rfl
    · exact Prod.ext (congrFun h2 t) rfl
  change (∑ a : Fin (n - k) → X, ∑ b : Fin n → Y,
    ρ.toOp ((pairFunctions X Y n).symm ((splitLast hk).symm (i, a), b))
      ((pairFunctions X Y n).symm ((splitLast hk).symm (j, a), b))) =
    ∑ b : Fin k → Y, ∑ a : Fin (n - k) → X × Y,
      ρ.toOp ((splitLast hk).symm ((pairFunctions X Y k).symm (i, b), a))
        ((splitLast hk).symm ((pairFunctions X Y k).symm (j, b), a))
  have hs := Fintype.sum_equiv e
    (fun p : (Fin (n - k) → X) × (Fin n → Y) =>
      ρ.toOp ((pairFunctions X Y n).symm ((splitLast hk).symm (i, p.1), p.2))
        ((pairFunctions X Y n).symm ((splitLast hk).symm (j, p.1), p.2)))
    (fun p : (Fin k → Y) × (Fin (n - k) → X × Y) =>
      ρ.toOp ((splitLast hk).symm ((pairFunctions X Y k).symm (i, p.1), p.2))
        ((splitLast hk).symm ((pairFunctions X Y k).symm (j, p.1), p.2)))
    (fun p => by rw [he, he])
  simpa only [Fintype.sum_prod_type] using hs

end Quantum.DeFinetti
