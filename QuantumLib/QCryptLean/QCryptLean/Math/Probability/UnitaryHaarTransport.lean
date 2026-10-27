import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.Probability.UnitaryHaar

/-! # Unitary Haar Transport -/


noncomputable section

namespace Matrix.UnitaryGroup

open MeasureTheory

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Reindexing as a continuous group isomorphism of finite unitary groups. -/
def reindexHomeomorph (e : X ≃ Y) : unitaryGroup X ℂ ≃ₜ* unitaryGroup Y ℂ where
  toMulEquiv := (Unitary.mapEquiv
    { toMulEquiv := (reindexRingEquiv ℂ e).toMulEquiv
      map_star' := fun A => by
        change reindex e e Aᴴ = (reindex e e A)ᴴ
        exact (conjTranspose_reindex e e A).symm }).toMulEquiv
  continuous_toFun := continuous_induced_rng.mpr
    (continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (e.symm j)).comp
        ((continuous_apply (e.symm i)).comp continuous_subtype_val))
  continuous_invFun := continuous_induced_rng.mpr
    (continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (e j)).comp ((continuous_apply (e i)).comp continuous_subtype_val))

/-- Haar probability remains a Haar measure after its positive finite normalization. -/
instance isHaarMeasure_haarProbUnitary : (haarProbUnitary X).IsHaarMeasure := by
  have : (haarOnUnitary X).IsHaarMeasure := by unfold haarOnUnitary; infer_instance
  unfold haarProbUnitary
  apply Measure.IsHaarMeasure.smul
  · exact ENNReal.inv_ne_zero.mpr (ne_of_lt (haarOnUnitary_finite X))
  · exact ENNReal.inv_ne_top.mpr (ne_of_gt (haarOnUnitary_pos X))

/-- Relabelling finite unitary registers preserves probability Haar measure. -/
theorem measurePreserving_reindexHomeomorph (e : X ≃ Y) :
    MeasurePreserving (reindexHomeomorph e) (haarProbUnitary X) (haarProbUnitary Y) := by
  let := isProbabilityMeasure_haarProbUnitary X
  let := isProbabilityMeasure_haarProbUnitary Y
  exact (reindexHomeomorph e).toMonoidHom.measurePreserving
    (reindexHomeomorph e).continuous (reindexHomeomorph e).surjective (by simp)

end Matrix.UnitaryGroup
