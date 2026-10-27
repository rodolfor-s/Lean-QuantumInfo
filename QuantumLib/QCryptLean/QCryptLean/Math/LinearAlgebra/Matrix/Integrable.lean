import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Matrix integrability from entries

This module uses the Frobenius norm locally. The entrywise finite-function norm
and the Frobenius norm have the same finite-dimensional topology; the identity
linear map supplies the needed continuous transport.
-/

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

noncomputable section

namespace Matrix

private local instance {m n : Type*} [Fintype m] [Fintype n] : ContinuousENorm (Matrix m n ℂ) :=
  SeminormedAddGroup.toContinuousENorm

/-- A finite complex matrix-valued map is integrable if all its entries are integrable. -/
lemma integrable_of_apply_apply {α m n : Type*} [MeasurableSpace α] [Fintype m] [Fintype n]
    {μ : MeasureTheory.Measure α} {F : α → Matrix m n ℂ}
    (hF : ∀ i j, MeasureTheory.Integrable (fun x => F x i j) μ) :
    MeasureTheory.Integrable F μ := by
  let G : α → m → n → ℂ := fun x i j => F x i j
  have hG : MeasureTheory.Integrable G μ :=
    MeasureTheory.Integrable.of_eval fun i =>
      MeasureTheory.Integrable.of_eval fun j => hF i j
  let toMatrix : (m → n → ℂ) →L[ℝ] Matrix m n ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun A => A
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact toMatrix.integrable_comp hG

end Matrix
