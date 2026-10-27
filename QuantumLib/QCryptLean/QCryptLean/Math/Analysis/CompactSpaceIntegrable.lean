import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Continuous functions on a compact space are integrable

On a compact space whose open sets are measurable, a continuous function with values in any normed
group is integrable against every finite measure: it has compact support
(`HasCompactSupport.of_compactSpace`), and a finite measure is finite on compact sets. The codomain
need be neither finite-dimensional nor second countable; compactness of the source replaces both.

This is the companion of Mathlib's `Continuous.aestronglyMeasurable_of_compactSpace`. Applied to
the compact space of density operators (`Quantum.Operators.DensityOp`), it makes every continuous
function of a quantum state integrable against every probability measure on states.

## Main statements

- `Continuous.integrable_of_compactSpace`: `Continuous f → Integrable f μ` for finite `μ` on a
  compact space.
-/

open MeasureTheory

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [CompactSpace X] [NormedAddCommGroup E] {μ : Measure X} [IsFiniteMeasure μ] {f : X → E}

/-- A continuous function on a compact space is integrable against every finite measure. -/
theorem Continuous.integrable_of_compactSpace (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
