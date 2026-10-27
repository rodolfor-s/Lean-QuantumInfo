import Mathlib.Analysis.Normed.Operator.NormedSpace
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Frobenius
import QCryptLean.Quantum.Operators.Basic

/-!
# Boundedness of the intrinsic diamond supremum

The auxiliary continuity argument uses local Frobenius normed-space instances.
It imposes no nonempty assumptions, does not encode either register, and leaves
matrix norm instances in importing files unchanged.
-/

noncomputable section

namespace Quantum.Channels

open Quantum.Operators Quantum.Metrics

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The intrinsic all-operator set is bounded above, including empty registers. -/
theorem diamondNorm_bddAbove (Φ : Operation X Y) :
    BddAbove {t : ℝ | ∃ A : Op (X × X), traceNorm A ≤ 1 ∧
      t = traceNorm (mapTensorId Φ X A)} := by
  let L := (mapTensorId Φ X).toContinuousLinearMap
  obtain ⟨C, hC, hL⟩ := L.bound
  refine ⟨√(Fintype.card (Y × X) : ℝ) * C, ?_⟩
  rintro t ⟨A, hA, rfl⟩
  calc traceNorm (mapTensorId Φ X A)
      ≤ √(Fintype.card (Y × X) : ℝ) * ‖L A‖ := traceNorm_le_sqrt_card_mul_frobenius _
    _ ≤ √(Fintype.card (Y × X) : ℝ) * (C * ‖A‖) :=
      mul_le_mul_of_nonneg_left (hL A) (Real.sqrt_nonneg _)
    _ ≤ √(Fintype.card (Y × X) : ℝ) * C := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact mul_le_of_le_one_right hC.le ((frobenius_le_traceNorm A).trans hA)

/-- A uniform bound on the unit ball bounds the diamond norm. -/
theorem diamondNorm_le_of_forall (Φ : Operation X Y) (c : ℝ)
    (h : ∀ A : Op (X × X), traceNorm A ≤ 1 → traceNorm (mapTensorId Φ X A) ≤ c) :
    diamondNorm Φ ≤ c := by
  exact csSup_le (diamondNorm_set_nonempty Φ) (by rintro _ ⟨A, hA, rfl⟩; exact h A hA)

/-- Each value on the trace-norm unit ball is at most the diamond norm. -/
theorem traceNorm_mapTensorId_le_diamondNorm (Φ : Operation X Y) (A : Op (X × X))
    (hA : traceNorm A ≤ 1) : traceNorm (mapTensorId Φ X A) ≤ diamondNorm Φ :=
  le_csSup (diamondNorm_bddAbove Φ) ⟨A, hA, rfl⟩

end Quantum.Channels
