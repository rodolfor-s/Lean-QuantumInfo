import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Diamond -/


noncomputable section

namespace Quantum.Channels

open Quantum.Operators Quantum.Metrics

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Completely bounded trace norm, over all operators and an input-sized reference. -/
def diamondNorm (Φ : Operation X Y) : ℝ :=
  sSup {t : ℝ | ∃ A : Op (X × X), traceNorm A ≤ 1 ∧ t = traceNorm (mapTensorId Φ X A)}

/-- Channel distinguishing distance, with its factor one half. -/
def diamondDist (Φ Ψ : Operation X Y) : ℝ := (1 / 2) * diamondNorm (Φ - Ψ)

/-- Zero belongs to the set defining the diamond norm, including for empty registers. -/
theorem diamondNorm_set_zero_mem (Φ : Operation X Y) :
    (0 : ℝ) ∈ {t : ℝ | ∃ A : Op (X × X), traceNorm A ≤ 1 ∧
      t = traceNorm (mapTensorId Φ X A)} := by
  exact ⟨0, by simp, by simp⟩

/-- The diamond-norm supremum is nonempty, without nonempty-register assumptions. -/
theorem diamondNorm_set_nonempty (Φ : Operation X Y) :
    {t : ℝ | ∃ A : Op (X × X), traceNorm A ≤ 1 ∧
      t = traceNorm (mapTensorId Φ X A)}.Nonempty := ⟨0, diamondNorm_set_zero_mem Φ⟩

/-- The real supremum is nonnegative. Boundedness is established in the estimate API. -/
theorem diamondNorm_nonneg (Φ : Operation X Y) : 0 ≤ diamondNorm Φ := by
  unfold diamondNorm
  by_cases h : BddAbove {t : ℝ | ∃ A : Op (X × X), traceNorm A ≤ 1 ∧
      t = traceNorm (mapTensorId Φ X A)}
  · exact le_csSup h (diamondNorm_set_zero_mem Φ)
  · rw [csSup_of_not_bddAbove h, Real.sSup_empty]

/-- Distinguishing distance is nonnegative. -/
theorem diamondDist_nonneg (Φ Ψ : Operation X Y) : 0 ≤ diamondDist Φ Ψ :=
  mul_nonneg (by norm_num) (diamondNorm_nonneg _)

/-- The zero operation has zero diamond norm on arbitrary finite registers. -/
@[simp] theorem diamondNorm_zero : diamondNorm (0 : Operation X Y) = 0 := by
  have he : {t : ℝ | ∃ A : Op (X × X), traceNorm A ≤ 1 ∧
      t = traceNorm (mapTensorId (0 : Operation X Y) X A)} = {0} := by
    ext t
    constructor
    · rintro ⟨A, _, ht⟩
      have hz : mapTensorId (0 : Operation X Y) X A = 0 := rfl
      simpa only [hz, traceNorm_zero, Set.mem_singleton_iff] using ht
    · intro ht
      refine ⟨0, by simp, ?_⟩
      simpa using ht
  unfold diamondNorm
  rw [he, csSup_singleton]

/-- Identical operations have distinguishing distance zero. -/
@[simp] theorem diamondDist_self (Φ : Operation X Y) : diamondDist Φ Φ = 0 := by
  simp [diamondDist]

end Quantum.Channels
