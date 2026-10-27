import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic

/-! # Finite averages of quantum channels

Averages use real nonnegative weights on complex linear maps. Positivity is
`Matrix.PosSemidef`; no matrix order or norm instance is installed.
-/

namespace Quantum.Channels

open Matrix Quantum.Operators
open scoped BigOperators ComplexOrder

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

/-- A convex combination of channels is a channel. -/
theorem IsChannel.convexCombination (Φ : I → Operation X Y)
    (hΦ : ∀ i, IsChannel (Φ i)) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (htotal : ∑ i, w i = 1) : IsChannel (∑ i, (w i : ℂ) • Φ i) := by
  constructor
  · have he : choiMatrix (∑ i, (w i : ℂ) • Φ i) = ∑ i, (w i : ℂ) • choiMatrix (Φ i) := by
      classical
      ext p q
      simp [choiMatrix, LinearMap.sum_apply, Matrix.sum_apply]
    rw [IsCompletelyPositive, he]
    exact posSemidef_sum _ fun i _ => (hΦ i).1.smul (by exact_mod_cast hw i)
  · intro A
    have ht : ∀ i, trace (Φ i A) = trace A := fun i => (hΦ i).2 A
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, trace_sum, trace_smul, ht,
      smul_eq_mul, ← Finset.sum_mul, ← Complex.ofReal_sum, htotal,
      Complex.ofReal_one, one_mul]

/-- The uniform average over a nonempty finite family of channels is a channel. -/
theorem IsChannel.uniformAverage [Nonempty I] (Φ : I → Operation X Y)
    (hΦ : ∀ i, IsChannel (Φ i)) :
    IsChannel ((Fintype.card I : ℂ)⁻¹ • ∑ i, Φ i) := by
  have h := IsChannel.convexCombination Φ hΦ (fun _ => (Fintype.card I : ℝ)⁻¹)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) (by simp [Fintype.card_ne_zero])
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast, ← Finset.smul_sum] using h

end Quantum.Channels
