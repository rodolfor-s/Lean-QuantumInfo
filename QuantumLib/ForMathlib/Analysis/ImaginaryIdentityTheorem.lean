import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
# Entire functions vanishing on the imaginary axis

Entire functions vanishing on the imaginary axis.
-/

open Complex Set Filter
open scoped Topology

noncomputable section

/-- An entire scalar function vanishing on the imaginary axis vanishes everywhere. -/
lemma _root_.Complex.eq_zero_of_differentiable_of_eq_zero_on_imaginary {f : ℂ → ℂ} (hf :
    Differentiable ℂ f)
    (hzero : ∀ t : ℝ, f ((t : ℂ) * Complex.I) = 0) : f = 0 := by
  apply (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_frequently_eq
    analyticOnNhd_const (z₀ := 0)
  have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.I)
      (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) :=
        Complex.continuous_ofReal.mul continuous_const
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact ht.frequently (Filter.Eventually.of_forall hzero).frequently

end
