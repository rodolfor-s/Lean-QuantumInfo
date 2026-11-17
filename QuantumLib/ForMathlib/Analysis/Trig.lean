import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Real-analysis trig helpers for angles in `[0, π/2]`

Elementary monotonicity / sum facts about `Real.sin` and `Real.cos` restricted
to the interval `[0, π/2]`. Used by the Bures-angle triangle inequality
(`Quantum.Metrics.purifiedDistance_triangle`).
-/

namespace Real

/-- Elementary fact: `sin α + cos α ≥ 1` for `α ∈ [0, π/2]`.

    Proof via `(sin α + cos α)^2 = 1 + 2 sin α cos α ≥ 1` and nonnegativity. -/
lemma one_le_sin_add_cos_of_mem_Icc {α : ℝ}
    (h₀ : 0 ≤ α) (h₁ : α ≤ Real.pi / 2) :
    1 ≤ Real.sin α + Real.cos α := by
  have hpi := Real.pi_pos
  have hs : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi h₀ (by linarith)
  have hc : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, h₁⟩
  have hsum : 0 ≤ Real.sin α + Real.cos α := add_nonneg hs hc
  have hpy := Real.sin_sq_add_cos_sq α
  have hsc : 0 ≤ Real.sin α * Real.cos α := mul_nonneg hs hc
  have hsq : 1 ≤ (Real.sin α + Real.cos α) ^ 2 := by nlinarith [hpy, hsc]
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_one, Real.sqrt_sq hsum] at this

/-- Elementary real-analysis lemma: if `α, β, γ ∈ [0, π/2]` and `γ ≤ α + β`,
    then `sin γ ≤ sin α + sin β`.  Used to turn the Bures angle triangle
    inequality into the purified distance triangle inequality. -/
lemma sin_le_sin_add_sin_of_le_add
    {α β γ : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2))
    (hβ : β ∈ Set.Icc 0 (Real.pi / 2))
    (hγ : γ ∈ Set.Icc 0 (Real.pi / 2))
    (hsum : γ ≤ α + β) :
    Real.sin γ ≤ Real.sin α + Real.sin β := by
  obtain ⟨hα0, hαpi⟩ := hα
  obtain ⟨hβ0, hβpi⟩ := hβ
  obtain ⟨hγ0, hγpi⟩ := hγ
  have hpi := Real.pi_pos
  have hsα : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα0 (by linarith)
  have hsβ : 0 ≤ Real.sin β :=
    Real.sin_nonneg_of_nonneg_of_le_pi hβ0 (by linarith)
  have hsγ_le_one : Real.sin γ ≤ 1 := Real.sin_le_one γ
  by_cases hcase : α + β ≤ Real.pi / 2
  · -- Case 1: α + β ≤ π/2.  Use monotonicity of sin and sin_add.
    have hγmem : γ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith, hγpi⟩
    have hαβmem : α + β ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith, hcase⟩
    have hmono : Real.sin γ ≤ Real.sin (α + β) :=
      Real.strictMonoOn_sin.monotoneOn hγmem hαβmem hsum
    have hcα0 : 0 ≤ Real.cos α :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, hαpi⟩
    have hcβ0 : 0 ≤ Real.cos β :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, hβpi⟩
    have hcα1 : Real.cos α ≤ 1 := Real.cos_le_one α
    have hcβ1 : Real.cos β ≤ 1 := Real.cos_le_one β
    have hsin_add : Real.sin (α + β) =
        Real.sin α * Real.cos β + Real.cos α * Real.sin β := Real.sin_add α β
    have h1 : Real.sin α * Real.cos β ≤ Real.sin α := by
      have := mul_le_mul_of_nonneg_left hcβ1 hsα
      simpa using this
    have h2 : Real.cos α * Real.sin β ≤ Real.sin β := by
      have := mul_le_mul_of_nonneg_right hcα1 hsβ
      simpa using this
    linarith [hmono, hsin_add, h1, h2]
  · -- Case 2: α + β > π/2.  Show sin α + sin β ≥ 1 ≥ sin γ.
    push Not at hcase
    have hβ_ge : Real.pi / 2 - α ≤ β := by linarith
    have hmem1 : Real.pi / 2 - α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith, by linarith⟩
    have hmem2 : β ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith, hβpi⟩
    have hsinβ_ge : Real.sin (Real.pi / 2 - α) ≤ Real.sin β :=
      Real.strictMonoOn_sin.monotoneOn hmem1 hmem2 hβ_ge
    rw [Real.sin_pi_div_two_sub] at hsinβ_ge
    have hscα := one_le_sin_add_cos_of_mem_Icc hα0 hαpi
    linarith [hsγ_le_one, hsinβ_ge, hscα]

end Real
