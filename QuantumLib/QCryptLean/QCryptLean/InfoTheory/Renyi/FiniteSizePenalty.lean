import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import QCryptLean.InfoTheory.Renyi.SecondOrderConstants
import QCryptLean.Math.Analysis.LogBounds

/-! # Finite Size Penalty -/

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace InfoTheory.Renyi

open InfoTheory.Renyi

/-- `log₂(2/ε²) > 1` for `0 < ε < 1`: the argument exceeds `2`. -/
lemma one_lt_logb_two_div_sq (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    1 < Real.logb 2 (2 / ε ^ 2) := by
  have hsq : (0 : ℝ) < ε ^ 2 := by positivity
  have hsq1 : ε ^ 2 < 1 := by nlinarith
  have h2 : (2 : ℝ) < 2 / ε ^ 2 := by
    rw [lt_div_iff₀ hsq]
    nlinarith
  have := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) h2
  rwa [Real.logb_self_eq_one (by norm_num)] at this

/-- The variance cap `log₂²(1 + √2) ≈ 1.6168`: the bound
`condVariance_le_logb_sq_of_card_eq_two` gives for `V(X|B)` at `d_A = 2`.  This is the
variance cap the Bell–Rényi BB84 theorem charges its Cor IV.2 penalty at. It improves
Dupuis–Fawzi's classical-register cap `log₂²(2 d_A + 1)`; no attainment is asserted. -/
noncomputable def binaryVarianceBound : ℝ := Real.logb 2 (1 + Real.sqrt 2) ^ 2

/-- The variance cap is positive: `log₂(2) = 1 < log₂(1+√2)` since `2 < 1+√2`. -/
lemma binaryVarianceBound_pos : 0 < binaryVarianceBound := by
  have h2 : (2 : ℝ) < 1 + Real.sqrt 2 := by linarith [Real.one_lt_sqrt_two]
  have h1 : (1 : ℝ) < Real.logb 2 (1 + Real.sqrt 2) := by
    have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) h2
    rwa [Real.logb_self_eq_one (by norm_num)] at h
  rw [binaryVarianceBound]
  exact pow_pos (lt_trans (by norm_num) h1) 2

/-- **The cap times `log 2` is bracketed: `1.1195 ≤ V·log 2 ≤ 1.122`** (true
`1.1207135`).  `V·log 2 = Δ²/log 2` with `Δ = log(1+√2)` bracketed by
`Real.log_one_add_sqrt_two_mem_Icc` and `log 2` by the decimal `log 2` lemmas. -/
lemma binaryVarianceBound_mul_log_two_mem_Icc :
    binaryVarianceBound * Real.log 2 ∈ Set.Icc (1.1195 : ℝ) 1.122 := by
  obtain ⟨hLlo, hLhi⟩ := Real.log_one_add_sqrt_two_mem_Icc
  have hl2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog2lo := Real.log_two_gt_d9
  have hlog2hi := Real.log_two_lt_d9
  have hform : binaryVarianceBound * Real.log 2
      = Real.log (1 + Real.sqrt 2) ^ 2 / Real.log 2 := by
    rw [binaryVarianceBound, Real.logb, div_pow, div_mul_eq_mul_div, pow_two (Real.log 2),
      mul_comm (Real.log (1 + Real.sqrt 2) ^ 2) (Real.log 2),
      mul_div_mul_left _ _ (ne_of_gt hl2pos)]
  rw [hform]
  have key1 : (1.1195 : ℝ) * Real.log 2
      ≤ Real.log (1 + Real.sqrt 2) * Real.log (1 + Real.sqrt 2) := by
    calc (1.1195 : ℝ) * Real.log 2 ≤ 1.1195 * 0.6931471808 :=
        mul_le_mul_of_nonneg_left hlog2hi.le (by norm_num)
      _ ≤ 0.88093 * 0.88093 := by norm_num
      _ ≤ Real.log (1 + Real.sqrt 2) * Real.log (1 + Real.sqrt 2) :=
        mul_self_le_mul_self (by norm_num) hLlo
  have key2 : Real.log (1 + Real.sqrt 2) * Real.log (1 + Real.sqrt 2) ≤ 1.122 * Real.log 2 := by
    calc Real.log (1 + Real.sqrt 2) * Real.log (1 + Real.sqrt 2)
        ≤ 0.88184 * 0.88184 := mul_self_le_mul_self (le_trans (by norm_num) hLlo) hLhi
      _ ≤ 1.122 * 0.6931471803 := by norm_num
      _ ≤ 1.122 * Real.log 2 := mul_le_mul_of_nonneg_left hlog2lo.le (by norm_num)
  refine ⟨?_, ?_⟩
  · -- `1.1195·log 2 ≤ 1.1195·0.6931471808 ≤ 0.88093² ≤ Δ²`
    rw [le_div_iff₀ hl2pos, pow_two (Real.log (1 + Real.sqrt 2))]
    exact key1
  · -- `Δ² ≤ 0.88184² ≤ 1.122·0.6931471803 ≤ 1.122·log 2`
    rw [div_le_iff₀ hl2pos, pow_two (Real.log (1 + Real.sqrt 2))]
    exact key2

/-- Tomamichel's smoothing logarithm `b(ε) = log₂(2/ε²)`. -/
noncomputable def smoothingLog (ε : ℝ) : ℝ := Real.logb 2 (2 / ε ^ 2)

/-- Linear variance term of the Dupuis–Fawzi finite-size penalty, in bits. -/
noncomputable def renyiVariancePenalty (V : ℝ) (m : ℕ) (β : ℝ) : ℝ :=
  V / 2 * Real.log 2 * (m : ℝ) * β

/-- Quadratic remainder term `K_β m β²` of the finite-size penalty. -/
noncomputable def renyiRemainderPenalty (m : ℕ) (β : ℝ) : ℝ :=
  binarySecondOrderRemainderBound β * (m : ℝ) * β ^ 2

/-- Rényi-to-smooth-min-entropy conversion cost `b(ε)/β`, in bits. -/
noncomputable def renyiSmoothingPenalty (ε β : ℝ) : ℝ := smoothingLog ε / β

/-- **The clamped Dupuis–Fawzi `α`-offset at variance cap `V`**,
`β⋆ = min(1/16, √(2·B/(V·log 2·m)))`.

The unclamped branch is DF's optimiser `:1061` `\label{eq_alphachoiceext}` evaluated at
`ρ[Ω] = 1` and variance cap `V`. The clamp makes this fixed choice admissible (`β⋆ < 1`)
without a block-size or smoothing regime assumption; the raw square root can exceed `1`. -/
noncomputable def clampedRenyiOffset (V : ℝ) (m : ℕ) (ε : ℝ) : ℝ :=
  min (1 / 16) (Real.sqrt (2 * smoothingLog ε / (V * Real.log 2 * (m : ℝ))))

/-- **The Cor IV.2 finite-size AEP penalty at variance cap `V`.**

`(V/2)·log 2·m·β + K_β·m·β² + log₂(2/ε²)/β` at `β = clampedRenyiOffset V m ε`.  The first
summand is `((α−1)·log 2/2)·V·m` at a state with `V(X|B) ≤ V`.

On `UnclampedRegime V m ε` it equals
`√(2·V·log 2·m·log₂(2/ε²)) + 2·K_β·log₂(2/ε²)/(V·log 2)`
(`clampedRenyiPenalty_eq_closedForm`). -/
noncomputable def clampedRenyiPenalty (V : ℝ) (m : ℕ) (ε : ℝ) : ℝ :=
  renyiVariancePenalty V m (clampedRenyiOffset V m ε) +
    renyiRemainderPenalty m (clampedRenyiOffset V m ε) +
    renyiSmoothingPenalty ε (clampedRenyiOffset V m ε)

/-- **The Cor IV.2 finite-size AEP penalty at variance cap `V`, charged at a free Rényi offset
`β`.**

`(V/2)·log 2·m·β + K_β·m·β² + log₂(2/ε²)/β` — the Dupuis–Fawzi Cor. IV.2 bound's finite-size
penalty at an arbitrary `β ∈ (0, 1)`, not only at the clamped optimiser `clampedRenyiOffset`
(which ignores the `K_β·m·β²` remainder). The free-β version lets the Bell–Rényi BB84 theorem pick
any
admissible offset. -/
noncomputable def renyiPenalty (V : ℝ) (m : ℕ) (ε β : ℝ) : ℝ :=
  renyiVariancePenalty V m β + renyiRemainderPenalty m β + renyiSmoothingPenalty ε β

/-- The fixed-β⋆ penalty is the free-β penalty at `β = clampedRenyiOffset V m ε`. -/
lemma clampedRenyiPenalty_eq (V : ℝ) (m : ℕ) (ε : ℝ) :
    clampedRenyiPenalty V m ε
      = renyiPenalty V m ε (clampedRenyiOffset V m ε) :=
  rfl


/-- `0 ≤ β⋆`. -/
lemma clampedRenyiOffset_nonneg (V : ℝ) (m : ℕ) (ε : ℝ) : 0 ≤ clampedRenyiOffset V m ε :=
  le_min (by norm_num) (Real.sqrt_nonneg _)

/-- The fixed offset satisfies `β⋆ ≤ 1/16` unconditionally. -/
lemma clampedRenyiOffset_le_one_sixteenth (V : ℝ) (m : ℕ) (ε : ℝ) :
    clampedRenyiOffset V m ε ≤ 1 / 16 :=
  min_le_left _ _

/-- `0 < β⋆` whenever `0 < V`, `0 < ε < 1` and `m ≥ 1`. -/
lemma clampedRenyiOffset_pos (V : ℝ) (hV : 0 < V) (m : ℕ) [NeZero m] (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) : 0 < clampedRenyiOffset V m ε := by
  have hB : 1 < Real.logb 2 (2 / ε ^ 2) := one_lt_logb_two_div_sq ε hε hε1
  have hm : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hden : (0 : ℝ) < V * Real.log 2 * (m : ℝ) := mul_pos (mul_pos hV hl2) hm
  refine lt_min (by norm_num) (Real.sqrt_pos.mpr ?_)
  exact div_pos (by change 0 < 2 * Real.logb 2 (2 / ε ^ 2); linarith) hden

/-- The Cor IV.2 penalty at variance cap `V` is nonnegative for `V ≥ 0`, with no hypotheses on
`m`, `ε`.  Under Lean's junk-value conventions the degenerate inputs collapse the whole expression
to `0`: at `m = 0`, at `ε = 0` and at `ε ≥ √2` the `√` argument is non-positive, so `β⋆ = 0` and
the third summand is `B/0 = 0`. -/
lemma clampedRenyiPenalty_nonneg (V : ℝ) (hV : 0 ≤ V) (m : ℕ) (ε : ℝ) :
    0 ≤ clampedRenyiPenalty V m ε := by
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hβnn : 0 ≤ clampedRenyiOffset V m ε := clampedRenyiOffset_nonneg V m ε
  rcases eq_or_lt_of_le hβnn with h0 | hpos
  · rw [clampedRenyiPenalty,
    InfoTheory.Renyi.renyiVariancePenalty,
    InfoTheory.Renyi.renyiRemainderPenalty,
    InfoTheory.Renyi.renyiSmoothingPenalty,
    InfoTheory.Renyi.smoothingLog, ← h0]
    simp
  · -- β⋆ > 0 forces a positive square-root branch, hence `B > 0`.
    have hsq : 0 < Real.sqrt (2 * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2 * (m : ℝ))) :=
      lt_of_lt_of_le hpos (min_le_right _ _)
    have harg : 0 < 2 * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2 * (m : ℝ)) := by
      by_contra hc
      push Not at hc
      rw [Real.sqrt_eq_zero_of_nonpos hc] at hsq
      exact lt_irrefl _ hsq
    have hB : 0 < Real.logb 2 (2 / ε ^ 2) := by
      by_contra hc
      push Not at hc
      have hnum : 2 * Real.logb 2 (2 / ε ^ 2) ≤ 0 := by linarith
      have hden : (0 : ℝ) ≤ V * Real.log 2 * (m : ℝ) :=
        mul_nonneg (mul_nonneg hV hl2) (Nat.cast_nonneg _)
      have hquot : 2 * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2 * (m : ℝ)) ≤ 0 := by
        rcases eq_or_lt_of_le hden with hd | hd
        · rw [← hd, div_zero]
        · exact div_nonpos_of_nonpos_of_nonneg hnum hd.le
      linarith
    have t1 : (0 : ℝ) ≤ V / 2 * Real.log 2 * (m : ℝ) * clampedRenyiOffset V m ε := by
      have h1 : (0 : ℝ) ≤ V / 2 := div_nonneg hV (by norm_num)
      exact mul_nonneg (mul_nonneg (mul_nonneg h1 hl2) (Nat.cast_nonneg _)) hβnn
    have hK := binarySecondOrderRemainderBound_nonneg
      ((clampedRenyiOffset_le_one_sixteenth V m ε).trans (by norm_num))
    have t2 : 0 ≤ binarySecondOrderRemainderBound (clampedRenyiOffset V m ε) * (m : ℝ)
        * clampedRenyiOffset V m ε ^ 2 := by positivity
    have t3 : 0 ≤ Real.logb 2 (2 / ε ^ 2) / clampedRenyiOffset V m ε := (div_pos hB hpos).le
    rw [clampedRenyiPenalty,
    InfoTheory.Renyi.renyiVariancePenalty,
    InfoTheory.Renyi.renyiRemainderPenalty,
    InfoTheory.Renyi.renyiSmoothingPenalty,
    InfoTheory.Renyi.smoothingLog]
    linarith

/-- The free-offset Cor IV.2 penalty is nonnegative for `V ≥ 0`, `0 < ε ≤ 1` and
`0 ≤ β ≤ 1`. -/
lemma renyiPenalty_nonneg (V : ℝ) (hV : 0 ≤ V) (m : ℕ)
    (ε β : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    0 ≤ renyiPenalty V m ε β := by
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsq : ε ^ 2 ≤ 1 := by nlinarith
  have harg : (1 : ℝ) ≤ 2 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity : 0 < ε ^ 2)]
    linarith
  have hB : 0 ≤ Real.logb 2 (2 / ε ^ 2) :=
    Real.logb_nonneg (by norm_num) harg
  have hK := binarySecondOrderRemainderBound_nonneg hβ1
  simp only [renyiPenalty,
    InfoTheory.Renyi.renyiVariancePenalty,
    InfoTheory.Renyi.renyiRemainderPenalty,
    InfoTheory.Renyi.renyiSmoothingPenalty,
    InfoTheory.Renyi.smoothingLog]
  positivity

end InfoTheory.Renyi

end -- noncomputable section
