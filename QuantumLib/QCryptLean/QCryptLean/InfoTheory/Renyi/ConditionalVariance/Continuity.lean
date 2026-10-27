import Batteries.Tactic.OpenPrivate
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.CQReference
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.Defs
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
import QCryptLean.InfoTheory.Renyi.PetzConditional

/-! # Continuity -/


open Matrix 
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace InfoTheory.Renyi

private local instance (m : Type*) [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}


open private classical_continuity_le
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments

open private one_le_sum_mul_exp_of_sum_mul_eq_zero
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments

open private ns_two_rpow_eq
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private ns_divVar_eq
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private ns_Y_sum
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private ns_sum_one
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsD
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsW_nonneg
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsL
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsW
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights


/-- Scalar prefactor of the Dupuis–Fawzi third-order continuity remainder, in bits. -/
def continuityRemainderScale (μ : ℝ) : ℝ := 1 / (6 * μ ^ 3 * Real.log 2)

/-- Gap between Petz Rényi divergence and relative entropy, both in bits. -/
def petzDivergenceGap {m : Type*} [Fintype m] [DecidableEq m]
    (α : ℝ) (ρ σ : Matrix m m ℂ) : ℝ :=
  petzRenyiDivergence α ρ σ - relativeEntropyBits ρ σ

/-- `K_{ρ,σ}(α,μ)` of DF `:715`, verbatim and with NO hidden `sup`: DF's `sup_{0<γ≤ν}` at
`:731` is internal to their proof, and the remainder is pointwise monotone in `γ`
(`∂_γ (z^γ ln³z) = z^γ ln⁴z ≥ 0`), so the supremum is superfluous and the statement carries
none. -/
def petzContinuityK {m : Type*} [Fintype m] [DecidableEq m]
    (α μ : ℝ) (ρ σ : Matrix m m ℂ) : ℝ :=
  continuityRemainderScale μ * (2 : ℝ) ^ ((α - 1) * petzDivergenceGap α ρ σ) *
    (Real.log ((2 : ℝ) ^ ((α + μ - 1) * petzDivergenceGap (α + μ) ρ σ) + Real.exp 2)) ^ 3

/-- **DF `:713` (lemma head `:710`, `\label{lem_HalphaH_second_order_new}` at `:711`), the
`D'_α ≤ …` half only.** The `D_α ≤ D'_α` half is about the SANDWICHED divergence and is NOT
stated here.

No cap on `α + μ` is needed; see the module docstring.

Proof: the classical MGF chain
`ln (M ν) ≤ ν²V̂/2 + (ν³/6)·R` from `exp u ≤ 1 + u + u²/2 + (u³/6)·exp u` and
`ln (1+x) ≤ x`, with `R` controlled by concavity of `t ↦ ln³(t + e²)`, lifted to operators
by the Nussbaum–Szkoła identity (§2.2, DF `:770`–`:774`). -/
theorem petzRenyiDivergence_le_relEntropy_add {m : Type*} [Fintype m] [DecidableEq m]
    (α μ : ℝ) (hα : 1 < α) (hμ0 : 0 < μ)
    (ρ σ : Matrix m m ℂ) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hnorm : ρ.trace.re = 1)
    (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) :
    petzRenyiDivergence α ρ σ
      ≤ relativeEntropyBits ρ σ
        + ((α - 1) * Real.log 2 / 2) * petzDivergenceVariance ρ σ
        + (α - 1) ^ 2 * petzContinuityK α μ ρ σ := by
  have hρh : ρ.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hρ).isHermitian
  have hσh : σ.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hσ).isHermitian
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hν : (0 : ℝ) < α - 1 := by linarith
  have hβ2 : (1 : ℝ) < α + μ := by linarith
  -- `Mv` and `Mvm`
  have hMv := ns_two_rpow_eq hρh hσh hρ hσ hnorm hsupp hα
  have hMvm := ns_two_rpow_eq hρh hσh hρ hσ hnorm hsupp hβ2
  rw [show α + μ - 1 = (α - 1) + μ from by ring] at hMvm
  -- `D'_α − D`
  have hMge := one_le_sum_mul_exp_of_sum_mul_eq_zero (nsW hρh hσh) (fun p => nsL hρh hσh p - nsD
    hρh hσh)
    (fun p => nsW_nonneg hρh hσh hρ p) (ns_sum_one hρh hσh hnorm) (ns_Y_sum hρh hσh hnorm)
    (α - 1)
  have hMpos : (0 : ℝ) < ∑ p : m × m, nsW hρh hσh p
      * Real.exp ((α - 1) * (nsL hρh hσh p - nsD hρh hσh)) := lt_of_lt_of_le zero_lt_one hMge
  have hdiff : petzRenyiDivergence α ρ σ - relativeEntropyBits ρ σ
      = Real.log (∑ p : m × m, nsW hρh hσh p
          * Real.exp ((α - 1) * (nsL hρh hσh p - nsD hρh hσh))) / ((α - 1) * Real.log 2) := by
    have h := hMv
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    have hlog := congrArg Real.log h
    rw [Real.log_exp] at hlog
    field_simp at hlog ⊢
    linarith [hlog]
  -- the classical bound
  have hcl := classical_continuity_le (nsW hρh hσh) (fun p => nsL hρh hσh p - nsD hρh hσh)
    (fun p => nsW_nonneg hρh hσh hρ p) (ns_sum_one hρh hσh hnorm) (ns_Y_sum hρh hσh hnorm)
    hν hμ0
  simp only [petzContinuityK, continuityRemainderScale, petzDivergenceGap]
  rw [ show α + μ - 1 = α - 1 + μ from by ring, hMv, hMvm,
    ns_divVar_eq hρh hσh hnorm]
  set A : ℝ := Real.log (∑ p : m × m, nsW hρh hσh p
      * Real.exp ((α - 1) * (nsL hρh hσh p - nsD hρh hσh))) with hA
  set B : ℝ := ∑ p : m × m, nsW hρh hσh p * (nsL hρh hσh p - nsD hρh hσh) ^ 2 with hB
  set Mv : ℝ := ∑ p : m × m, nsW hρh hσh p
      * Real.exp ((α - 1) * (nsL hρh hσh p - nsD hρh hσh)) with hMvdef
  set L3 : ℝ := (Real.log ((∑ p : m × m, nsW hρh hσh p
      * Real.exp (((α - 1) + μ) * (nsL hρh hσh p - nsD hρh hσh))) + Real.exp 2)) ^ 3 with hL3
  have hgoal : A / ((α - 1) * Real.log 2)
      ≤ (α - 1) * Real.log 2 / 2 * (B / Real.log 2 ^ 2)
        + (α - 1) ^ 2 * (1 / (6 * μ ^ 3 * Real.log 2) * Mv * L3) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (α - 1) * Real.log 2)]
    have hrw : ((α - 1) * Real.log 2 / 2 * (B / Real.log 2 ^ 2)
          + (α - 1) ^ 2 * (1 / (6 * μ ^ 3 * Real.log 2) * Mv * L3)) * ((α - 1) * Real.log 2)
        = (α - 1) ^ 2 * B / 2 + (α - 1) ^ 3 / (6 * μ ^ 3) * Mv * L3 := by
      field_simp
    rw [hrw]
    exact hcl
  have := hdiff
  linarith [hgoal, hdiff]


end InfoTheory.Renyi

end
