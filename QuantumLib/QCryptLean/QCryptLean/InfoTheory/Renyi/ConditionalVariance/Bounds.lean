import Batteries.Tactic.OpenPrivate
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.CQReference
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.Defs
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
import QCryptLean.InfoTheory.Renyi.PetzConditional

/-! # Bounds -/


open Matrix 
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace InfoTheory.Renyi

private local instance (m : Type*) [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}


open private klein_scaled
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments

open private holder_three
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments

open private one_le_sum_mul_exp_of_sum_mul_eq_zero
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments

open private classical_var_le
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments

open private two_rpow_relEnt
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private ns_M_eq
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private ns_divVar_eq
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private ns_Y_sum
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private ns_relEnt_eq
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private ns_sum_one
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsD
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsRef_sum
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsW_exp_neg_le
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsW_exp_sum
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsW_sum
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsW_nonneg
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsL
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsW
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private ns_support
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private ns_eigenvalues_nonneg
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private ns_petzTrace
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsOverlap_nonneg
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private nsOverlap
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights


/-- **DF `:394` `\label{lem:divergence-variance-general-bounds}`**, equation
`\label{eq:bound_dalpha}` at `:398` with the display at `:399`.

`2^{ν D'_{1+ν}} = Tr[ρ^{1+ν}σ^{-ν}] = petzTrace (1+ν) ρ σ` (`:420`) and
`2^{-ν D'_{1-ν}} = Tr[ρ^{1-ν}σ^{ν}] = petzTrace (1-ν) ρ σ` (`:424`), so the source's
display is stated here through `petzTrace`, which is defined at EVERY real order. This is
what keeps the leaf inside the `1 < α ≤ 2` branch of `petzRenyiDivergence` — see the
module docstring.

`hnorm` strengthens DF `:395` and is required; see the module docstring.

Proof: the classical chain
`V̂ ≤ ν⁻² ln²(M ν + M (−ν) + 1)` from `(log t)² ≤ (log (t + t⁻¹ + 1))²` and concavity of
`ln²` on `[e,∞)`, lifted to operators by the Nussbaum–Szkoła identity (§2.2, DF
`:770`–`:774`). -/
theorem petzDivergenceVariance_le {m : Type*} [Fintype m] [DecidableEq m]
    (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν < 1)
    (ρ σ : Matrix m m ℂ) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hnorm : ρ.trace.re = 1)
    (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) :
    petzDivergenceVariance ρ σ ≤
      (1 / ν ^ 2) * (Real.logb 2
        ((2 : ℝ) ^ (-ν * relativeEntropyBits ρ σ) * petzTrace (1 + ν) ρ σ
          + (2 : ℝ) ^ (ν * relativeEntropyBits ρ σ) * petzTrace (1 - ν) ρ σ
          + 1)) ^ 2 := by
  have hρh : ρ.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hρ).isHermitian
  have hσh : σ.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hσ).isHermitian
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hM1 : (2 : ℝ) ^ (-ν * relativeEntropyBits ρ σ) * petzTrace (1 + ν) ρ σ
      = ∑ p : m × m, nsW hρh hσh p * Real.exp (ν * (nsL hρh hσh p - nsD hρh hσh)) := by
    rw [two_rpow_relEnt hρh hσh hnorm (-ν),
      ns_M_eq hρh hσh hρ hσ hsupp (s := ν) (by linarith),
      show -ν * nsD hρh hσh = -(ν * nsD hρh hσh) from by ring]
  have hM2 : (2 : ℝ) ^ (ν * relativeEntropyBits ρ σ) * petzTrace (1 - ν) ρ σ
      = ∑ p : m × m, nsW hρh hσh p * Real.exp (-ν * (nsL hρh hσh p - nsD hρh hσh)) := by
    rw [two_rpow_relEnt hρh hσh hnorm ν,
      ns_M_eq hρh hσh hρ hσ hsupp (s := -ν) (by linarith),
      show (1 : ℝ) + -ν = 1 - ν from by ring,
      show -(-ν * nsD hρh hσh) = ν * nsD hρh hσh from by ring]
  have hcl := classical_var_le (nsW hρh hσh) (fun p => nsL hρh hσh p - nsD hρh hσh)
    (fun p => nsW_nonneg hρh hσh hρ p) (ns_sum_one hρh hσh hnorm) hν0
  rw [← hM1, ← hM2] at hcl
  rw [ns_divVar_eq hρh hσh hnorm, Real.logb, div_le_iff₀ (by positivity : (0:ℝ) < Real.log 2 ^ 2)]
  refine hcl.trans (le_of_eq ?_)
  field_simp


end InfoTheory.Renyi

end
