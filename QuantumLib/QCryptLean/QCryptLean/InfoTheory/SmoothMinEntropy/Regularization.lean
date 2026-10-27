import Mathlib.Analysis.SpecialFunctions.Log.Base
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.FeasibleRegularization
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.RealRegularity
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.SmoothTransport
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.Regularized
import QCryptLean.Quantum.Operators.StateOperations

/-! # Regularization -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators
open scoped ComplexOrder

variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq Q] [Nonempty Q]

variable [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
/-- The original reference, scaled by the retained weight, lies below its regularization. -/
theorem opLe_smul_regularized (σ : SubDensityOp Q) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    OpLe (((1 - γ : ℝ) : ℂ) • σ.toOp) (σ.regularized γ hγ0 hγ1).toOp := by
  apply opLe_of_posSemidef_sub
  change (((1 - γ : ℝ) : ℂ) • σ.toOp +
    (γ : ℂ) • (DensityOp.maxMixed (X := Q)).toOp -
    ((1 - γ : ℝ) : ℂ) • σ.toOp).PosSemidef
  rw [add_sub_cancel_left]
  exact DensityOp.maxMixed.posSemidef.smul (Complex.nonneg_iff.mpr ⟨hγ0, rfl⟩)

/-- Regularization preserves a floor with the exact signed logarithmic correction.
Every smoothing witness retains a feasible scale after the logarithmic correction. -/
theorem smoothMinEntropy_regularized_ge (ε : ℝ) (ρ : CQState C Q) (σ : SubDensityOp Q)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    ENNReal.ofReal (k + Real.log (1 - γ) / Real.log 2) ≤
      smoothMinEntropy ε ρ (σ.regularized γ hγ0 hγ1.le) := by
  have hp : 0 < 1 - γ := sub_pos.mpr hγ1
  let c := -(Real.log (1 - γ) / Real.log 2)
  have hc : 0 ≤ c := neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
    (Real.log_nonpos hp.le (by linarith)) (Real.log_pos one_lt_two).le)
  have h := smoothMinEntropy_le_add_of_feasible_transport
    ρ σ ρ (σ.regularized γ hγ0 hγ1.le) ε ε c hc
  have hb : (2 : ℝ) ^ c * (1 - γ) = 1 := by
    rw [show c = -Real.logb 2 (1 - γ) from rfl, Real.rpow_neg (by norm_num),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hp]
    exact inv_mul_cancel₀ hp.ne'
  have hh : smoothMinEntropy ε ρ σ ≤
      smoothMinEntropy ε ρ (σ.regularized γ hγ0 hγ1.le) + ENNReal.ofReal c := by
    apply h
    intro τ hd
    refine ⟨τ, hd, fun t ht => ⟨mul_nonneg
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le ht.1,
      fun z => (ht.2 z).trans ?_⟩⟩
    have hpsd := (opLe_iff_posSemidef_sub
      (σ.posSemidef.smul (Complex.zero_le_real.mpr hp.le)).isHermitian
      (σ.regularized γ hγ0 hγ1.le).isHermitian).mp
        (opLe_smul_regularized σ γ hγ0 hγ1.le)
    apply opLe_of_posSemidef_sub
    have hs := hpsd.smul (Complex.zero_le_real.mpr
      (mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) c).le ht.1))
    convert hs using 1
    rw [smul_sub, smul_smul]
    congr 2
    push_cast
    have hh : (2 : ℝ) ^ c * t * (1 - γ) = t := by
      calc _ = ((2 : ℝ) ^ c * (1 - γ)) * t := by ring
           _ = t := by rw [hb, one_mul]
    simpa only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one] using
      congrArg Complex.ofReal hh.symm
  have hf := tsub_le_iff_right.mpr (hk.trans hh)
  rw [← ENNReal.ofReal_sub _ hc] at hf
  simpa only [c, sub_neg_eq_add] using hf
/-- A positive real floor transfers with its signed logarithmic correction.
The weight condition is retained for the full smoothing ball. -/
theorem add_log_le_smoothMinEntropyReal_regularized_of_pos_floor [Nonempty C]
    (ε : ℝ) (hε : 0 ≤ ε) (ρ : CQState C Q) (σ : SubDensityOp Q)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hweight : 2 * ε < ∑ c, (ρ.stateMap c).trace) (k : ℝ) (hkpos : 0 < k)
    (hk : k ≤ smoothMinEntropyReal ε ρ σ) :
    k + Real.log (1 - γ) / Real.log 2 ≤
      smoothMinEntropyReal ε ρ (σ.regularized γ hγ0.le hγ1.le) := by
  let σ' := σ.regularized γ hγ0.le hγ1.le
  let c := 1 - γ
  have hc : 0 < c := sub_pos.mpr hγ1
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hbdd := smoothMinEntropyReal_bddAbove_of_weight ε ρ hweight σ'
  apply le_of_forall_pos_le_add
  intro ν hν
  let ν' := min ν (k / 2)
  have hν' : 0 < ν' := lt_min hν (by linarith)
  have hνν : ν' ≤ ν := min_le_left _ _
  have hrpos : 0 < k - ν' := by have := min_le_right ν (k / 2); dsimp [ν']; linarith
  obtain ⟨r, ⟨τ, rfl, hd⟩, hr⟩ := exists_lt_of_lt_csSup
    (smoothedSetReal_nonempty ρ σ hε) (show k - ν' < smoothMinEntropyReal ε ρ σ by linarith)
  have hw : 0 < ∑ z, (τ.stateMap z).trace :=
    (sub_pos.mpr hweight).trans_le (ρ.weight_sub_two_mul_le_of_purifiedDistance_le τ hd)
  have hfeas : HasScale τ σ := by
    by_contra hn
    simp only [minEntropyReal, minScale_eq_zero_of_not_hasScale τ σ hn,
      Real.log_zero, neg_zero, zero_div] at hr
    exact (not_lt_of_ge hrpos.le) hr
  have hp : 0 < minScale τ σ :=
    (div_pos hw (Nat.cast_pos.mpr Fintype.card_pos)).trans_le
      (weight_div_card_le_minScale_of_hasScale τ σ hfeas)
  have her : ENNReal.ofReal (k - ν') < minEntropy τ σ := by
    rw [minEntropy_eq_of_pos τ σ hp]
    exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hr, (hrpos.trans hr)⟩
  obtain ⟨a, ha, har⟩ := exists_isFeasible_lt_rpow_of_lt_minEntropy τ σ her
  let t := (2 : ℝ) ^ (-(k - ν' + Real.log c / Real.log 2))
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have htc : t * c = 2 ^ (-(k - ν')) := by
    dsimp [t]
    rw [neg_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (Real.log c / Real.log 2)]
    rw [show Real.log c / Real.log 2 = Real.logb 2 c from rfl,
      Real.rpow_logb (by norm_num) (by norm_num) hc]
    rw [mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]
  have hf : IsFeasible τ σ' t := by
    refine ⟨ht.le, fun z => ((ha.mono har.le).2 z).trans ?_⟩
    apply opLe_of_posSemidef_sub
    have hp' := (opLe_iff_posSemidef_sub
      (σ.posSemidef.smul (Complex.zero_le_real.mpr hc.le)).isHermitian σ'.isHermitian).mp
      (opLe_smul_regularized σ γ hγ0.le hγ1.le)
    have hh := hp'.smul (Complex.zero_le_real.mpr ht.le)
    simpa only [smul_sub, smul_smul, ← Complex.ofReal_mul, htc] using hh
  have hp' : 0 < minScale τ σ' :=
    (div_pos hw (Nat.cast_pos.mpr Fintype.card_pos)).trans_le
      (weight_div_card_le_minScale_of_hasScale τ σ' ⟨t, hf⟩)
  have hlevel : k - ν' + Real.log c / Real.log 2 ≤ minEntropyReal τ σ' := by
    have hh := Real.log_le_log hp' (minScale_le_of_isFeasible τ σ' hf)
    change Real.log (minScale τ σ') ≤ Real.log ((2 : ℝ) ^ _) at hh
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hh
    apply (le_div_iff₀ hlog).mpr
    change _ ≤ -Real.log (minScale τ σ')
    nlinarith only [hh]
  have hsup : minEntropyReal τ σ' ≤ smoothMinEntropyReal ε ρ σ' :=
    le_csSup hbdd ⟨τ, rfl, hd⟩
  change _ ≤ smoothMinEntropyReal ε ρ σ' + ν
  dsimp [c] at hlevel
  linarith

omit [DecidableEq Q] in
/-- Every strict real level below an extended floor has a positive-definite reference.
Mixing an arbitrarily small positive identity component realizes each strict level. -/
theorem exists_posDef_ofReal_le_smoothMinEntropy_of_lt (ε : ℝ)
    (ρ : CQState C Q) (σ : SubDensityOp Q) (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) (t : ℝ) (ht : t < k) :
    ∃ σ' : SubDensityOp Q, σ'.toOp.PosDef ∧ ENNReal.ofReal t ≤ smoothMinEntropy ε ρ σ' := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  let c : ℝ := Real.exp ((t - k) * Real.log 2)
  have hc_pos : 0 < c := Real.exp_pos _
  have hc_lt : c < 1 := by
    change Real.exp _ < 1
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (sub_neg.mpr ht) hlog2)
  let γ : ℝ := 1 - c
  have hγ0 : 0 < γ := sub_pos.mpr hc_lt
  have hγ1 : γ < 1 := by dsimp [γ]; linarith
  refine ⟨σ.regularized γ hγ0.le hγ1.le,
    SubDensityOp.posDef_regularized σ γ hγ0 hγ1.le, ?_⟩
  have h := smoothMinEntropy_regularized_ge ε ρ σ γ hγ0.le hγ1 k hk
  have hone_sub : (1 : ℝ) - γ = c := by dsimp [γ]; ring
  rw [hone_sub, show c = Real.exp ((t - k) * Real.log 2) from rfl, Real.log_exp] at h
  have hlevel : k + (t - k) * Real.log 2 / Real.log 2 = t := by
    rw [mul_div_cancel_right₀ _ hlog2.ne']
    ring
  rwa [hlevel] at h
end InfoTheory.SmoothMinEntropy
