import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Strict entropy witnesses with positive definite references

Regularization preserves every strictly larger feasible coefficient. Entropy is
in bits, with the same extended positive-part and infeasible-reference conventions.
The matrix order used for positivity is local.
-/
noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder
variable {C Q : Type*} [Fintype C] [Fintype Q]

/-- A strict extended entropy level admits a feasible coefficient below its exponential. -/
theorem exists_isFeasible_lt_rpow_of_lt_minEntropy (ρ : CQState C Q) (σ : SubDensityOp Q)
    {k : ℝ} (hk : ENNReal.ofReal k < minEntropy ρ σ) :
    ∃ t, IsFeasible ρ σ t ∧ t < 2 ^ (-k) := by
  have hscale : HasScale ρ σ := by
    by_contra hn
    rw [minEntropy_eq_zero_of_not_hasScale ρ σ hn] at hk
    exact (not_lt_of_ge zero_le) hk
  apply exists_lt_of_csInf_lt hscale
  by_cases hp : 0 < minScale ρ σ
  · rw [minEntropy_eq_of_pos ρ σ hp] at hk
    have hh : k < minEntropyReal ρ σ := ENNReal.ofReal_lt_ofReal_iff'.mp hk |>.1
    have hl : Real.log (minScale ρ σ) < -k * Real.log 2 := by
      have h := (lt_div_iff₀ (Real.log_pos one_lt_two)).mp hh
      change k * Real.log 2 < -Real.log (minScale ρ σ) at h
      linarith
    apply (Real.log_lt_log_iff hp (Real.rpow_pos_of_pos (by norm_num) _)).mp
    rwa [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  · exact (le_of_not_gt hp).trans_lt (Real.rpow_pos_of_pos (by norm_num) _)

/-- Increasing a feasible coefficient strictly allows a positive definite reference. -/
theorem IsFeasible.exists_posDef_of_lt [Nonempty Q]
    {ρ : CQState C Q} {σ : SubDensityOp Q} {a t : ℝ}
    (ha : IsFeasible ρ σ a) (hat : a < t) :
    ∃ σ' : SubDensityOp Q, σ'.toOp.PosDef ∧ IsFeasible ρ σ' t := by
  classical
  have ht : 0 < t := ha.1.trans_lt hat
  let c := a / t
  have hc : 0 ≤ c := div_nonneg ha.1 ht.le
  have hc1 : c < 1 := (div_lt_one ht).mpr hat
  let b := (1 - c) / (Fintype.card Q : ℝ)
  have hb : 0 < b := div_pos (sub_pos.mpr hc1) (by exact_mod_cast Fintype.card_pos)
  let B : Matrix Q Q ℂ := (c : ℂ) • σ.toOp + (b : ℂ) • 1
  have hB : B.PosDef := by
    change ((c : ℂ) • σ.toOp + (b : ℂ) • (1 : Matrix Q Q ℂ)).PosDef
    exact Matrix.PosDef.posSemidef_add
      (σ.posSemidef.smul (Complex.zero_le_real.mpr hc))
      (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hb))
  have htr : B.trace.re ≤ 1 := by
    change (((c : ℂ) • σ.toOp + (b : ℂ) • (1 : Matrix Q Q ℂ)).trace).re ≤ 1
    simp only [trace_add, trace_smul, trace_one, Complex.add_re, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.natCast_re]
    have hbn : b * (Fintype.card Q : ℝ) = 1 - c :=
      div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    rw [hbn]
    nlinarith [mul_le_mul_of_nonneg_left σ.trace_le_one hc]
  refine ⟨⟨B, hB.posSemidef, htr⟩, hB, ht.le, fun z => (ha.2 z).trans ?_⟩
  apply opLe_of_posSemidef_sub
  have htc : t * c = a := by dsimp [c]; field_simp
  have he : (t : ℂ) • B - (a : ℂ) • σ.toOp = ((t * b : ℝ) : ℂ) • 1 := by
    simp only [B, smul_add, smul_smul, ← Complex.ofReal_mul, htc, add_sub_cancel_left]
  rw [he]
  exact Matrix.PosSemidef.one.smul (Complex.nonneg_iff.mpr ⟨mul_nonneg ht.le hb.le, rfl⟩)

end InfoTheory.SmoothMinEntropy
