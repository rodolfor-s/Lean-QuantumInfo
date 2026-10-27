import QCryptLean.InfoTheory.RelativeEntropy.Basic
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
import QCryptLean.InfoTheory.Renyi.PetzConditional
import QCryptLean.InfoTheory.VonNeumannEntropy.TraceFormula
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.PurifiedBasic
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Metrics.PurifiedOrder
import QCryptLean.Quantum.Metrics.TraceDuality
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification

/-! # Support-sensitive relative entropy theorems on finite registers -/

noncomputable section

namespace InfoTheory.RelativeEntropy

open Matrix Quantum.Operators

open InfoTheory.VonNeumannEntropy
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open private nsW nsL nsW_nonneg ns_sum_one nsW_exp_neg_le nsWL_sum nsW_exp_sum
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private one_le_sum_mul_exp_of_sum_mul_eq_zero
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Relative entropy vanishes on equal states. -/
theorem relativeEntropyReal_self (ρ : DensityOp Q) : relativeEntropyReal ρ ρ = 0 := by
  rw [relativeEntropyReal,
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy_eq_neg_trace_mul_log, neg_neg]
  exact sub_self _

/-- The signed value is nonnegative by generic spectral weights under kernel inclusion. -/
theorem relativeEntropyReal_nonneg_of_ker_sub (ρ σ : DensityOp Q)
    (h : ∀ v, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    0 ≤ relativeEntropyReal ρ σ := by
  classical
  have hsum : (∑ p : Q × Q, nsW ρ.isHermitian σ.isHermitian p) = 1 :=
    ns_sum_one ρ.isHermitian σ.isHermitian (by rw [ρ.trace_one, Complex.one_re])
  have hb := nsW_exp_neg_le ρ.isHermitian σ.isHermitian
    ρ.posSemidef.nonneg σ.posSemidef.nonneg h
  have hl : (∑ p : Q × Q, nsW ρ.isHermitian σ.isHermitian p *
      (1 - nsL ρ.isHermitian σ.isHermitian p)) ≤
        ∑ p : Q × Q, nsW ρ.isHermitian σ.isHermitian p *
          Real.exp (-nsL ρ.isHermitian σ.isHermitian p) := by
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_left _
      (nsW_nonneg ρ.isHermitian σ.isHermitian ρ.posSemidef.nonneg p)
    linarith [Real.add_one_le_exp (-nsL ρ.isHermitian σ.isHermitian p)]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum,
    nsWL_sum ρ.isHermitian σ.isHermitian] at hl
  rw [σ.trace_one, Complex.one_re] at hb
  rw [relativeEntropyReal,
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy_eq_neg_trace_mul_log, neg_neg,
    traceProductLogSigma]
  rw [Matrix.trace_sub, Complex.sub_re] at hl
  change 0 ≤ (ρ.toOp * CFC.log ρ.toOp).trace.re - (ρ.toOp * CFC.log σ.toOp).trace.re
  linarith

/-- Extended relative entropy vanishes exactly on equal states,
by spectral Jensen and fidelity separation. -/
theorem relativeEntropy_eq_zero_iff (ρ σ : DensityOp Q) :
    relativeEntropy ρ σ = 0 ↔ ρ = σ := by
  classical
  let : Nonempty Q := ρ.nonempty
  constructor
  · intro hz
    have hs : ∀ v, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0 := by
      by_contra h
      rw [relativeEntropy_eq_top_of_not_ker_sub ρ σ h] at hz
      exact ENNReal.top_ne_zero hz
    rw [relativeEntropy_eq_ofReal_of_ker_sub ρ σ hs, ENNReal.ofReal_eq_zero] at hz
    have hD := le_antisymm hz (relativeEntropyReal_nonneg_of_ker_sub ρ σ hs)
    have hw : ∑ p : Q × Q, nsW ρ.isHermitian σ.isHermitian p = 1 :=
      ns_sum_one ρ.isHermitian σ.isHermitian (by rw [ρ.trace_one, Complex.one_re])
    have hL : ∑ p : Q × Q, nsW ρ.isHermitian σ.isHermitian p *
        nsL ρ.isHermitian σ.isHermitian p = 0 := by
      rw [nsWL_sum, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
      rw [relativeEntropyReal, vonNeumannEntropy_eq_neg_trace_mul_log, neg_neg,
        traceProductLogSigma] at hD
      exact hD
    have hj := one_le_sum_mul_exp_of_sum_mul_eq_zero
      (nsW ρ.isHermitian σ.isHermitian) (nsL ρ.isHermitian σ.isHermitian)
      (nsW_nonneg ρ.isHermitian σ.isHermitian ρ.posSemidef.nonneg) hw hL ((1 / 2 : ℝ) - 1)
    rw [nsW_exp_sum ρ.isHermitian σ.isHermitian ρ.posSemidef.nonneg
      σ.posSemidef.nonneg hs (by norm_num : (0 : ℝ) < 1 / 2)] at hj
    have ha : 1 ≤ (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp).trace.re := by
      simpa only [InfoTheory.Renyi.petzTrace, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num,
        ← CFC.sqrt_eq_rpow] using hj
    have hf : 1 ≤ Quantum.Metrics.fidelity
        ρ.toSubDensityOp.toPosSemidefOp σ.toSubDensityOp.toPosSemidefOp := by
      have h := Quantum.Metrics.norm_overlap_le_fidelity
        ρ.toPosSemidefOp σ.toPosSemidefOp
        ρ.toPosSemidefOp.purificationKet σ.toPosSemidefOp.purificationKet
        ρ.toPosSemidefOp.partialTraceRight_purificationKet
        σ.toPosSemidefOp.partialTraceRight_purificationKet
      change ‖((Ket.vectorize (CFC.sqrt ρ.toOp)).dag *
        Ket.vectorize (CFC.sqrt σ.toOp) : ℂ)‖ ≤ _ at h
      rw [Ket.vectorize_inner, (Matrix.nonneg_iff_posSemidef.mp
        (CFC.sqrt_nonneg ρ.toOp)).isHermitian.eq] at h
      exact (ha.trans (Complex.re_le_norm _)).trans h
    have hg : Quantum.Metrics.fidelityGen ρ.toSubDensityOp σ.toSubDensityOp = 1 := by
      apply le_antisymm (Quantum.Metrics.fidelityGen_le_one _ _)
      rwa [Quantum.Metrics.fidelityGen_eq_fidelity_of_trace_one _ _
        (by exact congrArg Complex.re ρ.trace_one)]
    have he := (Quantum.Metrics.purifiedDistance_eq_zero_iff
      ρ.toSubDensityOp σ.toSubDensityOp).mp (by
        simp [Quantum.Metrics.purifiedDistance, hg])
    exact DensityOp.ext (congrArg SubDensityOp.toOp he)
  · rintro rfl
    rw [relativeEntropy_eq_ofReal_of_ker_sub ρ ρ (fun _ h => h), relativeEntropyReal_self]
    exact ENNReal.ofReal_zero

end InfoTheory.RelativeEntropy
