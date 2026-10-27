import QCryptLean.InfoTheory.RelativeEntropy.Basic
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.InfoTheory.VonNeumannEntropy.Variational
import QCryptLean.Math.Analysis.Matrix.GoldenThompson
import QCryptLean.Math.LinearAlgebra.Matrix.DiagonalConjugation
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic

/-! # Support-sensitive Gibbs variational inequality -/

noncomputable section
namespace InfoTheory.RelativeEntropy
open Quantum.Operators InfoTheory.VonNeumannEntropy Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The exponential pairing of a state with a Hermitian matrix is strictly positive. -/
lemma trace_mul_exp_pos (σ : DensityOp Q) (A : Op Q) (hA : A.IsHermitian) :
    0 < (σ.toOp * NormedSpace.exp A).trace.re := by
  let U := hA.eigenvectorUnitary.val
  let r : Q → ℝ := fun i => ((Uᴴ * σ.toOp * U) i i).re
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hn (i : Q) : 0 ≤ r i := by
    have h := (σ.posSemidef.mul_mul_conjTranspose_same Uᴴ).diag_nonneg (i := i)
    simpa only [conjTranspose_conjTranspose] using (Complex.nonneg_iff.mp h).1
  have hs : ∑ i, r i = 1 := by
    rw [← Complex.re_sum]
    change (Uᴴ * σ.toOp * U).trace.re = 1
    rw [trace_mul_cycle, hU, one_mul, σ.trace_one, Complex.one_re]
  have ht : (σ.toOp * NormedSpace.exp A).trace.re =
      ∑ i, r i * Real.exp (hA.eigenvalues i) := by
    rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint, hA.cfc_eq]
    exact trace_mul_conj_real_diagonal_re σ.toOp U _
  rw [ht]
  have hex : ∃ i, 0 < r i := by
    by_contra! h
    have hz := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    linarith
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hn i) (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

/-- Gibbs variational bound, including singular reference states under support containment. -/
lemma gibbs_variational_bound_of_ker_sub
    (ρ σ : DensityOp Q) (A : Op Q) (hA : A.IsHermitian)
    (hker : ∀ v, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    (ρ.toOp * A).trace.re - Real.log (σ.toOp * NormedSpace.exp A).trace.re ≤
      relativeEntropyReal ρ σ := by
  classical
  let g : ℝ → ℝ := fun t => if t = 0 then 1 else 0
  let P : Op Q := cfc g σ.toOp
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ σ.toOp) :=
    (Matrix.finite_real_spectrum (A := σ.toOp)).continuousOn _
  have hσP : σ.toOp * P = 0 := by
    rw [show σ.toOp * P = cfc (fun t : ℝ => t * g t) σ.toOp by
      rw [cfc_mul (fun t : ℝ => t) g σ.toOp (hc _) (hc _),
        cfc_id' ℝ σ.toOp σ.isHermitian.isSelfAdjoint]]
    have hz : (fun t : ℝ => t * g t) = fun _ => 0 := by
      funext t; by_cases ht : t = 0 <;> simp [g, ht]
    rw [hz, cfc_const (0 : ℝ) σ.toOp σ.isHermitian.isSelfAdjoint, map_zero]
  have hρP : ρ.toOp * P = 0 := by
    ext i j
    have hcol : σ.toOp.mulVec (fun k => P k j) = 0 := by
      funext i
      exact congrFun (congrFun hσP i) j
    exact congrFun (hker _ hcol) i
  let L (C : ℝ) : Op Q := cfc (fun t : ℝ => Real.log t - C * g t) σ.toOp
  have hL (C : ℝ) : (L C).IsHermitian :=
    (show IsSelfAdjoint (L C) from
      cfc_predicate (fun t : ℝ => Real.log t - C * g t) σ.toOp).isHermitian
  have hpair (C : ℝ) : (ρ.toOp * L C).trace.re = traceProductLogSigma ρ σ := by
    have he : L C = cfc Real.log σ.toOp - C • P := by
      change cfc _ σ.toOp = _
      rw [cfc_sub _ _ _ (hc _) (hc _), cfc_const_mul _ _ _ (hc _)]
    rw [he, mul_sub, Matrix.mul_smul, hρP, smul_zero, sub_zero]
    rfl
  have hexp (C : ℝ) : NormedSpace.exp (L C) = σ.toOp + Real.exp (-C) • P := by
    rw [← CFC.real_exp_eq_normedSpace_exp (hL C).isSelfAdjoint]
    change cfc Real.exp (cfc _ σ.toOp) = _
    rw [← cfc_comp Real.exp _ σ.toOp σ.isHermitian.isSelfAdjoint
      Real.continuous_exp.continuousOn (hc _)]
    have he : cfc (fun t : ℝ => t + Real.exp (-C) * g t) σ.toOp =
        σ.toOp + Real.exp (-C) • P := by
      rw [cfc_add _ _ _ (hc _) (hc _), cfc_id' ℝ σ.toOp σ.isHermitian.isSelfAdjoint,
        cfc_const_mul _ _ _ (hc _)]
    rw [← he]
    apply cfc_congr
    intro t ht
    have hn : 0 ≤ t := spectrum_nonneg_of_nonneg
      (Matrix.nonneg_iff_posSemidef.mpr σ.posSemidef) ht
    by_cases hz : t = 0
    · simp [g, hz]
    · simp [g, hz, Real.exp_log (lt_of_le_of_ne hn (Ne.symm hz))]
  have hbound (C : ℝ) : vonNeumannEntropy ρ + traceProductLogSigma ρ σ +
      (ρ.toOp * A).trace.re ≤ Real.log ((σ.toOp * NormedSpace.exp A).trace.re +
        Real.exp (-C) * (P * NormedSpace.exp A).trace.re) := by
    have hp := vonNeumannEntropy_add_re_trace_mul_le_log_re_trace_exp ρ (L C + A)
      ((hL C).add hA)
    rw [mul_add, trace_add, Complex.add_re, hpair] at hp
    have hg := golden_thompson_trace_ineq (L C) A (hL C) hA
    have hpos : 0 < (NormedSpace.exp (L C + A)).trace.re := by
      let : Nonempty Q := ρ.nonempty
      rw [← CFC.real_exp_eq_normedSpace_exp ((hL C).add hA).isSelfAdjoint,
        ((hL C).add hA).trace_cfc, Complex.re_sum]
      exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
    have ht := hp.trans (Real.log_le_log hpos hg)
    rw [hexp, add_mul, smul_mul_assoc, trace_add, trace_smul, Complex.add_re] at ht
    simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_assoc] using ht
  have ht : Filter.Tendsto (fun C : ℝ => Real.log ((σ.toOp * NormedSpace.exp A).trace.re +
      Real.exp (-C) * (P * NormedSpace.exp A).trace.re)) Filter.atTop
      (nhds (Real.log (σ.toOp * NormedSpace.exp A).trace.re)) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.mul_const (P * NormedSpace.exp A).trace.re
    have h' := h.const_add (σ.toOp * NormedSpace.exp A).trace.re
    simp only [zero_mul, add_zero] at h'
    exact (Real.continuousAt_log (ne_of_gt (trace_mul_exp_pos σ A hA))).tendsto.comp h'
  have h := ge_of_tendsto' ht hbound
  dsimp [relativeEntropyReal]
  linarith
end InfoTheory.RelativeEntropy
