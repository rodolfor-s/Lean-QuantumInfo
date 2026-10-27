import Batteries.Tactic.OpenPrivate
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.Defs
import QCryptLean.InfoTheory.Renyi.PetzConditional

/-!
# Nussbaum–Szkoła spectral weights

Eigenvector overlaps reduce logarithmic trace expressions and Petz traces to finite weighted
sums of log-likelihood ratios.

## Main declarations

The private spectral weights and trace identities express relative entropy, its variance,
and exponential moments as classical sums.

## References

See the cited results in the declaration docstrings.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace InfoTheory.Renyi

private local instance (m : Type*) [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}


open private one_le_sum_mul_exp_of_sum_mul_eq_zero
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments


/-! ### The Nussbaum–Szkoła identity -/

section NS

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The Nussbaum–Szkoła overlap `c x y = |⟨e_x | f_y⟩|²`. -/
private def nsOverlap {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (x y : m) : ℝ :=
  Complex.normSq ((star (hρ.eigenvectorUnitary : Matrix m m ℂ)
    * (hσ.eigenvectorUnitary : Matrix m m ℂ)) x y)

private lemma nsOverlap_nonneg {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (x y : m) : 0 ≤ nsOverlap hρ hσ x y := Complex.normSq_nonneg _

/-- **The Nussbaum–Szkoła spectral identity** (DF `:770`–`:774`). -/
private lemma trace_cfc_mul_cfc_eq_ns {ρ σ : Matrix m m ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f ρ * cfc g σ).trace
      = ((∑ x : m, ∑ y : m,
          f (hρ.eigenvalues x) * g (hσ.eigenvalues y) * nsOverlap hρ hσ x y : ℝ) : ℂ) := by
  classical
  rw [hρ.cfc_eq, hσ.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  set U : Matrix m m ℂ := (hρ.eigenvectorUnitary : Matrix m m ℂ) with hUdef
  set W : Matrix m m ℂ := (hσ.eigenvectorUnitary : Matrix m m ℂ) with hWdef
  set Df : Matrix m m ℂ := diagonal (RCLike.ofReal ∘ f ∘ hρ.eigenvalues) with hDf
  set Dg : Matrix m m ℂ := diagonal (RCLike.ofReal ∘ g ∘ hσ.eigenvalues) with hDg
  set M : Matrix m m ℂ := star U * W with hMdef
  have hcyc : (U * Df * star U * (W * Dg * star W)).trace
      = (Df * M * Dg * star M).trace := by
    rw [hMdef, StarMul.star_mul, star_star]
    simp only [mul_assoc]
    rw [Matrix.trace_mul_comm U]
    simp only [mul_assoc]
  rw [hcyc]
  have hrow : ∀ x y : m, (Df * M * Dg) x y
      = ((f (hρ.eigenvalues x) : ℝ) : ℂ) * M x y * ((g (hσ.eigenvalues y) : ℝ) : ℂ) := by
    intro x y
    rw [hDg, Matrix.mul_diagonal, hDf, Matrix.diagonal_mul]
    simp [Function.comp_def]
  rw [Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hrow x y, Matrix.star_apply, RCLike.star_def,
    show ((f (hρ.eigenvalues x) : ℝ) : ℂ) * M x y * ((g (hσ.eigenvalues y) : ℝ) : ℂ)
        * (starRingEnd ℂ) (M x y)
      = ((f (hρ.eigenvalues x) : ℝ) : ℂ) * ((g (hσ.eigenvalues y) : ℝ) : ℂ)
        * (M x y * (starRingEnd ℂ) (M x y)) from by ring, Complex.mul_conj]
  push_cast [nsOverlap, hMdef]
  ring

private lemma contOn_spec' (f : ℝ → ℝ) (a : Matrix m m ℂ) : ContinuousOn f (spectrum ℝ a) :=
  (Matrix.finite_real_spectrum (A := a)).continuousOn f

private lemma cfc_one_eq {a : Matrix m m ℂ} (ha : a.IsHermitian) :
    cfc (fun _ : ℝ => (1 : ℝ)) a = 1 := by
  rw [cfc_const (1 : ℝ) a ha.isSelfAdjoint]; simp

private lemma cfc_id_mul_log (a : Matrix m m ℂ) (ha : a.IsHermitian) :
    cfc (fun t : ℝ => t * Real.log t) a = a * CFC.log a := by
  rw [cfc_mul (fun t : ℝ => t) Real.log a (contOn_spec' _ a) (contOn_spec' _ a),
    cfc_id' ℝ a ha.isSelfAdjoint]
  rfl

private lemma cfc_id_mul_log_mul_log (a : Matrix m m ℂ) (ha : a.IsHermitian) :
    cfc (fun t : ℝ => t * Real.log t * Real.log t) a = a * CFC.log a * CFC.log a := by
  rw [cfc_mul (fun t : ℝ => t * Real.log t) Real.log a (contOn_spec' _ a) (contOn_spec' _ a),
    cfc_id_mul_log a ha]
  rfl

private lemma cfc_log_mul_log (a : Matrix m m ℂ) :
    cfc (fun t : ℝ => Real.log t * Real.log t) a = CFC.log a * CFC.log a := by
  rw [cfc_mul Real.log Real.log a (contOn_spec' _ a) (contOn_spec' _ a)]
  rfl

private lemma ns_trace_rho {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ρ.trace.re = ∑ x : m, ∑ y : m, hρ.eigenvalues x * nsOverlap hρ hσ x y := by
  have h := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t) (fun _ : ℝ => (1 : ℝ))
  rw [cfc_id' ℝ ρ hρ.isSelfAdjoint, cfc_one_eq hσ, mul_one] at h
  rw [h, Complex.ofReal_re]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

private lemma ns_trace_sigma {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    σ.trace.re = ∑ x : m, ∑ y : m, hσ.eigenvalues y * nsOverlap hρ hσ x y := by
  have h := trace_cfc_mul_cfc_eq_ns hρ hσ (fun _ : ℝ => (1 : ℝ)) (fun t : ℝ => t)
  rw [cfc_id' ℝ σ hσ.isSelfAdjoint, cfc_one_eq hρ, one_mul] at h
  rw [h, Complex.ofReal_re]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

private lemma ns_petzTrace {ρ σ : Matrix m m ℂ} (hρ0 : 0 ≤ ρ) (hσ0 : 0 ≤ σ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (a : ℝ) :
    petzTrace a ρ σ
      = ∑ x : m, ∑ y : m,
          hρ.eigenvalues x ^ a * hσ.eigenvalues y ^ (1 - a) * nsOverlap hρ hσ x y := by
  have h := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t ^ a) (fun t : ℝ => t ^ (1 - a))
  rw [← CFC.rpow_eq_cfc_real hρ0, ← CFC.rpow_eq_cfc_real hσ0] at h
  rw [petzTrace, h, Complex.ofReal_re]

private lemma log_eq_cfc' (a : Matrix m m ℂ) : CFC.log a = cfc Real.log a := rfl

private lemma ns_trace_relEnt {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (ρ * (CFC.log ρ - CFC.log σ)).trace.re
      = ∑ x : m, ∑ y : m, hρ.eigenvalues x
          * (Real.log (hρ.eigenvalues x) - Real.log (hσ.eigenvalues y))
          * nsOverlap hρ hσ x y := by
  have h1 := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t * Real.log t) (fun _ : ℝ => (1 : ℝ))
  rw [cfc_id_mul_log ρ hρ, cfc_one_eq hσ, mul_one] at h1
  have h2 := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t) Real.log
  rw [cfc_id' ℝ ρ hρ.isSelfAdjoint, ← log_eq_cfc' σ] at h2
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re, h1, h2, Complex.ofReal_re, Complex.ofReal_re,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

private lemma ns_trace_relEntSq {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (ρ * (CFC.log ρ - CFC.log σ) ^ 2).trace.re
      = ∑ x : m, ∑ y : m, hρ.eigenvalues x
          * (Real.log (hρ.eigenvalues x) - Real.log (hσ.eigenvalues y)) ^ 2
          * nsOverlap hρ hσ x y := by
  have hcomm : CFC.log ρ * ρ = ρ * CFC.log ρ := by
    have h1 : cfc (fun t : ℝ => Real.log t * t) ρ = CFC.log ρ * ρ := by
      rw [cfc_mul Real.log (fun t : ℝ => t) ρ (contOn_spec' _ ρ) (contOn_spec' _ ρ),
        cfc_id' ℝ ρ hρ.isSelfAdjoint]
      rfl
    have hfun : (fun t : ℝ => Real.log t * t) = (fun t : ℝ => t * Real.log t) := by
      funext t; ring
    rw [← h1, hfun, cfc_id_mul_log ρ hρ]
  have h1 := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t * Real.log t * Real.log t)
    (fun _ : ℝ => (1 : ℝ))
  rw [cfc_id_mul_log_mul_log ρ hρ, cfc_one_eq hσ, mul_one] at h1
  have h2 := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t * Real.log t) Real.log
  rw [cfc_id_mul_log ρ hρ, ← log_eq_cfc' σ] at h2
  have h4 := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t)
    (fun t : ℝ => Real.log t * Real.log t)
  rw [cfc_id' ℝ ρ hρ.isSelfAdjoint, cfc_log_mul_log σ] at h4
  have h3 : (ρ * (CFC.log σ * CFC.log ρ)).trace = (ρ * CFC.log ρ * CFC.log σ).trace := by
    rw [← mul_assoc, Matrix.trace_mul_comm (ρ * CFC.log σ) (CFC.log ρ), ← mul_assoc, hcomm]
  have hexp : ρ * (CFC.log ρ - CFC.log σ) ^ 2
      = ρ * CFC.log ρ * CFC.log ρ - ρ * CFC.log ρ * CFC.log σ
        - (ρ * (CFC.log σ * CFC.log ρ) - ρ * (CFC.log σ * CFC.log σ)) := by
    rw [pow_two]; noncomm_ring
  rw [hexp, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, h3, h1, h2, h4,
    Complex.sub_re, Complex.sub_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re,
    Complex.ofReal_re, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

private lemma ns_eigenvalues_nonneg {ρ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hρ0 : 0 ≤ ρ)
    (x : m) : 0 ≤ hρ.eigenvalues x :=
  (Matrix.nonneg_iff_posSemidef.mp hρ0).eigenvalues_nonneg x

/-- The support condition, lifted to the NS pair: if `μ y = 0` then the whole `y`-column of
the NS weight `λ x · c x y` vanishes. -/
private lemma ns_support {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ0 : 0 ≤ ρ) (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0)
    {y : m} (hy : hσ.eigenvalues y = 0) (x : m) :
    hρ.eigenvalues x * nsOverlap hρ hσ x y = 0 := by
  classical
  set g : ℝ → ℝ := fun t => if t = 0 then (1 : ℝ) else 0 with hg
  set P : Matrix m m ℂ := cfc g σ with hP
  have hσP : σ * P = 0 := by
    have hmul : cfc (fun t : ℝ => t * g t) σ = σ * P := by
      rw [cfc_mul (fun t : ℝ => t) g σ (contOn_spec' _ σ) (contOn_spec' _ σ),
        cfc_id' ℝ σ hσ.isSelfAdjoint]
    rw [← hmul]
    have hfun : (fun t : ℝ => t * g t) = fun _ : ℝ => (0 : ℝ) := by
      funext t; by_cases h : t = 0 <;> simp [hg, h]
    rw [hfun, cfc_const (0 : ℝ) σ hσ.isSelfAdjoint, map_zero]
  have hcol : ∀ j : m, σ.mulVec (fun k => P k j) = 0 := by
    intro j
    funext i
    have h0 : (σ * P) i j = 0 := by rw [hσP]; simp
    rw [Matrix.mul_apply] at h0
    simpa [Matrix.mulVec, dotProduct] using h0
  have hρP : ρ * P = 0 := by
    ext i j
    have h1 := hsupp _ (hcol j)
    have h2 : ρ.mulVec (fun k => P k j) i = 0 := by rw [h1]; rfl
    rw [Matrix.mulVec, dotProduct] at h2
    simpa [Matrix.mul_apply] using h2
  have htr : (ρ * P).trace = 0 := by rw [hρP, Matrix.trace_zero]
  have hns := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t) g
  rw [cfc_id' ℝ ρ hρ.isSelfAdjoint, ← hP, htr] at hns
  have hsum : (∑ x : m, ∑ y : m,
      hρ.eigenvalues x * g (hσ.eigenvalues y) * nsOverlap hρ hσ x y) = 0 := by
    exact_mod_cast hns.symm
  have hnn : ∀ x' : m, 0 ≤ ∑ y' : m,
      hρ.eigenvalues x' * g (hσ.eigenvalues y') * nsOverlap hρ hσ x' y' := by
    intro x'
    refine Finset.sum_nonneg fun y' _ => ?_
    have h1 : 0 ≤ g (hσ.eigenvalues y') := by
      by_cases h : hσ.eigenvalues y' = 0 <;> simp [hg, h]
    exact mul_nonneg (mul_nonneg (ns_eigenvalues_nonneg hρ hρ0 x') h1)
      (nsOverlap_nonneg hρ hσ x' y')
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg fun x' _ => hnn x').mp hsum x (Finset.mem_univ x)
  have hcell := (Finset.sum_eq_zero_iff_of_nonneg fun y' _ => by
      have h1 : 0 ≤ g (hσ.eigenvalues y') := by
        by_cases h : hσ.eigenvalues y' = 0 <;> simp [hg, h]
      exact mul_nonneg (mul_nonneg (ns_eigenvalues_nonneg hρ hρ0 x) h1)
        (nsOverlap_nonneg hρ hσ x y')).mp hrow y (Finset.mem_univ y)
  simpa [hg, hy] using hcell

end NS

/-! ### The classical core -/
/-! ### The `(w, ℓ)` reduction -/

section NSWeights

variable {m : Type*} [Fintype m] [DecidableEq m]

private def nsW {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (p : m × m) : ℝ :=
  hρ.eigenvalues p.1 * nsOverlap hρ hσ p.1 p.2

private def nsL {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (p : m × m) : ℝ :=
  Real.log (hρ.eigenvalues p.1) - Real.log (hσ.eigenvalues p.2)

private lemma nsW_nonneg {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ0 : 0 ≤ ρ) (p : m × m) : 0 ≤ nsW hρ hσ p :=
  mul_nonneg (ns_eigenvalues_nonneg hρ hρ0 p.1) (nsOverlap_nonneg hρ hσ p.1 p.2)

private lemma nsW_sum {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ∑ p : m × m, nsW hρ hσ p = ρ.trace.re := by
  rw [ns_trace_rho hρ hσ, Fintype.sum_prod_type]
  rfl

private lemma nsWL_sum {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ∑ p : m × m, nsW hρ hσ p * nsL hρ hσ p
      = (ρ * (CFC.log ρ - CFC.log σ)).trace.re := by
  rw [ns_trace_relEnt hρ hσ, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    simp only [nsW, nsL]; ring

private lemma nsWL2_sum {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ∑ p : m × m, nsW hρ hσ p * (nsL hρ hσ p) ^ 2
      = (ρ * (CFC.log ρ - CFC.log σ) ^ 2).trace.re := by
  rw [ns_trace_relEntSq hρ hσ, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    simp only [nsW, nsL]; ring

/-- The `petzTrace` at every positive order, in `(w, ℓ)` form. This is where `hsupp` enters. -/
private lemma nsW_exp_sum {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ0 : 0 ≤ ρ) (hσ0 : 0 ≤ σ) (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0)
    {a : ℝ} (ha : 0 < a) :
    ∑ p : m × m, nsW hρ hσ p * Real.exp ((a - 1) * nsL hρ hσ p) = petzTrace a ρ σ := by
  rw [ns_petzTrace hρ0 hσ0 hρ hσ a, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [nsW, nsL]
  by_cases hc : nsOverlap hρ hσ x y = 0
  · rw [hc]; ring
  rcases eq_or_lt_of_le (ns_eigenvalues_nonneg hρ hρ0 x) with hlam | hlam
  · rw [← hlam, Real.zero_rpow (ne_of_gt ha)]; ring
  have hmu : 0 < hσ.eigenvalues y := by
    rcases eq_or_lt_of_le (ns_eigenvalues_nonneg hσ hσ0 y) with hm | hm
    · exfalso
      rcases mul_eq_zero.mp (ns_support hρ hσ hρ0 hsupp hm.symm x) with h | h
      · linarith
      · exact hc h
    · exact hm
  obtain ⟨L, hL⟩ : ∃ L : ℝ, hρ.eigenvalues x = Real.exp L :=
    ⟨Real.log (hρ.eigenvalues x), (Real.exp_log hlam).symm⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, hσ.eigenvalues y = Real.exp N :=
    ⟨Real.log (hσ.eigenvalues y), (Real.exp_log hmu).symm⟩
  rw [hL, hN, Real.log_exp, Real.log_exp,
    Real.rpow_def_of_pos (Real.exp_pos L), Real.rpow_def_of_pos (Real.exp_pos N),
    Real.log_exp, Real.log_exp, ← Real.exp_add]
  rw [show Real.exp L * nsOverlap hρ hσ x y * Real.exp ((a - 1) * (L - N))
      = Real.exp (L + (a - 1) * (L - N)) * nsOverlap hρ hσ x y from by
        rw [Real.exp_add]; ring]
  congr 2
  ring

/-- The `ν = 1` endpoint of the reference sum: `∑ w e^{−ℓ} ≤ Tr σ`. -/
private lemma nsW_exp_neg_le {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ0 : 0 ≤ ρ) (hσ0 : 0 ≤ σ) (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) :
    ∑ p : m × m, nsW hρ hσ p * Real.exp (-(nsL hρ hσ p)) ≤ σ.trace.re := by
  rw [ns_trace_sigma hρ hσ, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  simp only [nsW, nsL]
  by_cases hc : nsOverlap hρ hσ x y = 0
  · rw [hc]; simp
  rcases eq_or_lt_of_le (ns_eigenvalues_nonneg hρ hρ0 x) with hlam | hlam
  · rw [← hlam]
    simp only [zero_mul]
    exact mul_nonneg (ns_eigenvalues_nonneg hσ hσ0 y) (nsOverlap_nonneg hρ hσ x y)
  have hmu : 0 < hσ.eigenvalues y := by
    rcases eq_or_lt_of_le (ns_eigenvalues_nonneg hσ hσ0 y) with hm | hm
    · exfalso
      rcases mul_eq_zero.mp (ns_support hρ hσ hρ0 hsupp hm.symm x) with h | h
      · linarith
      · exact hc h
    · exact hm
  obtain ⟨L, hL⟩ : ∃ L : ℝ, hρ.eigenvalues x = Real.exp L :=
    ⟨Real.log (hρ.eigenvalues x), (Real.exp_log hlam).symm⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, hσ.eigenvalues y = Real.exp N :=
    ⟨Real.log (hσ.eigenvalues y), (Real.exp_log hmu).symm⟩
  rw [hL, hN, Real.log_exp, Real.log_exp,
    show Real.exp L * nsOverlap hρ hσ x y * Real.exp (-(L - N))
      = Real.exp (L + -(L - N)) * nsOverlap hρ hσ x y from by rw [Real.exp_add]; ring,
    show L + -(L - N) = N from by ring]

private lemma nsRef_sum {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ∑ p : m × m, hσ.eigenvalues p.2 * nsOverlap hρ hσ p.1 p.2 = σ.trace.re := by
  rw [ns_trace_sigma hρ hσ, Fintype.sum_prod_type]

private def nsD {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) : ℝ :=
  ∑ p : m × m, nsW hρ hσ p * nsL hρ hσ p

private lemma ns_sum_one {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hnorm : ρ.trace.re = 1) : ∑ p : m × m, nsW hρ hσ p = 1 := by
  rw [nsW_sum hρ hσ, hnorm]

private lemma ns_relEnt_eq {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hnorm : ρ.trace.re = 1) :
    relativeEntropyBits ρ σ = nsD hρ hσ / Real.log 2 := by
  rw [relativeEntropyBits, hnorm, one_mul, nsD, nsWL_sum hρ hσ]

private lemma ns_Y_sum {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hnorm : ρ.trace.re = 1) :
    ∑ p : m × m, nsW hρ hσ p * (nsL hρ hσ p - nsD hρ hσ) = 0 := by
  have hterm : ∀ p : m × m, nsW hρ hσ p * (nsL hρ hσ p - nsD hρ hσ)
      = nsW hρ hσ p * nsL hρ hσ p - nsD hρ hσ * nsW hρ hσ p := fun p => by ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ns_sum_one hρ hσ hnorm, mul_one, ← nsD]
  ring

private lemma ns_divVar_eq {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hnorm : ρ.trace.re = 1) :
    petzDivergenceVariance ρ σ
      = (∑ p : m × m, nsW hρ hσ p * (nsL hρ hσ p - nsD hρ hσ) ^ 2) / (Real.log 2) ^ 2 := by
  have hexp : ∀ p : m × m, nsW hρ hσ p * (nsL hρ hσ p - nsD hρ hσ) ^ 2
      = nsW hρ hσ p * (nsL hρ hσ p) ^ 2
        - 2 * nsD hρ hσ * (nsW hρ hσ p * nsL hρ hσ p)
        + (nsD hρ hσ) ^ 2 * nsW hρ hσ p := fun p => by ring
  rw [Finset.sum_congr rfl (fun p _ => hexp p), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ns_sum_one hρ hσ hnorm, mul_one, ← nsD,
    nsWL2_sum hρ hσ, petzDivergenceVariance, hnorm, one_mul,
    ns_relEnt_eq hρ hσ hnorm]
  have hl2 : Real.log 2 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  field_simp
  ring

private lemma ns_M_eq {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ0 : 0 ≤ ρ) (hσ0 : 0 ≤ σ) (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0)
    {s : ℝ} (hs : 0 < 1 + s) :
    ∑ p : m × m, nsW hρ hσ p * Real.exp (s * (nsL hρ hσ p - nsD hρ hσ))
      = Real.exp (-(s * nsD hρ hσ)) * petzTrace (1 + s) ρ σ := by
  have hterm : ∀ p : m × m, nsW hρ hσ p * Real.exp (s * (nsL hρ hσ p - nsD hρ hσ))
      = Real.exp (-(s * nsD hρ hσ))
        * (nsW hρ hσ p * Real.exp ((1 + s - 1) * nsL hρ hσ p)) := by
    intro p
    rw [show (1 : ℝ) + s - 1 = s from by ring,
      show Real.exp (-(s * nsD hρ hσ)) * (nsW hρ hσ p * Real.exp (s * nsL hρ hσ p))
        = nsW hρ hσ p * (Real.exp (-(s * nsD hρ hσ)) * Real.exp (s * nsL hρ hσ p)) from by ring,
      ← Real.exp_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.mul_sum,
    nsW_exp_sum hρ hσ hρ0 hσ0 hsupp hs]

private lemma two_rpow_relEnt {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hnorm : ρ.trace.re = 1) (t : ℝ) :
    (2 : ℝ) ^ (t * relativeEntropyBits ρ σ) = Real.exp (t * nsD hρ hσ) := by
  have hl2 : Real.log 2 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  rw [ns_relEnt_eq hρ hσ hnorm, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  congr 1
  field_simp

/-- `2^{(β−1)(D'_β − D)} = M(β−1)`, the identity that turns `petzContinuityK` into the
classical remainder. -/
private lemma ns_two_rpow_eq {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ0 : 0 ≤ ρ) (hσ0 : 0 ≤ σ) (hnorm : ρ.trace.re = 1)
    (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) {β : ℝ} (hβ : 1 < β) :
    (2 : ℝ) ^ ((β - 1) * (petzRenyiDivergence β ρ σ - relativeEntropyBits ρ σ))
      = ∑ p : m × m, nsW hρ hσ p * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ)) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hβ1 : (0 : ℝ) < β - 1 := by linarith
  have hMv := ns_M_eq hρ hσ hρ0 hσ0 hsupp (s := β - 1) (by linarith)
  rw [show (1 : ℝ) + (β - 1) = β from by ring] at hMv
  have hM1 := one_le_sum_mul_exp_of_sum_mul_eq_zero (nsW hρ hσ) (fun p => nsL hρ hσ p - nsD hρ hσ)
    (fun p => nsW_nonneg hρ hσ hρ0 p) (ns_sum_one hρ hσ hnorm) (ns_Y_sum hρ hσ hnorm) (β - 1)
  have hMpos : (0 : ℝ) < ∑ p : m × m, nsW hρ hσ p
      * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ)) := lt_of_lt_of_le zero_lt_one hM1
  have hpt : petzTrace β ρ σ = Real.exp ((β - 1) * nsD hρ hσ)
      * ∑ p : m × m, nsW hρ hσ p * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ)) := by
    rw [hMv, ← mul_assoc, ← Real.exp_add,
      show (β - 1) * nsD hρ hσ + -((β - 1) * nsD hρ hσ) = 0 from by ring, Real.exp_zero, one_mul]
  have hdiv : petzRenyiDivergence β ρ σ - relativeEntropyBits ρ σ
      = Real.log (∑ p : m × m, nsW hρ hσ p * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ)))
        / ((β - 1) * Real.log 2) := by
    rw [petzRenyiDivergence, hpt, Real.logb,
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hMpos), Real.log_exp,
      ns_relEnt_eq hρ hσ hnorm]
    field_simp
    ring
  rw [hdiv, show (β - 1) * (Real.log (∑ p : m × m, nsW hρ hσ p
        * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ))) / ((β - 1) * Real.log 2))
      = Real.log (∑ p : m × m, nsW hρ hσ p
        * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ))) / Real.log 2 from by
      field_simp,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    show Real.log 2 * (Real.log (∑ p : m × m, nsW hρ hσ p
          * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ))) / Real.log 2)
      = Real.log (∑ p : m × m, nsW hρ hσ p
        * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ))) from by field_simp,
    Real.exp_log hMpos]

end NSWeights

end InfoTheory.Renyi

end
