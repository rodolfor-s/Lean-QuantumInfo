import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDCumulative
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapBasis
import QCryptLean.Quantum.Operators.Algebra

/-! # Spectral Cap Coefficients -/


noncomputable section
namespace InfoTheory.SmoothMinEntropy.SpectralCap
open Matrix Quantum.Operators
open InfoTheory.SmoothMinEntropy.AEP.IID.Cumulative
open scoped ComplexOrder MatrixOrder
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The increment of the capped reference spectrum at one input eigenvalue. -/
def coefficient (σ : PosSemidefOp Q) (p ell : ℝ) (z : Fin (Fintype.card Q)) : ℝ :=
  betaIncr (fun j => min p (ell * eigenvalue σ j)) z

/-- Cap increments are nonnegative. -/
theorem coefficient_nonneg (σ : PosSemidefOp Q) {p ell : ℝ} (hp : 0 ≤ p) (hell : 0 ≤ ell)
    (z : Fin (Fintype.card Q)) : 0 ≤ coefficient σ p ell z :=
  betaIncr_nonneg _ (fun _ _ hij => min_le_min le_rfl
    (mul_le_mul_of_nonneg_left (eigenvalue_monotone σ hij) hell))
    (fun j => le_min hp (mul_nonneg hell (eigenvalue_nonneg σ j))) z

/-- Every cap increment is at most the corresponding scaled reference increment. -/
theorem coefficient_le (σ : PosSemidefOp Q) {p ell : ℝ} (hell : 0 ≤ ell)
    (z : Fin (Fintype.card Q)) :
    coefficient σ p ell z ≤ ell * betaIncr (eigenvalue σ) z := by
  unfold coefficient betaIncr
  rw [lamShift_succ, lamShift_succ]
  rcases Fin.eq_zero_or_eq_succ z.castSucc with h | ⟨w, hw⟩
  · rw [h, lamShift_zero, lamShift_zero, sub_zero, sub_zero]
    exact min_le_right _ _
  · rw [hw, lamShift_succ, lamShift_succ]
    have hle : eigenvalue σ w ≤ eigenvalue σ z := by
      apply eigenvalue_monotone σ
      have hv := congrArg Fin.val hw
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      rw [Fin.le_def]
      omega
    have hm := mul_le_mul_of_nonneg_left hle hell
    by_cases hp : p ≤ ell * eigenvalue σ w
    · rw [min_eq_left hp, min_eq_left (hp.trans hm), sub_self]
      exact mul_nonneg hell (sub_nonneg.mpr hle)
    · rw [min_eq_right (le_of_not_ge hp)]
      have hh := min_le_right p (ell * eigenvalue σ z)
      linarith

/-- Partial cap sums recover the capped reference eigenvalue exactly. -/
theorem partialSum_coefficient (σ : PosSemidefOp Q) (p ell : ℝ)
    (z : Fin (Fintype.card Q)) :
    (∑ j ∈ Finset.univ.filter (fun j => j ≤ z), coefficient σ p ell j) =
      min p (ell * eigenvalue σ z) := sum_betaIncr_filter_le_eq _ z

/-- The total finite cap mass never exceeds the input eigenvalue. -/
theorem sum_coefficient_le (σ : PosSemidefOp Q) {p : ℝ} (hp : 0 ≤ p) (ell : ℝ) :
    ∑ z, coefficient σ p ell z ≤ p := by
  let f : Fin (Fintype.card Q) → ℝ := fun z => min p (ell * eigenvalue σ z)
  have he (z : Fin (Fintype.card Q)) : coefficient σ p ell z =
      lamNat f (z.val + 1) - lamNat f z.val := by
    rw [lamNat_succ, lamNat_castSucc]
    rfl
  rw [Finset.sum_congr rfl (fun z _ => he z),
    Fin.sum_univ_eq_sum_range (fun j => lamNat f (j + 1) - lamNat f j),
    Finset.sum_range_sub, lamNat_zero, sub_zero]
  unfold lamNat
  rw [dite_eq_left (Nat.lt_succ_self _)]
  rcases Fin.eq_zero_or_eq_succ
    (⟨Fintype.card Q, Nat.lt_succ_self _⟩ : Fin (Fintype.card Q + 1)) with h | ⟨w, hw⟩
  · rw [h, lamShift_zero]
    exact hp
  · rw [hw, lamShift_succ]
    exact min_le_left _ _

/-- The reference is the increment-weighted sum of its cumulative projectors. -/
theorem reference_eq_sum_cumulative (σ : PosSemidefOp Q) :
    σ.val = ∑ z, (betaIncr (eigenvalue σ) z : ℂ) • cumulativeProjector σ z := by
  have hs : (∑ z, ∑ j ∈ Finset.univ.filter (fun j => z ≤ j),
        (betaIncr (eigenvalue σ) z : ℂ) • eigenprojector σ j) =
      ∑ j, ∑ z ∈ Finset.univ.filter (fun z => z ≤ j),
        (betaIncr (eigenvalue σ) z : ℂ) • eigenprojector σ j := by
    apply Finset.sum_comm'
    intro z j
    simp [Finset.mem_filter]
  simp only [cumulativeProjector, Finset.smul_sum]
  rw [hs]
  simp only [← Finset.sum_smul, ← Complex.ofReal_sum, sum_betaIncr_filter_le_eq]
  exact (sum_eigenvalue_smul_eigenprojector σ).symm

end InfoTheory.SmoothMinEntropy.SpectralCap
