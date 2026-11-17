import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# Rayleigh quotients against a spectral upper bound, and the equality case

For a Hermitian matrix `A` whose eigenvalues are all at most `lam`, the quadratic form is
bounded by `lam` times the squared norm,

`Re ⟪x, A x⟫ ≤ lam · Re ⟪x, x⟫`,

and — this is the content of the module — a vector that *attains* the bound is an
eigenvector for `lam`:

`Re ⟪x, A x⟫ = lam · Re ⟪x, x⟫ ↔ A x = lam • x`.

Both come from one observation: `lam • 1 - A` is positive semidefinite, and a positive
semidefinite matrix annihilates exactly the null vectors of its quadratic form
(`Matrix.PosSemidef.dotProduct_mulVec_zero_iff`). The bound alone does not identify the
equality case; the min–max bounds of
`Math.LinearAlgebra.SubmoduleDim.eigenvalues₀_le_re_dotProduct_mulVec_of_mem`
and `Math.LinearAlgebra.SubmoduleDim.re_dotProduct_mulVec_le_eigenvalues₀_of_mem` are inequalities
for vectors in prescribed eigenspaces and do
not give it either.

The hypothesis is an arbitrary upper bound `lam` for the spectrum rather than the largest
eigenvalue, which is both more general and basis-free; the largest-eigenvalue bounds are the
specialization `lam = hA.eigenvalues₀ 0` in the second section, and the third section adds
the positive semidefinite power comparison `A ^ m ≤ lam ^ (m-1) • A` with the transfer of
saturation from `A ^ m` back to `A`.

## Main statements

- `Math.SpectralTheory.posSemidef_smul_one_sub` : `lam • 1 - A` is positive semidefinite.
- `Math.SpectralTheory.rayleigh_re_le` : the Rayleigh bound.
- `Math.SpectralTheory.rayleigh_re_eq_iff` : **equality holds exactly at eigenvectors.**
- `Math.SpectralTheory.rayleigh_re_le_top_eigenvalue`,
  `Math.SpectralTheory.mulVec_eq_of_rayleigh_re_eq_top_eigenvalue` : the same at the
  largest eigenvalue `hA.eigenvalues₀ 0`.
- `Math.SpectralTheory.posSemidef_smul_sub_pow` : `A ^ m ≤ lam ^ (m-1) • A` for positive
  semidefinite `A`.
- `Math.SpectralTheory.pow_top_eigenvalue` : `λ_max (A ^ m) = λ_max A ^ m`.
- `Math.SpectralTheory.mulVec_eq_of_pow_rayleigh_re_eq` and
  `Math.SpectralTheory.mulVec_eq_of_pow_rayleigh_re_eq_top_eigenvalue` : a vector
  saturating the bound `lam ^ m` for `A ^ m` is already an eigenvector of `A` for `lam`.

## References

- R. Bhatia, *Matrix Analysis*, Springer (1997), Chapter III (variational principles for
  eigenvalues).
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

noncomputable section

namespace Math.SpectralTheory

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

attribute [local instance] Matrix.instPartialOrder Matrix.instStarOrderedRing
  Matrix.instNonnegSpectrumClass

/-! ### An upper bound for the spectrum -/

/-- Real part of the quadratic form of `lam • 1 - A`. -/
private theorem re_dotProduct_smul_one_sub (A : Matrix n n ℂ) (lam : ℝ) (x : n → ℂ) :
    (star x ⬝ᵥ (((lam : ℂ) • (1 : Matrix n n ℂ) - A) *ᵥ x)).re
      = lam * (star x ⬝ᵥ x).re - (star x ⬝ᵥ (A *ᵥ x)).re := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul]
  simp

/-- **A spectral upper bound is an operator upper bound**: if every eigenvalue of the
Hermitian matrix `A` is at most `lam`, then `lam • 1 - A` is positive semidefinite. -/
theorem posSemidef_smul_one_sub (hA : A.IsHermitian) {lam : ℝ}
    (hle : ∀ i, hA.eigenvalues i ≤ lam) :
    (((lam : ℂ) • (1 : Matrix n n ℂ) - A)).PosSemidef := by
  have hsa : IsSelfAdjoint A := hA
  have hnonneg : 0 ≤ cfc (fun t : ℝ => lam - t) A := by
    refine cfc_nonneg fun t ht => ?_
    rw [hA.spectrum_real_eq_range_eigenvalues] at ht
    obtain ⟨i, rfl⟩ := ht
    exact sub_nonneg.mpr (hle i)
  have hsub : cfc (fun t : ℝ => lam - t) A
      = cfc (fun _ : ℝ => lam) A - cfc (fun t : ℝ => t) A :=
    cfc_sub (fun _ : ℝ => lam) (fun t : ℝ => t) A (by fun_prop) (by fun_prop)
  have hconst : cfc (fun _ : ℝ => lam) A = algebraMap ℝ (Matrix n n ℂ) lam := cfc_const lam A
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A
  have heq : cfc (fun t : ℝ => lam - t) A = (lam : ℂ) • (1 : Matrix n n ℂ) - A := by
    rw [hsub, hconst, hid]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply (R := ℝ) (α := ℂ), hij]
  rw [← heq]
  exact Matrix.nonneg_iff_posSemidef.mp hnonneg

/-- **Rayleigh bound.** If every eigenvalue of the Hermitian matrix `A` is at most `lam`,
then `Re ⟪x, A x⟫ ≤ lam · Re ⟪x, x⟫` for every vector `x`; no normalisation is assumed. -/
theorem rayleigh_re_le (hA : A.IsHermitian) {lam : ℝ} (hle : ∀ i, hA.eigenvalues i ≤ lam)
    (x : n → ℂ) : (star x ⬝ᵥ (A *ᵥ x)).re ≤ lam * (star x ⬝ᵥ x).re := by
  have h := (posSemidef_smul_one_sub hA hle).dotProduct_mulVec_nonneg x
  have h' : (0 : ℝ) ≤ (star x ⬝ᵥ (((lam : ℂ) • (1 : Matrix n n ℂ) - A) *ᵥ x)).re := by
    simpa using (Complex.le_def.mp h).1
  rw [re_dotProduct_smul_one_sub] at h'
  linarith

/-- **The equality case of the Rayleigh bound.** A vector attains `Re ⟪x, A x⟫ = lam ·
Re ⟪x, x⟫` if and only if it is an eigenvector of `A` for the eigenvalue `lam` — the zero
vector included, for which both sides vanish. The bound `rayleigh_re_le` alone does not
determine this. -/
theorem rayleigh_re_eq_iff (hA : A.IsHermitian) {lam : ℝ} (hle : ∀ i, hA.eigenvalues i ≤ lam)
    (x : n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re = lam * (star x ⬝ᵥ x).re ↔ A *ᵥ x = (lam : ℂ) • x := by
  have hB := posSemidef_smul_one_sub hA hle
  have happly : ((lam : ℂ) • (1 : Matrix n n ℂ) - A) *ᵥ x = (lam : ℂ) • x - A *ᵥ x := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · intro hx
    have hzero : star x ⬝ᵥ (((lam : ℂ) • (1 : Matrix n n ℂ) - A) *ᵥ x) = 0 := by
      refine Complex.ext ?_ ?_
      · rw [re_dotProduct_smul_one_sub, hx]
        simp
      · exact (Complex.nonneg_iff.mp (hB.dotProduct_mulVec_nonneg x)).2.symm
    have := hB.dotProduct_mulVec_zero_iff.mp hzero
    rw [happly] at this
    exact (sub_eq_zero.mp this).symm
  · intro hx
    rw [hx, dotProduct_smul, smul_eq_mul]
    simp

/-- **Rayleigh saturation forces an eigenvector**, the forward direction of
`rayleigh_re_eq_iff`. -/
theorem mulVec_eq_of_rayleigh_re_eq (hA : A.IsHermitian) {lam : ℝ}
    (hle : ∀ i, hA.eigenvalues i ≤ lam) {x : n → ℂ}
    (hx : (star x ⬝ᵥ (A *ᵥ x)).re = lam * (star x ⬝ᵥ x).re) : A *ᵥ x = (lam : ℂ) • x :=
  (rayleigh_re_eq_iff hA hle x).mp hx

/-! ### The largest eigenvalue -/

section Top

variable [Nonempty n]

/-- Every eigenvalue is bounded by the top entry of the antitone listing `eigenvalues₀`. -/
theorem eigenvalues_le_top_eigenvalue (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i ≤ hA.eigenvalues₀ 0 := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (by simp)
  have hzero : (0 : Fin (Fintype.card n)) ≤ e.symm i := by
    simp
  simpa [Matrix.IsHermitian.eigenvalues, e] using hA.eigenvalues₀_antitone hzero

/-- The largest eigenvalue belongs to the complex spectrum. -/
theorem top_eigenvalue_mem_spectrum (hA : A.IsHermitian) :
    ((hA.eigenvalues₀ 0 : ℝ) : ℂ) ∈ spectrum ℂ A := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (by simp)
  rw [hA.spectrum_eq_image_range]
  refine ⟨hA.eigenvalues (e 0), ⟨e 0, rfl⟩, ?_⟩
  have hrel : hA.eigenvalues (e 0) = hA.eigenvalues₀ 0 := by
    simp [Matrix.IsHermitian.eigenvalues, e]
  simp [hrel]

/-- `λ_max • 1 - A` is positive semidefinite. -/
theorem posSemidef_top_eigenvalue_smul_one_sub (hA : A.IsHermitian) :
    (((hA.eigenvalues₀ 0 : ℝ) : ℂ) • (1 : Matrix n n ℂ) - A).PosSemidef :=
  posSemidef_smul_one_sub hA (eigenvalues_le_top_eigenvalue hA)

/-- The Rayleigh quotient is bounded by the largest eigenvalue. -/
theorem rayleigh_re_le_top_eigenvalue (hA : A.IsHermitian) (x : n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re ≤ hA.eigenvalues₀ 0 * (star x ⬝ᵥ x).re :=
  rayleigh_re_le hA (eigenvalues_le_top_eigenvalue hA) x

/-- **A vector attaining the largest eigenvalue as its Rayleigh quotient is a top
eigenvector.** -/
theorem mulVec_eq_of_rayleigh_re_eq_top_eigenvalue (hA : A.IsHermitian) {x : n → ℂ}
    (hx : (star x ⬝ᵥ (A *ᵥ x)).re = hA.eigenvalues₀ 0 * (star x ⬝ᵥ x).re) :
    A *ᵥ x = ((hA.eigenvalues₀ 0 : ℝ) : ℂ) • x :=
  mulVec_eq_of_rayleigh_re_eq hA (eigenvalues_le_top_eigenvalue hA) hx

end Top

/-! ### Powers of a positive semidefinite matrix -/

/-- A positive semidefinite matrix whose eigenvalues are all nonpositive is zero. -/
theorem eq_zero_of_eigenvalues_nonpos (hA : A.PosSemidef) (hle : ∀ i, hA.1.eigenvalues i ≤ 0) :
    A = 0 :=
  hA.1.eigenvalues_eq_zero_iff.mp
    (funext fun i => le_antisymm (hle i) (hA.eigenvalues_nonneg i))

/-- **The power gap.** For positive semidefinite `A` with spectrum below `lam` and `1 ≤ m`,
`A ^ m ≤ lam ^ (m-1) • A`: on the spectrum, `t ^ m = t ^ (m-1) · t ≤ lam ^ (m-1) · t`. -/
theorem posSemidef_smul_sub_pow (hA : A.PosSemidef) {lam : ℝ}
    (hle : ∀ i, hA.1.eigenvalues i ≤ lam) {m : ℕ} (hm : 1 ≤ m) :
    ((lam ^ (m - 1)) • A - A ^ m).PosSemidef := by
  have hsa : IsSelfAdjoint A := hA.1
  have hnonneg : 0 ≤ cfc (fun t : ℝ => lam ^ (m - 1) * t - t ^ m) A := by
    refine cfc_nonneg fun t ht => ?_
    rw [hA.1.spectrum_real_eq_range_eigenvalues] at ht
    obtain ⟨i, rfl⟩ := ht
    have h0 : 0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg i
    have hpow : (hA.1.eigenvalues i) ^ (m - 1) ≤ lam ^ (m - 1) :=
      pow_le_pow_left₀ h0 (hle i) (m - 1)
    have hsplit : (hA.1.eigenvalues i) ^ m = (hA.1.eigenvalues i) ^ (m - 1) *
        hA.1.eigenvalues i := by
      nth_rewrite 1 [show m = (m - 1) + 1 from (Nat.succ_pred_eq_of_pos hm).symm]
      rw [pow_succ]
    rw [hsplit]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right hpow h0)
  have hsub : cfc (fun t : ℝ => lam ^ (m - 1) * t - t ^ m) A
      = cfc (fun t : ℝ => lam ^ (m - 1) * t) A - cfc (fun t : ℝ => t ^ m) A :=
    cfc_sub (fun t : ℝ => lam ^ (m - 1) * t) (fun t : ℝ => t ^ m) A (by fun_prop) (by fun_prop)
  have hlin : cfc (fun t : ℝ => lam ^ (m - 1) * t) A = (lam ^ (m - 1)) • A :=
    cfc_const_mul_id (lam ^ (m - 1)) A
  have hpow : cfc (fun t : ℝ => t ^ m) A = A ^ m := cfc_pow_id A m
  have heq : cfc (fun t : ℝ => lam ^ (m - 1) * t - t ^ m) A = (lam ^ (m - 1)) • A - A ^ m := by
    rw [hsub, hlin, hpow]
  rw [← heq]
  exact Matrix.nonneg_iff_posSemidef.mp hnonneg

/-- **Saturation transfers from a power back to the matrix.** If `x` attains the bound
`lam ^ m` for `A ^ m`, then it already attains `lam` for `A`. -/
theorem rayleigh_re_eq_of_pow (hA : A.PosSemidef) {lam : ℝ} (hlam : 0 ≤ lam)
    (hle : ∀ i, hA.1.eigenvalues i ≤ lam) {m : ℕ} (hm : 1 ≤ m) {x : n → ℂ}
    (hx : (star x ⬝ᵥ ((A ^ m) *ᵥ x)).re = lam ^ m * (star x ⬝ᵥ x).re) :
    (star x ⬝ᵥ (A *ᵥ x)).re = lam * (star x ⬝ᵥ x).re := by
  rcases eq_or_lt_of_le hlam with hzero | hlam
  · -- `lam = 0` forces `A = 0` and both sides vanish.
    have hA0 : A = 0 := eq_zero_of_eigenvalues_nonpos hA (fun i => hzero ▸ hle i)
    rw [hA0, ← hzero]
    simp
  have hgap := (posSemidef_smul_sub_pow hA hle hm).dotProduct_mulVec_nonneg x
  have hgap' : (0 : ℝ) ≤ (star x ⬝ᵥ (((lam ^ (m - 1)) • A - A ^ m) *ᵥ x)).re := by
    simpa using (Complex.le_def.mp hgap).1
  have hexp : (star x ⬝ᵥ (((lam ^ (m - 1)) • A - A ^ m) *ᵥ x)).re
      = lam ^ (m - 1) * (star x ⬝ᵥ (A *ᵥ x)).re - (star x ⬝ᵥ ((A ^ m) *ᵥ x)).re := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, Complex.sub_re,
      Complex.smul_re, smul_eq_mul]
  rw [hexp, hx] at hgap'
  have hsplit : lam ^ m = lam ^ (m - 1) * lam := by
    nth_rewrite 1 [show m = (m - 1) + 1 from (Nat.succ_pred_eq_of_pos hm).symm]
    rw [pow_succ]
  have hpow_pos : 0 < lam ^ (m - 1) := pow_pos hlam _
  have hge : lam * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (A *ᵥ x)).re := by
    rw [hsplit] at hgap'
    nlinarith [hgap', hpow_pos]
  exact le_antisymm (rayleigh_re_le hA.1 hle x) hge

/-- **A vector saturating the bound for a power is an eigenvector of the matrix itself.** -/
theorem mulVec_eq_of_pow_rayleigh_re_eq (hA : A.PosSemidef) {lam : ℝ} (hlam : 0 ≤ lam)
    (hle : ∀ i, hA.1.eigenvalues i ≤ lam) {m : ℕ} (hm : 1 ≤ m) {x : n → ℂ}
    (hx : (star x ⬝ᵥ ((A ^ m) *ᵥ x)).re = lam ^ m * (star x ⬝ᵥ x).re) :
    A *ᵥ x = (lam : ℂ) • x :=
  mulVec_eq_of_rayleigh_re_eq hA.1 hle (rayleigh_re_eq_of_pow hA hlam hle hm hx)

/-- **The largest eigenvalue of a power.** For positive semidefinite `A`,
`λ_max (A ^ m) = λ_max A ^ m`. The upper bound is the power gap tested against a top
eigenvector of `A ^ m`; the lower bound is the spectral mapping theorem. -/
theorem pow_top_eigenvalue [Nonempty n] (hA : A.PosSemidef) (m : ℕ) :
    (hA.1.pow m).eigenvalues₀ 0 = (hA.1.eigenvalues₀ 0) ^ m := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (by simp)
  have hB := hA.1.pow m
  have hspec : (spectrum ℂ A).Nonempty := ⟨_, top_eigenvalue_mem_spectrum hA.1⟩
  have hupper : hB.eigenvalues₀ 0 ≤ (hA.1.eigenvalues₀ 0) ^ m := by
    have hmem : ((hB.eigenvalues₀ 0 : ℝ) : ℂ) ∈ spectrum ℂ (A ^ m) := by
      simpa using top_eigenvalue_mem_spectrum hB
    rw [spectrum.map_pow_of_nonempty hspec m] at hmem
    obtain ⟨z, hz, hzpow⟩ := hmem
    rw [hA.1.spectrum_eq_image_range] at hz
    obtain ⟨r, ⟨i, hi⟩, hzr⟩ := hz
    have heq : hB.eigenvalues₀ 0 = (hA.1.eigenvalues i) ^ m := by
      refine Complex.ofReal_injective ?_
      calc ((hB.eigenvalues₀ 0 : ℝ) : ℂ)
          = z ^ m := hzpow.symm
        _ = ((hA.1.eigenvalues i : ℝ) : ℂ) ^ m := by
            rw [← hzr, hi]
            rfl
        _ = (((hA.1.eigenvalues i) ^ m : ℝ) : ℂ) := by norm_num
    rw [heq]
    exact pow_le_pow_left₀ (hA.eigenvalues_nonneg i)
      (eigenvalues_le_top_eigenvalue hA.1 i) m
  have hlower : (hA.1.eigenvalues₀ 0) ^ m ≤ hB.eigenvalues₀ 0 := by
    have hmem := spectrum.pow_mem_pow (𝕜 := ℂ) A m (top_eigenvalue_mem_spectrum hA.1)
    rw [hB.spectrum_eq_image_range] at hmem
    obtain ⟨r, ⟨i, hi⟩, hr⟩ := hmem
    have heq : (hA.1.eigenvalues₀ 0) ^ m = hB.eigenvalues i := by
      refine Complex.ofReal_injective ?_
      calc (((hA.1.eigenvalues₀ 0) ^ m : ℝ) : ℂ)
          = ((hA.1.eigenvalues₀ 0 : ℝ) : ℂ) ^ m := by norm_num
        _ = (r : ℂ) := hr.symm
        _ = ((hB.eigenvalues i : ℝ) : ℂ) := by rw [hi]
    rw [heq]
    exact eigenvalues_le_top_eigenvalue hB i
  exact le_antisymm hupper hlower

/-- The top-eigenvalue form of `mulVec_eq_of_pow_rayleigh_re_eq`: a vector attaining the
largest eigenvalue of `A ^ m` as its Rayleigh quotient is a top eigenvector of `A`. -/
theorem mulVec_eq_of_pow_rayleigh_re_eq_top_eigenvalue [Nonempty n] (hA : A.PosSemidef)
    {m : ℕ} (hm : 1 ≤ m) {x : n → ℂ}
    (hx : (star x ⬝ᵥ ((A ^ m) *ᵥ x)).re = (hA.1.pow m).eigenvalues₀ 0 * (star x ⬝ᵥ x).re) :
    A *ᵥ x = ((hA.1.eigenvalues₀ 0 : ℝ) : ℂ) • x := by
  refine mulVec_eq_of_pow_rayleigh_re_eq hA ?_ (eigenvalues_le_top_eigenvalue hA.1) hm ?_
  · exact le_trans (hA.eigenvalues_nonneg (Classical.arbitrary n))
      (eigenvalues_le_top_eigenvalue hA.1 (Classical.arbitrary n))
  · rwa [← pow_top_eigenvalue hA m]

end Math.SpectralTheory

end
