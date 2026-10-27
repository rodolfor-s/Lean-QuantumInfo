import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The Moore–Penrose pseudoinverse of a Hermitian matrix, as a function

For a Hermitian matrix `M` the Moore–Penrose pseudoinverse is `M⁺ = cfc (·⁻¹) M`: apply `x ↦ x⁻¹`
through the real continuous functional calculus.  Lean's junk convention `(0 : ℝ)⁻¹ = 0` is exactly
the kernel-annihilating convention of the pseudoinverse, so no invertibility or support hypothesis
appears anywhere, and since a matrix spectrum is finite (`Matrix.finite_real_spectrum`) there is no
continuity side condition either.

This presents the pseudoinverse as an ordinary **function of the matrix** rather than as the
subject of an existence statement, so it composes.  The whole theory below is the function algebra
of `cfc`, with identities such as `x · x⁻¹ · x = x` checked pointwise on `ℝ`, at `x = 0` too.

## Main definitions

* `Matrix.hermitianPinv`

## Main statements

* `Matrix.mul_hermitianPinv_mul_self`, `Matrix.hermitianPinv_mul_self_mul_hermitianPinv`,
  `Matrix.isHermitian_mul_hermitianPinv`, `Matrix.isHermitian_hermitianPinv` — the four
  Moore–Penrose identities;
* `Matrix.exists_moorePenrose_pinv_of_isHermitian` — the corresponding existence statement, now
  with an explicit witness and for every Hermitian (not only positive semidefinite) matrix.  It
  subsumes the existential `Quantum.Channels.exists_moorePenrose_pinv_of_posSemidef`;
* `Matrix.mul_self_mul_hermitianPinv` — `M · M · M⁺ = M`, the kernel-safe cancellation the
  polar/Uhlmann completions use;
* `Matrix.hermitianPinv_mul_sq_mul_hermitianPinv` — the sandwich `M⁺ · (M · M) · M⁺` is the range
  projector `cfc 1_{≠0} (M · M)`;
* `Matrix.cfc_eq_conj_diagonal` — the spectral form `cfc f H = W · diag(f ∘ eig) · Wᴴ`.
-/

open scoped ComplexOrder

noncomputable section

namespace Matrix

variable {m : ℕ}

/-- **Spectral form of the matrix continuous functional calculus:** for Hermitian `H` with
eigenvector unitary `W` and eigenvalues `eig`, `cfc f H = W · diag(ℝ→ℂ ∘ f ∘ eig) · Wᴴ`. This is
`Matrix.IsHermitian.cfc_eq` composed with the definitional unfolding of `Matrix.IsHermitian.cfc`
(itself the conjugation `conjStarAlgAut W (diagonal (ofReal ∘ f ∘ eig))`). -/
lemma cfc_eq_conj_diagonal {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) (f : ℝ → ℝ) :
    cfc f H = (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ f ∘ hH.eigenvalues) *
      (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ := by
  rw [hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose]

/-- Every real function is continuous on a matrix spectrum, because that spectrum is finite. A
convenience wrapper for the `cfc` side conditions below. -/
lemma continuousOn_real_spectrum (M : Matrix (Fin m) (Fin m) ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) :=
  (Matrix.finite_real_spectrum (A := M)).continuousOn f

/-- **Moore–Penrose pseudoinverse of a Hermitian matrix**, through the real continuous functional
calculus: `x ↦ x⁻¹` applied on the (finite) spectrum, with the junk value `(0 : ℝ)⁻¹ = 0`
implementing the kernel-annihilating pseudoinverse convention. On a non-selfadjoint input the
`cfc` junk convention returns `0`. -/
def hermitianPinv (M : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  cfc (fun x : ℝ => x⁻¹) M

/-- The pseudoinverse of a Hermitian matrix is Hermitian. This is the fourth Moore–Penrose
identity in the Hermitian case, and holds for any input by the `cfc` junk convention. -/
lemma isHermitian_hermitianPinv (M : Matrix (Fin m) (Fin m) ℂ) :
    (hermitianPinv M).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSelfAdjoint, hermitianPinv]
  exact IsSelfAdjoint.cfc (f := fun x : ℝ => x⁻¹) (a := M)

section

variable {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsHermitian)
include hM

/-- `M · M⁺` is the `cfc` of the indicator `x ↦ x·x⁻¹` (that is, `1` off the kernel and `0` on
it): the range projector of a Hermitian `M`. -/
lemma mul_hermitianPinv_eq_cfc :
    M * hermitianPinv M = cfc (fun x : ℝ => x * x⁻¹) M := by
  have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  calc M * hermitianPinv M
      = cfc (fun x : ℝ => x) M * cfc (fun x : ℝ => x⁻¹) M := by
        rw [cfc_id' ℝ M hsa, hermitianPinv]
    _ = cfc (fun x : ℝ => x * x⁻¹) M := by
        rw [← cfc_mul (fun x : ℝ => x) (fun x : ℝ => x⁻¹) M
          (continuousOn_real_spectrum M _) (continuousOn_real_spectrum M _)]

/-- **First Moore–Penrose identity** `M · M⁺ · M = M`. Pointwise on the spectrum this is
`x · x⁻¹ · x = x`, which the junk convention makes true at `x = 0` too, so the identity is
kernel-safe and carries no support hypothesis. -/
lemma mul_hermitianPinv_mul_self : M * hermitianPinv M * M = M := by
  have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  have hfun : (fun x : ℝ => x * x⁻¹ * x) = (fun x : ℝ => x) := by
    funext x
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · rw [mul_assoc, inv_mul_cancel₀ h, mul_one]
  calc M * hermitianPinv M * M
      = cfc (fun x : ℝ => x * x⁻¹) M * cfc (fun x : ℝ => x) M := by
        rw [mul_hermitianPinv_eq_cfc hM, cfc_id' ℝ M hsa]
    _ = cfc (fun x : ℝ => x * x⁻¹ * x) M := by
        rw [← cfc_mul (fun x : ℝ => x * x⁻¹) (fun x : ℝ => x) M
          (continuousOn_real_spectrum M _) (continuousOn_real_spectrum M _)]
    _ = M := by rw [hfun, cfc_id' ℝ M hsa]

/-- **Second Moore–Penrose identity** `M⁺ · M · M⁺ = M⁺`. Pointwise `x⁻¹ · x · x⁻¹ = x⁻¹`,
including at `x = 0`. -/
lemma hermitianPinv_mul_self_mul_hermitianPinv :
    hermitianPinv M * M * hermitianPinv M = hermitianPinv M := by
  have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  have hfun : (fun x : ℝ => x⁻¹ * x * x⁻¹) = (fun x : ℝ => x⁻¹) := by
    funext x
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ h, one_mul]
  calc hermitianPinv M * M * hermitianPinv M
      = cfc (fun x : ℝ => x⁻¹) M * cfc (fun x : ℝ => x) M * cfc (fun x : ℝ => x⁻¹) M := by
        rw [cfc_id' ℝ M hsa, hermitianPinv]
    _ = cfc (fun x : ℝ => x⁻¹ * x) M * cfc (fun x : ℝ => x⁻¹) M := by
        rw [← cfc_mul (fun x : ℝ => x⁻¹) (fun x : ℝ => x) M
          (continuousOn_real_spectrum M _) (continuousOn_real_spectrum M _)]
    _ = cfc (fun x : ℝ => x⁻¹ * x * x⁻¹) M := by
        rw [← cfc_mul (fun x : ℝ => x⁻¹ * x) (fun x : ℝ => x⁻¹) M
          (continuousOn_real_spectrum M _) (continuousOn_real_spectrum M _)]
    _ = hermitianPinv M := by rw [hfun, hermitianPinv]

/-- **Third Moore–Penrose identity** `(M · M⁺)` is Hermitian: it is a real `cfc` of a selfadjoint
matrix (`mul_hermitianPinv_eq_cfc`). -/
lemma isHermitian_mul_hermitianPinv : (M * hermitianPinv M).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSelfAdjoint, mul_hermitianPinv_eq_cfc hM]
  exact IsSelfAdjoint.cfc (f := fun x : ℝ => x * x⁻¹) (a := M)

/-- The fourth identity in its usual form: `(M⁺ · M)` is Hermitian. For a Hermitian `M` the
functional calculus commutes, so this is the same projector as `M · M⁺`. -/
lemma isHermitian_hermitianPinv_mul : (hermitianPinv M * M).IsHermitian := by
  have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  have hcomm : hermitianPinv M * M = cfc (fun x : ℝ => x * x⁻¹) M := by
    calc hermitianPinv M * M
        = cfc (fun x : ℝ => x⁻¹) M * cfc (fun x : ℝ => x) M := by
          rw [cfc_id' ℝ M hsa, hermitianPinv]
      _ = cfc (fun x : ℝ => x⁻¹ * x) M := by
          rw [← cfc_mul (fun x : ℝ => x⁻¹) (fun x : ℝ => x) M
            (continuousOn_real_spectrum M _) (continuousOn_real_spectrum M _)]
      _ = cfc (fun x : ℝ => x * x⁻¹) M := by
          congr 1; funext x; rw [mul_comm]
  rw [Matrix.isHermitian_iff_isSelfAdjoint, hcomm]
  exact IsSelfAdjoint.cfc (f := fun x : ℝ => x * x⁻¹) (a := M)

/-- **The squared Hermitian matrix cancels its own pseudoinverse:** `M · M · M⁺ = M`. Pointwise
`x · x · x⁻¹ = x`, at `x = 0` as well, so the identity is kernel-safe. This is the cancellation the
Gram/polar completions consume. -/
lemma mul_self_mul_hermitianPinv : M * M * hermitianPinv M = M := by
  have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  have hfun : (fun x : ℝ => x * x * x⁻¹) = (fun x : ℝ => x) := by
    funext x
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · rw [mul_assoc, mul_inv_cancel₀ h, mul_one]
  calc M * M * hermitianPinv M
      = cfc (fun x : ℝ => x) M * cfc (fun x : ℝ => x) M * cfc (fun x : ℝ => x⁻¹) M := by
        rw [cfc_id' ℝ M hsa, hermitianPinv]
    _ = cfc (fun x : ℝ => x * x) M * cfc (fun x : ℝ => x⁻¹) M := by
        rw [← cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) M
          (continuousOn_real_spectrum M _) (continuousOn_real_spectrum M _)]
    _ = cfc (fun x : ℝ => x * x * x⁻¹) M := by
        rw [← cfc_mul (fun x : ℝ => x * x) (fun x : ℝ => x⁻¹) M
          (continuousOn_real_spectrum M _) (continuousOn_real_spectrum M _)]
    _ = M := by rw [hfun, cfc_id' ℝ M hsa]

/-- **The pseudoinverse sandwich of the square is the range projector:**
`M⁺ · (M · M) · M⁺ = cfc 1_{≠0} (M · M)`. Pushing the sandwich through the function algebra gives
`cfc (x ↦ x⁻¹ · (x · x) · x⁻¹) M`, which agrees pointwise with `cfc (1_{≠0} ∘ (·²)) M`, i.e. with
`cfc 1_{≠0} (M · M)` by `cfc_comp`. -/
lemma hermitianPinv_mul_sq_mul_hermitianPinv :
    hermitianPinv M * (M * M) * hermitianPinv M =
      cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (M * M) := by
  have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  have hcont2 : ∀ g : ℝ → ℝ, ContinuousOn g ((fun x : ℝ => x * x) '' spectrum ℝ M) :=
    fun g => ((Matrix.finite_real_spectrum (A := M)).image _).continuousOn g
  have hMM : M * M = cfc (fun x : ℝ => x * x) M := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) M
      (continuousOn_real_spectrum M _) (continuousOn_real_spectrum M _), cfc_id' ℝ M hsa]
  rw [hMM,
    ← cfc_comp (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (fun x : ℝ => x * x) M hsa
      (hcont2 _) (continuousOn_real_spectrum M _), hermitianPinv,
    ← cfc_mul (fun x : ℝ => x⁻¹) (fun x : ℝ => x * x) M
      (continuousOn_real_spectrum M _) (continuousOn_real_spectrum M _),
    ← cfc_mul (fun x : ℝ => x⁻¹ * (x * x)) (fun x : ℝ => x⁻¹) M
      (continuousOn_real_spectrum M _) (continuousOn_real_spectrum M _)]
  congr 1
  funext x
  by_cases hx : x = 0
  · simp [hx]
  · have hxx : x * x ≠ 0 := mul_ne_zero hx hx
    simp only [Function.comp_apply, ite_eq_right hxx]
    field_simp

/-- **Existence of a Moore–Penrose pseudoinverse for a Hermitian matrix, with explicit witness.**
The witness is `hermitianPinv M`; the four identities are the lemmas above. This strengthens the
purely existential `Quantum.Channels.exists_moorePenrose_pinv_of_posSemidef` in two ways: the
hypothesis is
Hermitian rather than positive semidefinite, and the witness is a named function of `M`. -/
theorem exists_moorePenrose_pinv_of_isHermitian :
    ∃ Mp : Matrix (Fin m) (Fin m) ℂ,
      Mp = hermitianPinv M ∧ M * Mp * M = M ∧ Mp * M * Mp = Mp ∧
        (M * Mp).IsHermitian ∧ Mp.IsHermitian :=
  ⟨hermitianPinv M, rfl, mul_hermitianPinv_mul_self hM,
    hermitianPinv_mul_self_mul_hermitianPinv hM, isHermitian_mul_hermitianPinv hM,
    isHermitian_hermitianPinv M⟩

end

end Matrix

end -- noncomputable section
