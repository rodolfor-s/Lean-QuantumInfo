import QCryptLean.Math.SpectralTheory.MatrixCFC

/-!
# Complex spectral powers of a Hermitian matrix

Mathlib's continuous functional calculus gives real powers of a positive semidefinite
matrix (`CFC.rpow`) but no *complex* power. This module defines the complex spectral
power `hermCpow` of a Hermitian matrix and develops its algebra: the exponent
semigroup law, unitarity on the imaginary axis, agreement with the monoid power at
natural exponents and with `CFC.rpow` at real exponents, and the adjoint/trace laws.

For positive definite `A`, complex powers give the analytic family used in interpolation:
`z ↦ A ^ z`, whose values on a vertical line differ from `A ^ (Re z)` by a unitary
factor. That is the hypothesis pattern of the Hadamard three-lines theorem, used for the
Araki–Lieb–Thirring trace inequality (`ArakiLiebThirring.lean`).

## Main definitions

- `Math.SpectralTheory.hermCpow` : `hermCpow hA w = U · diagonal (λᵢ ^ w) · Uᴴ` for the
  eigenvalues `λ` and the eigenvector unitary `U = hA.eigenvectorUnitary` of a Hermitian
  `A`, with `λᵢ ^ w` the complex power `Complex.cpow`.

## Main statements

Exponent laws, valid for every Hermitian matrix:

- `hermCpow_zero`, `hermCpow_one`, `hermCpow_natCast` : the exponents `0`, `1` and
  `(k : ℂ)` give `1`, `A` and the monoid power `A ^ k`.
- `hermCpow_comm` : powers of the same matrix commute.
- `hermCpow_trace` : `Tr (A ^ w) = ∑ᵢ λᵢ ^ w`.

Laws that need only a **nowhere-vanishing spectrum**, `∀ i, λᵢ ≠ 0`, which is where
`Complex.cpow` is a group homomorphism in the exponent. Negative eigenvalues are allowed:

- `hermCpow_add_of_eigenvalues_ne_zero` : `A ^ z · A ^ w = A ^ (z + w)`.
- `isUnit_hermCpow_of_eigenvalues_ne_zero`, `hermCpow_mul_neg_self_of_eigenvalues_ne_zero`
  and `hermCpow_inv_of_eigenvalues_ne_zero` : `A ^ w` is invertible with inverse
  `A ^ (-w)`.

These fail on a singular matrix: at `z = 1`, `w = -1` the product `A ^ 1 · A ^ (-1)` is the
support projection of `A`, not `1`.

Further laws with a **sign** condition on the spectrum, which the group law alone does not
give, because the branch cut of `Complex.cpow` runs along the negative reals:

- `Matrix.PosDef.hermCpow_mem_unitary` : `A ^ w` is unitary for positive definite `A` and
  `Re w = 0`; `Matrix.PosDef.hermCpow_conjTranspose_mul_self` is the same fact in equational
  form. Positivity is doing real work on both sides. Semidefiniteness is not enough: for
  singular `A` and `w = I · t` with `t ≠ 0` the matrix `A ^ w` annihilates the kernel of
  `A`, so `(A ^ w)ᴴ (A ^ w)` is the support projection of `A` rather than `1`. A nonzero
  but negative eigenvalue is not enough either: `|λ ^ w| = |λ| ^ (Re w) · exp (-π · Im w)`
  there, which is `1` on the imaginary axis only at `w = 0`.
- `Matrix.PosDef.hermCpow_add`, `Matrix.PosDef.isUnit_hermCpow` : the positive definite rows of the
two
  nowhere-vanishing laws above, kept because that is the hypothesis the interpolation
  argument of `ArakiLiebThirring.lean` carries.
- `Matrix.PosSemidef.conjTranspose_hermCpow` : `(A ^ w)ᴴ = A ^ (conj w)` for positive
  semidefinite `A` — nonnegative eigenvalues keep the base off the branch cut of
  `Complex.cpow`.
- `Matrix.PosSemidef.hermCpow_ofReal` : at a real exponent this is `CFC.rpow`; combined with the
  trace formula this gives `trace_posSemidef_rpow_re`, the spectral expression
  `Re Tr (A ^ q) = ∑ᵢ λᵢ ^ q` for a real power of a positive semidefinite matrix.
- `Matrix.PosSemidef.hermCpow_conjTranspose_mul_self` : `(A ^ w)ᴴ (A ^ w) = A ^ (2 Re w)` for `0 <
Re w`. The
  conclusion can fail on a singular `A` at a nonzero imaginary exponent: the left side is
  the support projection while the right side is `A ^ 0 = 1`. At `w = 0` both sides are `1`.

The construction is written in `hA.eigenvectorUnitary`, Mathlib's *chosen* orthonormal
eigenbasis. This module does not prove that the value is independent of that choice, and
an explicit spectral formula is not choice-free merely because it is explicit. What is
proved is the real-exponent identification with `CFC.rpow`
(`Matrix.PosSemidef.hermCpow_ofReal`), which is basis-free, and the algebraic laws below, whose
statements never mention an eigenbasis.

## References

- R. Bhatia, *Matrix Analysis*, Springer (1997), Chapter IX.
- E. M. Stein, G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*,
  Chapter V (analytic families of operators).
-/

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open Matrix Unitary

noncomputable section

namespace Math.SpectralTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Complex spectral power of a Hermitian matrix.**
`hermCpow hA w = U · diagonal (λᵢ ^ w) · Uᴴ`, where `λ` are the eigenvalues of `A`,
`U = hA.eigenvectorUnitary`, and `λᵢ ^ w` is the complex power `Complex.cpow` of the
(real) eigenvalue.

At a nonnegative eigenvalue and real exponent this is the ordinary real power
(`Matrix.PosSemidef.hermCpow_ofReal`); at a natural exponent it is the monoid power
(`hermCpow_natCast`). `Complex.cpow` conventions are inherited: `0 ^ 0 = 1` and
`0 ^ w = 0` for `w ≠ 0`, so on a singular matrix `hermCpow hA w` annihilates the kernel
of `A` for every `w ≠ 0`, which is why the group and unitarity laws below need a strictly
positive spectrum. -/
def hermCpow {A : Matrix n n ℂ} (hA : A.IsHermitian) (w : ℂ) : Matrix n n ℂ :=
  conjStarAlgAut ℂ _ hA.eigenvectorUnitary
    (Matrix.diagonal fun i => ((hA.eigenvalues i : ℝ) : ℂ) ^ w)

/-- `hermCpow` at exponent `0` is the identity: `Complex.cpow` sends every base, `0`
included, to `1` at exponent `0`. -/
@[simp]
theorem hermCpow_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) : hermCpow hA 0 = 1 := by
  rw [hermCpow]
  simp

/-- `hermCpow` at exponent `1` recovers the matrix, by the spectral theorem. -/
@[simp]
theorem hermCpow_one {A : Matrix n n ℂ} (hA : A.IsHermitian) : hermCpow hA 1 = A := by
  rw [hermCpow]
  simp only [Complex.cpow_one]
  exact (hA.spectral_theorem).symm

/-- **Natural exponents are monoid powers**: `hermCpow hA (k : ℂ) = A ^ k`. This is the
identity between the spectral power and the algebraic power of the matrix ring. -/
theorem hermCpow_natCast {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    hermCpow hA (k : ℂ) = A ^ k := by
  have hd : (Matrix.diagonal fun i => ((hA.eigenvalues i : ℝ) : ℂ) ^ (k : ℂ))
      = (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix n n ℂ) ^ k := by
    rw [Matrix.diagonal_pow]
    congr 1
    funext i
    rw [Complex.cpow_natCast]
    rfl
  rw [hermCpow, hd, map_pow]
  exact congrArg (· ^ k) hA.spectral_theorem.symm

/-- **Trace of a complex spectral power**: `Tr (A ^ w) = ∑ᵢ λᵢ ^ w`. -/
theorem hermCpow_trace {A : Matrix n n ℂ} (hA : A.IsHermitian) (w : ℂ) :
    (hermCpow hA w).trace = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) ^ w := by
  rw [hermCpow, conjStarAlgAut_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]

/-- Complex powers of the same Hermitian matrix commute: both sides are the conjugate of
a product of diagonal matrices, and no spectral side condition is needed. -/
theorem hermCpow_comm {A : Matrix n n ℂ} (hA : A.IsHermitian) (z w : ℂ) :
    hermCpow hA z * hermCpow hA w = hermCpow hA w * hermCpow hA z := by
  rw [hermCpow, hermCpow, ← map_mul, ← map_mul, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  ring

/-- **Exponent additivity of `hermCpow`**: `A ^ z · A ^ w = A ^ (z + w)` for a Hermitian
matrix with no zero eigenvalue. Negative eigenvalues are allowed; what is needed is a
nonzero base, which is exactly where `Complex.cpow_add` applies.

A zero eigenvalue breaks the law: for singular positive semidefinite `A` it fails at
`z = 1`, `w = -1`, where the left side is the support projection of `A` and the right side
is `1`. -/
theorem hermCpow_add_of_eigenvalues_ne_zero {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h0 : ∀ i, hA.eigenvalues i ≠ 0) (z w : ℂ) :
    hermCpow hA z * hermCpow hA w = hermCpow hA (z + w) := by
  rw [hermCpow, hermCpow, hermCpow, ← map_mul, Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  exact (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (h0 i))).symm

/-- **Exponent additivity of `hermCpow`** for a *positive definite* matrix, the positive
definite row of `hermCpow_add_of_eigenvalues_ne_zero`. -/
theorem _root_.Matrix.PosDef.hermCpow_add {A : Matrix n n ℂ} (hA : A.PosDef) (z w : ℂ) :
    hermCpow hA.1 z * hermCpow hA.1 w = hermCpow hA.1 (z + w) :=
  hermCpow_add_of_eigenvalues_ne_zero hA.1 (fun i => (hA.eigenvalues_pos i).ne') z w

/-- **Adjoint of a complex spectral power** of a positive semidefinite matrix:
`(A ^ w)ᴴ = A ^ (conj w)`. Nonnegativity of the eigenvalues is what puts the base off the
branch cut of `Complex.cpow` (`Complex.conj_cpow` needs `arg ≠ π`). -/
theorem _root_.Matrix.PosSemidef.conjTranspose_hermCpow {A : Matrix n n ℂ} (hA : A.PosSemidef) (w :
    ℂ) :
    (hermCpow hA.1 w)ᴴ = hermCpow hA.1 (conj w) := by
  have hscal : ∀ i, star (((hA.1.eigenvalues i : ℝ) : ℂ) ^ w)
      = ((hA.1.eigenvalues i : ℝ) : ℂ) ^ (conj w) := by
    intro i
    have harg : ((hA.1.eigenvalues i : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg (hA.eigenvalues_nonneg i)]
      exact ne_of_lt Real.pi_pos
    have h := Complex.conj_cpow ((hA.1.eigenvalues i : ℝ) : ℂ) (conj w) harg
    rw [Complex.conj_ofReal, Complex.conj_conj] at h
    exact h.symm
  rw [hermCpow, hermCpow, ← Matrix.star_eq_conjTranspose, ← map_star,
    Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 2
  funext i
  simpa only [Pi.star_apply] using hscal i

/-- A real-exponent complex spectral power of a positive semidefinite matrix is
Hermitian. -/
theorem _root_.Matrix.PosSemidef.isHermitian_hermCpow {A : Matrix n n ℂ} (hA : A.PosSemidef) (x :
    ℝ) :
    (hermCpow hA.1 (x : ℂ)).IsHermitian := by
  change (hermCpow hA.1 (x : ℂ))ᴴ = hermCpow hA.1 (x : ℂ)
  rw [Matrix.PosSemidef.conjTranspose_hermCpow hA, Complex.conj_ofReal]

/-- **Real-exponent anchor**: on a positive semidefinite matrix the complex spectral power
at a real exponent is Mathlib's `CFC.rpow`, so every `hermCpow` statement specialises to
the real-power bank. -/
theorem _root_.Matrix.PosSemidef.hermCpow_ofReal {A : Matrix n n ℂ} (hA : A.PosSemidef) (x : ℝ) :
    hermCpow hA.1 (x : ℂ) = A ^ x := by
  have hd : (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ) ^ (x : ℂ))
      = (fun i => ((hA.1.eigenvalues i ^ x : ℝ) : ℂ)) := by
    funext i
    rw [Complex.ofReal_cpow (hA.eigenvalues_nonneg i)]
  rw [hermCpow, hd, ← Matrix.PosSemidef.cfcRpow_eq_conjStarAlgAut_diagonal hA x]

/-- **Gram matrix of a complex spectral power.** For positive semidefinite `A` and
`0 < Re w`, `(A ^ w)ᴴ (A ^ w) = A ^ (2 Re w)`, because `|λ ^ w|² = λ ^ (2 Re w)` on the
spectrum. Strict positivity of `Re w` is load-bearing on a singular `A`: at `Re w = 0`
with `w ≠ 0` the left side is the support projection of `A` while the right side is
`A ^ 0 = 1`, and only the inequality `≤` survives. -/
theorem _root_.Matrix.PosSemidef.hermCpow_conjTranspose_mul_self {A : Matrix n n ℂ} (hA :
    A.PosSemidef) {w : ℂ}
    (hw : 0 < w.re) : (hermCpow hA.1 w)ᴴ * hermCpow hA.1 w = A ^ (2 * w.re) := by
  have hnorm : ∀ i, ‖((hA.1.eigenvalues i : ℝ) : ℂ) ^ w‖ = hA.1.eigenvalues i ^ w.re := by
    intro i
    rcases lt_or_eq_of_le (hA.eigenvalues_nonneg i) with hpos | hzero
    · exact Complex.norm_cpow_eq_rpow_re_of_pos hpos w
    · rw [← hzero, Complex.ofReal_zero,
        Complex.zero_cpow (by intro h; rw [h] at hw; simp at hw), norm_zero,
        Real.zero_rpow (ne_of_gt hw)]
  have hscal : ∀ i, star (((hA.1.eigenvalues i : ℝ) : ℂ) ^ w) *
        (((hA.1.eigenvalues i : ℝ) : ℂ) ^ w)
      = ((hA.1.eigenvalues i ^ (2 * w.re) : ℝ) : ℂ) := by
    intro i
    rw [show star (((hA.1.eigenvalues i : ℝ) : ℂ) ^ w)
        = (starRingEnd ℂ) (((hA.1.eigenvalues i : ℝ) : ℂ) ^ w) from rfl, mul_comm,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm i, ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul (hA.eigenvalues_nonneg i)]
    norm_num
    ring_nf
  rw [hermCpow, ← Matrix.star_eq_conjTranspose, ← map_star, ← map_mul,
    Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  simp only [Pi.star_apply]
  rw [show (fun i => star (((hA.1.eigenvalues i : ℝ) : ℂ) ^ w) *
        (((hA.1.eigenvalues i : ℝ) : ℂ) ^ w))
      = (fun i => ((hA.1.eigenvalues i ^ (2 * w.re) : ℝ) : ℂ)) from funext hscal,
    ← Matrix.PosSemidef.cfcRpow_eq_conjStarAlgAut_diagonal hA (2 * w.re)]

/-- **Imaginary exponents give unitaries** (equational form). For positive definite `A`
and `Re w = 0`, `(A ^ w)ᴴ (A ^ w) = 1`: the eigenvalues `λᵢ ^ w` have modulus `1`.

Strict positivity of the spectrum cannot be weakened to semidefiniteness: for singular
`A` and `w = I · t` with `t ≠ 0` every zero eigenvalue contributes `0 ^ w = 0`, and the
left side is the support projection of `A`. It cannot be weakened to a merely
nowhere-vanishing spectrum either: at a *negative* eigenvalue the principal branch gives
`|λ ^ (I · t)| = exp (-π t)`, so the eigenvalue powers leave the unit circle. -/
theorem _root_.Matrix.PosDef.hermCpow_conjTranspose_mul_self {A : Matrix n n ℂ} (hA : A.PosDef) {w
    : ℂ}
    (hw : w.re = 0) : (hermCpow hA.1 w)ᴴ * hermCpow hA.1 w = 1 := by
  rw [Matrix.PosSemidef.conjTranspose_hermCpow hA.posSemidef, Matrix.PosDef.hermCpow_add hA,
    show conj w + w = ((2 * w.re : ℝ) : ℂ) from by rw [add_comm, Complex.add_conj], hw]
  simp only [mul_zero, Complex.ofReal_zero]
  exact hermCpow_zero hA.1

/-- **Imaginary exponents give unitaries.** For positive definite `A` and `Re w = 0`,
`A ^ w ∈ unitary`; the cornerstone of every analytic-family/modular-flow argument, since
it makes `‖A ^ (t + i u)‖ = ‖A ^ t‖` for a unitarily invariant norm. -/
theorem _root_.Matrix.PosDef.hermCpow_mem_unitary {A : Matrix n n ℂ} (hA : A.PosDef) {w : ℂ}
    (hw : w.re = 0) : hermCpow hA.1 w ∈ unitary (Matrix n n ℂ) := by
  have h1 : star (hermCpow hA.1 w) * hermCpow hA.1 w = 1 := by
    rw [Matrix.star_eq_conjTranspose]
    exact Matrix.PosDef.hermCpow_conjTranspose_mul_self hA hw
  exact Unitary.mem_iff.mpr ⟨h1, mul_eq_one_comm.mp h1⟩

/-- A complex spectral power of a Hermitian matrix with no zero eigenvalue is invertible:
`λᵢ ^ w ≠ 0` for `λᵢ ≠ 0`. -/
theorem isUnit_hermCpow_of_eigenvalues_ne_zero {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h0 : ∀ i, hA.eigenvalues i ≠ 0) (w : ℂ) : IsUnit (hermCpow hA w) := by
  rw [hermCpow]
  refine IsUnit.map _ ?_
  rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  exact isUnit_iff_ne_zero.mpr (Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr (h0 i))))

/-- Opposite exponents cancel on a Hermitian matrix with no zero eigenvalue. -/
theorem hermCpow_mul_neg_self_of_eigenvalues_ne_zero {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h0 : ∀ i, hA.eigenvalues i ≠ 0) (w : ℂ) :
    hermCpow hA w * hermCpow hA (-w) = 1 := by
  rw [hermCpow_add_of_eigenvalues_ne_zero hA h0, add_neg_cancel, hermCpow_zero]

/-- **The inverse of a complex spectral power is the power at the opposite exponent**, for
a Hermitian matrix with no zero eigenvalue. -/
theorem hermCpow_inv_of_eigenvalues_ne_zero {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h0 : ∀ i, hA.eigenvalues i ≠ 0) (w : ℂ) :
    (hermCpow hA w)⁻¹ = hermCpow hA (-w) :=
  Matrix.inv_eq_right_inv (hermCpow_mul_neg_self_of_eigenvalues_ne_zero hA h0 w)

/-- A complex spectral power of a positive definite matrix is invertible, the positive
definite row of `isUnit_hermCpow_of_eigenvalues_ne_zero`. -/
theorem _root_.Matrix.PosDef.isUnit_hermCpow {A : Matrix n n ℂ} (hA : A.PosDef) (w : ℂ) :
    IsUnit (hermCpow hA.1 w) :=
  isUnit_hermCpow_of_eigenvalues_ne_zero hA.1 (fun i => (hA.eigenvalues_pos i).ne') w

/-- Spectral formula for the trace of a real power of a positive semidefinite matrix. -/
theorem trace_posSemidef_rpow_re {A : Matrix n n ℂ} (hA : A.PosSemidef) (q : ℝ) :
    ((A ^ q).trace).re = ∑ i, hA.1.eigenvalues i ^ q := by
  rw [← Matrix.PosSemidef.hermCpow_ofReal hA q, hermCpow_trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_cpow (hA.eigenvalues_nonneg i), Complex.ofReal_re]

end Math.SpectralTheory

end
