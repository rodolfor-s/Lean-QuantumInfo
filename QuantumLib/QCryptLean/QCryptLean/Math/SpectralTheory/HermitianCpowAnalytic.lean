import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import QCryptLean.Math.SpectralTheory.HermitianCpow
import QCryptLean.Math.SpectralTheory.MatrixCFC

/-!
# The complex spectral power as an analytic family

An interpolation argument needs the complex spectral power
`Math.SpectralTheory.hermCpow` of a Hermitian matrix to be an *entire* family in the
exponent, and needs its size on a vertical line to be controlled by the real part of the
exponent alone. This module supplies both, together with the matrix-valued
differentiability plumbing they rest on.

Differentiability of a matrix-valued function is entrywise: `Matrix n n ℂ` carries the
product topology and module structure, and `differentiable_pi` reduces every statement
below to differentiability of finitely many scalar functions. The operator-norm section
at the end is the only part that fixes a norm on matrices (the L² operator norm, for
which unitary conjugation is isometric); it is separated so that the differentiability
statements do not depend on a scoped norm instance.

## Main statements

Matrix-valued differentiability (all entrywise, reusable):

- `differentiable_matrix_diagonal`, `differentiable_matrix_mul`,
  `differentiable_matrix_mul_left`, `differentiable_matrix_mul_right`,
  `differentiable_matrix_comp`, `differentiable_matrix_trace`.

The spectral power as an analytic family:

- `hermCpow_eq_sum_smul_eigenProj` : `A ^ w = ∑ᵢ λᵢ ^ w • |uᵢ⟩⟨uᵢ|`; the exponent enters
  only through the scalars.
- `hermCpow_differentiable` : `z ↦ A ^ z` is entire when no eigenvalue is `0`. At a zero
  eigenvalue the scalar `0 ^ z` jumps at `z = 0`, so the hypothesis is not removable.
- `differentiable_const_cpow_affine` : the scalar weights `z ↦ c ^ (a z + b)` of a test
  function are entire for `c ≠ 0`.
- `norm_hermCpow_apply_le` : each entry of `A ^ w` is bounded by the sum of the moduli of
  the spectral weights, a bound uniform along vertical lines.

Operator norm (L² operator norm, scoped instance):

- `hermCpow_l2_opNorm` : `‖A ^ w‖` is the supremum of the moduli of the spectral weights.
- `hermCpow_l2_opNorm_le`, `norm_cpow_eigenvalue_le_hermCpow_l2_opNorm`.
- `Matrix.PosDef.norm_hermCpow_eq_of_re_eq` : for positive definite `A`, `‖A ^ w‖` depends
  on `w` only through `Re w`.
-/

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open Matrix Unitary

noncomputable section

namespace Math.SpectralTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Differentiability plumbing for matrix-valued functions -/

-- The entrywise proof chooses a `Fintype` from propositional finiteness; the statement
-- does not depend on a particular enumeration.
omit [Fintype n] in
/-- A diagonal matrix with differentiable entries is a differentiable matrix-valued
function. -/
theorem differentiable_matrix_diagonal [Finite n] {d : n → ℂ → ℂ}
    (hd : ∀ i, Differentiable ℂ (d i)) :
    Differentiable ℂ fun z => Matrix.diagonal fun i => d i z := by
  classical
  let := Fintype.ofFinite n
  apply differentiable_pi.mpr; intro a
  apply differentiable_pi.mpr; intro b
  simp only [Matrix.diagonal_apply]
  split_ifs with h
  · subst h; exact hd a
  · exact differentiable_const 0

omit [DecidableEq n] in
/-- The pointwise product of two differentiable matrix-valued functions is differentiable:
each entry of the product is a finite sum of products of differentiable scalars. -/
theorem differentiable_matrix_mul {f g : ℂ → Matrix n n ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) : Differentiable ℂ fun z => f z * g z := by
  apply differentiable_pi.mpr; intro a
  apply differentiable_pi.mpr; intro b
  simp_rw [Matrix.mul_apply]
  refine Differentiable.fun_sum fun k _ => ?_
  exact ((differentiable_pi.mp ((differentiable_pi.mp hf) a)) k).mul
    ((differentiable_pi.mp ((differentiable_pi.mp hg) k)) b)

omit [DecidableEq n] in
/-- Left multiplication by a constant matrix preserves differentiability. -/
theorem differentiable_matrix_mul_left (C : Matrix n n ℂ) {f : ℂ → Matrix n n ℂ}
    (hf : Differentiable ℂ f) : Differentiable ℂ fun z => C * f z :=
  differentiable_matrix_mul (differentiable_const C) hf

omit [DecidableEq n] in
/-- Right multiplication by a constant matrix preserves differentiability. -/
theorem differentiable_matrix_mul_right (C : Matrix n n ℂ) {f : ℂ → Matrix n n ℂ}
    (hf : Differentiable ℂ f) : Differentiable ℂ fun z => f z * C :=
  differentiable_matrix_mul hf (differentiable_const C)

omit [DecidableEq n] in
omit [Fintype n] in
/-- Precomposing a differentiable matrix-valued function with a differentiable scalar
function is differentiable. -/
theorem differentiable_matrix_comp [Finite n] {f : ℂ → Matrix n n ℂ} (hf : Differentiable ℂ f)
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) : Differentiable ℂ fun z => f (g z) := by
  classical
  let := Fintype.ofFinite n
  apply differentiable_pi.mpr; intro a
  apply differentiable_pi.mpr; intro b
  exact ((differentiable_pi.mp ((differentiable_pi.mp hf) a)) b).comp hg

omit [DecidableEq n] in
/-- The trace of a differentiable matrix-valued function is differentiable. -/
theorem differentiable_matrix_trace {f : ℂ → Matrix n n ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ fun z => (f z).trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact Differentiable.fun_sum fun i _ =>
    (differentiable_pi.mp ((differentiable_pi.mp hf) i)) i

/-- A constant nonzero complex base raised to an affine function of `z` is entire. These
are the scalar weights of an interpolation test function. -/
theorem differentiable_const_cpow_affine {c : ℂ} (hc : c ≠ 0) (a b : ℂ) :
    Differentiable ℂ fun z : ℂ => c ^ (a * z + b) := by
  have : NeZero c := ⟨hc⟩
  exact (differentiable_const_cpow_of_neZero c).comp
    (((differentiable_const a).mul differentiable_id).add_const b)

/-! ### The spectral power as an analytic family -/

/-- **Eigenprojector expansion of a complex spectral power.**
`A ^ w = ∑ᵢ (λᵢ ^ w) • |uᵢ⟩⟨uᵢ|` for the orthonormal eigenbasis `u` of `A`. The exponent
enters only through the scalars, which is what makes `z ↦ A ^ z` an analytic family. -/
theorem hermCpow_eq_sum_smul_eigenProj {A : Matrix n n ℂ} (hA : A.IsHermitian) (w : ℂ) :
    hermCpow hA w = ∑ i, (((hA.eigenvalues i : ℝ) : ℂ) ^ w) •
      Matrix.vecMulVec ((hA.eigenvectorBasis i).ofLp)
        (star ((hA.eigenvectorBasis i).ofLp)) :=
  conjStarAlgAut_eigenvectorUnitary_diagonal hA _

/-- **`z ↦ A ^ z` is entire** for a Hermitian matrix with no zero eigenvalue: in the
spectral formula only the diagonal weights `λᵢ ^ z` depend on `z`, and each is entire.

The hypothesis is necessary for this formula: `Complex.cpow` has `0 ^ 0 = 1` and
`0 ^ z = 0` for `z ≠ 0`, so a singular matrix gives a family discontinuous at `z = 0`. -/
theorem hermCpow_differentiable {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hne : ∀ i, hA.eigenvalues i ≠ 0) : Differentiable ℂ (hermCpow hA) := by
  have hrw : hermCpow hA = fun z => (hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ) ^ z) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
    funext z
    rw [hermCpow, conjStarAlgAut_apply]
  rw [hrw]
  refine differentiable_matrix_mul_right _
    (differentiable_matrix_mul_left _ (differentiable_matrix_diagonal fun i => ?_))
  have : NeZero ((hA.eigenvalues i : ℝ) : ℂ) := ⟨Complex.ofReal_ne_zero.mpr (hne i)⟩
  exact differentiable_const_cpow_of_neZero _

/-- Entry bound for a complex spectral power: every entry is bounded by the sum of the
moduli of the spectral weights, since the eigenvector matrix is unitary. -/
theorem norm_hermCpow_apply_le {A : Matrix n n ℂ} (hA : A.IsHermitian) (w : ℂ) (i j : n) :
    ‖hermCpow hA w i j‖ ≤ ∑ m, ‖((hA.eigenvalues m : ℝ) : ℂ) ^ w‖ := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ :=
    hA.eigenvectorUnitary.2
  rw [hermCpow, conjStarAlgAut_apply, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [Matrix.mul_diagonal, norm_mul, norm_mul,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, norm_star]
  have h1 : ‖(hA.eigenvectorUnitary : Matrix n n ℂ) i m‖ ≤ 1 :=
    entry_norm_bound_of_unitary hU i m
  have h2 : ‖(hA.eigenvectorUnitary : Matrix n n ℂ) j m‖ ≤ 1 :=
    entry_norm_bound_of_unitary hU j m
  calc ‖(hA.eigenvectorUnitary : Matrix n n ℂ) i m‖ * ‖((hA.eigenvalues m : ℝ) : ℂ) ^ w‖ *
        ‖(hA.eigenvectorUnitary : Matrix n n ℂ) j m‖
      ≤ 1 * ‖((hA.eigenvalues m : ℝ) : ℂ) ^ w‖ * 1 := by
        gcongr
    _ = ‖((hA.eigenvalues m : ℝ) : ℂ) ^ w‖ := by ring

/-! ### Operator norm of a complex spectral power

This section fixes the L² operator norm on matrices (`Matrix.Norms.L2Operator`), the norm
for which unitary conjugation is isometric. -/

section OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- **Operator norm of a complex spectral power**: `‖A ^ w‖` is the supremum of the moduli
`|λᵢ ^ w|` of the spectral weights, since the eigenvector conjugation is isometric and the
L² operator norm of a diagonal matrix is the supremum of its entries. -/
theorem hermCpow_l2_opNorm {A : Matrix n n ℂ} (hA : A.IsHermitian) (w : ℂ) :
    ‖hermCpow hA w‖ = ‖fun i => ((hA.eigenvalues i : ℝ) : ℂ) ^ w‖ := by
  rw [hermCpow, conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary _ (star hA.eigenvectorUnitary),
    CStarRing.norm_coe_unitary_mul hA.eigenvectorUnitary, Matrix.l2_opNorm_diagonal]

/-- A uniform bound on the spectral weights bounds the operator norm of the spectral
power. -/
theorem hermCpow_l2_opNorm_le {A : Matrix n n ℂ} (hA : A.IsHermitian) (w : ℂ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, ‖((hA.eigenvalues i : ℝ) : ℂ) ^ w‖ ≤ c) :
    ‖hermCpow hA w‖ ≤ c := by
  rw [hermCpow_l2_opNorm]
  exact (pi_norm_le_iff_of_nonneg (G := fun _ : n => ℂ) hc).mpr h

/-- A single spectral weight is bounded by the operator norm of the spectral power. -/
theorem norm_cpow_eigenvalue_le_hermCpow_l2_opNorm {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (w : ℂ) (i : n) : ‖((hA.eigenvalues i : ℝ) : ℂ) ^ w‖ ≤ ‖hermCpow hA w‖ := by
  rw [hermCpow_l2_opNorm]
  exact norm_le_pi_norm (fun j => ((hA.eigenvalues j : ℝ) : ℂ) ^ w) i

/-- On a positive definite matrix the operator norm of `A ^ w` depends on `w` only through
`Re w`, since `|λ ^ w| = λ ^ Re w` for `λ > 0`. This is the vertical-line invariance an
interpolation argument on the strip `0 ≤ Re z ≤ 1` uses. -/
theorem _root_.Matrix.PosDef.norm_hermCpow_eq_of_re_eq {A : Matrix n n ℂ} (hA : A.PosDef) {w w' : ℂ}
    (hww : w.re = w'.re) : ‖hermCpow hA.1 w‖ = ‖hermCpow hA.1 w'‖ := by
  have key : ∀ v v' : ℂ, v.re = v'.re → ‖hermCpow hA.1 v‖ ≤ ‖hermCpow hA.1 v'‖ := by
    intro v v' hvv
    refine hermCpow_l2_opNorm_le hA.1 v (norm_nonneg _) fun i => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hA.eigenvalues_pos i) v, hvv,
      ← Complex.norm_cpow_eq_rpow_re_of_pos (hA.eigenvalues_pos i) v']
    exact norm_cpow_eigenvalue_le_hermCpow_l2_opNorm hA.1 v' i
  exact le_antisymm (key w w' hww) (key w' w hww.symm)

end OperatorNorm

end Math.SpectralTheory

end
