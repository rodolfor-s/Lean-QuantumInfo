import Mathlib.Analysis.Complex.Hadamard
import QCryptLean.Math.SpectralTheory.HermitianCpow
import QCryptLean.Math.SpectralTheory.HermitianCpowAnalytic
import QCryptLean.Math.SpectralTheory.LiebThirring
import QCryptLean.Math.SpectralTheory.RpowContinuity

/-!
# The Araki–Lieb–Thirring trace inequalities

For positive semidefinite matrices `C, D` and `0 < s ≤ 1`, the fractional trace bound is

`Tr ((D ^ (s/2) · C ^ s · D ^ (s/2)) ^ (1/s)) ≤ Tr (C · D)`,

and for every natural exponent `m` the integer form is

`Tr ((C · D) ^ m) ≤ Tr (C ^ m · D ^ m)`.

Both compare real traces; neither statement asserts operator order or eigenvalue
log-majorization. The fractional theorem is the reciprocal-outer-exponent specialization
of the two-exponent Araki–Lieb–Thirring inequality. The corollary
`re_trace_rpow_sandwich_le_re_trace_mul_rpow_of_one_le` has right-hand side `Tr (C ^ (rq) D ^ (rq))`
for
`0 < r`, `1 ≤ q`. This product-of-powers bound is distinct from the general ALT comparison
with `Tr ((D ^ (1/2) C D ^ (1/2)) ^ (rq))`; neither that full comparison nor the range
`q < 1` is established by these statements.

## Proof

The fractional form is proved by Stein's interpolation argument, which is where the
complex spectral power `Math.SpectralTheory.hermCpow` is used. With `F z = A ^ z · B ^ z`
for positive definite `A, B`, `H = F(s)ᴴ F(s) = B ^ s A ^ (2s) B ^ s`, and the polar
unitary `W = F(s) · H ^ (-1/2)`, the scalar function

`g z = Tr (H ^ ((2 - z)/(2s)) · Wᴴ · F z)`

is entire, takes the value `Tr (H ^ (1/s))` at `z = s`, is bounded by `Tr (H ^ (1/s))` on
the line `Re z = 0` (where `F z` is unitary, so the diagonal entries it contributes have
modulus at most one) and by `√(Tr (H ^ (1/s))) · √(Tr (A² B²))` on the line `Re z = 1` (by
Cauchy–Schwarz against the Hilbert–Schmidt norm). Hadamard's three-lines theorem at
`z = s` then gives `Tr (H ^ (1/s)) ≤ Tr (A² B²)`, which is the inequality.

Positive definiteness is what the interpolation argument needs: the exponent group law and
the unitarity of imaginary powers both fail on a singular matrix. It is removed once, at
the fractional statement, by the regularisation `C + ε`, `D + ε` together with the
continuity of `X ↦ X ^ t` on the positive semidefinite cone
(`Math.SpectralTheory.tendsto_rpow_of_posSemidef`). The integer form is then the
specialization `s = 1/m` and needs no separate limit.

## Main statements

- `Matrix.PosDef.re_trace_rpow_sandwich_sq_le` : the interpolation core, `0 < s < 1`, positive
definite.
- `Matrix.PosDef.re_trace_rpow_sandwich_le` : Araki's fractional form at positive definite
arguments,
  `0 < s ≤ 1`.
- `re_trace_rpow_sandwich_le_of_posSemidef` : the same bound for arbitrary positive semidefinite `C,
D`,
  singular ones included.
- `re_trace_rpow_sandwich_le_re_trace_mul_rpow_of_one_le` : the two free exponents `0 < r`, `1 ≤ q`,
  `Tr ((D ^ (r/2) C ^ r D ^ (r/2)) ^ q) ≤ Tr (C ^ (rq) D ^ (rq))`.
- `re_trace_mul_pow_le_of_posSemidef` : `Tr ((C D) ^ m) ≤ Tr (C ^ m D ^ m)` for positive
  semidefinite `C, D` and every `m` — the general integer inequality.
- `re_trace_sqrt_sandwich_pow_le` : the equivalent sandwich form
  `Tr ((√D Q √D) ^ m) ≤ Tr (√(D ^ m) Q ^ m √(D ^ m))`.

## General helpers

The module also proves reusable facts it needs: an exponent-interval bound for real
powers (`rpow_le_add_rpow_of_mem_Icc`), entrywise product bounds (`norm_mul_apply_le`),
the diagonal-versus-Frobenius bound (`sum_norm_sq_diag_le_trace_conjTranspose_mul`),
unitary invariance of the Hilbert–Schmidt trace (`trace_gram_unitary_conj`,
`trace_gram_unitary_left`), strict positivity of real powers, square roots and monoid
powers of a positive definite matrix (`posDef_rpow`, `posDef_sqrt`, `posDef_pow`) and
positive semidefiniteness of the sandwich itself (`posSemidef_rpow_sandwich`).

## References

- H. Araki, *On an inequality of Lieb and Thirring*, Lett. Math. Phys. **19** (1990),
  167–170.
- K. M. R. Audenaert, *On the Araki–Lieb–Thirring inequality*, Theorem 1,
  [arXiv:math/0701129](https://arxiv.org/abs/math/0701129).
- E. H. Lieb, W. E. Thirring, in *Studies in Mathematical Physics*, Princeton (1976).
- R. Bhatia, *Matrix Analysis*, Springer (1997), §IX.2.
- E. M. Stein, G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Ch. V
  (interpolation of analytic families).
-/

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open Matrix Unitary

noncomputable section

namespace Math.SpectralTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance] Matrix.instPartialOrder Matrix.instStarOrderedRing
  Matrix.instNonnegSpectrumClass

/-! ### Helpers -/

/-- On a compact exponent interval a real power is bounded by the sum of the endpoint
powers: `x ^ t ≤ x ^ a + x ^ b` for `0 < x` and `a ≤ t ≤ b`. -/
theorem rpow_le_add_rpow_of_mem_Icc {x a b t : ℝ} (hx : 0 < x) (hat : a ≤ t) (htb : t ≤ b) :
    x ^ t ≤ x ^ a + x ^ b := by
  rcases le_total 1 x with hx1 | hx1
  · have h := Real.rpow_le_rpow_of_exponent_le hx1 htb
    have := Real.rpow_nonneg hx.le a
    linarith
  · have h := Real.rpow_le_rpow_of_exponent_ge hx hx1 hat
    have := Real.rpow_nonneg hx.le b
    linarith

omit [DecidableEq n] in
/-- Entrywise bound for a matrix product. -/
theorem norm_mul_apply_le {X Y : Matrix n n ℂ} {cx cy : ℝ}
    (hx : ∀ i j, ‖X i j‖ ≤ cx) (hy : ∀ i j, ‖Y i j‖ ≤ cy) (i j : n) :
    ‖(X * Y) i j‖ ≤ Fintype.card n * (cx * cy) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖X i k * Y k j‖ ≤ ∑ _k : n, cx * cy := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hx i k) (hy k j) (norm_nonneg _)
          ((norm_nonneg _).trans (hx i k))
    _ = Fintype.card n * (cx * cy) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [DecidableEq n] in
/-- The diagonal of a matrix is dominated by its Frobenius norm. -/
theorem sum_norm_sq_diag_le_trace_conjTranspose_mul (M : Matrix n n ℂ) :
    ∑ k, ‖M k k‖ ^ 2 ≤ (Mᴴ * M).trace.re := by
  have hexp : (Mᴴ * M).trace.re = ∑ k, ∑ l, ‖M l k‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show star (M l k) * M l k = ((‖M l k‖ ^ 2 : ℝ) : ℂ) from by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      , Complex.ofReal_re]
  rw [hexp]
  refine Finset.sum_le_sum fun k _ => ?_
  exact Finset.single_le_sum (f := fun l => ‖M l k‖ ^ 2) (fun l _ => sq_nonneg _)
    (Finset.mem_univ k)

/-- Trace of a diagonal matrix times a matrix. -/
theorem trace_diagonal_mul (d : n → ℂ) (X : Matrix n n ℂ) :
    (Matrix.diagonal d * X).trace = ∑ k, d k * X k k := by
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]

/-- Unitary conjugation preserves the Hilbert–Schmidt (Frobenius) trace. -/
theorem trace_gram_unitary_conj {U M : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) :
    ((Uᴴ * M * U)ᴴ * (Uᴴ * M * U)).trace = (Mᴴ * M).trace := by
  have h1 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hU.2
  have key : (Uᴴ * M * U)ᴴ * (Uᴴ * M * U) = Uᴴ * (Mᴴ * M) * U := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Uᴴ * (Mᴴ * U) * (Uᴴ * M * U)
        = Uᴴ * Mᴴ * (U * Uᴴ) * M * U := by simp only [Matrix.mul_assoc]
      _ = Uᴴ * Mᴴ * M * U := by rw [h1, Matrix.mul_one]
      _ = Uᴴ * (Mᴴ * M) * U := by simp only [Matrix.mul_assoc]
  rw [key, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- Left multiplication by a unitary preserves the Hilbert–Schmidt (Frobenius) trace. -/
theorem trace_gram_unitary_left {U M : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) :
    ((Uᴴ * M)ᴴ * (Uᴴ * M)).trace = (Mᴴ * M).trace := by
  have h1 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hU.2
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc (Mᴴ * U * (Uᴴ * M)).trace
      = (Mᴴ * (U * Uᴴ) * M).trace := by simp only [Matrix.mul_assoc]
    _ = (Mᴴ * M).trace := by rw [h1, Matrix.mul_one]

/-! ### The interpolation core -/

/-- **Araki's trace inequality for positive definite matrices, interpolation form.**

For positive definite `A, B` and `0 < s < 1`,
`Tr ((B ^ s A ^ (2s) B ^ s) ^ (1/s)) ≤ Tr (A ^ 2 B ^ 2)`.

The proof is Stein's interpolation argument. With `F z = A ^ z B ^ z`,
`H = F(s)ᴴ F(s) = B ^ s A ^ (2s) B ^ s` and the polar unitary `W = F(s) H ^ (-1/2)`, the
scalar test function `g z = Tr (H ^ ((2 - z)/(2s)) Wᴴ F z)` is entire, satisfies
`g s = Tr (H ^ (1/s))`, is bounded by `Tr (H ^ (1/s))` on the line `Re z = 0` (there
`F z` is unitary) and by `√(Tr (H ^ (1/s))) √(Tr (A² B²))` on the line `Re z = 1` (by
Cauchy–Schwarz). Hadamard's three-lines theorem at `z = s` then forces
`Tr (H ^ (1/s)) ≤ Tr (A² B²)`. -/
theorem _root_.Matrix.PosDef.re_trace_rpow_sandwich_sq_le {A B : Matrix n n ℂ} (hA : A.PosDef) (hB
    : B.PosDef)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (((B ^ s * A ^ (2 * s) * B ^ s) ^ (1 / s)).trace).re ≤ (A ^ 2 * B ^ 2).trace.re := by
  have hAps := hA.posSemidef
  have hBps := hB.posSemidef
  -- The analytic family `F z = A ^ z * B ^ z`.
  set F : ℂ → Matrix n n ℂ := fun z => hermCpow hA.1 z * hermCpow hB.1 z with hFdef
  -- `F` takes unitary values on the imaginary axis and units everywhere.
  have hFunit : ∀ z : ℂ, IsUnit (F z) := fun z =>
    (Matrix.PosDef.isUnit_hermCpow hA z).mul (Matrix.PosDef.isUnit_hermCpow hB z)
  have hFuni : ∀ z : ℂ, z.re = 0 → F z ∈ unitary (Matrix n n ℂ) := fun z hz =>
    Submonoid.mul_mem _ (Matrix.PosDef.hermCpow_mem_unitary hA hz)
      (Matrix.PosDef.hermCpow_mem_unitary hB hz)
  -- The sandwich `H = F(s)ᴴ F(s)` and its identification with real powers.
  have hHeq : (F (s : ℂ))ᴴ * F (s : ℂ) = B ^ s * A ^ (2 * s) * B ^ s := by
    have hconj : conj ((s : ℝ) : ℂ) = ((s : ℝ) : ℂ) := Complex.conj_ofReal s
    rw [hFdef]
    simp only
    rw [Matrix.conjTranspose_mul, Matrix.PosSemidef.conjTranspose_hermCpow hAps,
      Matrix.PosSemidef.conjTranspose_hermCpow hBps, hconj, Matrix.mul_assoc,
      ← Matrix.mul_assoc (hermCpow hA.1 ((s : ℝ) : ℂ)), Matrix.PosDef.hermCpow_add hA,
      ← Matrix.mul_assoc, Matrix.PosSemidef.hermCpow_ofReal hBps,
      show ((s : ℝ) : ℂ) + ((s : ℝ) : ℂ) = ((2 * s : ℝ) : ℂ) from by push_cast; ring,
      Matrix.PosSemidef.hermCpow_ofReal hAps]
  set H : Matrix n n ℂ := (F (s : ℂ))ᴴ * F (s : ℂ) with hHdef
  have hHpd : H.PosDef := by
    refine (Matrix.PosSemidef.posDef_iff_isUnit ?_).mpr ?_
    · exact Matrix.posSemidef_conjTranspose_mul_self _
    · exact ((hFunit (s : ℂ)).star).mul (hFunit (s : ℂ))
  have hlampos : ∀ k, 0 < hHpd.1.eigenvalues k := fun k => hHpd.eigenvalues_pos k
  set L : ℝ := ∑ k, hHpd.1.eigenvalues k ^ (1 / s) with hLdef
  have hLnonneg : 0 ≤ L :=
    Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hlampos k).le _
  -- `T = Tr (A² B²)` is a nonnegative real.
  set T : ℝ := (A ^ 2 * B ^ 2).trace.re with hTdef
  -- The goal in terms of `L`.
  have hgoalL : (((B ^ s * A ^ (2 * s) * B ^ s) ^ (1 / s)).trace).re = L := by
    rw [← hHeq, trace_posSemidef_rpow_re hHpd.posSemidef]
  rw [hgoalL]
  -- The polar unitary `W = F(s) * H ^ (-1/2)`.
  have hhalfherm : ∀ x : ℝ, (hermCpow hHpd.1 ((x : ℝ) : ℂ))ᴴ = hermCpow hHpd.1 ((x : ℝ) : ℂ) :=
    fun x => by
      rw [Matrix.PosSemidef.conjTranspose_hermCpow hHpd.posSemidef, Complex.conj_ofReal]
  set W : Matrix n n ℂ := F (s : ℂ) * hermCpow hHpd.1 ((-(1 / 2 : ℝ) : ℝ) : ℂ) with hWdef
  have hWstar : Wᴴ = hermCpow hHpd.1 ((-(1 / 2 : ℝ) : ℝ) : ℂ) * (F (s : ℂ))ᴴ := by
    rw [hWdef, Matrix.conjTranspose_mul, hhalfherm]
  have hH1 : hermCpow hHpd.1 1 = H := hermCpow_one hHpd.1
  have hWF : Wᴴ * F (s : ℂ) = hermCpow hHpd.1 (((1 / 2 : ℝ) : ℝ) : ℂ) := by
    calc Wᴴ * F (s : ℂ)
        = hermCpow hHpd.1 ((-(1 / 2 : ℝ) : ℝ) : ℂ) * H := by
          rw [hWstar, Matrix.mul_assoc, ← hHdef]
      _ = hermCpow hHpd.1 ((-(1 / 2 : ℝ) : ℝ) : ℂ) * hermCpow hHpd.1 1 := by rw [hH1]
      _ = hermCpow hHpd.1 (((-(1 / 2 : ℝ) : ℝ) : ℂ) + 1) := Matrix.PosDef.hermCpow_add hHpd _ _
      _ = hermCpow hHpd.1 (((1 / 2 : ℝ) : ℝ) : ℂ) := by
          congr 1
          push_cast
          ring
  have hWuni : W ∈ unitary (Matrix n n ℂ) := by
    have e1 : Wᴴ * W = Wᴴ * F (s : ℂ) * hermCpow hHpd.1 ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [hWdef]
      simp only [Matrix.mul_assoc]
    have h1 : star W * W = 1 := by
      rw [Matrix.star_eq_conjTranspose, e1, hWF, Matrix.PosDef.hermCpow_add hHpd,
        show (((1 / 2 : ℝ) : ℝ) : ℂ) + ((-(1 / 2 : ℝ) : ℝ) : ℂ) = 0 from by push_cast; ring]
      exact hermCpow_zero hHpd.1
    exact Unitary.mem_iff.mpr ⟨h1, mul_eq_one_comm.mp h1⟩
  -- The eigenvector unitary of `H` and the conjugated family `Y`.
  set V : Matrix n n ℂ := (hHpd.1.eigenvectorUnitary : Matrix n n ℂ) with hVdef
  have hVuni : V ∈ unitary (Matrix n n ℂ) := hHpd.1.eigenvectorUnitary.2
  have hVV : V * star V = 1 := hVuni.2
  set Y : ℂ → Matrix n n ℂ := fun z => star V * (Wᴴ * F z) * V with hYdef
  -- The affine exponent `w z = (2 - z) / (2 s)`.
  set w : ℂ → ℂ := fun z => ((-(1 / (2 * s)) : ℝ) : ℂ) * z + ((1 / s : ℝ) : ℂ) with hwdef
  have hwre : ∀ z : ℂ, (w z).re = -(1 / (2 * s)) * z.re + 1 / s := by
    intro z
    rw [hwdef]
    simp [Complex.add_re, Complex.mul_re]
  -- The scalar test function.
  set g : ℂ → ℂ := fun z => (hermCpow hHpd.1 (w z) * (Wᴴ * F z)).trace with hgdef
  -- Sum form: the eigenbasis of `H` turns the trace into a weighted diagonal sum.
  have hgsum : ∀ z : ℂ, g z = ∑ k, ((hHpd.1.eigenvalues k : ℝ) : ℂ) ^ (w z) * Y z k k := by
    intro z
    rw [hgdef]
    simp only
    rw [hermCpow, conjStarAlgAut_apply, ← hVdef,
      show V * Matrix.diagonal (fun k => ((hHpd.1.eigenvalues k : ℝ) : ℂ) ^ (w z)) * star V *
            (Wᴴ * F z)
          = V * (Matrix.diagonal (fun k => ((hHpd.1.eigenvalues k : ℝ) : ℂ) ^ (w z)) *
            (star V * (Wᴴ * F z))) from by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show Matrix.diagonal (fun k => ((hHpd.1.eigenvalues k : ℝ) : ℂ) ^ (w z)) *
            (star V * (Wᴴ * F z)) * V
          = Matrix.diagonal (fun k => ((hHpd.1.eigenvalues k : ℝ) : ℂ) ^ (w z)) *
            (star V * (Wᴴ * F z) * V) from by simp only [Matrix.mul_assoc],
      trace_diagonal_mul, hYdef]
  -- The Gram trace of the family depends only on `Re z`.
  have hgram : ∀ z : ℂ, ((F z)ᴴ * F z).trace
      = (hermCpow hA.1 (conj z + z) * hermCpow hB.1 (conj z + z)).trace := by
    intro z
    rw [hFdef]
    simp only
    rw [Matrix.conjTranspose_mul, Matrix.PosSemidef.conjTranspose_hermCpow hAps,
      Matrix.PosSemidef.conjTranspose_hermCpow hBps,
      show hermCpow hB.1 (conj z) * hermCpow hA.1 (conj z) * (hermCpow hA.1 z * hermCpow hB.1 z)
          = hermCpow hB.1 (conj z) *
            (hermCpow hA.1 (conj z) * hermCpow hA.1 z * hermCpow hB.1 z) from by
        simp only [Matrix.mul_assoc],
      Matrix.PosDef.hermCpow_add hA, Matrix.trace_mul_comm,
      show hermCpow hA.1 (conj z + z) * hermCpow hB.1 z * hermCpow hB.1 (conj z)
          = hermCpow hA.1 (conj z + z) * (hermCpow hB.1 z * hermCpow hB.1 (conj z)) from by
        simp only [Matrix.mul_assoc],
      Matrix.PosDef.hermCpow_add hB, add_comm z (conj z)]
  -- The conjugated family has the same Gram trace.
  have hYgram : ∀ z : ℂ, ((Y z)ᴴ * Y z).trace = ((F z)ᴴ * F z).trace := by
    intro z
    have hYe : Y z = Vᴴ * (Wᴴ * F z) * V := by
      rw [hYdef]
      simp only [Matrix.star_eq_conjTranspose]
    rw [hYe, trace_gram_unitary_conj hVuni, trace_gram_unitary_left hWuni]
  -- Value at `z = s`.
  have hgs : g (s : ℂ) = ((L : ℝ) : ℂ) := by
    rw [hgdef]
    simp only
    rw [hWF, Matrix.PosDef.hermCpow_add hHpd,
      show w ((s : ℝ) : ℂ) + (((1 / 2 : ℝ) : ℝ) : ℂ) = ((1 / s : ℝ) : ℂ) from by
        rw [hwdef]
        simp only
        push_cast
        field_simp
        ring,
      hermCpow_trace, hLdef, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.ofReal_cpow (hlampos k).le]
  -- Left boundary: `‖g‖ ≤ L` on `Re z = 0`.
  have hleft : ∀ z : ℂ, z.re = 0 → ‖g z‖ ≤ L := by
    intro z hz
    have hYu : Y z ∈ unitary (Matrix n n ℂ) := by
      rw [hYdef]
      simp only
      refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hVuni) ?_) hVuni
      exact Submonoid.mul_mem _ (by
        rw [Matrix.star_eq_conjTranspose] at *
        exact Unitary.star_mem hWuni) (hFuni z hz)
    rw [hgsum z]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => ?_).trans_eq hLdef.symm
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hlampos k) (w z), hwre z, hz]
    have h1 : ‖Y z k k‖ ≤ 1 := entry_norm_bound_of_unitary hYu k k
    have h2 : (0 : ℝ) ≤ hHpd.1.eigenvalues k ^ (-(1 / (2 * s)) * 0 + 1 / s) :=
      Real.rpow_nonneg (hlampos k).le _
    calc hHpd.1.eigenvalues k ^ (-(1 / (2 * s)) * 0 + 1 / s) * ‖Y z k k‖
        ≤ hHpd.1.eigenvalues k ^ (-(1 / (2 * s)) * 0 + 1 / s) * 1 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = hHpd.1.eigenvalues k ^ (1 / s) := by
          rw [mul_one, show -(1 / (2 * s)) * 0 + 1 / s = 1 / s from by ring]
  -- `T` is nonnegative: it is the trace of the positive semidefinite `B A² B`.
  have hTnn : 0 ≤ T := by
    have hPSD : (B * A ^ 2 * B).PosSemidef := by
      have h := (hAps.pow 2).mul_mul_conjTranspose_same B
      rwa [hB.1.eq] at h
    have htr : T = (B * A ^ 2 * B).trace.re := by
      rw [hTdef, show A ^ 2 * B ^ 2 = A ^ 2 * B * B from by rw [pow_two B, ← Matrix.mul_assoc],
        Matrix.trace_mul_comm (A ^ 2 * B) B, Matrix.mul_assoc]
    rw [htr]
    have := hPSD.trace_nonneg
    simpa using (Complex.le_def.mp this).1
  -- Right boundary: `‖g‖ ≤ √L √T` on `Re z = 1`.
  have hright : ∀ z : ℂ, z.re = 1 → ‖g z‖ ≤ Real.sqrt L * Real.sqrt T := by
    intro z hz
    have hre : (w z).re = 1 / (2 * s) := by
      rw [hwre z, hz]
      field_simp
      ring
    have hT' : ((Y z)ᴴ * Y z).trace.re = T := by
      rw [hYgram z, hgram z, show conj z + z = ((2 : ℝ) : ℂ) from by
          rw [add_comm, Complex.add_conj, hz]; norm_num,
        show ((2 : ℝ) : ℂ) = ((2 : ℕ) : ℂ) from by norm_num,
        hermCpow_natCast hA.1 2, hermCpow_natCast hB.1 2, hTdef]
    rw [hgsum z]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ Finset.univ, ‖((hHpd.1.eigenvalues k : ℝ) : ℂ) ^ (w z) * Y z k k‖
        = hHpd.1.eigenvalues k ^ (1 / (2 * s)) * ‖Y z k k‖ := by
      intro k _
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hlampos k) (w z), hre]
    rw [Finset.sum_congr rfl hterm]
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k => hHpd.1.eigenvalues k ^ (1 / (2 * s))) (fun k => ‖Y z k k‖)
    have hsqL : ∑ k, (hHpd.1.eigenvalues k ^ (1 / (2 * s))) ^ 2 = L := by
      rw [hLdef]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Real.rpow_natCast (hHpd.1.eigenvalues k ^ (1 / (2 * s))) 2,
        ← Real.rpow_mul (hlampos k).le]
      congr 1
      push_cast
      field_simp
    have hsqY : ∑ k, ‖Y z k k‖ ^ 2 ≤ T := by
      refine (sum_norm_sq_diag_le_trace_conjTranspose_mul (Y z)).trans ?_
      rw [hT']
    have hnn : 0 ≤ ∑ k, hHpd.1.eigenvalues k ^ (1 / (2 * s)) * ‖Y z k k‖ :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (Real.rpow_nonneg (hlampos k).le _) (norm_nonneg _)
    rw [hsqL] at hCS
    have hbound : (∑ k, hHpd.1.eigenvalues k ^ (1 / (2 * s)) * ‖Y z k k‖) ^ 2 ≤ L * T :=
      hCS.trans (mul_le_mul_of_nonneg_left hsqY hLnonneg)
    calc ∑ k, hHpd.1.eigenvalues k ^ (1 / (2 * s)) * ‖Y z k k‖
        = Real.sqrt ((∑ k, hHpd.1.eigenvalues k ^ (1 / (2 * s)) * ‖Y z k k‖) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (L * T) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt L * Real.sqrt T := Real.sqrt_mul hLnonneg T
  -- A uniform bound on the closed strip.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖g z‖ ≤ C := by
    have hentry : ∀ (X : Matrix n n ℂ) (hX : X.PosDef) (z : ℂ), 0 ≤ z.re → z.re ≤ 1 →
        ∀ i j, ‖hermCpow hX.1 z i j‖ ≤ ∑ m, (1 + hX.1.eigenvalues m) := by
      intro X hX z hz0 hz1 i j
      refine (norm_hermCpow_apply_le hX.1 z i j).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (hX.eigenvalues_pos m) z]
      have h := rpow_le_add_rpow_of_mem_Icc (x := hX.1.eigenvalues m) (a := 0) (b := 1)
        (hX.eigenvalues_pos m) hz0 hz1
      rwa [Real.rpow_zero, Real.rpow_one] at h
    set cA : ℝ := ∑ m, (1 + hA.1.eigenvalues m) with hcAdef
    set cB : ℝ := ∑ m, (1 + hB.1.eigenvalues m) with hcBdef
    have hFentry : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ∀ i j,
        ‖F z i j‖ ≤ Fintype.card n * (cA * cB) := by
      intro z hz0 hz1 i j
      simp only [hFdef]
      exact norm_mul_apply_le (hentry A hA z hz0 hz1) (hentry B hB z hz0 hz1) i j
    have hRuni : star V * Wᴴ ∈ unitary (Matrix n n ℂ) := by
      refine Submonoid.mul_mem _ (Unitary.star_mem hVuni) ?_
      rw [Matrix.star_eq_conjTranspose] at *
      exact Unitary.star_mem hWuni
    have hRentry : ∀ i j, ‖(star V * Wᴴ) i j‖ ≤ 1 := fun i j =>
      entry_norm_bound_of_unitary hRuni i j
    have hVentry : ∀ i j, ‖V i j‖ ≤ 1 := fun i j => entry_norm_bound_of_unitary hVuni i j
    have hYentry : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ∀ k, ‖Y z k k‖ ≤
        Fintype.card n * (Fintype.card n * (1 * (Fintype.card n * (cA * cB))) * 1) := by
      intro z hz0 hz1 k
      have hYeq : Y z = star V * Wᴴ * F z * V := by
        rw [hYdef]
        simp only [Matrix.mul_assoc]
      rw [hYeq]
      exact norm_mul_apply_le (norm_mul_apply_le hRentry (hFentry z hz0 hz1)) hVentry k k
    refine ⟨(∑ k, (hHpd.1.eigenvalues k ^ (1 / (2 * s)) + hHpd.1.eigenvalues k ^ (1 / s))) *
      (Fintype.card n * (Fintype.card n * (1 * (Fintype.card n * (cA * cB))) * 1)), ?_⟩
    intro z hz0 hz1
    have hcard : (0 : ℝ) ≤ Fintype.card n * (Fintype.card n * (1 *
        (Fintype.card n * (cA * cB))) * 1) := by
      have hcA0 : 0 ≤ cA := Finset.sum_nonneg fun m _ =>
        add_nonneg zero_le_one (hA.eigenvalues_pos m).le
      have hcB0 : 0 ≤ cB := Finset.sum_nonneg fun m _ =>
        add_nonneg zero_le_one (hB.eigenvalues_pos m).le
      -- a product of the nonnegative factors `#n`, `cA` and `cB`
      have hN : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
      rw [one_mul, mul_one]
      exact mul_nonneg hN (mul_nonneg hN (mul_nonneg hN (mul_nonneg hcA0 hcB0)))
    rw [hgsum z, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hlampos k) (w z)]
    have hc : 1 / s = 2 * (1 / (2 * s)) := by field_simp
    have hcpos : 0 < 1 / (2 * s) := by positivity
    have h1 : hHpd.1.eigenvalues k ^ (w z).re
        ≤ hHpd.1.eigenvalues k ^ (1 / (2 * s)) + hHpd.1.eigenvalues k ^ (1 / s) := by
      refine rpow_le_add_rpow_of_mem_Icc (hlampos k) ?_ ?_
      · -- `t ≤ -t·x + 2t` for `t = 1/(2s) > 0` and `x = Re z ≤ 1`
        have := mul_le_mul_of_nonneg_left hz1 hcpos.le
        rw [hwre z, hc]
        linarith
      · -- `-t·x + 2t ≤ 2t` for `t > 0` and `x = Re z ≥ 0`
        have := mul_nonneg hcpos.le hz0
        rw [hwre z, hc]
        linarith
    exact mul_le_mul h1 (hYentry z hz0 hz1 k) (norm_nonneg _)
      (add_nonneg (Real.rpow_nonneg (hlampos k).le _) (Real.rpow_nonneg (hlampos k).le _))
  -- `g` is entire.
  have hgdiff : Differentiable ℂ g := by
    rw [hgdef]
    refine differentiable_matrix_trace (differentiable_matrix_mul ?_ ?_)
    · refine differentiable_matrix_comp
        (hermCpow_differentiable hHpd.1 fun k => (hlampos k).ne') ?_
      rw [hwdef]
      exact ((differentiable_const _).mul differentiable_id).add_const _
    · refine differentiable_matrix_mul_left _ ?_
      rw [hFdef]
      exact differentiable_matrix_mul
        (hermCpow_differentiable hA.1 fun k => (hA.eigenvalues_pos k).ne')
        (hermCpow_differentiable hB.1 fun k => (hB.eigenvalues_pos k).ne')
  -- Hadamard's three-lines theorem at `z = s`.
  have hstrip : ((s : ℝ) : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage,
      Complex.ofReal_re, Set.mem_Icc]
    exact ⟨hs0.le, hs1.le⟩
  have hbdd : BddAbove ((norm ∘ g) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨C, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage,
      Set.mem_Icc] at hz
    exact hC z hz.1 hz.2
  have h3 := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    g hstrip hgdiff.differentiableOn.diffContOnCl hbdd
    (fun z hz => hleft z (by simpa using hz)) (fun z hz => hright z (by simpa using hz))
  rw [hgs, show ‖((L : ℝ) : ℂ)‖ = L from by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLnonneg], Complex.ofReal_re] at h3
  -- Closing algebra: `L ≤ L ^ (1 - s/2) * T ^ (s/2)` forces `L ≤ T`.
  rcases eq_or_lt_of_le hLnonneg with hL0 | hLpos
  · rw [← hL0]; exact hTnn
  · have hsplit : (Real.sqrt L * Real.sqrt T) ^ s = L ^ (s / 2) * T ^ (s / 2) := by
      rw [Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
        Real.sqrt_eq_rpow, ← Real.rpow_mul hLnonneg, ← Real.rpow_mul hTnn]
      ring_nf
    rw [hsplit] at h3
    have hpow_pos : 0 < L ^ (1 - s / 2) := Real.rpow_pos_of_pos hLpos _
    have h4 : L ^ (s / 2) * L ^ (1 - s / 2) ≤ T ^ (s / 2) * L ^ (1 - s / 2) := by
      calc L ^ (s / 2) * L ^ (1 - s / 2) = L := by
            rw [← Real.rpow_add hLpos]
            norm_num
        _ ≤ L ^ (1 - s) * (L ^ (s / 2) * T ^ (s / 2)) := h3
        _ = T ^ (s / 2) * L ^ (1 - s / 2) := by
            rw [← mul_assoc, ← Real.rpow_add hLpos]
            ring_nf
    have hkey : L ^ (s / 2) ≤ T ^ (s / 2) := le_of_mul_le_mul_right h4 hpow_pos
    have h5 : (L ^ (s / 2)) ^ (2 / s) ≤ (T ^ (s / 2)) ^ (2 / s) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hLnonneg _) hkey (by positivity)
    rwa [← Real.rpow_mul hLnonneg, ← Real.rpow_mul hTnn,
      show s / 2 * (2 / s) = 1 from by field_simp, Real.rpow_one, Real.rpow_one] at h5

/-! ### Strict positivity of real powers -/

/-- Every real power of a positive definite matrix is positive definite: it is positive
semidefinite by `CFC.rpow_nonneg`, and invertible because `A ^ t · A ^ (-t) = 1`. -/
theorem posDef_rpow {C : Matrix n n ℂ} (hC : C.PosDef) (t : ℝ) : (C ^ t).PosDef := by
  refine (Matrix.PosSemidef.posDef_iff_isUnit
    (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg)).mpr ?_
  refine IsUnit.of_mul_eq_one (b := C ^ (-t)) ?_
  rw [← CFC.rpow_add hC.isUnit, add_neg_cancel, CFC.rpow_zero _ hC.posSemidef.nonneg]

open scoped Classical in
/-- The square root of a positive definite matrix is positive definite. -/
theorem posDef_sqrt {n : Type*} [Fintype n] {C : Matrix n n ℂ} (hC : C.PosDef) :
    (CFC.sqrt C).PosDef := by
  classical
  rw [CFC.sqrt_eq_rpow]
  exact posDef_rpow hC _

/-- A positive power of a positive definite matrix is positive definite. -/
theorem posDef_pow {C : Matrix n n ℂ} (hC : C.PosDef) (m : ℕ) : (C ^ m).PosDef :=
  (Matrix.PosSemidef.posDef_iff_isUnit (hC.posSemidef.pow m)).mpr (hC.isUnit.pow m)

/-- **Fractional Araki–Lieb–Thirring inequality at positive definite arguments.**
For positive definite `C, D` and `0 < s ≤ 1`,
`Tr ((D ^ (s/2) C ^ s D ^ (s/2)) ^ (1/s)) ≤ Tr (C D)`.

At `s = 1` this is an equality by trace cyclicity. Applying it to `C ^ m, D ^ m` at
`s = 1/m` gives the positive-exponent integer comparison. This theorem assumes positive
definiteness, used for the exponent group law and imaginary-power unitarity in its
interpolation proof; singular positive semidefinite inputs are not covered. -/
theorem _root_.Matrix.PosDef.re_trace_rpow_sandwich_le {C D : Matrix n n ℂ} (hC : C.PosDef) (hD :
    D.PosDef)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (((D ^ (s / 2) * C ^ s * D ^ (s / 2)) ^ (1 / s)).trace).re ≤ (C * D).trace.re := by
  have hCn := hC.posSemidef.nonneg
  have hDn := hD.posSemidef.nonneg
  have hA : (CFC.sqrt C).PosDef := posDef_sqrt hC
  have hB : (CFC.sqrt D).PosDef := posDef_sqrt hD
  have hAs : CFC.sqrt C ^ (2 * s) = C ^ s := by
    rw [CFC.sqrt_eq_rpow, CFC.rpow_rpow_of_exponent_nonneg C (1 / 2) (2 * s) (by norm_num)
      (by positivity) hCn]
    congr 1
    ring
  have hBs : CFC.sqrt D ^ s = D ^ (s / 2) := by
    rw [CFC.sqrt_eq_rpow, CFC.rpow_rpow_of_exponent_nonneg D (1 / 2) s (by norm_num) hs0.le hDn]
    congr 1
    ring
  have hA2 : CFC.sqrt C ^ 2 = C := CFC.sq_sqrt C hCn
  have hB2 : CFC.sqrt D ^ 2 = D := CFC.sq_sqrt D hDn
  rcases eq_or_lt_of_le hs1 with hs | hs
  · -- `s = 1`: the two sides agree by trace cyclicity.
    subst hs
    have hDhalf : D ^ ((1 : ℝ) / 2) * D ^ ((1 : ℝ) / 2) = D := by
      rw [← CFC.sqrt_eq_rpow]
      exact CFC.sqrt_mul_sqrt_self D hDn
    have hherm : (D ^ ((1 : ℝ) / 2))ᴴ = D ^ ((1 : ℝ) / 2) :=
      (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg).isHermitian
    have hsand : (0 : Matrix n n ℂ) ≤ D ^ ((1 : ℝ) / 2) * C ^ (1 : ℝ) * D ^ ((1 : ℝ) / 2) := by
      have h := (Matrix.nonneg_iff_posSemidef.mp
        (CFC.rpow_nonneg (a := C) (y := (1 : ℝ)))).mul_mul_conjTranspose_same (D ^ ((1 : ℝ) / 2))
      rw [hherm] at h
      exact h.nonneg
    rw [show (1 : ℝ) / 1 = 1 from by norm_num, CFC.rpow_one _ hsand, CFC.rpow_one C hCn]
    refine le_of_eq (congrArg Complex.re ?_)
    calc (D ^ ((1 : ℝ) / 2) * C * D ^ ((1 : ℝ) / 2)).trace
        = (D ^ ((1 : ℝ) / 2) * (D ^ ((1 : ℝ) / 2) * C)).trace := Matrix.trace_mul_comm _ _
      _ = (D ^ ((1 : ℝ) / 2) * D ^ ((1 : ℝ) / 2) * C).trace := by rw [Matrix.mul_assoc]
      _ = (D * C).trace := by rw [hDhalf]
      _ = (C * D).trace := Matrix.trace_mul_comm _ _
  · have h := Matrix.PosDef.re_trace_rpow_sandwich_sq_le hA hB hs0 hs
    rwa [hAs, hBs, hA2, hB2] at h

/-- The Araki–Lieb–Thirring sandwich `D ^ v · C ^ u · D ^ v` is positive semidefinite: the
real power `C ^ u` is positive semidefinite and `D ^ v` is Hermitian, so this is a
congruence. No hypothesis on `C, D` is needed, because `CFC.rpow` lands in the positive
cone by construction (`CFC.rpow_nonneg`); the intended use is for positive semidefinite
`C, D`, where the powers are the ordinary ones. -/
theorem posSemidef_rpow_sandwich (C D : Matrix n n ℂ) (u v : ℝ) :
    (D ^ v * C ^ u * D ^ v).PosSemidef := by
  have hDv : (D ^ v)ᴴ = D ^ v :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := D) (y := v))).isHermitian
  have h := (Matrix.nonneg_iff_posSemidef.mp
    (CFC.rpow_nonneg (a := C) (y := u))).mul_mul_conjTranspose_same (D ^ v)
  rwa [hDv] at h

/-- **Fractional Araki–Lieb–Thirring inequality.** For positive semidefinite `C, D` —
singular ones included — and `0 < s ≤ 1`,
`Tr ((D ^ (s/2) C ^ s D ^ (s/2)) ^ (1/s)) ≤ Tr (C D)`.

Both exponents are real; the outer power is `CFC.rpow`, so `1/s` need not be an integer.
The proof regularises to `C + ε`, `D + ε`, applies `Matrix.PosDef.re_trace_rpow_sandwich_le` — the
interpolation argument genuinely needs a strictly positive spectrum — and lets `ε → 0`
using continuity of every real power involved on the positive semidefinite cone
(`Math.SpectralTheory.tendsto_rpow_of_posSemidef`). All three exponents `s`, `s/2` and
`1/s` are positive, which is what that continuity requires. -/
theorem re_trace_rpow_sandwich_le_of_posSemidef {C D : Matrix n n ℂ} (hC : C.PosSemidef) (hD :
    D.PosSemidef)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (((D ^ (s / 2) * C ^ s * D ^ (s / 2)) ^ (1 / s)).trace).re ≤ (C * D).trace.re := by
  have hεpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hε0 : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  set Cε : ℕ → Matrix n n ℂ :=
    fun k => C + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) • (1 : Matrix n n ℂ) with hCε
  set Dε : ℕ → Matrix n n ℂ :=
    fun k => D + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) • (1 : Matrix n n ℂ) with hDε
  have hCpd : ∀ k, (Cε k).PosDef := fun k => posDef_add_smul_one hC (hεpos k)
  have hDpd : ∀ k, (Dε k).PosDef := fun k => posDef_add_smul_one hD (hεpos k)
  have hCtend : Filter.Tendsto Cε Filter.atTop (nhds C) := tendsto_add_smul_one C hε0
  have hDtend : Filter.Tendsto Dε Filter.atTop (nhds D) := tendsto_add_smul_one D hε0
  -- the three real powers converge on the positive semidefinite cone
  have hCs : Filter.Tendsto (fun k => Cε k ^ s) Filter.atTop (nhds (C ^ s)) :=
    tendsto_rpow_of_posSemidef
      (Filter.Eventually.of_forall fun k => (hCpd k).posSemidef) hC hs0.le hCtend
  have hDs : Filter.Tendsto (fun k => Dε k ^ (s / 2)) Filter.atTop (nhds (D ^ (s / 2))) :=
    tendsto_rpow_of_posSemidef
      (Filter.Eventually.of_forall fun k => (hDpd k).posSemidef) hD (by positivity) hDtend
  have hsand : Filter.Tendsto (fun k => Dε k ^ (s / 2) * Cε k ^ s * Dε k ^ (s / 2))
      Filter.atTop (nhds (D ^ (s / 2) * C ^ s * D ^ (s / 2))) := (hDs.mul hCs).mul hDs
  have houter : Filter.Tendsto
      (fun k => (Dε k ^ (s / 2) * Cε k ^ s * Dε k ^ (s / 2)) ^ (1 / s)) Filter.atTop
      (nhds ((D ^ (s / 2) * C ^ s * D ^ (s / 2)) ^ (1 / s))) :=
    tendsto_rpow_of_posSemidef
      (Filter.Eventually.of_forall fun k =>
        posSemidef_rpow_sandwich (Cε k) (Dε k) s (s / 2))
      (posSemidef_rpow_sandwich C D s (s / 2)) (by positivity) hsand
  have htr : ∀ (f : ℕ → Matrix n n ℂ) (X : Matrix n n ℂ),
      Filter.Tendsto f Filter.atTop (nhds X) →
      Filter.Tendsto (fun k => (f k).trace.re) Filter.atTop (nhds X.trace.re) :=
    fun f X hf => Complex.continuous_re.continuousAt.tendsto.comp
      ((continuous_id.matrix_trace).continuousAt.tendsto.comp hf)
  refine le_of_tendsto_of_tendsto (htr _ _ houter) (htr _ _ (hCtend.mul hDtend))
    (Filter.Eventually.of_forall fun k => ?_)
  exact Matrix.PosDef.re_trace_rpow_sandwich_le (hCpd k) (hDpd k) hs0 hs1

/-- **Product-of-powers trace bound with outer exponent at least one.**
For positive semidefinite `C, D`, `0 < r` and `1 ≤ q`,
`Tr ((D ^ (r/2) C ^ r D ^ (r/2)) ^ q) ≤ Tr (C ^ (rq) D ^ (rq))`.

This is `re_trace_rpow_sandwich_le_of_posSemidef` applied to `C ^ (rq)`, `D ^ (rq)` at `s = 1/q`;
the
restriction `1 ≤ q` is exactly `s ≤ 1` there, while `r` is any positive real. The
right-hand side is a trace of a product of powers, rather than the power-of-sandwich
expression `Tr ((D ^ (1/2) C D ^ (1/2)) ^ (rq))` in the general Araki–Lieb–Thirring
comparison. At `q = 1/r` (so `rq = 1`) these right-hand sides agree and the statement
specializes to `re_trace_rpow_sandwich_le_of_posSemidef`. -/
theorem re_trace_rpow_sandwich_le_re_trace_mul_rpow_of_one_le {C D : Matrix n n ℂ} (hC :
    C.PosSemidef)
    (hD : D.PosSemidef) {r q : ℝ} (hr : 0 < r) (hq : 1 ≤ q) :
    (((D ^ (r / 2) * C ^ r * D ^ (r / 2)) ^ q).trace).re
      ≤ (C ^ (r * q) * D ^ (r * q)).trace.re := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hrq : (0 : ℝ) < r * q := by positivity
  have hCrq : (C ^ (r * q)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := C) (y := r * q))
  have hDrq : (D ^ (r * q)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := D) (y := r * q))
  have hs0 : (0 : ℝ) < 1 / q := by positivity
  have hs1 : 1 / q ≤ 1 := by
    rw [div_le_one hq0]
    exact hq
  have h := re_trace_rpow_sandwich_le_of_posSemidef hCrq hDrq hs0 hs1
  have hCpow : (C ^ (r * q)) ^ (1 / q) = C ^ r := by
    rw [CFC.rpow_rpow_of_exponent_nonneg C (r * q) (1 / q) hrq.le hs0.le hC.nonneg]
    congr 1
    field_simp
  have hDpow : (D ^ (r * q)) ^ (1 / q / 2) = D ^ (r / 2) := by
    rw [CFC.rpow_rpow_of_exponent_nonneg D (r * q) (1 / q / 2) hrq.le (by positivity) hD.nonneg]
    congr 1
    field_simp
  rwa [hCpow, hDpow, show (1 : ℝ) / (1 / q) = q from by field_simp] at h

/-- **Integer Araki–Lieb–Thirring trace inequality** for positive semidefinite matrices:
`Tr ((C D) ^ m) ≤ Tr (C ^ m D ^ m)`.

This asserts a trace comparison, not an operator inequality. It is the fractional theorem
at `s = 1/m`, applied to `C ^ m` and `D ^ m` and read back through trace cyclicity; the
exponent `m = 0` is the trivial identity `Tr 1 = Tr 1`.

The Golden–Thompson chain elsewhere in the library consumes only the exponents
`2ᵏ` and proves them by an independent elementary argument
(`InfoTheory.RelativeEntropy.lieb_thirring_pow_two`); this statement subsumes that one. -/
theorem re_trace_mul_pow_le_of_posSemidef {C D : Matrix n n ℂ} (hC : C.PosSemidef) (hD :
    D.PosSemidef)
    (m : ℕ) : ((C * D) ^ m).trace.re ≤ (C ^ m * D ^ m).trace.re := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hs0 : (0 : ℝ) < 1 / m := by positivity
  have hs1 : 1 / (m : ℝ) ≤ 1 := by
    rw [div_le_one hm0]
    exact_mod_cast hm
  have h := re_trace_rpow_sandwich_le_of_posSemidef (hC.pow m) (hD.pow m) hs0 hs1
  -- identify the three powers
  have hCpow : (C ^ m) ^ (1 / (m : ℝ)) = C := by
    rw [← CFC.rpow_natCast C m hC.nonneg,
      CFC.rpow_rpow_of_exponent_nonneg C (m : ℝ) (1 / m) (by positivity) (by positivity) hC.nonneg,
      show (m : ℝ) * (1 / m) = 1 from by field_simp, CFC.rpow_one C hC.nonneg]
  have hDpow : (D ^ m) ^ (1 / (m : ℝ) / 2) = D ^ ((1 : ℝ) / 2) := by
    rw [← CFC.rpow_natCast D m hD.nonneg,
      CFC.rpow_rpow_of_exponent_nonneg D (m : ℝ) (1 / m / 2) (by positivity) (by positivity)
        hD.nonneg]
    congr 1
    field_simp
  have hOuter : (1 : ℝ) / (1 / (m : ℝ)) = (m : ℝ) := by field_simp
  have hsand : (0 : Matrix n n ℂ) ≤ D ^ ((1 : ℝ) / 2) * C * D ^ ((1 : ℝ) / 2) := by
    have hh := posSemidef_rpow_sandwich C D 1 ((1 : ℝ) / 2)
    rw [CFC.rpow_one C hC.nonneg] at hh
    exact hh.nonneg
  rw [hCpow, hDpow, hOuter, CFC.rpow_natCast _ m hsand] at h
  -- cyclicity: `Tr ((D^{1/2} C D^{1/2})^m) = Tr ((C D)^m)`
  have hcyc : ((D ^ ((1 : ℝ) / 2) * C * D ^ ((1 : ℝ) / 2)) ^ m).trace = ((C * D) ^ m).trace := by
    rw [Matrix.mul_assoc, trace_pow_mul_comm (D ^ ((1 : ℝ) / 2)) (C * D ^ ((1 : ℝ) / 2)) m,
      Matrix.mul_assoc, show D ^ ((1 : ℝ) / 2) * D ^ ((1 : ℝ) / 2) = D from by
        rw [← CFC.sqrt_eq_rpow]
        exact CFC.sqrt_mul_sqrt_self D hD.nonneg]
  rw [show ((D ^ ((1 : ℝ) / 2) * C * D ^ ((1 : ℝ) / 2)) ^ m).trace.re = ((C * D) ^ m).trace.re
    from congrArg Complex.re hcyc] at h
  exact h

/-- **Integer Araki–Lieb–Thirring inequality at positive definite arguments**:
`Tr ((C · D) ^ m) ≤ Tr (C ^ m · D ^ m)`. The positive definite row of
`re_trace_mul_pow_le_of_posSemidef`, kept because the positive definite hypothesis is the one the
interpolation core and its `posDef_*` companions carry. -/
theorem _root_.Matrix.PosDef.re_trace_mul_pow_le {C D : Matrix n n ℂ} (hC : C.PosDef) (hD :
    D.PosDef)
    (m : ℕ) : ((C * D) ^ m).trace.re ≤ (C ^ m * D ^ m).trace.re :=
  re_trace_mul_pow_le_of_posSemidef hC.posSemidef hD.posSemidef m

/-- **Araki–Lieb–Thirring trace inequality, sandwich form**: for positive semidefinite
`D, Q`, `Tr ((√D Q √D) ^ m) ≤ Tr (√(D ^ m) Q ^ m √(D ^ m))`.

Equivalent to `re_trace_mul_pow_le_of_posSemidef` by trace cyclicity: the sandwich and the product
have the same powered trace. -/
theorem re_trace_sqrt_sandwich_pow_le {D Q : Matrix n n ℂ} (hD : D.PosSemidef) (hQ : Q.PosSemidef)
    (m : ℕ) :
    ((CFC.sqrt D * Q * CFC.sqrt D) ^ m).trace.re
      ≤ (CFC.sqrt (D ^ m) * Q ^ m * CFC.sqrt (D ^ m)).trace.re := by
  have h := re_trace_mul_pow_le_of_posSemidef hQ hD m
  have hl : ((CFC.sqrt D * Q * CFC.sqrt D) ^ m).trace = ((Q * D) ^ m).trace := by
    rw [Matrix.mul_assoc, trace_pow_mul_comm (CFC.sqrt D) (Q * CFC.sqrt D) m, Matrix.mul_assoc,
      CFC.sqrt_mul_sqrt_self D hD.nonneg]
  have hr : (CFC.sqrt (D ^ m) * Q ^ m * CFC.sqrt (D ^ m)).trace = (Q ^ m * D ^ m).trace := by
    calc (CFC.sqrt (D ^ m) * Q ^ m * CFC.sqrt (D ^ m)).trace
        = (CFC.sqrt (D ^ m) * (CFC.sqrt (D ^ m) * Q ^ m)).trace := Matrix.trace_mul_comm _ _
      _ = (CFC.sqrt (D ^ m) * CFC.sqrt (D ^ m) * Q ^ m).trace := by rw [Matrix.mul_assoc]
      _ = (D ^ m * Q ^ m).trace := by rw [CFC.sqrt_mul_sqrt_self _ (hD.pow m).nonneg]
      _ = (Q ^ m * D ^ m).trace := Matrix.trace_mul_comm _ _
  rw [show ((CFC.sqrt D * Q * CFC.sqrt D) ^ m).trace.re = ((Q * D) ^ m).trace.re from
      congrArg Complex.re hl,
    show (CFC.sqrt (D ^ m) * Q ^ m * CFC.sqrt (D ^ m)).trace.re = (Q ^ m * D ^ m).trace.re from
      congrArg Complex.re hr]
  exact h

end Math.SpectralTheory

end
