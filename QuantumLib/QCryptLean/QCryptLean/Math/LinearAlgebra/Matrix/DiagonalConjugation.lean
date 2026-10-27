import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Diagonal entries and trace pairings of unitary conjugates -/
namespace Matrix
/-- The squared moduli in row `i` sum to the real diagonal entry of `T * T†`. -/
lemma sum_normSq_row_eq_diag_mul_conjTranspose {m n : Type*} [Fintype n]
    (T : Matrix m n ℂ) (i : m) :
    ∑ j, Complex.normSq (T i j) = ((T * T.conjTranspose) i i).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The squared moduli in column `j` sum to the real diagonal entry of `T† * T`. -/
lemma sum_normSq_col_eq_diag_conjTranspose_mul {m n : Type*} [Fintype m]
    (T : Matrix m n ℂ) (j : n) :
    ∑ i, Complex.normSq (T i j) = ((T.conjTranspose * T) j j).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Conjugating a real diagonal matrix by `T` turns diagonal entries into
weighted sums with weights `|T i j|²`. -/
lemma conj_diagonal_diag_eq_sum_normSq {m n : Type*} [Fintype n]
    [DecidableEq n] (T : Matrix m n ℂ) (diag : n → ℝ) (i : m) :
    ((T * Matrix.diagonal (fun j => (diag j : ℂ)) * T.conjTranspose) i i).re =
      ∑ j, Complex.normSq (T i j) * diag j := by
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  have h_simp : ∀ x,
      (∑ x_1, T i x_1 * (if x_1 = x then (diag x_1 : ℂ) else 0)) =
      T i x * (diag x : ℂ) := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hyx; simp [hyx]
    · intro hx; exact (hx (Finset.mem_univ x)).elim
  have h_sum_eq :
      (∑ x, (∑ x_1, T i x_1 * (if x_1 = x then (diag x_1 : ℂ) else 0)) *
        star (T i x)) =
      ∑ x, T i x * (diag x : ℂ) * star (T i x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [h_simp x]
  rw [h_sum_eq, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The real part of the trace against a real diagonal matrix only depends on the
    real parts of the diagonal entries. -/
lemma trace_mul_real_diagonal_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (d : ι → ℝ) :
    (M * Matrix.diagonal (fun j => (d j : ℂ))).trace.re =
      ∑ j, (M j j).re * d j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  · intro b _ hbj
    simp [hbj]
  · simp

/-- Conjugating a real diagonal matrix by `U` turns the trace pairing with `M`
into the diagonal pairing in the `U`-basis. -/
lemma trace_mul_conj_real_diagonal_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M U : Matrix ι ι ℂ) (d : ι → ℝ) :
    (M * (U * Matrix.diagonal (RCLike.ofReal ∘ d) * U.conjTranspose)).trace.re =
      ∑ i, ((U.conjTranspose * M * U) i i).re * d i := by
  have h1 : M * (U * Matrix.diagonal (RCLike.ofReal ∘ d) * U.conjTranspose) =
      (M * U) * (Matrix.diagonal (RCLike.ofReal ∘ d) * U.conjTranspose) := by
    simp [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  have h2 : Matrix.diagonal (RCLike.ofReal ∘ d) * U.conjTranspose * (M * U) =
      Matrix.diagonal (RCLike.ofReal ∘ d) * (U.conjTranspose * M * U) := by
    simp [Matrix.mul_assoc]
  rw [h2]
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Function.comp]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_comm]


end Matrix
