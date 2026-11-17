import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Positive Entries -/


namespace Matrix

open scoped ComplexOrder

variable {X : Type*}

/-- The squared norm of a positive matrix entry is bounded by its two diagonal entries. -/
theorem PosSemidef.norm_apply_sq_le_diag_mul {A : Matrix X X ℂ}
    (hA : A.PosSemidef) (i j : X) : ‖A i j‖ ^ 2 ≤ (A i i).re * (A j j).re := by
  have hi : (A i i).im = 0 := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).2.symm
  have hj : (A j j).im = 0 := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := j))).2.symm
  have hc : A j i = star (A i j) := (hA.isHermitian.apply j i).symm
  have hd := (Complex.nonneg_iff.mp (hA.submatrix ![i, j]).det_nonneg).1
  simp only [det_fin_two, submatrix_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at hd
  rw [hc] at hd
  simp only [Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, hi, hj, zero_mul, sub_zero, mul_neg, sub_neg_eq_add] at hd
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  linarith

/-- A positive matrix of real trace at most one has all entries in the complex unit ball. -/
theorem PosSemidef.norm_apply_le_one_of_trace_re_le_one [Fintype X] {A : Matrix X X ℂ}
    (hA : A.PosSemidef) (htr : A.trace.re ≤ 1) (i j : X) : ‖A i j‖ ≤ 1 := by
  have hn (k : X) : 0 ≤ (A k k).re := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := k))).1
  have hb (k : X) : (A k k).re ≤ 1 := by
    refine le_trans ?_ htr
    rw [trace, Complex.re_sum]
    exact Finset.single_le_sum (fun l _ => hn l) (Finset.mem_univ k)
  have hs := hA.norm_apply_sq_le_diag_mul i j
  have hmul := mul_le_mul (hb i) (hb j) (hn j) zero_le_one
  nlinarith [norm_nonneg (A i j)]

/-- Restriction to distinct principal coordinates cannot increase the real trace. -/
theorem PosSemidef.re_trace_submatrix_le [Fintype X] {Y : Type*} [Fintype Y]
    {A : Matrix X X ℂ} (hA : A.PosSemidef) (f : Y → X) (hf : Function.Injective f) :
    (A.submatrix f f).trace.re ≤ A.trace.re := by
  classical
  simp only [trace, diag, submatrix_apply, Complex.re_sum]
  calc
    (∑ y, (A (f y) (f y)).re) =
        ∑ x ∈ Finset.univ.map ⟨f, hf⟩, (A x x).re := by rw [Finset.sum_map]; rfl
    _ ≤ ∑ x, (A x x).re := Finset.sum_le_univ_sum_of_nonneg
      fun x => (Complex.nonneg_iff.mp (hA.diag_nonneg (i := x))).1

end Matrix
