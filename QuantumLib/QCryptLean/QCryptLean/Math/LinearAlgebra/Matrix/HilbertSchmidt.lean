import QCryptLean.Math.LinearAlgebra.Matrix.TraceBound

/-! # Hilbert–Schmidt trace pairing on rectangular matrices

Only scalar complex norms occur; no matrix norm instance is selected.
-/

namespace Matrix

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The real trace of a row Gram matrix is the sum of the squared entry norms. -/
theorem trace_mul_conjTranspose_re_eq_sum_norm_sq (A : Matrix X Y ℂ) :
    (A * Aᴴ).trace.re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  simp only [Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- Hilbert–Schmidt Cauchy–Schwarz for rectangular trace pairing. -/
theorem norm_trace_mul_sq_le_trace_mul_trace_conjTranspose
    (A : Matrix X Y ℂ) (B : Matrix Y X ℂ) :
    ‖(A * B).trace‖ ^ 2 ≤ (A * Aᴴ).trace.re * (Bᴴ * B).trace.re := by
  have hexpand : (A * B).trace = ∑ p : X × Y, A p.1 p.2 * B p.2 p.1 := by
    simp only [trace, diag, mul_apply, Fintype.sum_prod_type]
  have htri : ‖(A * B).trace‖ ≤ ∑ p : X × Y, ‖A p.1 p.2‖ * ‖B p.2 p.1‖ := by
    rw [hexpand]
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun p : X × Y =>
      A p.1 p.2 * B p.2 p.1)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : X × Y => ‖A p.1 p.2‖) (fun p : X × Y => ‖B p.2 p.1‖)
  have hB : (Bᴴ * B).trace.re = ∑ p : X × Y, ‖B p.2 p.1‖ ^ 2 := by
    rw [trace_mul_comm, trace_mul_conjTranspose_re_eq_sum_norm_sq,
      Fintype.sum_prod_type, Finset.sum_comm]
  apply (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans
  rw [trace_mul_conjTranspose_re_eq_sum_norm_sq, hB]
  simpa only [Fintype.sum_prod_type] using hCS

end Matrix
