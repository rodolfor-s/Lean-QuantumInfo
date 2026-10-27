import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.Matrix.SqrtScale
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Basic -/


noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The trace norm of an arbitrary operator, as the sum of its singular values. -/
def traceNorm (A : Op X) : ℝ := by
  classical
  exact ∑ i, Real.sqrt ((isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- Half the trace norm of the difference, on all operators. -/
def traceDistance (A B : Op X) : ℝ := (1 / 2) * traceNorm (A - B)

/-- The Hermitian trace norm, expressed using absolute eigenvalues. -/
def traceNormHermitian (A : Op X) (hA : A.IsHermitian) : ℝ := by
  classical
  exact ∑ i, |hA.eigenvalues i|

/-- The PSD square root, using matrix star order and Hermitian functional calculus. -/
def sqrtPosSemidefOp (A : PosSemidefOp X) : Op X := by
  classical
  exact CFC.sqrt A.val

/-- Unsquared Uhlmann fidelity of positive operators. -/
def fidelity (A B : PosSemidefOp X) : ℝ := by
  classical
  exact (CFC.sqrt (sqrtPosSemidefOp A * B.val * sqrtPosSemidefOp A)).trace.re

/-- Squared Uhlmann fidelity. -/
def fidelitySq (A B : PosSemidefOp X) : ℝ := fidelity A B ^ 2

/-- Generalized trace distance, including the missing-trace contribution. -/
def traceDistanceGen (A B : Op X) : ℝ :=
  traceDistance A B + (1 / 2) * |(A.trace - B.trace).re|

/-- Generalized fidelity of subnormalized states. -/
def fidelityGen (ρ σ : SubDensityOp X) : ℝ :=
  fidelity ρ.toPosSemidefOp σ.toPosSemidefOp +
    Real.sqrt ((1 - ρ.trace) * (1 - σ.trace))

/-- Purified distance of subnormalized states. -/
def purifiedDistance (ρ σ : SubDensityOp X) : ℝ :=
  Real.sqrt (1 - fidelityGen ρ σ ^ 2)

open scoped Classical in
/-- The singular-value sum is the real trace of the positive square root of the Gram matrix. -/
theorem traceNorm_eq_trace_sqrt (A : Op X) :
    traceNorm A = (CFC.sqrt (Aᴴ * A)).trace.re := by
  classical
  rw [CFC.sqrt_eq_real_sqrt _ (posSemidef_conjTranspose_mul_self A).nonneg,
    cfcₙ_eq_cfc (hf0 := Real.sqrt_zero),
    (isHermitian_conjTranspose_mul_self A).trace_cfc, Complex.re_sum]
  rfl

/-- The trace norm is absolutely homogeneous under complex scalars. -/
theorem traceNorm_smul (c : ℂ) (A : Op X) :
    traceNorm (c • A) = ‖c‖ * traceNorm A := by
  classical
  rw [traceNorm_eq_trace_sqrt, traceNorm_eq_trace_sqrt, conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  change (CFC.sqrt (((starRingEnd ℂ) c * c) • (Aᴴ * A))).trace.re = _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    (posSemidef_conjTranspose_mul_self A).sqrt_ofReal_smul (sq_nonneg _),
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Real.sqrt_sq (norm_nonneg _)]

/-- Singular values are nonnegative, including on the empty register. -/
theorem traceNorm_nonneg (A : Op X) : 0 ≤ traceNorm A :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- Trace distance is nonnegative on all operators. -/
theorem traceDistance_nonneg (A B : Op X) : 0 ≤ traceDistance A B :=
  mul_nonneg (by norm_num) (traceNorm_nonneg _)

/-- The zero operator has zero trace norm. -/
@[simp] theorem traceNorm_zero : traceNorm (0 : Op X) = 0 := by
  classical
  simp only [traceNorm, conjTranspose_zero, mul_zero]
  have h := (isHermitian_zero (n := X) (α := ℂ)).eigenvalues_eq_zero_iff.mpr rfl
  simp [h]

/-- Simultaneous relabelling preserves the trace norm. -/
theorem traceNorm_reindex (e : X ≃ Y) (A : Op X) :
    traceNorm (Matrix.reindex e e A) = traceNorm A := by
  classical
  have hprod : (Matrix.reindex e e A)ᴴ * Matrix.reindex e e A =
      Matrix.reindex e e (Aᴴ * A) := by
    simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  unfold traceNorm
  have h := (isHermitian_conjTranspose_mul_self A).eigenvalueMultiset_reindex e
  have h' : (isHermitian_conjTranspose_mul_self (Matrix.reindex e e A)).eigenvalueMultiset =
      (isHermitian_conjTranspose_mul_self A).eigenvalueMultiset := by
    simpa only [hprod] using h
  have hs := congrArg (fun s : Multiset ℝ => (s.map Real.sqrt).sum) h'
  simpa [IsHermitian.eigenvalueMultiset, Multiset.map_map] using hs

/-- Relabelling preserves the trace distance. -/
theorem traceDistance_reindex (e : X ≃ Y) (A B : Op X) :
    traceDistance (Matrix.reindex e e A) (Matrix.reindex e e B) = traceDistance A B := by
  unfold traceDistance
  change (1 / 2) * traceNorm (Matrix.reindex e e (A - B)) = _
  rw [traceNorm_reindex]

/-- The positive square root is Hermitian. -/
theorem isHermitian_sqrtPosSemidefOp (A : PosSemidefOp X) :
    (sqrtPosSemidefOp A).IsHermitian := by
  classical
  exact (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A.val)).isHermitian

/-- Squaring the positive square root recovers its argument. -/
theorem sqrtPosSemidefOp_mul_self (A : PosSemidefOp X) :
    sqrtPosSemidefOp A * sqrtPosSemidefOp A = A.val := by
  classical
  exact CFC.sqrt_mul_sqrt_self A.val A.property.nonneg

/-- Positive square roots commute with register relabelling. -/
theorem sqrtPosSemidefOp_reindex (e : X ≃ Y) (A : PosSemidefOp X) :
    sqrtPosSemidefOp (A.reindex e) = Matrix.reindex e e (sqrtPosSemidefOp A) := by
  classical
  exact (Matrix.reindex_cfcSqrt A.property e).symm

/-- Uhlmann fidelity is nonnegative. -/
theorem fidelity_nonneg (A B : PosSemidefOp X) : 0 ≤ fidelity A B := by
  classical
  exact (Complex.nonneg_iff.mp
    (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).trace_nonneg).1

/-- Fidelity is unchanged by a simultaneous relabelling. -/
theorem fidelity_reindex (e : X ≃ Y) (A B : PosSemidefOp X) :
    fidelity (A.reindex e) (B.reindex e) = fidelity A B := by
  classical
  have hp : (sqrtPosSemidefOp A * B.val * sqrtPosSemidefOp A).PosSemidef := by
    simpa only [(isHermitian_sqrtPosSemidefOp A).eq] using
      B.property.mul_mul_conjTranspose_same (sqrtPosSemidefOp A)
  unfold fidelity
  rw [sqrtPosSemidefOp_reindex]
  change (CFC.sqrt (reindex e e (sqrtPosSemidefOp A) * reindex e e B.val *
    reindex e e (sqrtPosSemidefOp A))).trace.re = _
  simp only [reindex_apply, submatrix_mul_equiv]
  rw [← reindex_apply, ← Matrix.reindex_cfcSqrt hp e, Matrix.reindex_trace]

/-- Generalized fidelity is nonnegative. -/
theorem fidelityGen_nonneg (ρ σ : SubDensityOp X) : 0 ≤ fidelityGen ρ σ :=
  add_nonneg (fidelity_nonneg _ _) (Real.sqrt_nonneg _)

/-- Purified distance is nonnegative. -/
theorem purifiedDistance_nonneg (ρ σ : SubDensityOp X) : 0 ≤ purifiedDistance ρ σ :=
  Real.sqrt_nonneg _

/-- Purified distance is at most one. -/
theorem purifiedDistance_le_one (ρ σ : SubDensityOp X) : purifiedDistance ρ σ ≤ 1 := by
  exact (Real.sqrt_le_one).mpr (sub_le_self _ (sq_nonneg _))

/-- The trace norm adds over two diagonal blocks, with arbitrary finite register types. -/
theorem traceNorm_fromBlocks_zero (A : Op X) (B : Op Y) :
    traceNorm (Matrix.fromBlocks A 0 0 B) = traceNorm A + traceNorm B := by
  classical
  rw [traceNorm_eq_trace_sqrt, traceNorm_eq_trace_sqrt A, traceNorm_eq_trace_sqrt B,
    fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply]
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [(posSemidef_conjTranspose_mul_self A).sqrt_fromBlocks_zero
    (posSemidef_conjTranspose_mul_self B)]
  simp [Matrix.trace, Fintype.sum_sum_type]
/-- Fidelity adds over two diagonal blocks on arbitrary finite registers. -/
theorem fidelity_fromBlocks_zero (A B : PosSemidefOp X) (C D : PosSemidefOp Y) :
    fidelity ⟨fromBlocks A.val 0 0 C.val, A.property.fromBlocks_zero C.property⟩
      ⟨fromBlocks B.val 0 0 D.val, B.property.fromBlocks_zero D.property⟩ =
      fidelity A B + fidelity C D := by
  classical
  have hAB : (CFC.sqrt A.val * B.val * CFC.sqrt A.val).PosSemidef := by
    simpa only [(nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A.val)).isHermitian.eq] using
      B.property.mul_mul_conjTranspose_same (CFC.sqrt A.val)
  have hCD : (CFC.sqrt C.val * D.val * CFC.sqrt C.val).PosSemidef := by
    simpa only [(nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.val)).isHermitian.eq] using
      D.property.mul_mul_conjTranspose_same (CFC.sqrt C.val)
  unfold fidelity sqrtPosSemidefOp
  rw [A.property.sqrt_fromBlocks_zero C.property, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [hAB.sqrt_fromBlocks_zero hCD]
  simp [Matrix.trace, Fintype.sum_sum_type]

end Quantum.Metrics
