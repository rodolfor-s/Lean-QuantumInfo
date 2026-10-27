import QCryptLean.Math.LinearAlgebra.Matrix.TraceBound
import QCryptLean.Math.LinearAlgebra.Matrix.UnitaryGram
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification

/-!
# Trace duality and rectangular purification overlaps

Only this file's operator-norm bounds select `Matrix.Norms.L2Operator`, locally.
The trace norm itself is the explicit singular-value function. Positive square
roots use matrix star order. Frobenius instances in importing modules are unchanged.
-/

noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {X R : Type*} [Fintype X] [Fintype R]

open Classical in
/-- The trace pairing is bounded by L2 operator norm times trace norm. -/
theorem norm_trace_mul_le_opNorm_mul_traceNorm [Nonempty X] (W A : Op X) :
    ‖(W * A).trace‖ ≤ ‖W‖ * traceNorm A := by
  classical
  obtain ⟨U, he⟩ := Matrix.exists_unitary_mul_eq_sqrt_gram A
  have hA : A = U.valᴴ * CFC.sqrt (Aᴴ * A) := by
    rw [← he, ← Matrix.mul_assoc, show U.valᴴ * U.val = 1 from U.property.1, Matrix.one_mul]
  have hn : ‖W * U.valᴴ‖ ≤ ‖W‖ := by
    calc
      _ ≤ ‖W‖ * ‖U.valᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖W‖ := by
        rw [Matrix.l2_opNorm_conjTranspose, CStarRing.norm_of_mem_unitary U.property, mul_one]
  calc
    ‖(W * A).trace‖ = ‖(W * U.valᴴ * CFC.sqrt (Aᴴ * A)).trace‖ := by
      conv_lhs => rw [hA]
      rw [Matrix.mul_assoc]
    _ ≤ ‖W * U.valᴴ‖ * (CFC.sqrt (Aᴴ * A)).trace.re :=
      (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).norm_trace_mul_le _
    _ ≤ ‖W‖ * traceNorm A := by
      rw [← traceNorm_eq_trace_sqrt]
      exact mul_le_mul_of_nonneg_right hn (traceNorm_nonneg A)

/-- Fidelity is the trace norm of the product of the positive square roots. -/
theorem traceNorm_sqrt_mul_sqrt (A B : PosSemidefOp X) :
    traceNorm (sqrtPosSemidefOp A * sqrtPosSemidefOp B) = fidelity A B := by
  classical
  rw [← traceNorm_conjTranspose, traceNorm_eq_trace_sqrt, conjTranspose_conjTranspose,
    conjTranspose_mul, (isHermitian_sqrtPosSemidefOp A).eq,
    (isHermitian_sqrtPosSemidefOp B).eq]
  rw [Matrix.mul_assoc (sqrtPosSemidefOp A), ← Matrix.mul_assoc (sqrtPosSemidefOp B),
    sqrtPosSemidefOp_mul_self, ← Matrix.mul_assoc]
  rfl

/-- Rectangular purifying matrices have overlap bounded by fidelity of their left Grams. -/
theorem norm_trace_conjTranspose_mul_le_fidelity [Nonempty X]
    (A B : Matrix X R ℂ) :
    ‖(Aᴴ * B).trace‖ ≤ fidelity ⟨A * Aᴴ, posSemidef_self_mul_conjTranspose A⟩
      ⟨B * Bᴴ, posSemidef_self_mul_conjTranspose B⟩ := by
  classical
  obtain ⟨U, hA, hU⟩ := Matrix.exists_sqrt_gram_mul_contraction A
  obtain ⟨V, hB, hV⟩ := Matrix.exists_sqrt_gram_mul_contraction B
  let P : PosSemidefOp X := ⟨A * Aᴴ, posSemidef_self_mul_conjTranspose A⟩
  let Q : PosSemidefOp X := ⟨B * Bᴴ, posSemidef_self_mul_conjTranspose B⟩
  have hn : ‖V * Uᴴ‖ ≤ 1 := by
    apply (Matrix.l2_opNorm_mul _ _).trans
    rw [Matrix.l2_opNorm_conjTranspose]
    exact (mul_le_mul_of_nonneg_right hV (norm_nonneg _)).trans (by simpa using hU)
  have he : (Aᴴ * B).trace = (V * Uᴴ *
      (sqrtPosSemidefOp P * sqrtPosSemidefOp Q)).trace := by
    calc
      _ = ((sqrtPosSemidefOp P * U)ᴴ * (sqrtPosSemidefOp Q * V)).trace := by
        conv_lhs => rw [hA, hB]
        rfl
      _ = _ := by
        rw [conjTranspose_mul, (isHermitian_sqrtPosSemidefOp P).eq]
        simp only [← Matrix.mul_assoc]
        rw [Matrix.trace_mul_cycle]
        simp only [Matrix.mul_assoc]
  rw [he]
  exact (norm_trace_mul_le_opNorm_mul_traceNorm _ _).trans
    ((mul_le_of_le_one_left (traceNorm_nonneg _) hn).trans_eq (traceNorm_sqrt_mul_sqrt P Q))

/-- Arbitrary finite ancillas obey the purification overlap bound. -/
theorem norm_overlap_le_fidelity [Nonempty X] (A B : PosSemidefOp X)
    (v w : Ket (X × R)) (hv : partialTraceRight v.projector = A.val)
    (hw : partialTraceRight w.projector = B.val) :
    ‖(v.dag * w : ℂ)‖ ≤ fidelity A B := by
  classical
  let V : Matrix X R ℂ := fun i r => v.vec (i, r)
  let W : Matrix X R ℂ := fun i r => w.vec (i, r)
  have hV : V * Vᴴ = A.val := hv
  have hW : W * Wᴴ = B.val := hw
  have he := norm_trace_conjTranspose_mul_le_fidelity V W
  have hp : (⟨V * Vᴴ, posSemidef_self_mul_conjTranspose V⟩ : PosSemidefOp X) = A :=
    Subtype.ext hV
  have hq : (⟨W * Wᴴ, posSemidef_self_mul_conjTranspose W⟩ : PosSemidefOp X) = B :=
    Subtype.ext hW
  rw [hp, hq, ← Ket.vectorize_inner] at he
  exact he


end Quantum.Metrics
