import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceDuality
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Lower fidelity bound from monotonicity of the positive square root

Matrix star order and the L2 operator norm are local to this proof.
-/
noncomputable section
namespace Quantum.Metrics
open Matrix Quantum.Operators
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {X : Type*} [Fintype X] [Nonempty X]

/-- The lower Fuchs--van de Graaf estimate for arbitrary positive, unnormalized operators. -/
theorem half_trace_add_sub_fidelity_le_traceDistance (A B : PosSemidefOp X) :
    (A.val.trace.re + B.val.trace.re) / 2 - fidelity A B ≤ traceDistance A.val B.val := by
  classical
  obtain ⟨P, Q, hP, hQ, he, hn⟩ :=
    exists_posSemidef_sub_traceNorm_eq (A.val - B.val)
      (A.property.isHermitian.sub B.property.isHermitian)
  let C := B.val + P
  have hC : C.PosSemidef := B.property.add hP
  have hCA : A.val ≤ C := by
    apply Matrix.le_iff.mpr
    have h : C - A.val = Q := by
      dsimp [C]
      rw [sub_eq_iff_eq_add.mp he]
      abel
    rwa [h]
  have hCB : B.val ≤ C := by
    apply Matrix.le_iff.mpr
    simpa only [C, add_sub_cancel_left] using hP
  have hSA := Matrix.nonneg_iff_posSemidef.mp
    (sub_nonneg.mpr (CFC.monotone_sqrt hCA))
  have hSB := Matrix.nonneg_iff_posSemidef.mp
    (sub_nonneg.mpr (CFC.monotone_sqrt hCB))
  have hA' := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A.val)
  have hB' := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B.val)
  have h1 := (Complex.nonneg_iff.mp (hSA.trace_mul_nonneg hA')).1
  have h2 := (Complex.nonneg_iff.mp (hB'.trace_mul_nonneg hSB)).1
  have h3 := (Complex.nonneg_iff.mp (hSA.trace_mul_nonneg hSB)).1
  rw [Matrix.sub_mul, trace_sub, CFC.sqrt_mul_sqrt_self _ A.property.nonneg,
    Complex.sub_re] at h1
  rw [Matrix.mul_sub, trace_sub, CFC.sqrt_mul_sqrt_self _ B.property.nonneg,
    Complex.sub_re] at h2
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, trace_sub, trace_sub, trace_sub,
    CFC.sqrt_mul_sqrt_self _ hC.nonneg] at h3
  simp only [Complex.sub_re] at h3
  rw [trace_mul_comm (CFC.sqrt C) (CFC.sqrt A.val)] at h1
  rw [trace_mul_comm (CFC.sqrt B.val) (CFC.sqrt C)] at h2
  have hf : (CFC.sqrt A.val * CFC.sqrt B.val).trace.re ≤ fidelity A B := by
    have h := norm_trace_mul_le_opNorm_mul_traceNorm (1 : Op X)
      (CFC.sqrt A.val * CFC.sqrt B.val)
    rw [Matrix.one_mul, norm_one, one_mul] at h
    change _ ≤ traceNorm (sqrtPosSemidefOp A * sqrtPosSemidefOp B) at h
    rw [traceNorm_sqrt_mul_sqrt] at h
    exact (Complex.re_le_norm _).trans h
  have ht := congrArg (fun M : Op X => M.trace.re) he
  simp only [trace_sub, Complex.sub_re] at ht
  have hc : C.trace.re = B.val.trace.re + P.trace.re := by
    rw [show C = B.val + P from rfl, trace_add, Complex.add_re]
  rw [Complex.add_re] at hn
  unfold traceDistance
  linarith

end Quantum.Metrics
