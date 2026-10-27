import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-!
# Orthogonal projectors and subnormalized projection

The projector predicate stores Hermiticity and idempotence. The trace estimate
uses a positive matrix product; comparison remains the real quadratic-form
predicate `OpLe`, with no new global order or norm instances.
-/

namespace Quantum.Operators

open Matrix
open scoped ComplexOrder

variable {X : Type*} [Fintype X]

/-- An orthogonal projector is a Hermitian idempotent operator. -/
structure IsOrthogonalProjector (P : Op X) : Prop where
  /-- The projector is Hermitian. -/
  isHermitian : P.IsHermitian
  /-- Applying the projector twice has the same effect as applying it once. -/
  idempotent : P * P = P

/-- A Hermitian idempotent is positive. -/
theorem IsOrthogonalProjector.posSemidef {P : Op X} (hP : IsOrthogonalProjector P) :
    P.PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self P
  rwa [hP.isHermitian.eq, hP.idempotent] at h

/-- The complementary projector is positive. -/
theorem IsOrthogonalProjector.posSemidef_one_sub [DecidableEq X]
    {P : Op X} (hP : IsOrthogonalProjector P) : ((1 : Op X) - P).PosSemidef := by
  apply IsOrthogonalProjector.posSemidef
  refine ⟨isHermitian_one.sub hP.isHermitian, ?_⟩
  rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, hP.idempotent]
  abel

/-- Projecting a positive operator cannot increase its real trace. -/
theorem IsOrthogonalProjector.re_trace_sandwich_le {P A : Op X}
    (hP : IsOrthogonalProjector P) (hA : A.PosSemidef) :
    (P * A * P).trace.re ≤ A.trace.re := by
  classical
  have h := (Complex.nonneg_iff.mp (hP.posSemidef_one_sub.trace_mul_nonneg hA)).1
  rw [sub_mul, one_mul, trace_sub, Complex.sub_re] at h
  rw [trace_mul_cycle, hP.idempotent]
  linarith

/-- An orthogonal projection preserves positivity and the subnormalization bound. -/
def SubDensityOp.projectorSandwich (ρ : SubDensityOp X) (P : Op X)
    (hP : IsOrthogonalProjector P) : SubDensityOp X where
  toOp := P * ρ.toOp * P
  posSemidef := by
    simpa only [hP.isHermitian.eq] using ρ.posSemidef.mul_mul_conjTranspose_same P
  trace_le_one := (hP.re_trace_sandwich_le ρ.posSemidef).trans ρ.trace_le_one

end Quantum.Operators
