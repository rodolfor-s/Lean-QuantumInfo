import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Isometry Conjugation -/


namespace Quantum.Operators

open Matrix
open scoped ComplexOrder

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]

/-- Conjugate a subnormalized state by a rectangular isometry. -/
def SubDensityOp.isometryConjugate (ρ : SubDensityOp X) (V : Matrix Y X ℂ)
    (hV : Vᴴ * V = 1) : SubDensityOp Y where
  toOp := V * ρ.toOp * Vᴴ
  posSemidef := ρ.posSemidef.mul_mul_conjTranspose_same V
  trace_le_one := by
    rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]
    exact ρ.trace_le_one

/-- Rectangular isometric conjugation preserves the trace deficit. -/
theorem SubDensityOp.trace_isometryConjugate (ρ : SubDensityOp X) (V : Matrix Y X ℂ)
    (hV : Vᴴ * V = 1) : (ρ.isometryConjugate V hV).trace = ρ.trace := by
  change (V * ρ.toOp * Vᴴ).trace.re = _
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]
  rfl

end Quantum.Operators
