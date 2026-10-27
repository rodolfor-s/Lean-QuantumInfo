import QCryptLean.Math.LinearAlgebra.Matrix.PositiveEntries
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Principal Submatrix -/


namespace Quantum.Operators

open scoped ComplexOrder

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Restrict a state to distinct principal coordinates, retaining the resulting trace deficit. -/
def SubDensityOp.submatrix (ρ : SubDensityOp X) (f : Y → X) (hf : Function.Injective f) :
    SubDensityOp Y where
  toOp := ρ.toOp.submatrix f f
  posSemidef := ρ.posSemidef.submatrix f
  trace_le_one := (ρ.posSemidef.re_trace_submatrix_le f hf).trans ρ.trace_le_one

end Quantum.Operators
