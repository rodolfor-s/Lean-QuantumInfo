import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-!
# Completing a subnormalized state with an abort outcome

The added outcome is a singleton summand of the basis type. The construction is
entrywise block diagonal and uses no enumeration, matrix order, or matrix norm.
-/

namespace Quantum.Operators

open Matrix
open scoped ComplexOrder

variable {X : Type*} [Fintype X]

/-- The nonnegative mass missing from a subnormalized state. -/
def SubDensityOp.defect (ρ : SubDensityOp X) : ℂ := ((1 - ρ.trace : ℝ) : ℂ)

/-- Place the live state and its missing mass in separate summands. -/
def SubDensityOp.extendOp (ρ : SubDensityOp X) : Op (X ⊕ Unit) :=
  Matrix.fromBlocks ρ.toOp 0 0 (ρ.defect • (1 : Op Unit))

/-- The block extension is positive, including for an empty live register. -/
theorem SubDensityOp.posSemidef_extendOp (ρ : SubDensityOp X) : ρ.extendOp.PosSemidef :=
  Matrix.PosSemidef.fromBlocks_zero ρ.posSemidef
    (Matrix.PosSemidef.one.smul (Complex.nonneg_iff.mpr
      ⟨sub_nonneg.mpr ρ.trace_le_one, rfl⟩))

/-- The abort outcome supplies exactly the missing trace. -/
theorem SubDensityOp.trace_extendOp (ρ : SubDensityOp X) : ρ.extendOp.trace = 1 := by
  have htr : ρ.toOp.trace = (ρ.trace : ℂ) := by
    apply Complex.ext
    · rfl
    · exact ρ.trace_im
  change (∑ i : X ⊕ Unit, ρ.extendOp i i) = 1
  rw [Fintype.sum_sum_type]
  change ρ.toOp.trace + ∑ i : Unit, ρ.defect * (1 : Op Unit) i i = 1
  simp [htr, SubDensityOp.defect]

/-- Complete a subnormalized state to a normalized state on the sum register. -/
def SubDensityOp.toDensityOpExtend (ρ : SubDensityOp X) : DensityOp (X ⊕ Unit) where
  toOp := ρ.extendOp
  posSemidef := ρ.posSemidef_extendOp
  trace_one := ρ.trace_extendOp

end Quantum.Operators
