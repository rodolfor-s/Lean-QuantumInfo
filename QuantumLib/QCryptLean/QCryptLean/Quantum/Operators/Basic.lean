import Mathlib.Analysis.Matrix.Order
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Positivity

/-! # Operators and density states on finite registers -/


namespace Quantum.Operators

open scoped ComplexOrder Kronecker

variable {X Y : Type*}

/-- The operator carrier, with no instance arguments. -/
abbrev Op (X : Type*) := Matrix X X ℂ

/-- A positive operator of trace one on a finite register. -/
structure DensityOp (X : Type*) [Fintype X] where
  /-- The underlying matrix of the density operator. -/
  toOp : Op X
  posSemidef : toOp.PosSemidef
  trace_one : toOp.trace = 1

/-- A positive operator whose real trace is at most one. -/
structure SubDensityOp (X : Type*) [Fintype X] where
  /-- The underlying matrix of the sub-density operator. -/
  toOp : Op X
  posSemidef : toOp.PosSemidef
  trace_le_one : toOp.trace.re ≤ 1

variable [Fintype X] [Fintype Y]

/-- Density operators are determined by their underlying matrices. -/
@[ext] theorem DensityOp.ext {ρ σ : DensityOp X} (h : ρ.toOp = σ.toOp) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- Sub-density operators are determined by their underlying matrices. -/
@[ext] theorem SubDensityOp.ext {ρ σ : SubDensityOp X} (h : ρ.toOp = σ.toOp) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- Hermiticity is derived from the stored positivity witness. -/
theorem DensityOp.isHermitian (ρ : DensityOp X) : ρ.toOp.IsHermitian :=
  ρ.posSemidef.isHermitian

/-- Hermiticity is derived from the stored positivity witness. -/
theorem SubDensityOp.isHermitian (ρ : SubDensityOp X) : ρ.toOp.IsHermitian :=
  ρ.posSemidef.isHermitian

/-- A density operator is also a sub-density operator. -/
def DensityOp.toSubDensityOp (ρ : DensityOp X) : SubDensityOp X where
  toOp := ρ.toOp
  posSemidef := ρ.posSemidef
  trace_le_one := by simp [ρ.trace_one]

/-- Density operators cannot inhabit an empty register. -/
theorem DensityOp.nonempty (ρ : DensityOp X) : Nonempty X := by
  cases isEmpty_or_nonempty X with
  | inl h => simpa [Matrix.trace] using ρ.trace_one
  | inr h => exact h

/-- Zero is a sub-density operator, including on an empty register. -/
def SubDensityOp.zero : SubDensityOp X where
  toOp := 0
  posSemidef := Matrix.PosSemidef.zero
  trace_le_one := by simp

/-- Discard the right register of a density operator. -/
def DensityOp.partialTraceRight (ρ : DensityOp (X × Y)) : DensityOp X where
  toOp := Matrix.partialTraceRight ρ.toOp
  posSemidef := ρ.posSemidef.partialTraceRight
  trace_one := (Matrix.trace_partialTraceRight ρ.toOp).trans ρ.trace_one

/-- Discard the left register of a density operator. -/
def DensityOp.partialTraceLeft (ρ : DensityOp (X × Y)) : DensityOp Y where
  toOp := Matrix.partialTraceLeft ρ.toOp
  posSemidef := ρ.posSemidef.partialTraceLeft
  trace_one := (Matrix.trace_partialTraceLeft ρ.toOp).trans ρ.trace_one

/-- Discard the right register of a sub-density operator. -/
def SubDensityOp.partialTraceRight (ρ : SubDensityOp (X × Y)) : SubDensityOp X where
  toOp := Matrix.partialTraceRight ρ.toOp
  posSemidef := ρ.posSemidef.partialTraceRight
  trace_le_one := by rw [Matrix.trace_partialTraceRight]; exact ρ.trace_le_one

/-- Discard the left register of a sub-density operator. -/
def SubDensityOp.partialTraceLeft (ρ : SubDensityOp (X × Y)) : SubDensityOp Y where
  toOp := Matrix.partialTraceLeft ρ.toOp
  posSemidef := ρ.posSemidef.partialTraceLeft
  trace_le_one := by rw [Matrix.trace_partialTraceLeft]; exact ρ.trace_le_one

/-- The right density marginal has the expected underlying operator. -/
@[simp] theorem DensityOp.partialTraceRight_toOp (ρ : DensityOp (X × Y)) :
    ρ.partialTraceRight.toOp = Matrix.partialTraceRight ρ.toOp := rfl

/-- The left density marginal has the expected underlying operator. -/
@[simp] theorem DensityOp.partialTraceLeft_toOp (ρ : DensityOp (X × Y)) :
    ρ.partialTraceLeft.toOp = Matrix.partialTraceLeft ρ.toOp := rfl

/-- The right sub-density marginal has the expected underlying operator. -/
@[simp] theorem SubDensityOp.partialTraceRight_toOp (ρ : SubDensityOp (X × Y)) :
    ρ.partialTraceRight.toOp = Matrix.partialTraceRight ρ.toOp := rfl

/-- The left sub-density marginal has the expected underlying operator. -/
@[simp] theorem SubDensityOp.partialTraceLeft_toOp (ρ : SubDensityOp (X × Y)) :
    ρ.partialTraceLeft.toOp = Matrix.partialTraceLeft ρ.toOp := rfl

/-- Tensor two density operators without choosing coordinates. -/
def DensityOp.kronecker (ρ : DensityOp X) (σ : DensityOp Y) : DensityOp (X × Y) where
  toOp := ρ.toOp ⊗ₖ σ.toOp
  posSemidef := ρ.posSemidef.kronecker σ.posSemidef
  trace_one := by rw [Matrix.trace_kronecker, ρ.trace_one, σ.trace_one, one_mul]

/-- Discarding the right factor of a product state returns the left state. -/
@[simp] theorem DensityOp.partialTraceRight_kronecker (ρ : DensityOp X) (σ : DensityOp Y) :
    (ρ.kronecker σ).partialTraceRight = ρ := by
  apply DensityOp.ext
  simp [kronecker, σ.trace_one]

/-- Discarding the left factor of a product state returns the right state. -/
@[simp] theorem DensityOp.partialTraceLeft_kronecker (ρ : DensityOp X) (σ : DensityOp Y) :
    (ρ.kronecker σ).partialTraceLeft = σ := by
  apply DensityOp.ext
  simp [kronecker, ρ.trace_one]

end Quantum.Operators
