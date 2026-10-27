import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # State Operations -/


namespace Quantum.Operators

open Matrix
open scoped ComplexOrder Kronecker

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Relabel a density state's register. -/
def DensityOp.reindex (e : X ≃ Y) (ρ : DensityOp X) : DensityOp Y where
  toOp := Matrix.reindex e e ρ.toOp
  posSemidef := (posSemidef_reindex_iff e _).mpr ρ.posSemidef
  trace_one := (reindex_trace e ρ.toOp).trans ρ.trace_one

/-- Relabel a sub-density state's register. -/
def SubDensityOp.reindex (e : X ≃ Y) (ρ : SubDensityOp X) : SubDensityOp Y where
  toOp := Matrix.reindex e e ρ.toOp
  posSemidef := (posSemidef_reindex_iff e _).mpr ρ.posSemidef
  trace_le_one := by rw [reindex_trace]; exact ρ.trace_le_one

/-- The real trace of a sub-density operator. -/
def SubDensityOp.trace (ρ : SubDensityOp X) : ℝ := ρ.toOp.trace.re

/-- Sub-density states have nonnegative trace. -/
theorem SubDensityOp.trace_nonneg (ρ : SubDensityOp X) : 0 ≤ ρ.trace :=
  (Complex.nonneg_iff.mp ρ.posSemidef.trace_nonneg).1

/-- The trace of a sub-density state has no imaginary part. -/
theorem SubDensityOp.trace_im (ρ : SubDensityOp X) : ρ.toOp.trace.im = 0 :=
  (Complex.nonneg_iff.mp ρ.posSemidef.trace_nonneg).2.symm

/-- Tensor two sub-density states on the product register. -/
def SubDensityOp.kronecker (ρ : SubDensityOp X) (σ : SubDensityOp Y) : SubDensityOp (X × Y) where
  toOp := ρ.toOp ⊗ₖ σ.toOp
  posSemidef := ρ.posSemidef.kronecker σ.posSemidef
  trace_le_one := by
    rw [Matrix.trace_kronecker, Complex.mul_re, ρ.trace_im, zero_mul, sub_zero]
    exact (mul_le_of_le_one_left σ.trace_nonneg ρ.trace_le_one).trans σ.trace_le_one

/-- Transposition preserves a density state. -/
def DensityOp.transpose (ρ : DensityOp X) : DensityOp X where
  toOp := ρ.toOpᵀ
  posSemidef := ρ.posSemidef.transpose
  trace_one := ρ.trace_one

/-- Transposition preserves a sub-density state. -/
def SubDensityOp.transpose (ρ : SubDensityOp X) : SubDensityOp X where
  toOp := ρ.toOpᵀ
  posSemidef := ρ.posSemidef.transpose
  trace_le_one := ρ.trace_le_one

/-- A convex mixture of normalized states. -/
def DensityOp.convexComb (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ρ σ : DensityOp X) : DensityOp X where
  toOp := (p : ℂ) • ρ.toOp + ((1 - p : ℝ) : ℂ) • σ.toOp
  posSemidef := (ρ.posSemidef.smul (Complex.nonneg_iff.mpr ⟨hp.1, rfl⟩)).add
    (σ.posSemidef.smul (Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr hp.2, rfl⟩))
  trace_one := by simp [Matrix.trace_add, Matrix.trace_smul, ρ.trace_one, σ.trace_one]

/-- Scale a sub-density state by a probability. -/
def SubDensityOp.smul (ρ : SubDensityOp X) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    SubDensityOp X where
  toOp := (p : ℂ) • ρ.toOp
  posSemidef := ρ.posSemidef.smul (Complex.nonneg_iff.mpr ⟨hp, rfl⟩)
  trace_le_one := by
    rw [Matrix.trace_smul]
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact (mul_le_of_le_one_left ρ.trace_nonneg hp1).trans ρ.trace_le_one

/-- Purity as the real trace of the squared density matrix. -/
def DensityOp.purity (ρ : DensityOp X) : ℝ := (ρ.toOp * ρ.toOp).trace.re

/-- A normalized state is pure exactly when its matrix is idempotent. -/
def DensityOp.IsPure (ρ : DensityOp X) : Prop := ρ.toOp * ρ.toOp = ρ.toOp

/-- Relabelling a finite register preserves purity. -/
theorem DensityOp.IsPure.reindex {ρ : DensityOp X} (hρ : ρ.IsPure) (e : X ≃ Y) :
    (ρ.reindex e).IsPure := by
  classical
  change (Matrix.reindexAlgEquiv ℂ ℂ e) ρ.toOp *
    (Matrix.reindexAlgEquiv ℂ ℂ e) ρ.toOp = (Matrix.reindexAlgEquiv ℂ ℂ e) ρ.toOp
  rw [← map_mul, hρ]

/-- The maximally mixed state requires a nonempty register. -/
noncomputable def DensityOp.maxMixed [DecidableEq X] [Nonempty X] : DensityOp X where
  toOp := ((Fintype.card X : ℝ)⁻¹ : ℂ) • (1 : Op X)
  posSemidef := by
    apply Matrix.PosSemidef.smul Matrix.PosSemidef.one
    exact inv_nonneg.mpr (Complex.nonneg_iff.mpr ⟨Nat.cast_nonneg _, rfl⟩)
  trace_one := by
    simp [Matrix.trace_smul, Matrix.trace_one, Fintype.card_ne_zero]

/-- A unitary preserves the trace under conjugation. -/
theorem UnitaryOp.trace_conjugate [DecidableEq X] (U : UnitaryOp X) (A : Op X) :
    (U.val * A * U.valᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_cycle]
  change ((star U.val * U.val) * A).trace = A.trace
  rw [Unitary.coe_star_mul_self, Matrix.one_mul]

/-- Evolve a density operator by a unitary. -/
def UnitaryOp.evolve [DecidableEq X] (U : UnitaryOp X) (ρ : DensityOp X) : DensityOp X where
  toOp := U.val * ρ.toOp * U.valᴴ
  posSemidef := ρ.posSemidef.mul_mul_conjTranspose_same U.val
  trace_one := (UnitaryOp.trace_conjugate U ρ.toOp).trans ρ.trace_one

/-- Evolve a sub-density operator by a unitary. -/
def SubDensityOp.unitaryConjugate [DecidableEq X] (ρ : SubDensityOp X) (U : UnitaryOp X) :
    SubDensityOp X where
  toOp := U.val * ρ.toOp * U.valᴴ
  posSemidef := ρ.posSemidef.mul_mul_conjTranspose_same U.val
  trace_le_one := by rw [UnitaryOp.trace_conjugate]; exact ρ.trace_le_one

end Quantum.Operators
