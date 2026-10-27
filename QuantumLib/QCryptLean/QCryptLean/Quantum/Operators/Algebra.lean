import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Positivity
import QCryptLean.Quantum.Operators.Basic

/-! # Algebra -/


namespace Quantum.Operators

open Matrix
open scoped ComplexOrder

variable {X Y : Type*}

/-- Hermitian operators use Mathlib's real vector space of self-adjoint elements. -/
abbrev HermitianOp (X : Type*) : Type _ := selfAdjoint (Op X)

/-- Positive operators store the Mathlib positivity predicate without a second witness. -/
abbrev PosSemidefOp (X : Type*) := {A : Op X // A.PosSemidef}

/-- Unitary operators use Mathlib's unitary group, including its inverse and star. -/
abbrev UnitaryOp (X : Type*) [Fintype X] [DecidableEq X] : Type _ := Matrix.unitaryGroup X ℂ

/-- The underlying matrix of a Hermitian operator. -/
def HermitianOp.toOp (A : HermitianOp X) : Op X := A.val

/-- The underlying matrix of a positive operator. -/
def PosSemidefOp.toOp (A : PosSemidefOp X) : Op X := A.val

/-- The stored self-adjoint witness is exactly matrix Hermiticity. -/
theorem HermitianOp.isHermitian (A : HermitianOp X) : A.toOp.IsHermitian := A.property

/-- A positive operator determines its Hermitian refinement. -/
def PosSemidefOp.toHermitianOp (A : PosSemidefOp X) : HermitianOp X :=
  ⟨A.val, A.property.isHermitian⟩

/-- A density operator determines its positive refinement. -/
def DensityOp.toPosSemidefOp [Fintype X] (ρ : DensityOp X) : PosSemidefOp X :=
  ⟨ρ.toOp, ρ.posSemidef⟩

/-- A sub-density operator determines its positive refinement. -/
def SubDensityOp.toPosSemidefOp [Fintype X] (ρ : SubDensityOp X) : PosSemidefOp X :=
  ⟨ρ.toOp, ρ.posSemidef⟩

/-- Transport a Hermitian operator through an equivalence of registers. -/
def HermitianOp.reindex (e : X ≃ Y) (A : HermitianOp X) : HermitianOp Y :=
  ⟨Matrix.reindex e e A.val, A.isHermitian.reindex e⟩

/-- Transport a positive operator through an equivalence of registers. -/
def PosSemidefOp.reindex (e : X ≃ Y) (A : PosSemidefOp X) : PosSemidefOp Y :=
  ⟨Matrix.reindex e e A.val, (Matrix.posSemidef_reindex_iff e A.val).mpr A.property⟩

/-- Discard a finite right register of a Hermitian operator. -/
def HermitianOp.partialTraceRight [Fintype Y] (A : HermitianOp (X × Y)) : HermitianOp X :=
  ⟨Matrix.partialTraceRight A.val, A.isHermitian.partialTraceRight⟩

/-- Discard a finite left register of a Hermitian operator. -/
def HermitianOp.partialTraceLeft [Fintype X] (A : HermitianOp (X × Y)) : HermitianOp Y :=
  ⟨Matrix.partialTraceLeft A.val, A.isHermitian.partialTraceLeft⟩

/-- Discard a finite right register of a positive operator. -/
def PosSemidefOp.partialTraceRight [Fintype Y] (A : PosSemidefOp (X × Y)) : PosSemidefOp X :=
  ⟨Matrix.partialTraceRight A.val, A.property.partialTraceRight⟩

/-- Discard a finite left register of a positive operator. -/
def PosSemidefOp.partialTraceLeft [Fintype X] (A : PosSemidefOp (X × Y)) : PosSemidefOp Y :=
  ⟨Matrix.partialTraceLeft A.val, A.property.partialTraceLeft⟩

variable [Fintype X]

/-- The complex quadratic form of an arbitrary operator. -/
def quadraticForm (A : Op X) (x : X → ℂ) : ℂ := star x ⬝ᵥ (A *ᵥ x)

/-- Comparison of real quadratic forms, with no Hermiticity hypothesis. -/
def OpLe (A B : Op X) : Prop := ∀ x, (quadraticForm A x).re ≤ (quadraticForm B x).re

/-- Real quadratic-form comparison is reflexive. -/
theorem OpLe.refl (A : Op X) : OpLe A A := fun _ => le_rfl

/-- Real quadratic-form comparison is transitive. -/
theorem OpLe.trans {A B C : Op X} (hAB : OpLe A B) (hBC : OpLe B C) : OpLe A C :=
  fun x => (hAB x).trans (hBC x)

/-- A positive difference implies quadratic-form comparison without additional assumptions. -/
theorem opLe_of_posSemidef_sub {A B : Op X} (h : (B - A).PosSemidef) : OpLe A B := by
  intro x
  have hx := (Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg x)).1
  simpa [quadraticForm, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] using hx

/-- On Hermitian matrices, comparison agrees with positivity of the difference. -/
theorem opLe_iff_posSemidef_sub {A B : Op X} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    OpLe A B ↔ (B - A).PosSemidef := by
  refine ⟨?_, opLe_of_posSemidef_sub⟩
  intro h
  apply PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA)
  intro x
  apply Complex.nonneg_iff.mpr
  constructor
  · simpa [quadraticForm, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] using
      sub_nonneg.mpr (h x)
  · have hs := (hB.sub hA).star_dotProduct_mulVec_comm x x
    have hi := congrArg Complex.im hs
    change -(star x ⬝ᵥ ((B - A) *ᵥ x)).im = (star x ⬝ᵥ ((B - A) *ᵥ x)).im at hi
    linarith

/-- Quadratic forms are unchanged when both matrix and vector coordinates are transported. -/
theorem quadraticForm_reindex [Fintype Y] (e : X ≃ Y) (A : Op X) (x : X → ℂ) :
    quadraticForm (Matrix.reindex e e A) (x ∘ e.symm) = quadraticForm A x := by
  change (∑ i : Y, star (x (e.symm i)) *
    ∑ j : Y, A (e.symm i) (e.symm j) * x (e.symm j)) =
      ∑ i : X, star (x i) * ∑ j : X, A i j * x j
  calc
    _ = ∑ i : Y, star (x (e.symm i)) * ∑ j : X, A (e.symm i) j * x j := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (star (x (e.symm i)) * ·)
        (Equiv.sum_comp e.symm (fun j => A (e.symm i) j * x j))
    _ = _ := Equiv.sum_comp e.symm (fun i => star (x i) * ∑ j, A i j * x j)

/-- Real quadratic-form comparison is invariant under register relabelling. -/
theorem opLe_reindex_iff [Fintype Y] (e : X ≃ Y) (A B : Op X) :
    OpLe (Matrix.reindex e e A) (Matrix.reindex e e B) ↔ OpLe A B := by
  constructor
  · intro h x
    simpa only [quadraticForm_reindex] using h (x ∘ e.symm)
  · intro h y
    have hy : y = (y ∘ e) ∘ e.symm := by ext i; simp
    rw [hy, quadraticForm_reindex, quadraticForm_reindex]
    exact h _

end Quantum.Operators
