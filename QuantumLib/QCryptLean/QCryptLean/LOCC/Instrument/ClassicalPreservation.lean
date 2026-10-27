import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.Instrument.Discard
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.Instrument.UniformChoice

/-!
# Branchwise preservation of diagonal finite registers

These predicates express that every observed branch of a finite instrument maps diagonal input
operators to diagonal output operators. The instrument model is the finite-outcome formulation of
Chitambar et al., arXiv:1210.4583, Section 2. The four closure facts below are exact properties of
the explicit library instruments, not results attributed to the BB84 literature.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

open Quantum.Operators (Op)

namespace LOCC

variable {A B R Y : Type}

section

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype Y]

/-- Every observed operation of `I` preserves matrix diagonality. -/
def Instrument.PreservesDiagonalBranches
    (I : Instrument A B Y) : Prop :=
  ∀ y rho, (∀ a a', a ≠ a' → rho a a' = 0) →
    ∀ b b', b ≠ b' → (I.operation y rho) b b' = 0

/-- A nondemolition deterministic readout preserves branchwise diagonality.

This is the direct finite-matrix property of `Instrument.nondemolitionReadout`; the classical
readout role in later BB84 processing is motivated by Renner, quant-ph/0512258v2, lines 673--736. -/
theorem Instrument.nondemolitionReadout_preservesDiagonalBranches
    [DecidableEq Y]
    (f : A → Y) : (Instrument.nondemolitionReadout f).PreservesDiagonalBranches := by
  intro y rho hrho a a' haa'
  rw [Instrument.nondemolitionReadout_operation_apply]
  split_ifs
  · exact hrho a a' haa'
  · rfl

/-- A deterministic relabelling with forgotten input preserves branchwise diagonality.

This is an exact property of the source-defined `Instrument.functionAndForget` operation. -/
theorem Instrument.functionAndForget_preservesDiagonalBranches
    (f : A → B) : (Instrument.functionAndForget f).PreservesDiagonalBranches := by
  intro y rho _ b b' hbb'
  rcases y with ⟨⟩
  rw [Instrument.functionAndForget_operation_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases hb : b = f a
  · by_cases hb' : b' = f a
    · exact (hbb' (hb.trans hb'.symm)).elim
    · simp [hb, hb']
  · simp [hb]

/-- Discarding a finite register to `Unit` preserves branchwise diagonality.

This is an exact property of the source-defined `Instrument.discardToUnit` operation. -/
theorem Instrument.discardToUnit_preservesDiagonalBranches :
    (Instrument.discardToUnit A).PreservesDiagonalBranches := by
  intro y rho _ b b' hbb'
  exact (hbb' (Subsingleton.elim b b')).elim

/-- A finite uniform choice preserves branchwise diagonality when every chosen instrument does.

This is the branchwise closure law for the source-defined `Instrument.uniformChoice`. -/
theorem Instrument.uniformChoice_preservesDiagonalBranches
    [Fintype R] [Nonempty R]
    (I : R → Instrument A B Y)
    (hI : ∀ r, (I r).PreservesDiagonalBranches) :
    (Instrument.uniformChoice I).PreservesDiagonalBranches := by
  rintro ⟨r, y⟩ rho hrho b b' hbb'
  rw [Instrument.uniformChoice_operation]
  simp only [LinearMap.smul_apply, Matrix.smul_apply]
  rw [hI r y rho hrho b b' hbb']
  simp
/-- Sampling a classical outcome leaves diagonal quantum registers diagonal. -/
theorem Instrument.uniformSample_preservesDiagonalBranches
    [Fintype R] [Nonempty R] :
    (Instrument.uniformSample A R).PreservesDiagonalBranches := by
  intro r rho hrho a b hab
  rw [Instrument.uniformSample_operation]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, Matrix.smul_apply, hrho a b hab,
    smul_zero]

end

end LOCC
