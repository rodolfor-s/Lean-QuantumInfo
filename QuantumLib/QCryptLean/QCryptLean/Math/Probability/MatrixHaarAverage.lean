import Mathlib.MeasureTheory.Group.Integral
import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.Probability.UnitaryHaar
import QCryptLean.Math.Probability.UnitaryHaarTransport

/-! # Entrywise Haar averages of finite-dimensional unitary representations

All integration is scalar complex integration. The entrywise matrix topology is
used, and no matrix norm or matrix order instance is installed.
-/
noncomputable section
namespace Matrix
open MeasureTheory
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Haar conjugation average for a unitary representation on a finite matrix register. -/
def unitaryHaarAverage (U : unitaryGroup Y ℂ →* unitaryGroup X ℂ) (A : Matrix X X ℂ) :
    Matrix X X ℂ :=
  of fun i j => ∫ g, ((U g).val * A * (U g).valᴴ) i j ∂UnitaryGroup.haarProbUnitary Y

/-- Entries of a continuous unitary conjugation are integrable against probability Haar. -/
theorem integrable_unitary_conjugate (U : unitaryGroup Y ℂ →* unitaryGroup X ℂ)
    (hU : Continuous U) (A : Matrix X X ℂ) (i j : X) :
    Integrable (fun g => ((U g).val * A * (U g).valᴴ) i j)
      (UnitaryGroup.haarProbUnitary Y) := by
  let := UnitaryGroup.isProbabilityMeasure_haarProbUnitary Y
  have hc := continuous_subtype_val.comp hU
  exact ((continuous_apply j).comp ((continuous_apply i).comp
    ((hc.mul continuous_const).mul hc.matrix_conjTranspose))).integrable_of_compactSpace

open scoped ComplexOrder in
/-- Haar averaging preserves positive semidefiniteness. -/
theorem PosSemidef.unitaryHaarAverage (U : unitaryGroup Y ℂ →* unitaryGroup X ℂ)
    (hU : Continuous U) {A : Matrix X X ℂ} (hA : A.PosSemidef) :
    (Matrix.unitaryHaarAverage U A).PosSemidef :=
  posSemidef_entryIntegral (fun g => hA.mul_mul_conjTranspose_same (U g).val)
    (integrable_unitary_conjugate U hU A)

/-- Haar averaging projects into the commutant of the unitary representation. -/
theorem commute_unitaryHaarAverage (U : unitaryGroup Y ℂ →* unitaryGroup X ℂ)
    (hU : Continuous U) (A : Matrix X X ℂ) (g : unitaryGroup Y ℂ) :
    Commute (U g).val (unitaryHaarAverage U A) := by
  have hc (h : unitaryGroup Y ℂ) :
      (U g).val * ((U h).val * A * (U h).valᴴ) * (U g).valᴴ =
      (U (g * h)).val * A * (U (g * h)).valᴴ := by
    simp only [map_mul, Submonoid.coe_mul, conjTranspose_mul, Matrix.mul_assoc]
  have he : (U g).val * unitaryHaarAverage U A * (U g).valᴴ = unitaryHaarAverage U A := by
    rw [unitaryHaarAverage, sandwich_entryIntegral _ (integrable_unitary_conjugate U hU A)]
    ext i j
    simp only [of_apply, hc]
    exact integral_mul_left_eq_self (fun h => ((U h).val * A * (U h).valᴴ) i j) g
  have hu : (U g).valᴴ * (U g).val = 1 := Unitary.coe_star_mul_self _
  have h := congrArg (· * (U g).val) he
  change (U g).val * unitaryHaarAverage U A = unitaryHaarAverage U A * (U g).val
  simpa only [Matrix.mul_assoc, hu, Matrix.mul_one] using h

/-- Trace pairings against a commuting matrix are unchanged by Haar averaging. -/
theorem trace_mul_unitaryHaarAverage (U : unitaryGroup Y ℂ →* unitaryGroup X ℂ)
    (hU : Continuous U) (A S : Matrix X X ℂ) (hS : ∀ g, Commute S (U g).val) :
    (S * unitaryHaarAverage U A).trace = (S * A).trace := by
  let := UnitaryGroup.isProbabilityMeasure_haarProbUnitary Y
  have hi := integrable_unitary_conjugate U hU A
  have hint (i j) : Integrable (fun g => (S * ((U g).val * A * (U g).valᴴ)) i j)
      (UnitaryGroup.haarProbUnitary Y) := by
    change Integrable (fun g => ∑ z, S i z * ((U g).val * A * (U g).valᴴ) z j) _
    exact integrable_finsetSum _ fun z _ => (hi z j).const_mul (S i z)
  have he (g : unitaryGroup Y ℂ) :
      (S * ((U g).val * A * (U g).valᴴ)).trace = (S * A).trace := by
    have hu : (U g).valᴴ * (U g).val = 1 := Unitary.coe_star_mul_self _
    have heq : S * ((U g).val * A * (U g).valᴴ) =
        (U g).val * (S * A) * (U g).valᴴ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, (hS g).eq]
      simp only [Matrix.mul_assoc]
    rw [heq, trace_mul_cycle, hu, Matrix.one_mul]
  rw [unitaryHaarAverage, mul_entryIntegral S hi, trace_entryIntegral (fun i => hint i i)]
  simp only [he, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

end Matrix
