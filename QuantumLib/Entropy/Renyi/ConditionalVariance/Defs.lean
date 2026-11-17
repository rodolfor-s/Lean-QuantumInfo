import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-! # Defs -/


open Matrix 
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace InfoTheory.Renyi

private local instance (m : Type*) [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}


/-- `D(ρ‖σ) = (1/Tr[ρ]) · Tr[ρ (log₂ ρ − log₂ σ)]`, DF `:265`–`:269`,
`\label{def:petz-divergence}` at `:268`.

`CFC.log` is the NATURAL log, so the `/ Real.log 2` is the base-2 conversion and is
load-bearing. -/
def relativeEntropyBits {m : Type*} [Fintype m] [DecidableEq m]
    (ρ σ : Matrix m m ℂ) : ℝ :=
  (ρ * (CFC.log ρ - CFC.log σ)).trace.re / (ρ.trace.re * Real.log 2)

/-- `V(ρ‖σ) = (1/Tr[ρ]) · Tr[ρ (log₂ ρ − log₂ σ)²] − D(ρ‖σ)²`, DF `:353`. -/
def petzDivergenceVariance {m : Type*} [Fintype m] [DecidableEq m]
    (ρ σ : Matrix m m ℂ) : ℝ :=
  (ρ * (CFC.log ρ - CFC.log σ) ^ 2).trace.re / (ρ.trace.re * (Real.log 2) ^ 2)
    - (relativeEntropyBits ρ σ) ^ 2

end InfoTheory.Renyi

end
