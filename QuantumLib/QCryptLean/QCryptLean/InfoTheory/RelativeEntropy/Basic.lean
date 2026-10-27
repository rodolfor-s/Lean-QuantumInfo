import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Basic.ENNReal.Real
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Math.SpectralTheory.ReindexCFC
import QCryptLean.Quantum.Operators.Basic

/-!
# Relative entropy on finite registers

The signed value uses the natural logarithm, including its value zero at zero.
The extended value separately checks support containment by kernel inclusion.
Functional calculus uses the usual matrix topology and star structure; these
constructions install neither a matrix order nor a matrix norm instance.
-/

noncomputable section

namespace InfoTheory.RelativeEntropy

open Quantum.Operators InfoTheory.VonNeumannEntropy

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The logarithmic cross term, with `Real.log 0 = 0` on the kernel. -/
def traceProductLogSigma (ρ σ : DensityOp Q) : ℝ :=
  (ρ.toOp * cfc Real.log σ.toOp).trace.re

/-- Signed relative entropy in nats, before the support check. -/
def relativeEntropyReal (ρ σ : DensityOp Q) : ℝ :=
  -vonNeumannEntropy ρ - traceProductLogSigma ρ σ

/-- Extended relative entropy in nats, infinite outside support containment. -/
def relativeEntropy (ρ σ : DensityOp Q) : ENNReal := by
  classical
  exact if ∀ v, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0
  then ENNReal.ofReal (relativeEntropyReal ρ σ) else ⊤

/-- Kernel inclusion gives the finite branch of extended relative entropy. -/
theorem relativeEntropy_eq_ofReal_of_ker_sub (ρ σ : DensityOp Q)
    (h : ∀ v, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    relativeEntropy ρ σ = ENNReal.ofReal (relativeEntropyReal ρ σ) := ite_eq_left h

/-- Failure of kernel inclusion gives infinite extended relative entropy. -/
theorem relativeEntropy_eq_top_of_not_ker_sub (ρ σ : DensityOp Q)
    (h : ¬ ∀ v, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    relativeEntropy ρ σ = ⊤ := ite_eq_right h

end InfoTheory.RelativeEntropy
