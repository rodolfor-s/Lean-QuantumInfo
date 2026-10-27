import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic

/-! # The entropy trace formula on finite registers -/

noncomputable section
namespace InfoTheory.VonNeumannEntropy
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Entropy in nats is minus the trace of `ρ log ρ`, including zero eigenvalues. -/
theorem vonNeumannEntropy_eq_neg_trace_mul_log (ρ : DensityOp Q) :
    vonNeumannEntropy ρ = -(ρ.toOp * CFC.log ρ.toOp).trace.re := by
  cases Subsingleton.elim (inferInstance : DecidableEq Q) (Classical.decEq Q)
  classical
  have hρ : IsSelfAdjoint ρ.toOp := ρ.isHermitian
  have he : ρ.toOp * CFC.log ρ.toOp = cfc (fun x : ℝ => x * Real.log x) ρ.toOp := by
    rw [cfc_mul (fun x : ℝ => x) Real.log ρ.toOp
      ((Matrix.finite_real_spectrum (A := ρ.toOp)).continuousOn _)
      ((Matrix.finite_real_spectrum (A := ρ.toOp)).continuousOn _),
      cfc_id' ℝ ρ.toOp hρ]
    rfl
  rw [he, ρ.isHermitian.trace_cfc]
  simp only [vonNeumannEntropy, Complex.re_sum,
    Math.ClassicalEntropy.entropyTerm_eq_neg_mul_log, Finset.sum_neg_distrib]
  rfl

end InfoTheory.VonNeumannEntropy
