import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarsening
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Quantum.Operators.Basic

/-! # Relabel -/


noncomputable section

namespace InfoTheory.QuantumLHL

open Quantum.Operators InfoTheory.SmoothMinEntropy

variable {S C D Z Q : Type*} [Fintype S] [Fintype C] [Fintype D]
  [Fintype Z] [Fintype Q] [DecidableEq Z]

/-- Relabelling raw keys and precomposing the hash preserves the public-seed output. -/
theorem SeedKey.output_relabel (e : C ≃ D) (H : HashFamily S C Z) (ρ : CQState C Q) :
    SeedKey.output (H.precomp e.symm) (ρ.relabel e) = SeedKey.output H ρ := by
  apply CQState.ext
  funext sz
  apply SubDensityOp.ext
  change (1 / Fintype.card S : ℝ) •
    (∑ d, if H.hash sz.1 (e.symm d) = sz.2 then (ρ.stateMap (e.symm d)).toOp else 0) = _
  exact congrArg (fun M : Op Q => (1 / Fintype.card S : ℝ) • M)
    (Equiv.sum_comp e.symm (fun c =>
      if H.hash sz.1 c = sz.2 then (ρ.stateMap c).toOp else 0))

end InfoTheory.QuantumLHL
