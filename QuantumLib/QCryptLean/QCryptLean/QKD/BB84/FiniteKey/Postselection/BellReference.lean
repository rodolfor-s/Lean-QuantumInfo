import QCryptLean.Math.Combinatorics.BellSymmetricDim
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.ReferencePurification
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.BellReference

/-! # The canonical Bell de Finetti purification

The Bell reference lives on the actual signal-word register. Its Boolean qubit
labels are identified componentwise with `Bit`, without numbering any composite
register. Purification retains a second signal-word register.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Symmetry QKD.BB84.Measurement

/-- The canonical square-root purification of the Bell reference on signal words. -/
def bellCKRDeFinettiPurification (n : ℕ) : DensityOp (Signals n × Signals n) :=
  ((bellDeFinettiDensity n).reindex
    (Equiv.piCongrRight fun _ => finTwoEquiv.symm.prodCongr finTwoEquiv.symm)).purification

/-- A pure extension with the Bell de Finetti signal marginal. -/
structure IsBellCKRDeFinettiPurification {n : ℕ} {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) : Prop where
  /-- Purity of the extension. -/
  isPure : τ.IsPure
  /-- Discarding the reference gives the Bell signal state. -/
  marginal : τ.partialTraceRight = (bellDeFinettiDensity n).reindex
    (Equiv.piCongrRight fun _ => finTwoEquiv.symm.prodCongr finTwoEquiv.symm)

/-- The canonical square-root state has the required purity and Bell marginal. -/
theorem isPurification_bellCKRDeFinettiPurification (n : ℕ) :
    IsBellCKRDeFinettiPurification (bellCKRDeFinettiPurification n) :=
  ⟨DensityOp.isPure_purification _, DensityOp.partialTraceRight_purification _⟩

end QKD.BB84.FiniteKey
