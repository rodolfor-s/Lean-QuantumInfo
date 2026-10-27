import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Symmetry.Paired

/-! # Canonical purification of the mixed CKR reference -/

noncomputable section

namespace Quantum.Channels

open Quantum.Operators Quantum.Symmetry

/-- Purify the mixed CKR marginal on a second copy of its function register. -/
def ckrDeFinettiCanonicalPurification (X : Type*) [Fintype X] [DecidableEq X]
    [Nonempty X] (k : ℕ) : DensityOp ((Fin k → X) × (Fin k → X)) :=
  (ckrDeFinettiState X k).purification

/-- The canonical CKR state satisfies the purification predicate, including at zero sites. -/
theorem isCKRDeFinettiPurification_canonical (X : Type*) [Fintype X] [DecidableEq X]
    [Nonempty X] (k : ℕ) :
    IsCKRDeFinettiPurification (ckrDeFinettiCanonicalPurification X k) :=
  ⟨(ckrDeFinettiState X k).isPure_purification,
    (ckrDeFinettiState X k).partialTraceRight_purification⟩

end Quantum.Channels
