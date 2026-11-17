import QuantumLib.QKD.BB84.FiniteKey.PrivacyAmplification.SymmetricPurifier
import QuantumLib.QKD.BB84.Registers
import QuantumLib.ForPhyslib.QuantumInfo.Channels.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Channels.CKRConsequences
import QuantumLib.ForPhyslib.QuantumInfo.Channels.CKRReference
import QuantumLib.ForPhyslib.QuantumInfo.Channels.Postselection
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.Paired

/-! # Moving the CKR norm to the small paired purifier

The canonical and polynomial-auxiliary purifications have the same signal marginal.
Common reference freedom therefore preserves the complete amplified trace norm,
without a numerical embedding or a reference-dimension hypothesis.
-/

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Symmetry
open QKD.BB84.Measurement

/-- The CKR norm is unchanged when the canonical reference is replaced by the paired purifier. -/
theorem ckrTraceNorm_canonical_eq_enV {n : ℕ} {Y : Type*} [Fintype Y]
    (V : SymmetricPurifier n) (Δ : Operation (Signals n) Y) :
    ckrTraceNorm Δ (ckrDeFinettiCanonicalPurification Signal n) =
      ckrTraceNorm Δ (enVCKRPurification V) :=
  tensorTraceNorm_eq_of_shared_marginal Δ (ckrDeFinettiState Signal n) _ _
    (isCKRDeFinettiPurification_canonical Signal n).isPure
    (isPurification_enVCKRPurification V).isPure
    (isCKRDeFinettiPurification_canonical Signal n).marginal
    (isPurification_enVCKRPurification V).marginal

end QKD.BB84.FiniteKey
