import QCryptLean.InfoTheory.Renyi.Basic
import QCryptLean.InfoTheory.Renyi.Bounds
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PhaseErrorUncertainty
import QCryptLean.QKD.BB84.FiniteKey.PerRound.DevetakWinter
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification

/-!
# Conditional von Neumann entropy of the BB84 Alice-Z state

`condVonNeumannBits_componentAliceZCQState_eq_rate` identifies the conditional von Neumann
entropy of the component Alice-Z CQ state with `componentAliceZRate`. It applies the general
conditional-entropy identity to the normalized BB84 component state.
-/

open Quantum.Operators QKD.BB84.Measurement
open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy
open InfoTheory.Renyi
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace QKD.BB84.FiniteKey

/-- **`H(X|B)` at the BB84 component state is the Devetak–Winter rate.**

The identity
`condVonNeumannBits_eq_vonNeumannEntropy_sub_div_log_two`
instantiated at
`ρ = componentAliceZCQState σ`, whose right-hand side is `componentAliceZRate σ`
(`DevetakWinter.lean`) verbatim. This is the identification that lets the Rényi argument land on the
same expression the Bennett entropy bound's AEP lift produces. -/
theorem condVonNeumannBits_componentAliceZCQState_eq_rate (σ : DensityOp Signal) :
    InfoTheory.SmoothMinEntropy.CQState.condVonNeumannBits (componentAliceZCQState σ) =
      componentAliceZRate σ := by
  exact condVonNeumannBits_eq_vonNeumannEntropy_sub_div_log_two
    (componentAliceZCQState σ) (aliceZCQState_weight_eq_one Signal σ.purification)

end QKD.BB84.FiniteKey

end -- noncomputable section
