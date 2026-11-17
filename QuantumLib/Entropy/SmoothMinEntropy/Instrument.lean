import QuantumLib.Entropy.SmoothMinEntropy.CQOperations
import QuantumLib.Entropy.SmoothMinEntropy.CQState
import QuantumLib.ForPhyslib.QuantumInfo.Channels.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Channels.Kraus
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic

/-! # Instrument -/


namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Quantum.Channels

variable {C Q R : Type*} [Fintype C] [Fintype Q] [Fintype R]

/-- Apply a completely positive instrument with a total acceptance-weight bound. -/
def CQState.ofInstrument (L : C → Operation Q R) (hL : ∀ c, IsCompletelyPositive (L c))
    (hw : ∀ ρ : DensityOp Q, ∑ c, (L c ρ.toOp).trace.re ≤ 1) (ρ : DensityOp Q) : CQState C R :=
  CQState.ofBlocks (fun c => L c ρ.toOp) (fun c => (hL c).posSemidef ρ.posSemidef) (hw ρ)

end InfoTheory.SmoothMinEntropy
