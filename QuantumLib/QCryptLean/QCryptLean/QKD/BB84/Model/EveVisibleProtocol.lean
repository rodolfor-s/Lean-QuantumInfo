import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Channels.Basic

/-!
# Protocol maps with a retained reference

The public transcript is an actual finite type. Real and ideal maps have the same
full two-key, Boolean-flag, public-register output, and retain an arbitrary finite
reference as their right factor.
-/

universe u

namespace QKD.BB84.Model

open Measurement Quantum.Channels

/-- An analytical protocol family retaining its reference register. -/
structure EveVisibleProtocolScheme (n ℓ : ℕ) where
  /-- The public data accompanying the acceptance flag. -/
  Public : Type
  /-- The public register is finite. -/
  [fintypePublic : Fintype Public]
  /-- Real operation with the entire reference retained. -/
  realProtocolMap : {E : Type u} → [Fintype E] →
    Operation (Signals n × E) (KeyedOutput ℓ Public × E)
  /-- Ideal operation on the same padded output register. -/
  idealProtocolMap : {E : Type u} → [Fintype E] →
    Operation (Signals n × E) (KeyedOutput ℓ Public × E)

attribute [instance] EveVisibleProtocolScheme.fintypePublic

end QKD.BB84.Model
