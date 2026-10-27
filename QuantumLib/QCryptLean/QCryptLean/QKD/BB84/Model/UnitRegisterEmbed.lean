import Mathlib.LinearAlgebra.Matrix.Kronecker
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Operators.Basic

/-!
# The unit reference register

The attack-free reference is `Unit`. Adding it is the structural equivalence
between the signal register and its product with `Unit`, preserving every entry.
-/

noncomputable section

namespace QKD.BB84.Model

open Quantum.Operators Quantum.Channels Measurement Matrix
open scoped Kronecker

/-- Add the one-point reference to an unmodified signal register. -/
def unitRegisterEmbed (n : ℕ) : Operation (Signals n) (Signals n × Unit) :=
  (reindexLinearEquiv ℂ ℂ (Equiv.prodUnique (Signals n) Unit).symm
    (Equiv.prodUnique (Signals n) Unit).symm).toLinearMap

/-- Adding a one-point reference is a channel on all input operators. -/
theorem isChannel_unitRegisterEmbed (n : ℕ) : IsChannel (unitRegisterEmbed n) :=
  isChannel_reindex _

/-- Adding the one-point reference tensors with its identity operator. -/
theorem unitRegisterEmbed_apply (n : ℕ) (A : Op (Signals n)) :
    unitRegisterEmbed n A = A ⊗ₖ (1 : Op Unit) := by
  ext ⟨i, u⟩ ⟨j, v⟩
  simp [unitRegisterEmbed, reindex_apply, kroneckerMap_apply, one_apply]

end QKD.BB84.Model
