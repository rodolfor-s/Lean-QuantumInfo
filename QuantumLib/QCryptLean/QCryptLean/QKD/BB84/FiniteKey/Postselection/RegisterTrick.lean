import QCryptLean.QKD.BB84.FiniteKey.Postselection.PEAnnounceRelabel
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RoundKernel
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.RecordedConjugation
import QCryptLean.Quantum.Operators.Basic

/-!
# Bell covariance of the pre-channel

Covariance is an explicit restriction on the pre-channel. Complete positivity alone does
not imply it. The attack-free unit register embedding satisfies this restriction.
-/

namespace QKD.BB84.FiniteKey

open Matrix Quantum.Operators Quantum.Channels
open QKD.BB84.Model QKD.BB84.Measurement
open scoped Kronecker

open scoped Classical in
/-- A pre-channel carries each bilateral Bell conjugation to the same signal conjugation. -/
def IsBellTwirlCovariantPre {n : ℕ} {E : Type*} [Fintype E]
    (pre : Operation (Signals n) (Signals n × E)) : Prop :=
  ∀ (g : Fin n → Fin 4) (A : Op (Signals n)),
    pre (signalBellUnitary g * A * (signalBellUnitary g)ᴴ) =
      (signalBellUnitary g ⊗ₖ (1 : Op E)) * pre A * (signalBellUnitary g ⊗ₖ (1 : Op E))ᴴ

open scoped Classical in
/-- Adjoining the unit reference commutes with every bilateral Bell conjugation. -/
theorem isBellTwirlCovariantPre_unitRegisterEmbed (n : ℕ) :
    IsBellTwirlCovariantPre (unitRegisterEmbed n) := by
  classical
  intro g A
  ext ⟨i, u⟩ ⟨j, v⟩
  simp [unitRegisterEmbed, reindex_apply, kroneckerMap_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply]

end QKD.BB84.FiniteKey
