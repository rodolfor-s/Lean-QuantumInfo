import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.OutputLayout

/-!
# Terminal ownership of local keys

A terminal value identifies the key factors in the parties' actual final registers.
The value describes ownership and does not perform a physical operation.
-/

namespace QKD
open LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- A terminal key disposition with explicit factors in two designated local registers. -/
structure KeyEnd (alice bob : P) (R : MultipartiteSystem P) where
  /-- Accepted key length, or abort. -/
  disposition : BoundaryKeyLayout.Disposition
  /-- Alice's retained non-key register. -/
  AliceResidual : Type
  /-- Bob's retained non-key register. -/
  BobResidual : Type
  /-- Finite enumeration of Alice's residual register. -/
  [finAliceResidual : Fintype AliceResidual]
  /-- Decidable equality on Alice's residual register. -/
  [decAliceResidual : DecidableEq AliceResidual]
  /-- Inhabitation of Alice's residual register. -/
  [nonemptyAliceResidual : Nonempty AliceResidual]
  /-- Finite enumeration of Bob's residual register. -/
  [finBobResidual : Fintype BobResidual]
  /-- Decidable equality on Bob's residual register. -/
  [decBobResidual : DecidableEq BobResidual]
  /-- Inhabitation of Bob's residual register. -/
  [nonemptyBobResidual : Nonempty BobResidual]
  /-- Alice's key factor belongs to Alice's actual terminal register. -/
  aliceSplit : R.reg alice ≃ disposition.Key × AliceResidual
  /-- Bob's key factor belongs to Bob's actual terminal register. -/
  bobSplit : R.reg bob ≃ disposition.Key × BobResidual

attribute [instance] KeyEnd.finAliceResidual KeyEnd.decAliceResidual KeyEnd.nonemptyAliceResidual
  KeyEnd.finBobResidual KeyEnd.decBobResidual KeyEnd.nonemptyBobResidual

/-- Declare the entire Alice and Bob registers as accepted keys of length `ℓ`. -/
def KeyEnd.keys (ℓ : ℕ) : KeyEnd .alice .bob
    (TwoParty.system ((Fin ℓ → Fin 2)) ((Fin ℓ → Fin 2))) :=
  ⟨.accept ℓ, Unit, Unit, (Equiv.prodPUnit _).symm, (Equiv.prodPUnit _).symm⟩

/-- Declare an abort after both local registers have been discarded. -/
def KeyEnd.abort : KeyEnd .alice .bob (TwoParty.system Unit Unit) :=
  ⟨.abort, Unit, Unit, (Equiv.prodPUnit _).symm, (Equiv.prodPUnit _).symm⟩

/-- Declare keys in the first factors and retain both local residual registers. -/
def KeyEnd.keysWithResidual (ℓ : ℕ) {A B : Type}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] : KeyEnd .alice .bob
    (TwoParty.system ((Fin ℓ → Fin 2) × A) ((Fin ℓ → Fin 2) × B)) :=
  ⟨.accept ℓ, A, B, Equiv.refl _, Equiv.refl _⟩

/-- Declare no keys and retain the entire local registers as residual data. -/
def KeyEnd.abortRetaining {A B : Type}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] :
    KeyEnd .alice .bob (TwoParty.system A B) :=
  ⟨.abort, A, B, (Equiv.punitProd _).symm, (Equiv.punitProd _).symm⟩

end QKD
