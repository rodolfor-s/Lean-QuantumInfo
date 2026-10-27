import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Symmetry.Paired

/-!
# The classical data of the two laboratories

Grouping the local bit strings round by round gives the joint measurement
outcome. Alice's and Bob's key restrictions then read their respective factors.
-/

namespace QKD.BB84.Model

open Measurement Quantum.Symmetry

/-- The joint outcome determined by Alice's and Bob's local bit strings. -/
abbrev jointOutcome (n : ℕ) (x y : Bits n) : Signals n :=
  (pairFunctions Bit Bit n).symm (x, y)

/-- Alice's restriction of the joint outcome is her local raw key. -/
theorem aliceKeyString_jointOutcome (n : ℕ) (peSel : Fin n → Bool) (x y : Bits n) :
    aliceKeyString peSel (jointOutcome n x y) = aliceRawKey n peSel x := rfl

/-- Bob's restriction of the joint outcome is his local raw key. -/
theorem bobKeyString_jointOutcome (n : ℕ) (peSel : Fin n → Bool) (x y : Bits n) :
    bobKeyString peSel (jointOutcome n x y) = bobRawKey n peSel y := rfl

end QKD.BB84.Model
