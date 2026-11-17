import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi

/-!
# BB84 registers and measurement records

Bits and bit strings label the local registers, keys, tags and syndromes of the protocol.
The measurement record retains the chosen basis and observed bit after destructive measurement.
-/

namespace QKD.BB84.Measurement

/-- The two BB84 measurement bases used by the one-round physical primitive. -/
inductive Basis | z | x
  deriving DecidableEq, Nonempty

/-- The measurement bases in constructor order. -/
protected abbrev Basis.enumList : List Basis := [.z, .x]

protected theorem Basis.enumList_getElem?_ctorIdx_eq (theta : Basis) :
    Basis.enumList[Basis.ctorIdx theta]? = some theta := by
  cases theta <;> rfl

protected theorem Basis.enumList_nodup : Basis.enumList.Nodup := by
  decide

instance instFintypeBasis : Fintype Basis where
  elems := ⟨Basis.enumList, Basis.enumList_nodup⟩
  complete theta := by
    change theta ∈ Basis.enumList
    exact List.mem_iff_getElem?.mpr
      ⟨Basis.ctorIdx theta, Basis.enumList_getElem?_ctorIdx_eq theta⟩

/-- A local BB84 measurement result. -/
abbrev Bit := Fin 2

/-- A bit string indexed by its physical bit positions. -/
abbrev Bits (n : ℕ) := Fin n → Bit

/-- One signal consists of Alice's and Bob's qubit labels. -/
abbrev Signal := Bit × Bit

/-- Signals indexed directly by their physical rounds. -/
abbrev Signals (n : ℕ) := Fin n → Signal

/-- The private basis and outcome retained by one laboratory. -/
abbrev Record := Basis × Bit

/-- The basis and outcome of one local measurement, preceded by `Unit` because
the measured qubit has been discarded. -/
abbrev StoredRecord := Unit × Record

/-- There are exactly two basis choices. -/
theorem card_basis : Fintype.card Basis = 2 := by
  decide

end QKD.BB84.Measurement
