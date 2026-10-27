import QCryptLean.QKD.BB84.Constants
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQ
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.PairedAlgebra

/-!
# BB84 CKR paired support — polynomial dimension

The BB84 specialization of the generic paired-CKR rank bound: `ckrSymmetricDim` identified with the
paired symmetric-subspace dimension, giving a rank bound on the BB84 paired de Finetti state.

## Main results

* `ckrSymmetricDim_eq_choose` — `ckrSymmetricDim n` in the parenthesization the generic
  paired CKR lemmas use.
* `rank_pairedDeFinettiState_le_ckrSymmetricDim` — the BB84 paired de Finetti state has rank at
  most `ckrSymmetricDim n`.
-/

open Quantum.Operators Quantum.Symmetry Matrix
open QKD.BB84.Measurement
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.FiniteKey

/-- The BB84 polynomial dimension in the parenthesization used by the generic
paired CKR lemmas. -/
lemma ckrSymmetricDim_eq_choose (n : ℕ) :
    ckrSymmetricDim n =
      Nat.choose (n + (signalDim ^ 2 - 1)) (signalDim ^ 2 - 1) := by
  rfl

/-- The BB84 paired de Finetti state has rank at most `ckrSymmetricDim n`. -/
lemma rank_pairedDeFinettiState_le_ckrSymmetricDim
    (n : ℕ) :
    Matrix.rank (pairedDeFinettiState Signal n).toOp ≤ ckrSymmetricDim n := by
  change (Matrix.reindex (pairFunctions Signal Signal n) (pairFunctions Signal Signal n)
    (deFinettiState (Signal × Signal) n).toOp).rank ≤ _
  rw [Matrix.rank_reindex, rank_deFinettiState]
  simp [ckrSymmetricDim, Signal, Bit, signalDim]

end QKD.BB84.FiniteKey

end -- noncomputable section
