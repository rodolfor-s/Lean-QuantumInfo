import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.Model.BB84Locality
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SiftOperation
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.RandomizedBlocking

/-! # De Padded Quantum Stack -/


open Quantum.Operators Quantum.Channels Quantum.Symmetry Matrix
open QKD.BB84.Measurement
open scoped Kronecker

noncomputable section

namespace QKD.BB84.Model

/-- Sifted conjugation commutes with adjoining the trivial reference register. -/
theorem siftedConjChannel_unitRegisterEmbed (n : ℕ) (peSel xSel : Fin n → Bool)
    (A : Op (Signals n)) :
    siftedConjChannel Unit n peSel xSel (unitRegisterEmbed n A) =
      unitRegisterEmbed n (siftedRotation n peSel xSel * A * (siftedRotation n peSel xSel)ᴴ) := by
  let : DecidableEq Unit := Classical.decEq _
  rw [siftedConjChannel, ← mapTensorId_conjLinearMap]
  exact mapTensorId_prodUnique (R := Unit) (Matrix.conjLinearMap _) A

/-- The local laboratory operations fuse into the joint sift-after-permutation. -/
theorem siftPermHalf_pair_conj_reindex (n : ℕ)
    (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) (ρ : Op (Signals n)) :
    (siftPermHalf n peSel xSel π ⊗ₖ siftPermHalf n peSel xSel π) *
        Matrix.reindex (pairFunctions Bit Bit n) (pairFunctions Bit Bit n) ρ *
        (siftPermHalf n peSel xSel π ⊗ₖ siftPermHalf n peSel xSel π)ᴴ =
      Matrix.reindex (pairFunctions Bit Bit n) (pairFunctions Bit Bit n)
        (siftedRotation n peSel xSel * permConjLin π ρ *
          (siftedRotation n peSel xSel)ᴴ) := by
  simp only [siftPermHalf]
  rw [siftedRotation_conj_reindex_roundGroupEquiv,
    permuteSignalLinear_reindex_roundGroupEquiv, mul_kronecker_mul]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

end QKD.BB84.Model
