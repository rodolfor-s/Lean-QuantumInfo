import Mathlib.Data.Sym.Card
import QuantumLib.ForMathlib.LinearAlgebra.PartialTrace.Basic
import QuantumLib.QKD.BB84.Constants
import QuantumLib.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQ
import QuantumLib.QKD.BB84.FiniteKey.Postselection.CKRPairedSupport
import QuantumLib.QKD.BB84.Registers
import QuantumLib.ForPhyslib.QuantumInfo.Channels.CKRReference
import QuantumLib.ForPhyslib.QuantumInfo.Channels.Postselection
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Operators.RankPurificationBounds
import QuantumLib.ForPhyslib.QuantumInfo.Operators.StateOperations
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.Paired

/-! # A polynomial-size purifier of the paired symmetric reference

The auxiliary register purifies the paired state, whose rank is polynomial in
round count. It is distinct from a purifier of the full-rank CKR marginal.
The latter's retained register is the structural product of the signal-word
reference with this auxiliary register. The existence proof uses occupation
types as its finite auxiliary register, without numbering them.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Symmetry
open QKD.BB84.Measurement Matrix

/-- A pure extension of the paired symmetric state with a polynomial-size auxiliary register. -/
structure SymmetricPurifier (n : ℕ) where
  /-- The finite auxiliary register. -/
  reg : Type
  /-- The auxiliary register's finite basis. -/
  [fintypeReg : Fintype reg]
  /-- The pure extension of the paired signal-word state. -/
  purifier : DensityOp ((Signals n × Signals n) × reg)
  /-- Purity of the joint extension. -/
  purifier_isPure : purifier.IsPure
  /-- Discarding the auxiliary register recovers the paired symmetric state. -/
  purifier_partialTraceRight : purifier.partialTraceRight = pairedDeFinettiState Signal n
  /-- The reference-size charge is bounded by the symmetric dimension. -/
  card_reg_le_ckrSymmetricDim : Fintype.card reg ≤ ckrSymmetricDim n

attribute [instance] SymmetricPurifier.fintypeReg

/-- Occupation types provide a sufficiently large reference of exactly the polynomial size. -/
theorem nonempty_symmetricPurifier (n : ℕ) : Nonempty (SymmetricPurifier n) := by
  classical
  let R := Sym (Signal × Signal) n
  have hc : Fintype.card R = ckrSymmetricDim n := by
    rw [Sym.card_sym_eq_choose]
    have he : Fintype.card (Signal × Signal) + n - 1 = n + 15 := by
      simp [Signal, Bit]
      omega
    rw [he]
    have h := Nat.choose_symm (by omega : 15 ≤ n + 15)
    simpa [ckrSymmetricDim, signalDim] using h
  obtain ⟨ψ, hψ, hm⟩ :=
    (pairedDeFinettiState Signal n).exists_isPure_partialTraceRight_eq_of_rank_le (R := R)
      (by rw [hc]; exact rank_pairedDeFinettiState_le_ckrSymmetricDim n)
  exact ⟨{
    reg := R
    fintypeReg := inferInstance
    purifier := ψ
    purifier_isPure := hψ
    purifier_partialTraceRight := hm
    card_reg_le_ckrSymmetricDim := hc.le }⟩

/-- Expose the full CKR reference as a signal-word register paired with the small purifier. -/
def enVCKRPurification {n : ℕ} (V : SymmetricPurifier n) :
    DensityOp (Signals n × (Signals n × V.reg)) :=
  V.purifier.reindex (Equiv.prodAssoc _ _ _)

/-- Reassociation preserves purity and gives the CKR marginal by iterated partial trace. -/
theorem isPurification_enVCKRPurification {n : ℕ} (V : SymmetricPurifier n) :
    IsCKRDeFinettiPurification (enVCKRPurification V) := by
  classical
  refine ⟨?_, ?_⟩
  · exact V.purifier_isPure.reindex _
  · apply DensityOp.ext
    change partialTraceRight (Matrix.reindex (Equiv.prodAssoc _ _ _)
      (Equiv.prodAssoc _ _ _) V.purifier.toOp) = _
    rw [← partialTraceRight_partialTraceRight]
    change partialTraceRight V.purifier.partialTraceRight.toOp = _
    rw [V.purifier_partialTraceRight]
    rfl

end QKD.BB84.FiniteKey
