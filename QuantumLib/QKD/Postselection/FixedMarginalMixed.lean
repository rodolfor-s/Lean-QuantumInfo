import QuantumLib.QKD.Postselection.FixedMarginalDomination
import QuantumLib.QKD.Postselection.FixedMarginalMeasure
import QuantumLib.QKD.Postselection.FixedMarginalMoment
import QuantumLib.QKD.Postselection.DeFinettiPrefactor
import QuantumLib.ForMathlib.LinearAlgebra.PartialTrace.Basic
import QuantumLib.ForMathlib.LinearAlgebra.PartialTrace.Positivity
import QuantumLib.ForPhyslib.QuantumInfo.DeFinetti.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Purification
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Tensor
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.Paired
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.Purification

/-! # Fixed Marginal Mixed -/


noncomputable section
namespace InfoTheory.Postselection
open Matrix Quantum.Operators Quantum.DeFinetti
  Quantum.Symmetry Math.Combinatorics
open scoped ComplexOrder MatrixOrder
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Nonempty A] [Nonempty B]

/-- A permutation-invariant fixed-marginal state is dominated by the fixed-marginal Haar mixture. -/
theorem le_integralTensorPower_fixedMarginalHaarMeasure (σA : DensityOp A)
    (hσA : σA.toOp.PosDef) (e : A ↪ B × (A × B)) (k : ℕ)
    (ρ : DensityOp (Fin k → A × B)) (hρ : IsPermutationInvariant ρ)
    (hmarg : partialTraceRight (reindex (pairFunctions A B k) (pairFunctions A B k) ρ.toOp) =
      (σA.tensorPow k).toOp) :
    ρ.toOp ≤ (deFinettiPrefactor (Fintype.card A ^ 2 * Fintype.card B ^ 2) k : ℂ) •
      integralTensorPower k (fixedMarginalHaarMeasure σA e) := by
  have hp := purification_in_paired_symmetric_subspace ρ hρ
  have hs : pairedProjectorOf (A × B) (A × B) k * ρ.purification.toOp =
      ρ.purification.toOp := by
    let P := pairedProjectorOf (A × B) (A × B) k
    change P * ρ.purification.toOp * P = ρ.purification.toOp at hp
    change P * ρ.purification.toOp = _
    calc
      _ = P * (P * ρ.purification.toOp * P) := congrArg (P * ·) hp.symm
      _ = P * ρ.purification.toOp * P := by
        simp only [P, ← Matrix.mul_assoc, pairedProjectorOf_mul_self]
      _ = _ := hp
  have hm : partialTraceRight ρ.purification.toOp = ρ.toOp :=
    congrArg DensityOp.toOp ρ.partialTraceRight_purification
  have h := le_fixedMarginalReference σA hσA e k ρ.purification hs (by rwa [hm])
  have ht := (Matrix.le_iff.mp h).partialTraceRight
  rw [partialTraceRight_sub, partialTraceRight_smul, partialTraceRight_fixedMarginalReference,
    hm] at ht
  have hc : Fintype.card A * Fintype.card B * Fintype.card (A × B) =
      Fintype.card A ^ 2 * Fintype.card B ^ 2 := by rw [Fintype.card_prod]; ring
  rw [hc] at ht
  exact Matrix.le_iff.mpr ht

end InfoTheory.Postselection
