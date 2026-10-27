import QCryptLean.InfoTheory.Renyi.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Quantum.Operators.Basic

/-! # CQReference -/


noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators
open scoped MatrixOrder ComplexOrder
variable {C Q : Type*} [Fintype C] [Fintype Q]

/-- Each positive classical block is dominated by the quantum marginal. -/
theorem CQState.stateMap_le_quantumMarginal (ρ : CQState C Q) (c : C) :
    (ρ.stateMap c).toOp ≤ ρ.quantumMarginal.toOp := by
  classical
  apply Matrix.le_iff.mpr
  have he : ρ.quantumMarginal.toOp - (ρ.stateMap c).toOp =
      ∑ d ∈ Finset.univ.erase c, (ρ.stateMap d).toOp := by
    change (∑ d, (ρ.stateMap d).toOp) - (ρ.stateMap c).toOp = _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), add_sub_cancel_left]
  rw [he]
  exact Matrix.posSemidef_sum _ (fun d _ => (ρ.stateMap d).posSemidef)

/-- The joint CQ operator is dominated by the block-diagonal quantum marginal. -/
theorem CQState.toJointOp_le_reference [DecidableEq C] (ρ : CQState C Q) :
    ρ.toJointOp ≤ Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp) := by
  classical
  rw [CQState.toJointOp, Matrix.le_iff, ← Matrix.blockDiagonal_sub]
  exact Matrix.posSemidef_blockDiagonal
    (fun c => Matrix.le_iff.mp (ρ.stateMap_le_quantumMarginal c))

end InfoTheory.SmoothMinEntropy
