import QCryptLean.InfoTheory.Renyi.PetzConditional
import QCryptLean.InfoTheory.Renyi.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.Matrix.BlockCFC
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Math.LinearAlgebra.Matrix.TensorRpow
import QCryptLean.Quantum.Operators.Basic

/-! # Petz Tensor -/


noncomputable section
namespace InfoTheory.Renyi
open Matrix Quantum.Operators InfoTheory.SmoothMinEntropy
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {C Q : Type*} [Fintype C] [DecidableEq C] [Fintype Q] [DecidableEq Q]

omit [DecidableEq C] [DecidableEq Q] in
/-- The quantum marginal of a CQ tensor power is the tensor power of its marginal. -/
theorem _root_.InfoTheory.SmoothMinEntropy.CQState.tensorPower_quantumMarginal
    (ρ : CQState C Q) (k : ℕ) :
    (ρ.tensorPower k).quantumMarginal.toOp =
      piTensorProduct (fun _ : Fin k => ρ.quantumMarginal.toOp) := by
  ext x y
  change (∑ cs : Fin k → C, piTensorProduct (fun i => (ρ.stateMap (cs i)).toOp)) x y = _
  simp only [Matrix.sum_apply, piTensorProduct_apply, CQState.quantumMarginal]
  exact (Fintype.prod_sum (fun i : Fin k => fun c : C => (ρ.stateMap c).toOp (x i) (y i))).symm

private theorem petzTrace_blocks (α : ℝ) (ρ : CQState C Q) :
    petzTrace α ρ.toJointOp (blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp)) =
      ∑ c, petzTrace α (ρ.stateMap c).toOp ρ.quantumMarginal.toOp := by
  have hp (A : C → Op Q) (hA : ∀ c, (A c).PosSemidef) (r : ℝ) :
      blockDiagonal A ^ r = blockDiagonal (fun c => A c ^ r) := by
    rw [CFC.rpow_eq_cfc_real (posSemidef_blockDiagonal hA).nonneg,
      cfc_blockDiagonal _ (fun c => (hA c).isHermitian) _]
    congr 1
    funext c
    exact (CFC.rpow_eq_cfc_real (hA c).nonneg).symm
  simp only [petzTrace, CQState.toJointOp]
  rw [hp _ (fun c => (ρ.stateMap c).posSemidef),
    hp _ (fun _ => ρ.quantumMarginal.posSemidef), ← blockDiagonal_mul,
    trace_blockDiagonal, Complex.re_sum]

/-- The fixed-marginal Petz trace is multiplicative on every CQ tensor power. -/
theorem petzTrace_tensorPower (α : ℝ) (ρ : CQState C Q) (k : ℕ) :
    petzTrace α (ρ.tensorPower k).toJointOp
        (blockDiagonal (fun _ : Fin k → C => (ρ.tensorPower k).quantumMarginal.toOp)) =
      (petzTrace α ρ.toJointOp (blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp))) ^ k := by
  have hr (c : C) :
      (((ρ.stateMap c).toOp ^ α) * (ρ.quantumMarginal.toOp ^ (1 - α))).trace =
        (petzTrace α (ρ.stateMap c).toOp ρ.quantumMarginal.toOp : ℂ) := by
    have h := (Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := (ρ.stateMap c).toOp) (y := α))).trace_mul_nonneg
      (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := ρ.quantumMarginal.toOp) (y := 1 - α)))
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp h).2.symm
  rw [petzTrace_blocks, petzTrace_blocks]
  have ht (cs : Fin k → C) :
      petzTrace α ((ρ.tensorPower k).stateMap cs).toOp
        (ρ.tensorPower k).quantumMarginal.toOp =
          ∏ i : Fin k, petzTrace α (ρ.stateMap (cs i)).toOp ρ.quantumMarginal.toOp := by
    rw [CQState.tensorPower_quantumMarginal]
    change ((piTensorProduct (fun i => (ρ.stateMap (cs i)).toOp) ^ α) *
      (piTensorProduct (fun _ : Fin k => ρ.quantumMarginal.toOp) ^ (1 - α))).trace.re = _
    rw [PosSemidef.rpow_piTensorProduct _ (fun i => (ρ.stateMap (cs i)).posSemidef),
      PosSemidef.rpow_piTensorProduct _ (fun _ => ρ.quantumMarginal.posSemidef),
      piTensorProduct_mul, trace_piTensorProduct]
    simp only [hr, ← Complex.ofReal_prod, Complex.ofReal_re]
  simp_rw [ht]
  rw [← Fintype.prod_sum (fun _ : Fin k => fun c : C =>
    petzTrace α (ρ.stateMap c).toOp ρ.quantumMarginal.toOp)]
  simp

end InfoTheory.Renyi
