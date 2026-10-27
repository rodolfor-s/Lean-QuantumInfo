import QCryptLean.InfoTheory.Renyi.ConditionalVariance.CQReference
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
import QCryptLean.InfoTheory.Renyi.PetzConditional
import QCryptLean.InfoTheory.Renyi.Basic
import QCryptLean.InfoTheory.Renyi.CQReference
import QCryptLean.InfoTheory.Renyi.PetzTensor
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.CollisionReference
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapBound
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Petz Smooth -/


namespace InfoTheory.Renyi
open Matrix Quantum.Operators InfoTheory.SmoothMinEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open private nsW nsL nsW_nonneg ns_sum_one nsW_exp_sum
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private mulVec_eq_zero_of_le
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.CQReference
open private petzTrace_blocks
  from QCryptLean.InfoTheory.Renyi.PetzTensor
variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q]

/-- A normalized CQ state has a positive fixed-marginal Petz trace at every positive order. -/
theorem petzTrace_marginal_pos (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    {α : ℝ} (hα : 0 < α) :
    0 < petzTrace α ρ.toJointOp (blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp)) := by
  let hR : ρ.toJointOp.IsHermitian := ρ.toJointDensity.posSemidef.isHermitian
  let hS := (posSemidef_blockDiagonal (fun _ : C => ρ.quantumMarginal.posSemidef)).isHermitian
  have hnorm : ρ.toJointOp.trace.re = 1 := (ρ.toJointDensity_trace).trans hρ
  have hsupp (v : Q × C → ℂ) := mulVec_eq_zero_of_le ρ.toJointDensity.posSemidef.nonneg
    ρ.toJointOp_le_reference (v := v)
  rw [← nsW_exp_sum hR hS ρ.toJointDensity.posSemidef.nonneg
    (posSemidef_blockDiagonal (fun _ : C => ρ.quantumMarginal.posSemidef)).nonneg hsupp hα]
  have hnn (p : (Q × C) × (Q × C)) : 0 ≤ nsW hR hS p :=
    nsW_nonneg hR hS ρ.toJointDensity.posSemidef.nonneg p
  obtain ⟨p, hp, hw⟩ := (Finset.sum_pos_iff_of_nonneg (fun p _ => hnn p)).mp
    (show 0 < ∑ p, nsW hR hS p by rw [ns_sum_one hR hS hnorm]; norm_num)
  exact (Finset.sum_pos_iff_of_nonneg (fun p _ =>
    mul_nonneg (hnn p) (Real.exp_pos _).le)).mpr ⟨p, hp, mul_pos hw (Real.exp_pos _)⟩

/-- The one-shot Petz floor holds for every positive smoothing radius and every order above one. -/
theorem ofReal_condPetzRenyiDown_sub_le_smoothMinEntropy
    (α : ℝ) (hα : 1 < α) (ε : ℝ) (hε : 0 < ε)
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1) :
    ENNReal.ofReal (condPetzRenyiDown α ρ - Real.logb 2 (2 / ε ^ 2) / (α - 1)) ≤
      smoothMinEntropy ε ρ ρ.quantumMarginal := by
  let : Nonempty Q := (ρ.quantumMarginalDensityOp hρ).nonempty
  have hs : 0 < α - 1 := sub_pos.mpr hα
  let M := petzTrace α ρ.toJointOp (blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp))
  have hM : 0 < M := petzTrace_marginal_pos ρ hρ (lt_trans zero_lt_one hα)
  have hq : 0 < 2 / ε ^ 2 := div_pos zero_lt_two (sq_pos_of_pos hε)
  let k := condPetzRenyiDown α ρ - Real.logb 2 (2 / ε ^ 2) / (α - 1)
  apply SpectralCap.ofReal_le_smoothMinEntropy_of_moment_bound ρ hρ ρ.quantumMarginal
    ⟨1, by
      refine ⟨zero_le_one, fun c => ?_⟩
      simpa only [Complex.ofReal_one, one_smul] using
        opLe_of_posSemidef_sub (Matrix.le_iff.mp (ρ.stateMap_le_quantumMarginal c))⟩
    k hs.le hε.le
  have he : (∑ c, ((ρ.stateMap c).toOp ^ (1 + (α - 1)) *
      ρ.quantumMarginal.toOp ^ (-(α - 1))).trace.re) = M := by
    rw [show 1 + (α - 1) = α by ring, show -(α - 1) = 1 - α by ring]
    exact (petzTrace_blocks α ρ).symm
  rw [he]
  have hek : -k * -(α - 1) = -Real.logb 2 M - Real.logb 2 (2 / ε ^ 2) := by
    dsimp [k, condPetzRenyiDown, petzRenyiDivergence, M]
    field_simp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), hek, sub_eq_add_neg,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb zero_lt_two (by norm_num) hM,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb zero_lt_two (by norm_num) hq]
  field_simp
  nlinarith

end InfoTheory.Renyi
