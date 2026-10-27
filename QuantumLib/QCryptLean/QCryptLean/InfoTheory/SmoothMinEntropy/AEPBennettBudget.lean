import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBennett
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPBits
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPLogEnvelope
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPRates
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.CollisionReference
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Exact Bennett calibration for native CQ moments -/
namespace InfoTheory.SmoothMinEntropy.AEP.IID
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder
open private bennett_remainder_nonpos
  from QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBennett
variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q]

/-- In the Bennett regime, the exact negative tilt meets the smoothing moment budget. -/
theorem exists_bennett_moment_budget (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) (σ : DensityOp Q)
    (hscale : HasScale ρ σ.toSubDensityOp) (k : ℕ) [NeZero k] (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hregime : InfoTheory.SmoothMinEntropy.AEP.IID.BennettRegime k ε) :
    ∃ s : ℝ, 0 ≤ s ∧
      2 * ((2 : ℝ) ^ (-bitBennettBlockEntropyFloor ρ hρ σ k ε)) ^ (-s) *
        (∑ c, ((ρ.stateMap c).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace.re) ^ k ≤ ε ^ 2 := by
  let w := InfoTheory.SmoothMinEntropy.bennettTiltWidth k ε
  have hw : 0 ≤ w := InfoTheory.SmoothMinEntropy.bennettTiltWidth_nonneg k ε
  have hw1 : w ≤ 1 := InfoTheory.SmoothMinEntropy.bennettTiltWidth_le_one hregime
  have hμ : 1 < rtBoundBase ρ σ := by
    unfold rtBoundBase
    linarith [ρ.tracedSquareTimesInvFactor_nonneg σ, Nat.cast_nonneg (α := ℝ) ρ.classicalRank]
  have hL : 0 < Real.log (rtBoundBase ρ σ) := Real.log_pos hμ
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  let s := Real.log (1 + w) / Real.log (rtBoundBase ρ σ)
  have hs : 0 ≤ s := div_nonneg (Real.log_nonneg (by linarith)) hL.le
  have hv : s * Real.log (rtBoundBase ρ σ) = Real.log (1 + w) := div_mul_cancel₀ _ hL.ne'
  have hrange : s * Real.log (rtBoundBase ρ σ) ≤ Real.log 2 := by
    rw [hv]
    exact Real.log_le_log (by linarith) (by linarith)
  let M := ∑ c, ((ρ.stateMap c).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace.re
  have hM : 0 < M := Spectral.moment_pos ρ hρ σ hscale hs
  let bnd := -s * referenceCondVonNeumannBits ρ hρ σ +
    (Real.exp (Real.log (1 + w)) - Real.log (1 + w) - 1) / Real.log 2
  have hb : Real.logb 2 M ≤ bnd := by
    have h := Spectral.logb_moment_le ρ hρ σ hscale hs hrange
    rwa [hv] at h
  have hm : M ≤ (2 : ℝ) ^ bnd := by
    conv_lhs => rw [← Real.rpow_logb zero_lt_two (by norm_num) hM]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hb
  have hds : bennettPenalty ρ σ k ε * s = Real.log (1 + w) * w / Real.log 2 := by
    dsimp [bennettPenalty, s, Real.logb, w]
    field_simp
  have hstep : (Real.exp (Real.log (1 + w)) - Real.log (1 + w) - 1) / Real.log 2 -
      bennettPenalty ρ σ k ε * s + (3 * w ^ 2 / (6 + 2 * w)) / Real.log 2 ≤ 0 := by
    rw [hds]
    have he : (Real.exp (Real.log (1 + w)) - Real.log (1 + w) - 1) / Real.log 2 -
        Real.log (1 + w) * w / Real.log 2 + (3 * w ^ 2 / (6 + 2 * w)) / Real.log 2 =
        (Real.exp (Real.log (1 + w)) - Real.log (1 + w) - 1 - Real.log (1 + w) * w +
          3 * w ^ 2 / (6 + 2 * w)) / Real.log 2 := by ring
    rw [he]
    exact div_nonpos_of_nonpos_of_nonneg (bennett_remainder_nonpos hw) hl2.le
  have hexp : -bitBennettBlockEntropyFloor ρ hρ σ k ε * -s + bnd * (k : ℝ) ≤
      -(k : ℝ) * (3 * w ^ 2 / (6 + 2 * w)) / Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg k)
    apply sub_nonpos.mp
    calc
      _ = (k : ℝ) * ((Real.exp (Real.log (1 + w)) - Real.log (1 + w) - 1) / Real.log 2 -
          bennettPenalty ρ σ k ε * s + (3 * w ^ 2 / (6 + 2 * w)) / Real.log 2) := by
        dsimp [bitBennettBlockEntropyFloor, bitBennettEntropyFloor, bnd]
        ring
      _ ≤ 0 := by simpa only [mul_zero] using hh
  refine ⟨s, hs, ?_⟩
  calc
    _ ≤ 2 * ((2 : ℝ) ^ (-bitBennettBlockEntropyFloor ρ hρ σ k ε)) ^ (-s) *
        ((2 : ℝ) ^ bnd) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM.le hm k) (by positivity)
    _ = 2 * (2 : ℝ) ^ (-bitBennettBlockEntropyFloor ρ hρ σ k ε * -s + bnd * (k : ℝ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ bnd) k,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * (2 : ℝ) ^ (-(k : ℝ) * (3 * w ^ 2 / (6 + 2 * w)) / Real.log 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) zero_le_two
    _ ≤ ε ^ 2 := by
      have h := InfoTheory.SmoothMinEntropy.AEP.IID.bennettRtErrorBound_le_smoothingTraceBudget
        (n_copies := k) hε hε1 (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k))
      change (2 : ℝ) ^ (-(k : ℝ) * (3 * w ^ 2 / (6 + 2 * w)) / Real.log 2) ≤ ε ^ 2 / 2 at h
      linarith

end InfoTheory.SmoothMinEntropy.AEP.IID
