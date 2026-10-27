import QCryptLean.InfoTheory.Renyi.FiniteSizePenalty
import QCryptLean.InfoTheory.Renyi.SecondOrderConstants
import QCryptLean.InfoTheory.Renyi.SecondOrderRemainderBounds
import QCryptLean.InfoTheory.Security.FiniteKey
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.Math.Analysis.LogBounds
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.BernoulliTails
import QCryptLean.QKD.Acceptance
import QCryptLean.QKD.BB84.Comparison.KeyLengthGap
import QCryptLean.QKD.BB84.Comparison.TupkaryTanLutkenhaus
import QCryptLean.QKD.BB84.Completeness
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellHaarMixture
import QCryptLean.QKD.BB84.FiniteKey.KeyRate.BellRenyi
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhaseTail
import QCryptLean.QKD.BB84.LinearReconciliation
import QCryptLean.QKD.BB84.Measurement.HonestSource
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Parameters
import QCryptLean.QKD.BB84.QuantitativeRobustness
import QCryptLean.QKD.BB84.Reduction.PackedSelector
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.MatchedCounts
import QCryptLean.QKD.BB84.Sampling.QuotaFailure
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.Security.BellRenyi
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.Protocol
import QCryptLean.Quantum.Operators.Basic

/-! # Million Sifted Rounds -/


open Quantum.Operators (Op)

open Math.Combinatorics

open InfoTheory.Renyi

open Math.ClassicalEntropy Quantum.DeFinetti

noncomputable section

namespace QKD.BB84.Comparison

open QKD.BB84.FiniteKey
open LOCC

/-- Reconciliation schemes with 500000 key bits and 24700 syndrome bits
on the million-sifted layout. -/
abbrev MillionSiftedECScheme :=
  ECScheme (500000 + 250000 + 250000) (@Sampling.packedPESel 500000 250000 250000) 24700

/-- Honest decoding failure budget: the KL tail at decoding radius `2761` over the 500000 key
rounds, plus a 21-bit collision margin. -/
def millionSiftedDecodingBudget : ℝ :=
  Real.exp
    (-(500000 : ℝ) * Math.Concentration.BernoulliKL.klBer ((2761 : ℝ) / 500000) (1 / 200)) +
    1 / (2 : ℝ) ^ 21


/-- `h₂(177/20000)` in closed form, from `177/20000 = (3²/2¹⁰)·(1888/1875)`. -/
private lemma binaryEntropy_177_eq :
    binaryEntropy ((177 : ℝ) / 20000) =
      (177 / 20000) * (10 * Real.log 2 - 2 * Real.log 3 - Real.log ((1888 : ℝ) / 1875))
        + (19823 / 20000) * Real.log ((20000 : ℝ) / 19823) := by
  rw [binaryEntropy, entropyTerm_eq_neg_mul_log, entropyTerm_eq_neg_mul_log]
  have h1 : Real.log ((177 : ℝ) / 20000)
      = 2 * Real.log 3 - 10 * Real.log 2 + Real.log ((1888 : ℝ) / 1875) := by
    rw [show ((177 : ℝ) / 20000) = (3 ^ 2 / 2 ^ 10) * (1888 / 1875) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_div (by norm_num) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h2 : Real.log ((1 : ℝ) - 177 / 20000) = -Real.log ((20000 : ℝ) / 19823) := by
    rw [show ((1 : ℝ) - 177 / 20000) = ((20000 : ℝ) / 19823)⁻¹ by norm_num, Real.log_inv]
  rw [h1, h2]
  ring

/-- **`h₂(177/20000) ∈ [0.0506, 0.0507]`** (true `0.0506477`).  `177/20000 = Q + δ + dev` is the
phase-error bracket of the key-rate condition and the accept tail; the width `10⁻⁴` moves the
rate term by `≈ 72` bits (`≈ 36` per side), well inside its ≈ 319-bit true slack. -/
private lemma binaryEntropy_177_bounds :
    (506 : ℝ) / 10000 ≤ binaryEntropy ((177 : ℝ) / 20000) ∧
      binaryEntropy ((177 : ℝ) / 20000) ≤ 507 / 10000 := by
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  have h3hi := Real.log_three_lt_d8
  -- `2·log 3 = 3·log 2 + log(9/8)` with the Padé lower bound `2/17 ≤ log(9/8)`
  have h98 : 2 * Real.log 3 = 3 * Real.log 2 + Real.log ((9 : ℝ) / 8) := by
    rw [Real.log_div (by norm_num) (by norm_num), show ((9 : ℝ)) = 3 ^ 2 by norm_num,
      show ((8 : ℝ)) = 2 ^ 3 by norm_num, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h98lo : (2 : ℝ) / 17 ≤ Real.log ((9 : ℝ) / 8) := by
    have hp := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 / 8 by norm_num)
    rw [show ((1 : ℝ) + 1 / 8) = 9 / 8 by norm_num] at hp
    norm_num at hp
    exact hp
  have ha := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1888 / 1875 by norm_num)
  have hb := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1888 / 1875 by norm_num)
  have hc := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 20000 / 19823 by norm_num)
  have hd := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 20000 / 19823 by norm_num)
  norm_num at ha hb hc hd
  rw [binaryEntropy_177_eq]
  constructor
  · linarith
  · linarith

/-- **`klBer(23/4000) (177/20000) ≥ 224·log 2/250000 ≈ 6.21·10⁻⁴`** (true `6.25·10⁻⁴`), so the
accept tail is at most `2⁻²²⁴` and its square root at most `2⁻¹¹²`. -/
private lemma klBer_23_4000_177_20000_ge :
    (224 : ℝ) * Real.log 2 / 250000 ≤
      Math.Concentration.BernoulliKL.klBer ((23 : ℝ) / 4000) ((177 : ℝ) / 20000) := by
  have h2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h3hi : Real.log 3 < 1.09861233 := Real.log_three_lt_d8
  -- Padé upper bound on `log(1 + 3/115)` and Padé lower bound on `log(1 + 62/19823)`
  have hp1 := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (3 / 115)
    (show (0 : ℝ) ≤ 3 / 115 by norm_num)
  have hp2 := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 62 / 19823 by norm_num)
  norm_num at hp1 hp2
  -- `log(115/177) = log 2 - log 3 - log(1 + 3/115)`, from `115/177 = (2/3)·(115/118)`
  have h1 : Real.log ((115 : ℝ) / 177) = Real.log 2 - Real.log 3 - Real.log (1 + 3 / 115) := by
    have e : ((118 : ℝ) / 115) = 1 + 3 / 115 := by norm_num
    rw [show ((115 : ℝ) / 177) = 2 / 3 * (115 / 118) from by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num),
      show ((115 : ℝ) / 118) = ((118 : ℝ) / 115)⁻¹ from by norm_num, Real.log_inv, e]
    ring
  have h2 : Real.log ((19885 : ℝ) / 19823) = Real.log (1 + 62 / 19823) := by
    rw [show ((19885 : ℝ) / 19823) = 1 + 62 / 19823 from by norm_num]
  rw [Math.Concentration.BernoulliKL.klBer,
    show (((23 : ℝ) / 4000) / (177 / 20000)) = 115 / 177 from by norm_num,
    show (((1 : ℝ) - 23 / 4000) / (1 - 177 / 20000)) = 19885 / 19823 from by norm_num,
    h1, h2, div_le_iff₀ (show (0 : ℝ) < 250000 by norm_num)]
  linarith

/-- **`klBer(23/4000) (1/200) ≥ 13.4/250000`** (true `13.48/250000`): the upper Z-test tail
exponent of the honest abort budget. -/
private lemma klBer_23_4000_one_200_ge :
    (13.4 : ℝ) / 250000 ≤
      Math.Concentration.BernoulliKL.klBer ((23 : ℝ) / 4000) ((1 : ℝ) / 200) := by
  -- `log(23/20) = log(1.1) + log(1 + 1/22)`, from `23/20 = (11/10)·(23/22)`
  have h1 : Real.log ((23 : ℝ) / 20) = Real.log 1.1 + Real.log (1 + 1 / 22) := by
    rw [show ((23 : ℝ) / 20) = 1.1 * (23 / 22) from by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      show ((23 : ℝ) / 22) = 1 + 1 / 22 from by norm_num]
  -- `log(3977/3980) = -log(1 + 3/3977)`
  have h2 : Real.log ((3977 : ℝ) / 3980) = -Real.log (1 + 3 / 3977) := by
    rw [show ((3977 : ℝ) / 3980) = ((3980 : ℝ) / 3977)⁻¹ from by norm_num, Real.log_inv,
      show ((3980 : ℝ) / 3977) = 1 + 3 / 3977 from by norm_num]
  -- Padé lower bound on `log(1 + 1/22)` and Padé upper bound on `log(1 + 3/3977)`
  have hp1 := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 / 22 by norm_num)
  have hp2 := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (3 / 3977)
    (show (0 : ℝ) ≤ 3 / 3977 by norm_num)
  norm_num at hp1 hp2
  rw [Math.Concentration.BernoulliKL.klBer,
    show (((23 : ℝ) / 4000) / (1 / 200)) = 23 / 20 from by norm_num,
    show (((1 : ℝ) - 23 / 4000) / (1 - 1 / 200)) = 3977 / 3980 from by norm_num,
    h1, h2, div_le_iff₀ (show (0 : ℝ) < 250000 by norm_num)]
  linarith [Real.log_one_point_one_gt_d4]

/-- **`klBer(17/4000) (1/200) ≥ 14.7/250000`** (true `14.894/250000`): the lower Z-test tail
exponent of the honest abort budget. -/
private lemma klBer_17_4000_one_200_ge :
    (14.7 : ℝ) / 250000 ≤
      Math.Concentration.BernoulliKL.klBer ((17 : ℝ) / 4000) ((1 : ℝ) / 200) := by
  -- `log(17/20) = -(log 1.25 - log(9/8) + log(1 + 1/17))` from
  -- `20/17 = (5/4)·(16/17)` and `16/17 = (8/9)·(18/17)`
  have hneg : Real.log ((17 : ℝ) / 20) = -Real.log ((20 : ℝ) / 17) := by
    rw [show ((17 : ℝ) / 20) = ((20 : ℝ) / 17)⁻¹ from by norm_num, Real.log_inv]
  have e1 : Real.log ((20 : ℝ) / 17) = Real.log 1.25 + Real.log ((16 : ℝ) / 17) := by
    rw [show ((20 : ℝ) / 17) = 1.25 * (16 / 17) from by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have e2 : Real.log ((16 : ℝ) / 17) = -Real.log ((9 : ℝ) / 8) + Real.log (1 + 1 / 17) := by
    rw [show ((16 : ℝ) / 17) = (8 / 9) * (18 / 17) from by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      show ((8 : ℝ) / 9) = ((9 : ℝ) / 8)⁻¹ from by norm_num, Real.log_inv,
      show ((18 : ℝ) / 17) = 1 + 1 / 17 from by norm_num]
  -- `log(9/8) = log(1.1) + log(1 + 1/44)`, from `9/8 = (11/10)·(45/44)`
  have e4 : Real.log ((9 : ℝ) / 8) = Real.log 1.1 + Real.log (1 + 1 / 44) := by
    rw [show ((9 : ℝ) / 8) = 1.1 * (45 / 44) from by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      show ((45 : ℝ) / 44) = 1 + 1 / 44 from by norm_num]
  -- Padé lower bounds on `log(1 + 1/44)` and `log(1 + 3/3980)`, Padé upper bound on
  -- `log(1 + 1/17)`
  have hp1 := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 / 44 by norm_num)
  have hp2 := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (1 / 17)
    (show (0 : ℝ) ≤ 1 / 17 by norm_num)
  have hp3 := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 3 / 3980 by norm_num)
  norm_num at hp1 hp2 hp3
  rw [Math.Concentration.BernoulliKL.klBer,
    show (((17 : ℝ) / 4000) / (1 / 200)) = 17 / 20 from by norm_num,
    show (((1 : ℝ) - 17 / 4000) / (1 - 1 / 200)) = 3983 / 3980 from by norm_num,
    show ((3983 : ℝ) / 3980) = 1 + 3 / 3980 from by norm_num,
    hneg, e1, e2, e4, div_le_iff₀ (show (0 : ℝ) < 250000 by norm_num)]
  linarith [Real.log_one_point_one_gt_d4, Real.log_one_point_two_five_lt_d5]

/-- **`klBer(2761/500000) (1/200) ≥ 13/500000`** (true `13.24/500000`): the decoding-tail
exponent of the honest abort budget. -/
private lemma klBer_decode_ge :
    (13 : ℝ) / 500000 ≤
      Math.Concentration.BernoulliKL.klBer ((2761 : ℝ) / 500000) ((1 : ℝ) / 200) := by
  -- `log(2761/2500) = log(1.1) + log(1 + 11/2750)`, from `2761/2500 = (11/10)·(2761/2750)`
  have h1 : Real.log ((2761 : ℝ) / 2500) = Real.log 1.1 + Real.log (1 + 11 / 2750) := by
    rw [show ((2761 : ℝ) / 2500) = 1.1 * (2761 / 2750) from by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      show ((2761 : ℝ) / 2750) = 1 + 11 / 2750 from by norm_num]
  -- `log(497239/497500) = -log(1 + 261/497239)`
  have h2 : Real.log ((497239 : ℝ) / 497500) = -Real.log (1 + 261 / 497239) := by
    rw [show ((497239 : ℝ) / 497500) = ((497500 : ℝ) / 497239)⁻¹ from by norm_num, Real.log_inv,
      show ((497500 : ℝ) / 497239) = 1 + 261 / 497239 from by norm_num]
  -- Padé lower bound on `log(1 + 11/2750)`, Padé upper bound on `log(1 + 261/497239)`
  have hp1 := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 11 / 2750 by norm_num)
  have hp2 := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (261 / 497239)
    (show (0 : ℝ) ≤ 261 / 497239 by norm_num)
  norm_num at hp1 hp2
  rw [Math.Concentration.BernoulliKL.klBer,
    show (((2761 : ℝ) / 500000) / (1 / 200)) = 2761 / 2500 from by norm_num,
    show (((1 : ℝ) - 2761 / 500000) / (1 - 1 / 200)) = 497239 / 497500 from by norm_num,
    h1, h2, div_le_iff₀ (show (0 : ℝ) < 500000 by norm_num)]
  linarith [Real.log_one_point_one_gt_d4]

/-- **Both quota-tail exponents at the uniform four-million-round layout exceed 100 nats**
(`4000000·klBer(749999/4000000) (1/4)` and `4000000·klBer(249999/4000000) (1/4)`; the uniform
matched probability is `1/4`, and the divergences themselves are ≈ 0.011 and ≈ 0.12). -/
private lemma klBer_quota_million_ge :
    (100 : ℝ) ≤ 4000000 * Math.Concentration.BernoulliKL.klBer
        ((749999 : ℝ) / 4000000) ((1 : ℝ) / 4) ∧
      (100 : ℝ) ≤ 4000000 * Math.Concentration.BernoulliKL.klBer
        ((249999 : ℝ) / 4000000) ((1 : ℝ) / 4) := by
  constructor
  · -- quadratic KL bound with `c = 2 ≤ 1/(2b)`: `2·(250001/4000000)² ≤ klBer`, and
    -- `4000000·2·(250001/4000000)² = 31250.25`
    have h := Math.Concentration.BernoulliKL.mul_sq_le_klBer
      (a := (749999 : ℝ) / 4000000) (b := (1 : ℝ) / 4) (c := 2)
      (show (0 : ℝ) < 749999 / 4000000 by norm_num)
      (show (749999 : ℝ) / 4000000 ≤ 1 / 4 by norm_num)
      (show ((1 : ℝ) / 4) < 1 by norm_num)
      (show (2 : ℝ) * 2 * (1 / 4) ≤ 1 by norm_num)
    rw [show ((1 : ℝ) / 4 - 749999 / 4000000) = 250001 / 4000000 from by norm_num] at h
    calc (100 : ℝ) ≤ 4000000 * (2 * (250001 / 4000000) ^ 2) := by norm_num
      _ ≤ 4000000 * Math.Concentration.BernoulliKL.klBer ((749999 : ℝ) / 4000000)
          ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_left h (by norm_num)
  · have h := Math.Concentration.BernoulliKL.mul_sq_le_klBer
      (a := (249999 : ℝ) / 4000000) (b := (1 : ℝ) / 4) (c := 2)
      (show (0 : ℝ) < 249999 / 4000000 by norm_num)
      (show (249999 : ℝ) / 4000000 ≤ 1 / 4 by norm_num)
      (show ((1 : ℝ) / 4) < 1 by norm_num)
      (show (2 : ℝ) * 2 * (1 / 4) ≤ 1 by norm_num)
    rw [show ((1 : ℝ) / 4 - 249999 / 4000000) = 750001 / 4000000 from by norm_num] at h
    calc (100 : ℝ) ≤ 4000000 * (2 * (750001 / 4000000) ^ 2) := by norm_num
      _ ≤ 4000000 * Math.Concentration.BernoulliKL.klBer ((249999 : ℝ) / 4000000)
          ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_left h (by norm_num)

/-- **`h₂(69/12500) ≤ 24679/500000`** (true `≈ 0.04934781674`): `69/12500 = 2760/500000` is the
decoder's normalised radius, and the entropy test funds its ball within 24700 syndrome bits. -/
private lemma binaryEntropy_69_12500_le :
    binaryEntropyBits ((69 : ℝ) / 12500) ≤ 24679 / 500000 := by
  -- `12500/69 = 2⁷·1.25·(1 + 1/8)·(1 + 4/621)`, so `−log p = 7·log 2 + log 1.25 + log(1+1/8)
  -- + log(1 + 4/621)`
  have h1 : Real.log ((69 : ℝ) / 12500)
      = -(7 * Real.log 2 + Real.log 1.25 + Real.log (1 + 1 / 8)
          + Real.log (1 + 4 / 621)) := by
    rw [show ((69 : ℝ) / 12500)
        = ((2 ^ 7 : ℝ) * 1.25 * (1 + 1 / 8) * (1 + 4 / 621))⁻¹ from by norm_num,
      Real.log_inv, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  -- `log(1 − p) = −log(1 + 69/12431)`
  have h2 : Real.log ((1 : ℝ) - 69 / 12500) = -Real.log (1 + 69 / 12431) := by
    rw [show ((1 : ℝ) - 69 / 12500) = ((12500 : ℝ) / 12431)⁻¹ from by norm_num, Real.log_inv,
      show ((12500 : ℝ) / 12431) = 1 + 69 / 12431 from by norm_num]
  -- Padé `[2,1]` upper bounds on the three small logs
  have hp1 := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (1 / 8)
    (show (0 : ℝ) ≤ 1 / 8 by norm_num)
  have hp2 := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (4 / 621)
    (show (0 : ℝ) ≤ 4 / 621 by norm_num)
  have hp3 := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (69 / 12431)
    (show (0 : ℝ) ≤ 69 / 12431 by norm_num)
  norm_num at hp1 hp2 hp3
  unfold binaryEntropyBits
  rw [binaryEntropy, entropyTerm_eq_neg_mul_log, entropyTerm_eq_neg_mul_log, h1, h2,
    div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, Real.log_one_point_two_five_lt_d5]


/-- `C(1000003, 3) ≤ 2⁵⁸` (true value `2^57.2098`). -/
private lemma choose_million_three_le :
    ((Nat.choose 1000003 3 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 58 := by
  have h := Nat.choose_le_pow_div (α := ℝ) 3 1000003
  rw [show ((Nat.factorial 3 : ℕ) : ℝ) = 6 from by norm_num [Nat.factorial]] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by norm_num)]
  norm_num

/-- `C(1000003, 3) ≤ (5/4)·2⁵⁷` (true value `2^57.2098`): the sharper prefactor bracket behind
the Bell-budget certificate, a factor `5/8 = 2^(−0.678…)` times `choose_million_three_le`. -/
private lemma choose_million_three_le_five_quarters :
    ((Nat.choose 1000003 3 : ℕ) : ℝ) ≤ (5 : ℝ) / 4 * (2 : ℝ) ^ 57 := by
  have h := Nat.choose_le_pow_div (α := ℝ) 3 1000003
  rw [show ((Nat.factorial 3 : ℕ) : ℝ) = 6 from by norm_num [Nat.factorial]] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by norm_num)]
  norm_num

/-- `2⁵⁷ ≤ C(1000003, 3)`. -/
private lemma choose_million_three_ge :
    (2 : ℝ) ^ 57 ≤ ((Nat.choose 1000003 3 : ℕ) : ℝ) := by
  have h := Nat.pow_le_choose (α := ℝ) 3 1000003
  rw [show (1000003 + 1 - 3 : ℕ) = 1000001 from by norm_num,
    show ((Nat.factorial 3 : ℕ) : ℝ) = 6 from by norm_num [Nat.factorial]] at h
  refine le_trans ?_ h
  rw [le_div_iff₀ (by norm_num)]
  norm_num

/-- **`57·log 2 ≤ log C(1000003, 3) ≤ 58·log 2`**. -/
private lemma log_choose_million_three_bounds :
    57 * Real.log 2 ≤ Real.log ((Nat.choose 1000003 3 : ℕ) : ℝ) ∧
      Real.log ((Nat.choose 1000003 3 : ℕ) : ℝ) ≤ 58 * Real.log 2 := by
  have hCpos : (0 : ℝ) < ((Nat.choose 1000003 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 3 ≤ 1000003 by norm_num)
  constructor
  · have := Real.log_le_log (by positivity) choose_million_three_ge
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  · have := Real.log_le_log hCpos choose_million_three_le
    rwa [Real.log_pow, Nat.cast_ofNat] at this


/-- **The free-offset Cor IV.2 penalty at `500 000` key rounds, `ε_AEP = 2⁻¹¹²` and `β = 1/40`
is approximately `16 931`**, bracketed `[16 770, 17 107]` using `5/2 ≤ K_β ≤ 7/2` and
`V·log 2 ∈ [1.1195, 1.122]` (`binaryVarianceBound_mul_log_two_mem_Icc`). The exact form is
`(V·log 2)·6250 + K_β·625/2 + 9000`; the third summand is exact because
`logb 2 (2/2⁻²²⁴) = 225 = 9000/40`. -/
private lemma renyiPenalty_million_bounds :
    (16770 : ℝ) ≤ renyiPenalty binaryVarianceBound 500000
        (((2 : ℝ) ^ 112)⁻¹) (1 / 40) ∧
      renyiPenalty binaryVarianceBound 500000
        (((2 : ℝ) ^ 112)⁻¹) (1 / 40) ≤ 17107 := by
  obtain ⟨hlo, hhi⟩ := binaryVarianceBound_mul_log_two_mem_Icc
  have hsplit : renyiPenalty binaryVarianceBound 500000
      (((2 : ℝ) ^ 112)⁻¹) (1 / 40)
      = (binaryVarianceBound * Real.log 2) * 6250
        + InfoTheory.Renyi.binarySecondOrderRemainderBound (1 / 40) * (625 / 2) + 9000 := by
    simp only [renyiPenalty,
    InfoTheory.Renyi.renyiVariancePenalty,
    InfoTheory.Renyi.renyiRemainderPenalty,
    InfoTheory.Renyi.renyiSmoothingPenalty,
    InfoTheory.Renyi.smoothingLog]
    -- the third summand is exact: `2 / (2⁻¹¹²)² = 2²²⁵`, so `log₂ = 225`
    have hpow : Real.logb 2 (2 / (((2 : ℝ) ^ 112)⁻¹ ^ 2)) = 225 := by
      rw [show (2 / (((2 : ℝ) ^ 112)⁻¹ ^ 2) : ℝ) = (2 : ℝ) ^ 225 from by
          norm_num [inv_pow], Real.logb_pow]
      norm_num
    rw [hpow]
    ring
  have hKup := InfoTheory.Renyi.binarySecondOrderRemainderBound_le_seven_halves
    (1 / 40) (by norm_num)
  have hKlo : (5 : ℝ) / 2 ≤ InfoTheory.Renyi.binarySecondOrderRemainderBound (1 / 40) := by
    have hbase := InfoTheory.Renyi.five_halves_le_binarySecondOrderRemainderBase
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 40) :=
      Real.one_le_rpow (by norm_num) (by norm_num)
    unfold InfoTheory.Renyi.binarySecondOrderRemainderBound
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (1 - 1 / 40) ^ 3)]
    have hmul := mul_le_mul_of_nonneg_left hpow (show
      0 ≤ InfoTheory.Renyi.binarySecondOrderRemainderBase by linarith)
    nlinarith
  rw [hsplit]
  constructor
  · linarith
  · linarith


/-- **`log₂(1/ε_PA) ∈ [108, 109]`** at the Bell-symmetric lift over `10⁶` rounds (true
`108.2098`). -/
private lemma logb_inv_liftedPrivacyAmplificationError_million_bounds :
    (108 : ℝ) ≤ Real.logb 2 (liftedPrivacyAmplificationError 4 1000000
        (((2 : ℝ) ^ 50)⁻¹))⁻¹ ∧
      Real.logb 2 (liftedPrivacyAmplificationError 4 1000000 (((2 : ℝ) ^ 50)⁻¹))⁻¹
        ≤ 109 := by
  obtain ⟨hglo, hghi⟩ := log_choose_million_three_bounds
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  rw [logb_inv_liftedPrivacyAmplificationError_inv_two_pow, deFinettiPrefactor_four,
    show (1000000 + 3 : ℕ) = 1000003 from by norm_num, Real.logb]
  norm_num only [Nat.cast_ofNat]
  have h1 : (57 : ℝ) ≤ Real.log ((Nat.choose 1000003 3 : ℕ) : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hL]
    linarith
  have h2 : Real.log ((Nat.choose 1000003 3 : ℕ) : ℝ) / Real.log 2 ≤ 58 := by
    rw [div_le_iff₀ hL]
    linarith
  constructor
  · linarith
  · linarith

/-- **The Bell-lifted literature penalty at `500 000` key rounds is `23 422.92`**, bracketed
`[23 325, 23 601]`. -/
private lemma literatureFiniteSizePenalty_million_bounds :
    (23325 : ℝ) ≤ literatureFiniteSizePenalty 500000
        (liftedPrivacyAmplificationError 4 1000000 (((2 : ℝ) ^ 50)⁻¹)) ∧
      literatureFiniteSizePenalty 500000
          (liftedPrivacyAmplificationError 4 1000000 (((2 : ℝ) ^ 50)⁻¹)) ≤ 23601 := by
  obtain ⟨hWlo, hWhi⟩ := logb_inv_liftedPrivacyAmplificationError_million_bounds
  obtain ⟨hb3lo, hb3hi⟩ := Real.logb_two_three_mem_Icc
  rw [literatureFiniteSizePenalty_eq_logb_three_mul_sqrt 500000 _ (by norm_num)
      (liftedPrivacyAmplificationError_pos _ _ (by positivity))
      (liftedPrivacyAmplificationError_lt_one _ _
        (inv_lt_one_of_one_lt₀ (one_lt_pow₀ one_lt_two (by norm_num))).le),
    show (((500000 : ℕ)) : ℝ) = 500000 from by norm_num]
  set W : ℝ :=
    Real.logb 2 (liftedPrivacyAmplificationError 4 1000000 (((2 : ℝ) ^ 50)⁻¹))⁻¹
  have hs_lo : (7348 : ℝ) ≤ Real.sqrt (500000 * W) := by
    calc (7348 : ℝ) = Real.sqrt ((7348 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  have hs_hi : Real.sqrt (500000 * W) ≤ 7383 := by
    calc Real.sqrt (500000 * W) ≤ Real.sqrt ((7383 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 7383 := Real.sqrt_sq (by norm_num)
  have hprod_lo : (1.58 : ℝ) * 7348 ≤ Real.logb 2 3 * Real.sqrt (500000 * W) :=
    mul_le_mul hb3lo hs_lo (by norm_num) (by linarith)
  have hprod_hi : Real.logb 2 3 * Real.sqrt (500000 * W) ≤ (1.591 : ℝ) * 7383 :=
    mul_le_mul hb3hi hs_hi (Real.sqrt_nonneg _) (by norm_num)
  constructor
  · linarith
  · linarith

/-- **The unlifted literature penalty at `500 000` key rounds is at most `16 119`** (true
`16 056.34`): prefactor `1`, so `ε_PA = 2⁻⁵¹`. -/
private lemma literatureFiniteSizePenalty_one_million_le :
    literatureFiniteSizePenalty 500000
        (liftedPrivacyAmplificationError 1 1000000 (((2 : ℝ) ^ 50)⁻¹)) ≤ 16119 := by
  obtain ⟨hb3lo, hb3hi⟩ := Real.logb_two_three_mem_Icc
  have hg : (deFinettiPrefactor 1 1000000 : ℝ) = 1 := by
    norm_num [deFinettiPrefactor]
  have hW : Real.logb 2 (liftedPrivacyAmplificationError 1 1000000
      (((2 : ℝ) ^ 50)⁻¹))⁻¹ = 51 := by
    rw [logb_inv_liftedPrivacyAmplificationError_inv_two_pow, hg, Real.logb_one]
    norm_num
  rw [literatureFiniteSizePenalty_eq_logb_three_mul_sqrt 500000 _ (by norm_num)
      (liftedPrivacyAmplificationError_pos _ _ (by positivity))
      (liftedPrivacyAmplificationError_lt_one _ _
        (inv_lt_one_of_one_lt₀ (one_lt_pow₀ one_lt_two (by norm_num))).le),
    hW, show (((500000 : ℕ)) : ℝ) = 500000 from by norm_num]
  have hs_hi : Real.sqrt (500000 * 51) ≤ 5050 := by
    calc Real.sqrt (500000 * 51) ≤ Real.sqrt ((5050 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 5050 := Real.sqrt_sq (by norm_num)
  have hprod_hi : Real.logb 2 3 * Real.sqrt (500000 * 51) ≤ (1.591 : ℝ) * 5050 :=
    mul_le_mul hb3hi hs_hi (Real.sqrt_nonneg _) (by norm_num)
  set s : ℝ := Real.logb 2 3 * Real.sqrt (500000 * 51)
  linarith


/-- **The shared rate term `500 000·(1 − h₂(177/20000)/log 2)` lies in `[463 420, 463 505]`**
(true ≈ `463 465`; over the `h₂` box `[0.0506, 0.0507]` and the 9-digit `log 2` box the true
range is `[463 427.7, 463 499.8]`). -/
private lemma rate_million_bounds :
    (463420 : ℝ) ≤ (500000 : ℝ) / Real.log 2 * (Real.log 2 - binaryEntropy ((177 : ℝ) / 20000)) ∧
      (500000 : ℝ) / Real.log 2 * (Real.log 2 - binaryEntropy ((177 : ℝ) / 20000)) ≤ 463505 := by
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨hh2lo, hh2hi⟩ := binaryEntropy_177_bounds
  rw [div_mul_eq_mul_div]
  constructor
  · rw [le_div_iff₀ hL]
    linarith
  · rw [div_le_iff₀ hL]
    linarith


/-- **`BellRenyiKeyRate` holds at `ℓ = 421 000`** (true slack
`378.0` bits): the rate term `321 247` nats funds leak, tag, `2·log C(1000003, 3)`, the
free-offset penalty and `2·log(1/2⁻¹¹⁴) − 2 log 2`. -/
private lemma bellRenyiKeyRate_million :
    BellRenyiKeyRate 1000000 500000 421000 116 24700 ((1 : ℝ) / 200) ((3 : ℝ) / 4000)
      (31 / 10000) (((2 : ℝ) ^ 112)⁻¹) (((2 : ℝ) ^ 114)⁻¹) (1 / 40) := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  -- the bracket `Q + δ + dev` is `177/20000`, and the key-round count is `500 000`
  have hQ : ((1 : ℝ) / 200 + 3 / 4000 + 31 / 10000) = (177 : ℝ) / 20000 := by norm_num
  have hK : (keyRounds 1000000 500000 : ℝ) = 500000 := by
    simp only [keyRounds]
    norm_num
  have hC3 : (Nat.choose (1000000 + 3) 3 : ℕ) = Nat.choose 1000003 3 := rfl
  -- the rate bound transposed into nats
  have hr2 : (463420 : ℝ) * Real.log 2 ≤
      (500000 : ℝ) * (Real.log 2 - binaryEntropy ((177 : ℝ) / 20000)) := by
    have h1 := (rate_million_bounds).1
    rw [div_mul_eq_mul_div] at h1
    rwa [le_div_iff₀ hL] at h1
  -- the funding terms in bits: 421000 + 24700 + 116 + 116 + 17107 + 226 = 463265 ≤ 463420
  obtain ⟨_, hC⟩ := log_choose_million_three_bounds
  have hCn : (2 : ℝ) * Real.log ((Nat.choose 1000003 3 : ℕ) : ℝ) ≤ 116 * Real.log 2 := by
    linarith
  have hPn : Real.log 2 * renyiPenalty binaryVarianceBound 500000
      (((2 : ℝ) ^ 112)⁻¹) (1 / 40) ≤ 17107 * Real.log 2 := by
    calc Real.log 2 * renyiPenalty binaryVarianceBound 500000
          (((2 : ℝ) ^ 112)⁻¹) (1 / 40) ≤
        Real.log 2 * 17107 :=
        mul_le_mul_of_nonneg_left (renyiPenalty_million_bounds).2 hL.le
      _ = 17107 * Real.log 2 := by ring
  have hpa : 2 * Real.log (1 / (((2 : ℝ) ^ 114)⁻¹)) = 228 * Real.log 2 := by
    rw [one_div, inv_inv, Real.log_pow]
    ring
  rw [bellRenyiKeyRate_iff]
  rw [hQ, hK, hC3, hpa]
  calc (421000 : ℝ) * Real.log 2 + 24700 * Real.log 2 + 116 * Real.log 2
        + 2 * Real.log ((Nat.choose 1000003 3 : ℕ) : ℝ)
        + Real.log 2 * renyiPenalty binaryVarianceBound 500000
            (((2 : ℝ) ^ 112)⁻¹) (1 / 40) + (228 * Real.log 2 - 2 * Real.log 2)
      ≤ 463267 * Real.log 2 := by linarith
    _ ≤ 463420 * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by norm_num) hL.le
    _ ≤ 500000 * (Real.log 2 - binaryEntropy ((177 : ℝ) / 20000)) := hr2

/-- **Every key length the Bell–Rényi key-rate condition admits at the witness point is below
`421 600`** (the real-valued key-rate threshold is approximately `421 378.0`). -/
private lemma lt_of_bellRenyiKeyRate_million {ℓ : ℕ}
    (h : BellRenyiKeyRate 1000000 500000 ℓ 116 24700 ((1 : ℝ) / 200) ((3 : ℝ) / 4000)
      (31 / 10000) (((2 : ℝ) ^ 112)⁻¹) (((2 : ℝ) ^ 114)⁻¹) (1 / 40)) :
    (ℓ : ℝ) < 421600 := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  -- the bracket `Q + δ + dev` is `177/20000`, and the key-round count is `500 000`
  have hQ : ((1 : ℝ) / 200 + 3 / 4000 + 31 / 10000) = (177 : ℝ) / 20000 := by norm_num
  have hK : (keyRounds 1000000 500000 : ℕ) = 500000 := by
    simp only [keyRounds]
  have hC3 : (Nat.choose (1000000 + 3) 3 : ℕ) = Nat.choose 1000003 3 := rfl
  -- the rate bound transposed into nats (upper side only)
  have hr2 : (500000 : ℝ) * (Real.log 2 - binaryEntropy ((177 : ℝ) / 20000)) ≤
      463505 * Real.log 2 := by
    have h1 := (rate_million_bounds).2
    rw [div_mul_eq_mul_div] at h1
    rwa [div_le_iff₀ hL] at h1
  -- the Bell floor term funds at least `114` bits
  have hCn : (114 : ℝ) * Real.log 2 ≤ 2 * Real.log ((Nat.choose 1000003 3 : ℕ) : ℝ) :=
    by linarith [log_choose_million_three_bounds.1]
  -- the free-offset penalty funds at least `16770` bits
  have hPn : (16770 : ℝ) * Real.log 2 ≤ Real.log 2 * renyiPenalty
      binaryVarianceBound 500000 (((2 : ℝ) ^ 112)⁻¹) (1 / 40) := by
    calc (16770 : ℝ) * Real.log 2 = Real.log 2 * 16770 := by ring
      _ ≤ Real.log 2 * renyiPenalty binaryVarianceBound 500000
            (((2 : ℝ) ^ 112)⁻¹) (1 / 40) :=
        mul_le_mul_of_nonneg_left (renyiPenalty_million_bounds).1 hL.le
  have hpa : 2 * Real.log (1 / (((2 : ℝ) ^ 114)⁻¹)) = 228 * Real.log 2 := by
    rw [one_div, inv_inv, Real.log_pow]
    ring
  rw [bellRenyiKeyRate_iff] at h
  rw [hQ, hK, hC3, hpa] at h
  have key : (ℓ : ℝ) * Real.log 2
      < 421600 * Real.log 2 := by
    calc (ℓ : ℝ) * Real.log 2
          ≤ (463505 - 24700 - 116 - 226) * Real.log 2 - (114 : ℝ) * Real.log 2
              - (16770 : ℝ) * Real.log 2 := by linarith
        _ = 421579 * Real.log 2 := by ring
        _ < 421600 * Real.log 2 := mul_lt_mul_of_pos_right (by norm_num) hL
  exact lt_of_mul_lt_mul_right key hL.le

/-- The penalty gap at the witness point is at least one bit:
`17107 + 116 + 228 − 1 = 17450 ≤ 23325`. -/
private lemma penaltyGap_million :
    renyiPenalty binaryVarianceBound 500000 (((2 : ℝ) ^ 112)⁻¹) (1 / 40)
        + 2 * Real.log ((Nat.choose 1000003 3 : ℕ) : ℝ) / Real.log 2
        + 2 * Real.log (1 / ((2 : ℝ) ^ 114)⁻¹) / Real.log 2 - 1
      ≤ literatureFiniteSizePenalty 500000
          (liftedPrivacyAmplificationError 4 1000000 (((2 : ℝ) ^ 50)⁻¹)) := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨-, hP⟩ := renyiPenalty_million_bounds
  obtain ⟨hLit, -⟩ := literatureFiniteSizePenalty_million_bounds
  -- the Bell floor term funds at most `116` bits
  have hB : 2 * Real.log ((Nat.choose 1000003 3 : ℕ) : ℝ) / Real.log 2 ≤ 116 := by
    rw [div_le_iff₀ hL]
    linarith [log_choose_million_three_bounds.2]
  -- the privacy-amplification error term is exactly `228` bits
  have hpa : 2 * Real.log (1 / (((2 : ℝ) ^ 114)⁻¹)) = 228 * Real.log 2 := by
    rw [one_div, inv_inv, Real.log_pow]
    ring
  have hC : 2 * Real.log (1 / ((2 : ℝ) ^ 114)⁻¹) / Real.log 2 = 228 := by
    rw [hpa, mul_div_cancel_right₀ _ (ne_of_gt hL)]
  calc renyiPenalty binaryVarianceBound 500000 (((2 : ℝ) ^ 112)⁻¹) (1 / 40)
        + 2 * Real.log ((Nat.choose 1000003 3 : ℕ) : ℝ) / Real.log 2
        + 2 * Real.log (1 / ((2 : ℝ) ^ 114)⁻¹) / Real.log 2 - 1
      ≤ (17107 : ℝ) + 116 + 228 + 1 := by linarith
    _ ≤ 23325 := by norm_num
    _ ≤ literatureFiniteSizePenalty 500000
          (liftedPrivacyAmplificationError 4 1000000 (((2 : ℝ) ^ 50)⁻¹)) := hLit


/-- **The honest abort budget at the relative-entropy rate is below `2⁻¹⁷`** (true value
`≈ 2^(−17.41)`), at the uniform matched probability `1/4`: two Z-test tails at `klBer(23/4000)`
and `klBer(17/4000)`, the decoding tail at `klBer(2761/500000)`, the 21-bit collision margin, and
two quota tails above 100 nats. -/
private lemma millionSifted_abortBound_le :
    abortBound 4000000 500000 250000 250000 ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        ((1 : ℝ) / 200) ((3 : ℝ) / 4000) ((1 : ℝ) / 200) millionSiftedDecodingBudget
      ≤ ((2 : ℝ) ^ 17)⁻¹ := by
  simp only [abortBound,
    testAbortBound,
    millionSiftedDecodingBudget,
    Math.Concentration.bernoulliChernoffTail,
    Math.Concentration.bernoulliWindowTail]
  norm_num
  have hLlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hLhi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  -- Padé `[2,1]` upper bounds on `log(8/7)` and `log(8/5)`
  have hp7 := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (1 / 7)
    (show (0 : ℝ) ≤ 1 / 7 by norm_num)
  rw [show ((1 : ℝ) + 1 / 7) = 8 / 7 from by norm_num] at hp7
  norm_num at hp7
  have hp5 := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (3 / 5)
    (show (0 : ℝ) ≤ 3 / 5 by norm_num)
  rw [show ((1 : ℝ) + 3 / 5) = 8 / 5 from by norm_num] at hp5
  norm_num at hp5
  -- `log 7 = 3·log 2 − log(8/7)` and `log 5 = 3·log 2 − log(8/5)`
  have h7 : Real.log 7 = 3 * Real.log 2 - Real.log ((8 : ℝ) / 7) := by
    rw [show Real.log (7 : ℝ) = Real.log ((2 : ℝ) ^ 3 / (8 / 7)) from by
        rw [show ((2 : ℝ) ^ 3 / (8 / 7)) = 7 from by norm_num],
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have h5 : Real.log 5 = 3 * Real.log 2 - Real.log ((8 : ℝ) / 5) := by
    rw [show Real.log (5 : ℝ) = Real.log ((2 : ℝ) ^ 3 / (8 / 5)) from by
        rw [show ((2 : ℝ) ^ 3 / (8 / 5)) = 5 from by norm_num],
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  -- exponent lower bounds from the bracket lemmas
  have hE3 : (13.4 : ℝ) ≤ 250000 * Math.Concentration.BernoulliKL.klBer ((23 : ℝ) / 4000)
      ((1 : ℝ) / 200) := by
    have h := klBer_23_4000_one_200_ge
    rw [div_le_iff₀ (show (0 : ℝ) < 250000 by norm_num), mul_comm] at h
    exact h
  have hE4 : (14.7 : ℝ) ≤ 250000 * Math.Concentration.BernoulliKL.klBer ((17 : ℝ) / 4000)
      ((1 : ℝ) / 200) := by
    have h := klBer_17_4000_one_200_ge
    rw [div_le_iff₀ (show (0 : ℝ) < 250000 by norm_num), mul_comm] at h
    exact h
  have hE5 : (13 : ℝ) ≤ 500000 * Math.Concentration.BernoulliKL.klBer ((2761 : ℝ) / 500000)
      ((1 : ℝ) / 200) := by
    have h := klBer_decode_ge
    rw [div_le_iff₀ (show (0 : ℝ) < 500000 by norm_num), mul_comm] at h
    exact h
  -- the two upper Z-test tails are below `2⁻¹⁹` each (`13.4 ≥ 19·log 2`)
  have hA : Real.exp (-(250000 * Math.Concentration.BernoulliKL.klBer ((23 : ℝ) / 4000)
      ((1 : ℝ) / 200))) ≤ ((2 : ℝ) ^ 19)⁻¹ := by
    refine (Real.le_log_iff_exp_le (by positivity)).mp ?_
    rw [Real.log_inv, Real.log_pow]
    linarith
  -- the two lower Z-test tails are below `7·2⁻²⁴` each (`21·log 2 + log(8/7) ≥ 14.7`)
  have hB : Real.exp (-(250000 * Math.Concentration.BernoulliKL.klBer ((17 : ℝ) / 4000)
      ((1 : ℝ) / 200))) ≤ (7 : ℝ) * ((2 : ℝ) ^ 24)⁻¹ := by
    refine (Real.le_log_iff_exp_le (by positivity)).mp ?_
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_inv, Real.log_pow, h7]
    linarith
  -- the decoding tail is below `5·2⁻²¹` (`18·log 2 + log(8/5) ≥ 13`)
  have hC : Real.exp (-(500000 * Math.Concentration.BernoulliKL.klBer ((2761 : ℝ) / 500000)
      ((1 : ℝ) / 200))) ≤ (5 : ℝ) * ((2 : ℝ) ^ 21)⁻¹ := by
    refine (Real.le_log_iff_exp_le (by positivity)).mp ?_
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_inv, Real.log_pow, h5]
    linarith
  -- the two quota tails are below `2⁻¹⁴⁴` each (`100 ≥ 144·log 2`)
  have hQ1 : Real.exp (-(4000000 * Math.Concentration.BernoulliKL.klBer ((749999 : ℝ) / 4000000)
      ((1 : ℝ) / 4))) ≤ ((2 : ℝ) ^ 144)⁻¹ := by
    refine (Real.le_log_iff_exp_le (by positivity)).mp ?_
    rw [Real.log_inv, Real.log_pow]
    linarith [klBer_quota_million_ge.1]
  have hQ2 : Real.exp (-(4000000 * Math.Concentration.BernoulliKL.klBer ((249999 : ℝ) / 4000000)
      ((1 : ℝ) / 4))) ≤ ((2 : ℝ) ^ 144)⁻¹ := by
    refine (Real.le_log_iff_exp_le (by positivity)).mp ?_
    rw [Real.log_inv, Real.log_pow]
    linarith [klBer_quota_million_ge.2]
  -- numeric close: `2·2⁻¹⁹ + 14·2⁻²⁴ + 6·2⁻²¹ + 2·2⁻¹⁴⁴ = 126/2²⁴ < 128/2²⁴ = 2⁻¹⁷`
  have hrat : 2 * ((2 : ℝ) ^ 19)⁻¹ + 14 * ((2 : ℝ) ^ 24)⁻¹ + 5 * ((2 : ℝ) ^ 21)⁻¹
      + ((2 : ℝ) ^ 21)⁻¹ + 2 * ((2 : ℝ) ^ 144)⁻¹ ≤ ((2 : ℝ) ^ 17)⁻¹ := by norm_num
  norm_num at hA hB hC hQ1 hQ2 hrat
  linarith

/-- The million-sifted layout admits an equivariant scheme with the honest decoding budget. -/
theorem exists_decodesWhp_millionSifted :
    ∃ ec : MillionSiftedECScheme,
      ec.DecodesWhp (honestKeyErrWeight (500000 + 250000 + 250000) (1 / 200)
        (@Sampling.packedPESel 500000 250000 250000)
        (@Sampling.packedXSel 500000 250000 250000)) millionSiftedDecodingBudget ∧
      ec.IsTranslationEquivariant := by
  -- the packed selection keeps exactly the 500000 key rounds
  have hcard := Sampling.card_packedPESel_eq_false 500000 250000 250000
  -- the relative-entropy decoder at radius `t = 2760` with `s = 21` collision bits
  obtain ⟨ec, hdec, heq⟩ :=
    ECScheme.exists_decodesWhp_of_entropy_le
      (500000 + 250000 + 250000) ((1 : ℝ) / 200) ((69 : ℝ) / 12500)
      (@Sampling.packedPESel 500000 250000 250000)
      (@Sampling.packedXSel 500000 250000 250000)
      (by norm_num) 2760 24700 21
      (by rw [hcard]; norm_num)
      (by rw [hcard]; norm_num)
      (by norm_num) (by norm_num)
      (by rw [hcard]; norm_num)
      (by rw [hcard]
          -- entropy test: `500000·h₂(69/12500) + 21 = 24679 + 21 = 24700`
          have h2 := binaryEntropy_69_12500_le
          rw [le_div_iff₀ (show (0 : ℝ) < 500000 by norm_num)] at h2
          linarith)
  rw [hcard] at hdec
  push_cast at hdec
  -- `t + 1 = 2761` and the two budget expressions agree by definition
  have hbud : Real.exp (-(500000 : ℝ) * Math.Concentration.BernoulliKL.klBer
        (((2760 : ℝ) + 1) / 500000) (1 / 200)) + 1 / (2 : ℝ) ^ 21
      = millionSiftedDecodingBudget := by
    unfold millionSiftedDecodingBudget
    norm_num
  rw [hbud] at hdec
  exact ⟨ec, hdec, heq⟩

/-- Parameters with one million sifted rounds, supplied bases, physical batch size and decoder. -/
@[simps aliceBasis bobBasis rounds keyRounds zTests xTests keyLength tagLength leak
  tolerance errorRate]
def millionSiftedParameters (aliceBasis bobBasis : PMF Measurement.Basis) (rounds : ℕ)
    (ec : MillionSiftedECScheme) : Parameters where
  aliceBasis := aliceBasis
  bobBasis := bobBasis
  rounds := rounds
  keyRounds := 500000
  zTests := 250000
  xTests := 250000
  keyLength := 421000
  tagLength := 116
  leak := 24700
  ec := ec
  tolerance := 3 / 4000
  errorRate := 1 / 200

/-- Uniform bases and four million physical rounds for the million-sifted robustness instance. -/
abbrev millionSiftedUniformParameters (ec : MillionSiftedECScheme) : Parameters :=
  millionSiftedParameters (PMF.uniformOfFintype _) (PMF.uniformOfFintype _) 4000000 ec

variable (aliceBasis bobBasis : PMF Measurement.Basis) (rounds : ℕ) (ec : MillionSiftedECScheme)

/-- The configured experiment retains one million sifted rounds. -/
@[simp] theorem millionSiftedParameters_sifted :
    (millionSiftedParameters aliceBasis bobBasis rounds ec).sifted = 1000000 := by
  norm_num [Parameters.sifted]

/-- Half of the sifted rounds are tests. -/
@[simp] theorem millionSiftedParameters_tests :
    (millionSiftedParameters aliceBasis bobBasis rounds ec).tests = 500000 := by
  norm_num [Parameters.tests]

/-- The honest decoding guarantee gives acceptance at least `1 - 2⁻¹⁷` for every physical honest
input at rate `1/200`, through the relative-entropy honest abort budget. -/
theorem millionSiftedUniformParameters_one_sub_le_acceptProbability
    (hDecode : ec.DecodesWhp
      (honestKeyErrWeight (500000 + 250000 + 250000) (1 / 200)
        (@Sampling.packedPESel 500000 250000 250000)
        (@Sampling.packedXSel 500000 250000 250000)) millionSiftedDecodingBudget)
    (ρ : Op (Measurement.weightedStreamSystem Unit (millionSiftedUniformParameters
      ec).rounds).total)
    (hρ : Measurement.HonestOperation (millionSiftedUniformParameters ec).rounds (1 / 200) ρ) :
    1 - ((2 : ℝ) ^ 17)⁻¹ ≤ (millionSiftedUniformParameters ec).protocol.acceptProbability ρ := by
  have hq0 : (0 : ℝ) < 1 / 200 := by norm_num
  have hq1 : (1 : ℝ) / 200 < 1 := by norm_num
  -- the channel sits at the centre of the acceptance window
  have hband : |(1 : ℝ) / 200 - (millionSiftedUniformParameters ec).errorRate|
      < (millionSiftedUniformParameters ec).tolerance := by
    change |(1 : ℝ) / 200 -
        (millionSiftedParameters (PMF.uniformOfFintype _) (PMF.uniformOfFintype _) 4000000
          ec).errorRate|
      < (millionSiftedParameters (PMF.uniformOfFintype _) (PMF.uniformOfFintype _) 4000000
          ec).tolerance
    rw [millionSiftedParameters_errorRate, millionSiftedParameters_tolerance]
    norm_num
  -- the honest decoding guarantee, transported to the parameter projections
  have hdec : (millionSiftedUniformParameters ec).ec.DecodesWhp
      (honestKeyErrWeight (millionSiftedUniformParameters ec).sifted (1 / 200)
        (millionSiftedUniformParameters ec).peSel (millionSiftedUniformParameters ec).xSel)
      millionSiftedDecodingBudget := hDecode
  -- uniform bases match with probability `1/4`, and both quotas sit far below that
  have hZ : (((millionSiftedUniformParameters ec).keyRounds
        + (millionSiftedUniformParameters ec).zTests : ℝ) - 1)
      / (millionSiftedUniformParameters ec).rounds
      < (Sampling.matchedProb (millionSiftedUniformParameters ec).aliceBasis
        (millionSiftedUniformParameters ec).bobBasis Measurement.Basis.z).toReal := by
    simp
    norm_num
  have hZ1 : (Sampling.matchedProb (millionSiftedUniformParameters ec).aliceBasis
      (millionSiftedUniformParameters ec).bobBasis Measurement.Basis.z).toReal < 1 := by
    simp
    norm_num
  have hX : (((millionSiftedUniformParameters ec).xTests : ℝ) - 1)
      / (millionSiftedUniformParameters ec).rounds
      < (Sampling.matchedProb (millionSiftedUniformParameters ec).aliceBasis
        (millionSiftedUniformParameters ec).bobBasis Measurement.Basis.x).toReal := by
    simp
    norm_num
  have hX1 : (Sampling.matchedProb (millionSiftedUniformParameters ec).aliceBasis
      (millionSiftedUniformParameters ec).bobBasis Measurement.Basis.x).toReal < 1 := by
    simp
    norm_num
  have hmain := Parameters.one_sub_abortBound_le_acceptProbability
    (p := millionSiftedUniformParameters ec) ρ (1 / 200) millionSiftedDecodingBudget
    hq0 hq1 hband hdec hZ hZ1 hX hX1 hρ
  simp only [millionSiftedParameters_aliceBasis, millionSiftedParameters_bobBasis,
    millionSiftedParameters_rounds, millionSiftedParameters_keyRounds,
    millionSiftedParameters_zTests, millionSiftedParameters_xTests,
    millionSiftedParameters_errorRate, millionSiftedParameters_tolerance,
    Sampling.matchedProb_uniformOfFintype_toReal] at hmain
  linarith [millionSifted_abortBound_le]

/-- Every translation-equivariant scheme gives `BellRenyiConditions` at smoothing
`2⁻¹¹²`, `ε_PA = 2⁻¹¹⁴`, `β = 1/40` and deviation `dev = 31/10000` at window `δ = 3/4000`. -/
theorem bellRenyiConditions_millionSiftedParameters (hec : ec.IsTranslationEquivariant) :
    (millionSiftedParameters aliceBasis bobBasis rounds ec).BellRenyiConditions
      (((2 : ℝ) ^ 112)⁻¹) (((2 : ℝ) ^ 114)⁻¹) (1 / 40) (31 / 10000) where
  smoothing_pos := by positivity
  keyRate := by
    rw [millionSiftedParameters_sifted, millionSiftedParameters_tests]
    exact bellRenyiKeyRate_million
  ecTranslationEquivariant := hec
  epsPA_pos := by positivity
  beta_pos := by norm_num
  beta_lt_one := by norm_num
  dev_nonneg := by norm_num
  soundnessEdge_le_half := by
    simp only [millionSiftedParameters_errorRate, millionSiftedParameters_tolerance]
    norm_num

/-- `Parameters.bellRenyiBudget` is at most `2⁻⁵⁰`. -/
theorem millionSiftedParameters_bellRenyiBudget_le :
    (millionSiftedParameters aliceBasis bobBasis rounds ec).bellRenyiBudget
        (((2 : ℝ) ^ 112)⁻¹) (((2 : ℝ) ^ 114)⁻¹) (31 / 10000) ≤ ((2 : ℝ) ^ 50)⁻¹ := by
  -- the accept tail `E` is at most `2⁻²²⁴`, so `√(2E) ≤ (3/2)·2⁻¹¹²`
  have hQd : ((1 : ℝ) / 200 + 3 / 4000) = (23 : ℝ) / 4000 := by norm_num
  have hQ : ((1 : ℝ) / 200 + 3 / 4000 + 31 / 10000) = (177 : ℝ) / 20000 := by norm_num
  have hmX : (siftedXTestSampleSize
      (@Sampling.packedPESel 500000 250000 250000)
      (@Sampling.packedXSel 500000 250000 250000) : ℝ) = 250000 := by
    rw [QKD.BB84.Reduction.siftedXTestSampleSize_packed]; norm_num
  have hpow224 : Real.exp (-(224 : ℝ) * Real.log 2) = ((2 : ℝ) ^ 224)⁻¹ := by
    have h : Real.log (((2 : ℝ) ^ 224)⁻¹) = -(224 : ℝ) * Real.log 2 := by
      rw [Real.log_inv, Real.log_pow (2 : ℝ) 224]
      norm_num
    rw [← h, Real.exp_log (by positivity)]
  have hE : phaseTail
      (@Sampling.packedPESel 500000 250000 250000)
      (@Sampling.packedXSel 500000 250000 250000) ((1 : ℝ) / 200) ((3 : ℝ) / 4000) (31 / 10000)
      ≤ ((2 : ℝ) ^ 224)⁻¹ := by
    unfold phaseTail
    rw [hQ, hQd, hmX]
    refine le_trans (Real.exp_le_exp.mpr ?_) hpow224.le
    -- `224·log 2 ≤ 250000·klBer(23/4000) (177/20000)` from the accept-tail bracket
    have h1 : (224 : ℝ) * Real.log 2 ≤
        Math.Concentration.BernoulliKL.klBer ((23 : ℝ) / 4000) ((177 : ℝ) / 20000) * 250000 :=
      (div_le_iff₀ (show (0 : ℝ) < 250000 by norm_num)).mp klBer_23_4000_177_20000_ge
    linarith
  have hsqrt : Real.sqrt
      (2 * phaseTail
        (@Sampling.packedPESel 500000 250000 250000)
        (@Sampling.packedXSel 500000 250000 250000) ((1 : ℝ) / 200) ((3 : ℝ) / 4000) (31 / 10000))
      ≤ 3 / 2 * (((2 : ℝ) ^ 112)⁻¹) := by
    have hsq : (((2 : ℝ) ^ 112)⁻¹) ^ 2 = ((2 : ℝ) ^ 224)⁻¹ := by
      rw [inv_pow, ← pow_mul]
    refine (Real.sqrt_le_iff).2 ⟨by positivity, ?_⟩
    calc
      2 * phaseTail
          (@Sampling.packedPESel 500000 250000 250000)
          (@Sampling.packedXSel 500000 250000 250000) ((1 : ℝ) / 200) ((3 : ℝ) / 4000)
          (31 / 10000) ≤ 2 * ((2 : ℝ) ^ 224)⁻¹ := by linarith
      _ ≤ (3 / 2 * (((2 : ℝ) ^ 112)⁻¹)) ^ 2 := by
        rw [mul_pow, hsq]
        nlinarith [show 0 ≤ ((2 : ℝ) ^ 224)⁻¹ by positivity]
  -- The secrecy budget is at most `(21/4)·2⁻¹¹²`.
  have hinner : bellRenyiSecrecyBudget
      (phaseTail
        (@Sampling.packedPESel 500000 250000 250000)
        (@Sampling.packedXSel 500000 250000 250000) ((1 : ℝ) / 200) ((3 : ℝ) / 4000) (31 / 10000))
      (((2 : ℝ) ^ 112)⁻¹) (((2 : ℝ) ^ 114)⁻¹)
      ≤ (21 / 4 : ℝ) * ((2 : ℝ) ^ 112)⁻¹ := by
    simp only [bellRenyiSecrecyBudget,
    InfoTheory.Security.smoothingError,
    InfoTheory.Security.acceptanceError]
    have h2 : ((2 : ℝ) ^ 114)⁻¹ = (1 / 4) * ((2 : ℝ) ^ 112)⁻¹ := by
      rw [show ((2 : ℝ) ^ 114) = (2 : ℝ) ^ 2 * ((2 : ℝ) ^ 112) from by rw [← pow_add],
        mul_inv]
      norm_num
    linarith
  have hcor : (2 : ℝ) ^ (-(((116 : ℕ)) : ℝ)) =
      (1 / 16) * ((2 : ℝ) ^ 112)⁻¹ := by
    rw [Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num), Real.rpow_natCast (2 : ℝ) 116,
      show ((2 : ℝ) ^ 116) = (2 : ℝ) ^ 4 * ((2 : ℝ) ^ 112) from by rw [← pow_add],
      mul_inv]
    norm_num
  -- The budget adds correctness to `C(n+3,3)·secrecy`; the packed selectors and the
  -- `Nat.choose` stay symbolic so the kernel never evaluates a million-round count
  have hunfold : (millionSiftedParameters aliceBasis bobBasis rounds ec).bellRenyiBudget
      (((2 : ℝ) ^ 112)⁻¹) (((2 : ℝ) ^ 114)⁻¹) (31 / 10000)
      = (2 : ℝ) ^ (-((116 : ℕ) : ℝ)) +
        (((Nat.choose ((millionSiftedParameters aliceBasis bobBasis rounds ec).sifted + 3) 3 :
          ℕ) : ℝ)) *
        (bellRenyiSecrecyBudget
          (phaseTail
            (@Sampling.packedPESel 500000 250000 250000)
            (@Sampling.packedXSel 500000 250000 250000) ((1 : ℝ) / 200) ((3 : ℝ) / 4000)
              (31 / 10000))
          (((2 : ℝ) ^ 112)⁻¹) (((2 : ℝ) ^ 114)⁻¹)) := by
    unfold Parameters.bellRenyiBudget QKD.BB84.FiniteKey.bellRenyiBudget
      InfoTheory.Security.verificationError
    rw [Math.Combinatorics.deFinettiPrefactor_four]
    -- the tail's selectors depend on `p.sifted`, so `sifted` itself is never rewritten here
    rw [millionSiftedParameters_tagLength, millionSiftedParameters_errorRate,
      millionSiftedParameters_tolerance,
      show Parameters.peSel (millionSiftedParameters aliceBasis bobBasis rounds ec)
          = @Sampling.packedPESel 500000 250000 250000 from rfl,
      show Parameters.xSel (millionSiftedParameters aliceBasis bobBasis rounds ec)
          = @Sampling.packedXSel 500000 250000 250000 from rfl]
    rfl
  rw [hunfold, hcor,
    show ((millionSiftedParameters aliceBasis bobBasis rounds ec).sifted + 3 : ℕ) = 1000003 from
      by simp only [millionSiftedParameters_sifted]]
  refine (add_le_add le_rfl (mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _))).trans ?_
  have h62 : (1 / 16 : ℝ) + (105 / 16) * (2 : ℝ) ^ 57 ≤ (2 : ℝ) ^ 62 := by norm_num
  have hsplit : ((2 : ℝ) ^ 112) = ((2 : ℝ) ^ 62) * ((2 : ℝ) ^ 50) := by
    rw [← pow_add]
  calc (1 / 16 : ℝ) * ((2 : ℝ) ^ 112)⁻¹ +
        ((Nat.choose 1000003 3 : ℕ) : ℝ) * ((21 / 4 : ℝ) * ((2 : ℝ) ^ 112)⁻¹)
      ≤ (1 / 16 : ℝ) * ((2 : ℝ) ^ 112)⁻¹ +
          ((5 : ℝ) / 4 * (2 : ℝ) ^ 57) * ((21 / 4 : ℝ) * ((2 : ℝ) ^ 112)⁻¹) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right
          choose_million_three_le_five_quarters (by positivity))
    _ = ((1 / 16 : ℝ) + (105 / 16) * (2 : ℝ) ^ 57) * (((2 : ℝ) ^ 112)⁻¹) := by ring
    _ ≤ ((2 : ℝ) ^ 62) * (((2 : ℝ) ^ 112)⁻¹) :=
      mul_le_mul_of_nonneg_right h62 (by positivity)
    _ = ((2 : ℝ) ^ 50)⁻¹ := by
      rw [hsplit]
      field_simp

/-- The real–ideal distance of the configured protocol is at most `2⁻⁵⁰`. -/
theorem millionSiftedParameters_realIdealDistance_le (hec : ec.IsTranslationEquivariant) :
    (millionSiftedParameters aliceBasis bobBasis rounds ec).protocol.realIdealDistance
      ≤ ((2 : ℝ) ^ 50)⁻¹ :=
  (millionSiftedParameters aliceBasis bobBasis rounds ec).realIdealDistance_le_bellRenyiBudget
    (bellRenyiConditions_millionSiftedParameters aliceBasis bobBasis rounds ec hec) |>.trans
    (millionSiftedParameters_bellRenyiBudget_le aliceBasis bobBasis rounds ec)

/-- Every translation-equivariant scheme is fully interface-secure at `2⁻⁵⁰`. -/
theorem isSecure_millionSiftedParameters (hec : ec.IsTranslationEquivariant) :
    (millionSiftedParameters aliceBasis bobBasis rounds ec).protocol.IsSecure
      ((2 : ℝ) ^ 50)⁻¹ :=
  ((millionSiftedParameters aliceBasis bobBasis rounds ec).isSecure_of_bellRenyiConditions
    (bellRenyiConditions_millionSiftedParameters aliceBasis bobBasis rounds ec hec)).mono
      (millionSiftedParameters_bellRenyiBudget_le aliceBasis bobBasis rounds ec)

/-- **The million-round instance sits in the Bell–Rényi comparison region**
`BellRenyiAdvantageRegion` at smoothing `2⁻¹¹²`, `ε_PA = 2⁻¹¹⁴`, `β = 1/40`, deviation
`dev = 31/10000` and shared total `2⁻⁵⁰`: every field holds at the configured point, with entropy
bracket `177/20000 ∈ [0, 1/2]`, comparator PA error below one, and key length nonnegative by the
rate lower bracket
(`463420 − 24700 − 116 − 23601 > 0`), and the penalty gap certified by `penaltyGap_million`. -/
theorem bellRenyiAdvantageRegion_millionSiftedParameters (hec : ec.IsTranslationEquivariant) :
    (millionSiftedParameters aliceBasis bobBasis rounds ec).BellRenyiAdvantageRegion
      (((2 : ℝ) ^ 112)⁻¹) (((2 : ℝ) ^ 114)⁻¹) (1 / 40) (31 / 10000) (((2 : ℝ) ^ 50)⁻¹) := by
  have hcond := bellRenyiConditions_millionSiftedParameters aliceBasis bobBasis rounds ec hec
  refine { smoothing_pos := hcond.smoothing_pos
           epsPA_pos := hcond.epsPA_pos
           beta_pos := hcond.beta_pos
           beta_lt_one := hcond.beta_lt_one
           dev_nonneg := hcond.dev_nonneg
           acceptanceEdge_pos := by norm_num
           soundnessEdge_le_half := hcond.soundnessEdge_le_half
           ecTranslationEquivariant := hec
           bellRenyiBudget_le :=
             millionSiftedParameters_bellRenyiBudget_le _ _ _ ec
           liftedPrivacyAmplificationError_lt_one := liftedPrivacyAmplificationError_lt_one _ _ (by
             norm_num)
           liftedLiteratureKeyLength_nonneg := ?_
           penalty_le_literatureFiniteSizePenalty := ?_ }
  · -- the comparator at the bracket funds at least `463420 − 24700 − 116 − 23601 > 0` bits
    unfold Parameters.liftedLiteratureKeyLength
    rw [millionSiftedParameters_sifted, millionSiftedParameters_keyRounds,
      millionSiftedParameters_tagLength, millionSiftedParameters_leak,
      millionSiftedParameters_errorRate, millionSiftedParameters_tolerance,
      liftedLiteratureKeyLength, literatureKeyLength,
      show ((1 : ℝ) / 200 + 2 * (((3 : ℝ) / 4000 + 31 / 10000) / 2)) = (177 : ℝ) / 20000 from
        by norm_num]
    obtain ⟨hrate, -⟩ := rate_million_bounds
    obtain ⟨-, hPlit⟩ := literatureFiniteSizePenalty_million_bounds
    push_cast
    linarith
  · rw [millionSiftedParameters_keyRounds, millionSiftedParameters_sifted]
    exact penaltyGap_million

/-- **The key exceeds the lifted literature comparator at the same phase-error bracket
`Q + δ + dev` by at least 5500 bits** (true `5773`). -/
theorem MillionSifted.le_keyLength_sub_liftedLiteratureKeyLength :
    (5500 : ℝ) ≤ (millionSiftedParameters aliceBasis bobBasis rounds ec).keyLength -
      liftedLiteratureKeyLength 4 1000000 500000 116 24700 ((1 : ℝ) / 200)
        (((3 : ℝ) / 4000 + 31 / 10000) / 2) (((2 : ℝ) ^ 50)⁻¹) := by
  have hcmp : liftedLiteratureKeyLength 4 1000000 500000 116 24700 ((1 : ℝ) / 200)
      (((3 : ℝ) / 4000 + 31 / 10000) / 2) (((2 : ℝ) ^ 50)⁻¹) ≤ 415500 := by
    obtain ⟨-, hrate⟩ := rate_million_bounds
    obtain ⟨hP, -⟩ := literatureFiniteSizePenalty_million_bounds
    rw [liftedLiteratureKeyLength, literatureKeyLength,
      show ((1 : ℝ) / 200 + 2 * (((3 : ℝ) / 4000 + 31 / 10000) / 2))
          = (177 : ℝ) / 20000 from by norm_num]
    push_cast
    linarith
  norm_num [millionSiftedParameters_keyLength]
  linarith [hcmp]

/-- **Without the coherent-attack lift, the prefactor-one comparator at the same phase-error
bracket exceeds every key length certified by the Bell–Rényi key-rate condition at this numerical
point.** -/
theorem MillionSifted.keyLength_lt_liftedLiteratureKeyLength_one
    {ℓ : ℕ} (h : BellRenyiKeyRate 1000000 500000 ℓ 116 24700 ((1 : ℝ) / 200)
      ((3 : ℝ) / 4000) (31 / 10000) (((2 : ℝ) ^ 112)⁻¹) (((2 : ℝ) ^ 114)⁻¹) (1 / 40)) :
    (ℓ : ℝ) < liftedLiteratureKeyLength 1 1000000 500000 116 24700 ((1 : ℝ) / 200)
      (((3 : ℝ) / 4000 + 31 / 10000) / 2) (((2 : ℝ) ^ 50)⁻¹) := by
  have hcmp : (421600 : ℝ) ≤ liftedLiteratureKeyLength 1 1000000 500000 116 24700
      ((1 : ℝ) / 200) (((3 : ℝ) / 4000 + 31 / 10000) / 2) (((2 : ℝ) ^ 50)⁻¹) := by
    obtain ⟨hrate, -⟩ := rate_million_bounds
    have hP := literatureFiniteSizePenalty_one_million_le
    rw [liftedLiteratureKeyLength, literatureKeyLength,
      show ((1 : ℝ) / 200 + 2 * (((3 : ℝ) / 4000 + 31 / 10000) / 2))
          = (177 : ℝ) / 20000 from by norm_num]
    push_cast
    linarith
  exact (lt_of_bellRenyiKeyRate_million h).trans_le hcmp

/-- An honest-decodable configuration with security `2⁻⁵⁰`, a 5500-bit lifted-comparator gap at
the same phase-error bracket, and acceptance at least `1 - 2⁻¹⁷` on every physical honest input
exists. -/
theorem exists_millionSiftedUniformParameters_isSecure :
    ∃ ec : MillionSiftedECScheme,
      let p := millionSiftedUniformParameters ec
      ec.DecodesWhp (honestKeyErrWeight (500000 + 250000 + 250000) (1 / 200)
        (@Sampling.packedPESel 500000 250000 250000)
        (@Sampling.packedXSel 500000 250000 250000)) millionSiftedDecodingBudget ∧
      p.BellRenyiConditions (((2 : ℝ) ^ 112)⁻¹) (((2 : ℝ) ^ 114)⁻¹) (1 / 40) (31 / 10000) ∧
      p.bellRenyiBudget (((2 : ℝ) ^ 112)⁻¹) (((2 : ℝ) ^ 114)⁻¹) (31 / 10000)
        ≤ ((2 : ℝ) ^ 50)⁻¹ ∧
      p.protocol.IsSecure ((2 : ℝ) ^ 50)⁻¹ ∧
      (5500 : ℝ) ≤ (p.keyLength : ℝ) - liftedLiteratureKeyLength 4 1000000 500000 116 24700
        ((1 : ℝ) / 200) (((3 : ℝ) / 4000 + 31 / 10000) / 2) (((2 : ℝ) ^ 50)⁻¹) ∧
      ∀ ρ, Measurement.HonestOperation p.rounds (1 / 200) ρ →
        1 - ((2 : ℝ) ^ 17)⁻¹ ≤ p.protocol.acceptProbability ρ := by
  obtain ⟨ec, hDecode, hec⟩ := exists_decodesWhp_millionSifted
  refine ⟨ec, hDecode, bellRenyiConditions_millionSiftedParameters _ _ _ ec hec, ?_, ?_, ?_, ?_⟩
  · exact millionSiftedParameters_bellRenyiBudget_le _ _ _ ec
  · exact isSecure_millionSiftedParameters _ _ _ ec hec
  · exact MillionSifted.le_keyLength_sub_liftedLiteratureKeyLength _ _ _ ec
  · exact millionSiftedUniformParameters_one_sub_le_acceptProbability
      ec hDecode

end QKD.BB84.Comparison

end
