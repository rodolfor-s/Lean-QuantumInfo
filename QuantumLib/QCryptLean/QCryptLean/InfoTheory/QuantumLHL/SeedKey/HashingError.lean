import QCryptLean.InfoTheory.QuantumLHL.HashingError
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.QuantumLHL.Main
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Hashing Error -/


namespace InfoTheory.QuantumLHL.SeedKey
open Quantum.Operators Quantum.Metrics
open InfoTheory.SmoothMinEntropy
variable {S C Z Q : Type*} [Fintype S] [Fintype C] [Fintype Z] [Fintype Q]
  [DecidableEq S] [DecidableEq C] [DecidableEq Z]
  [Nonempty S] [Nonempty C] [Nonempty Z] [Nonempty Q]

/-- Public-seed hashing evaluated at fixed-reference extended entropy, including infinity. -/
theorem traceDistanceGen_output_le_hashingError_add
    (H : HashFamily S C Z) (hH : H.IsTwoUniversal) (ρ : CQState C Q) (σ : SubDensityOp Q)
    (ε : ℝ) (hε : 0 ≤ ε) (l : ℕ) (hl : Fintype.card Z = 2 ^ l) :
    traceDistanceGen (output H ρ).toJointDensity.toOp
      (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp ≤
        hashingError l (smoothMinEntropy ε ρ σ) + 2 * ε := by
  have hf := smoothMinEntropy_le_smoothMinEntropyOpt ε ρ σ
  by_cases ht : smoothMinEntropy ε ρ σ = ⊤
  · rw [ht, hashingError_top, zero_add]
    apply traceDistanceGen_output_le_of_smoothMinEntropyOpt_eq_top H hH ρ ε hε
    exact top_le_iff.mp (ht ▸ hf)
  · rw [hashingError_of_ne_top l ht]
    let k := (smoothMinEntropy ε ρ σ).toReal
    have hk : ENNReal.ofReal k ≤ smoothMinEntropyOpt ε ρ := by
      rw [ENNReal.ofReal_toReal ht]
      exact hf
    have h := traceDistanceGen_output_le_of_le_smoothMinEntropyOpt H hH ρ ε hε k hk
    refine h.trans_eq ?_
    have hc : (Fintype.card Z : ℝ) = (2 : ℝ) ^ l := by rw [hl]; norm_cast
    rw [hc, Real.sqrt_eq_rpow, ← Real.rpow_natCast (2 : ℝ) l,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 3
    ring

end InfoTheory.QuantumLHL.SeedKey
