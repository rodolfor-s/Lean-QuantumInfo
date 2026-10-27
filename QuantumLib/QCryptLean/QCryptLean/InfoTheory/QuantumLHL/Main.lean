import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKey.ReferenceOptimised
import QCryptLean.InfoTheory.QuantumLHL.SeedKey.Smoothing
import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.QuantumLHL.SeedAverage
import QCryptLean.InfoTheory.QuantumLHL.SeedCollision
import QCryptLean.InfoTheory.QuantumLHL.SeedContractivity
import QCryptLean.InfoTheory.Renyi.CQReference
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.CQTraceDistance
import QCryptLean.InfoTheory.SmoothMinEntropy.FeasibleRegularization
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.GeneralizedTrace
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Main -/


noncomputable section

namespace InfoTheory.QuantumLHL

open Quantum.Operators InfoTheory.SmoothMinEntropy
open Quantum.Metrics

variable {S C Z Q : Type*} [Fintype S] [Nonempty S]
  [Fintype C] [DecidableEq C] [Nonempty C]
  [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype Q] [Nonempty Q]

namespace SeedKey

variable [DecidableEq S]

/-- Public-seed leftover hashing with optimized extended smooth entropy. -/
theorem traceDistanceGen_output_le_of_le_smoothMinEntropyOpt (H : HashFamily S C Z)
    (hH : H.IsTwoUniversal) (ρ : CQState C Q) (ε : ℝ) (hε : 0 ≤ ε)
    (k : ℝ) (hk : ENNReal.ofReal k ≤ smoothMinEntropyOpt ε ρ) :
    traceDistanceGen (output H ρ).toJointDensity.toOp
        (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt (Fintype.card Z * 2 ^ (-k)) + 2 * ε := by
  classical
  let D := traceDistanceGen (output H ρ).toJointDensity.toOp
    (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp
  let f : ℝ → ℝ := fun t => (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-t)) + 2 * ε
  have hbase : D ≤ (1 / 2) * Real.sqrt (Fintype.card Z : ℝ) := by
    have hfeas : IsFeasible ρ ρ.quantumMarginal 1 := by
      refine ⟨zero_le_one, fun c => ?_⟩
      simp only [Complex.ofReal_one, one_smul]
      exact opLe_of_posSemidef_sub (Matrix.le_iff.mp (ρ.stateMap_le_quantumMarginal c))
    simpa only [mul_one] using traceDistanceGen_output_le_of_isFeasible H hH ρ
      ρ.quantumMarginal hfeas
  have hbound (t : ℝ) (ht : t < k) : D ≤ f t := by
    by_cases htpos : 0 < t
    · have hlt : ENNReal.ofReal t < smoothMinEntropyOpt ε ρ :=
        (ENNReal.ofReal_lt_ofReal_iff (htpos.trans ht) |>.mpr ht).trans_le hk
      obtain ⟨σ, hσ⟩ := lt_iSup_iff.mp hlt
      obtain ⟨τ, hτ⟩ := lt_iSup_iff.mp hσ
      obtain ⟨hd, hfloor⟩ := lt_iSup_iff.mp hτ
      obtain ⟨a, ha, hak⟩ := exists_isFeasible_lt_rpow_of_lt_minEntropy τ σ hfloor
      have hmid := traceDistanceGen_output_le_of_isFeasible H hH τ σ ha
      have hmid' : traceDistanceGen (output H τ).toJointDensity.toOp
          (uniformCQState (C := S × Z) τ.quantumMarginal).toJointDensity.toOp ≤
          (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-t)) := hmid.trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
          (mul_le_mul_of_nonneg_left hak.le (Nat.cast_nonneg _))) (by norm_num))
      have hin : traceDistanceGen ρ.toJointDensity.toOp τ.toJointDensity.toOp ≤ ε :=
        (Quantum.Metrics.traceDistanceGen_le_purifiedDistance
          ρ.toJointDensity τ.toJointDensity).trans hd
      have hout := (traceDistanceGen_output_le H ρ τ).trans hin
      have hid : traceDistanceGen
          (uniformCQState (C := S × Z) τ.quantumMarginal).toJointDensity.toOp
          (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp ≤ ε := by
        rw [Quantum.Metrics.traceDistanceGen_symm, traceDistanceGen_uniformCQState]
        exact (ρ.traceDistanceGen_quantumMarginal_le τ).trans hin
      have htri := Quantum.Metrics.traceDistanceGen_triangle
        (output H ρ).toJointDensity.toOp (output H τ).toJointDensity.toOp
        (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp
      have htri' := Quantum.Metrics.traceDistanceGen_triangle
        (output H τ).toJointDensity.toOp
        (uniformCQState (C := S × Z) τ.quantumMarginal).toJointDensity.toOp
        (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp
      change _ ≤ _ at hout
      dsimp [D, f]
      linarith
    · have hp : (1 : ℝ) ≤ 2 ^ (-t) := Real.one_le_rpow one_le_two (by linarith)
      have hs : Real.sqrt (Fintype.card Z : ℝ) ≤
          Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-t)) :=
        Real.sqrt_le_sqrt (le_mul_of_one_le_right (Nat.cast_nonneg _) hp)
      dsimp [f]
      linarith
  have hf : Continuous f :=
    InfoTheory.QuantumLHL.SeedKey.continuous_half_mul_sqrt_mul_rpow_neg_add (Fintype.card Z) ε
  have hs : Filter.Tendsto (fun n : ℕ => k - 1 / ((n : ℝ) + 1))
      Filter.atTop (nhds k) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_sub k
  apply ge_of_tendsto' ((hf.tendsto k).comp hs)
  intro n
  exact hbound _ (sub_lt_self k (by positivity))

/-- Infinite optimized entropy leaves the public-seed smoothing charge. -/
theorem traceDistanceGen_output_le_of_smoothMinEntropyOpt_eq_top (H : HashFamily S C Z)
    (hH : H.IsTwoUniversal) (ρ : CQState C Q) (ε : ℝ) (hε : 0 ≤ ε)
    (hk : smoothMinEntropyOpt ε ρ = ⊤) :
    traceDistanceGen (output H ρ).toJointDensity.toOp
        (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp ≤ 2 * ε := by
  apply InfoTheory.QuantumLHL.le_two_mul_of_forall_hashing_bound _ ε (Fintype.card Z)
  intro k
  exact traceDistanceGen_output_le_of_le_smoothMinEntropyOpt H hH ρ ε hε k (by simp [hk])

end SeedKey

/-- Seed-averaged leftover hashing from optimized extended smooth entropy. -/
theorem extractorDistance_le_of_smoothMinEntropyOpt (H : HashFamily S C Z)
    (hH : H.IsTwoUniversal) (ρ : CQState C Q) (ε : ℝ) (hε : 0 ≤ ε)
    (k : ℝ) (hk : ENNReal.ofReal k ≤ smoothMinEntropyOpt ε ρ) :
    traceDistanceGen (extractorOutputState H ρ).toJointDensity.toOp
        (uniformCQState (C := Z) ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt (Fintype.card Z * 2 ^ (-k)) + 2 * ε := by
  classical
  exact (SeedKey.extractorDistance_le_outputDistance H ρ ρ.quantumMarginal).trans
    (SeedKey.traceDistanceGen_output_le_of_le_smoothMinEntropyOpt H hH ρ ε hε k hk)

/-- A fixed-reference entropy floor also supplies the seed-averaged bound. -/
theorem extractorDistance_le_of_smoothMinEntropy (H : HashFamily S C Z)
    (hH : H.IsTwoUniversal) (ρ : CQState C Q) (σ : SubDensityOp Q)
    (ε : ℝ) (hε : 0 ≤ ε) (k : ℝ) (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    traceDistanceGen (extractorOutputState H ρ).toJointDensity.toOp
        (uniformCQState (C := Z) ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt (Fintype.card Z * 2 ^ (-k)) + 2 * ε :=
  extractorDistance_le_of_smoothMinEntropyOpt H hH ρ ε hε k
    (hk.trans (smoothMinEntropy_le_smoothMinEntropyOpt ε ρ σ))

/-- Infinite optimized entropy leaves exactly the seed-averaged smoothing charge. -/
theorem extractorDistance_le_of_smoothMinEntropyOpt_top (H : HashFamily S C Z)
    (hH : H.IsTwoUniversal) (ρ : CQState C Q) (ε : ℝ) (hε : 0 ≤ ε)
    (hk : smoothMinEntropyOpt ε ρ = ⊤) :
    traceDistanceGen (extractorOutputState H ρ).toJointDensity.toOp
        (uniformCQState (C := Z) ρ.quantumMarginal).toJointDensity.toOp ≤ 2 * ε := by
  apply InfoTheory.QuantumLHL.le_two_mul_of_forall_hashing_bound _ ε (Fintype.card Z)
  intro k
  exact extractorDistance_le_of_smoothMinEntropyOpt H hH ρ ε hε k (by simp [hk])


end InfoTheory.QuantumLHL
