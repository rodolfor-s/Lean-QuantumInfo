import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKey.ReferenceOptimised
import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.QuantumLHL.Main
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Seed-visible leftover hashing from strict reference floors -/

noncomputable section

namespace InfoTheory.QuantumLHL.SeedKey

open Quantum.Operators InfoTheory.SmoothMinEntropy
open Quantum.Metrics
open scoped ComplexOrder

/-- Strict floors with arbitrary positive-definite reference witnesses imply the exact
seed-visible LHL bound. The proof uses the optimized theorem and continuity. -/
theorem traceDistanceGen_output_le_of_forall_exists_posDef_reference
    {S C Z Q : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Z] [DecidableEq Z] [Nonempty Z]
    [Fintype Q] [Nonempty Q] (H : HashFamily S C Z) (hH : H.IsTwoUniversal)
    (ρ : CQState C Q) (ε : ℝ) (hε : 0 ≤ ε) (k : ℝ)
    (hfloor : ∀ t : ℝ, t < k → ∃ σ : SubDensityOp Q,
      σ.toOp.PosDef ∧ ENNReal.ofReal t ≤ smoothMinEntropy ε ρ σ) :
    traceDistanceGen (output H ρ).toJointDensity.toOp
      (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) + 2 * ε := by
  let f : ℝ → ℝ := fun t => (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-t)) + 2 * ε
  have hf : Continuous f :=
    InfoTheory.QuantumLHL.SeedKey.continuous_half_mul_sqrt_mul_rpow_neg_add (Fintype.card Z) ε
  have hb (m : ℕ) : traceDistanceGen (output H ρ).toJointDensity.toOp
      (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp ≤
      f (k - 1 / ((m : ℝ) + 1)) := by
    obtain ⟨σ, _, hσ⟩ := hfloor (k - 1 / ((m : ℝ) + 1)) (by
      have : 0 < 1 / ((m : ℝ) + 1) := by positivity
      linarith)
    exact traceDistanceGen_output_le_of_le_smoothMinEntropyOpt H hH ρ ε hε _
      (hσ.trans (smoothMinEntropy_le_smoothMinEntropyOpt ε ρ σ))
  have ht : Filter.Tendsto (fun m : ℕ => k - 1 / ((m : ℝ) + 1)) Filter.atTop (nhds k) := by
    simpa using (tendsto_const_nhds (x := k)).sub tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto' ((hf.tendsto k).comp ht) hb

end InfoTheory.QuantumLHL.SeedKey
