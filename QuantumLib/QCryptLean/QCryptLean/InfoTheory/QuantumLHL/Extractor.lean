import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Quantum.Operators.Basic

/-! # Extractor -/


noncomputable section

namespace InfoTheory.QuantumLHL

open Quantum.Operators InfoTheory.SmoothMinEntropy
open scoped ComplexOrder

variable {S C Z Q : Type*} [Fintype S] [Fintype C] [Fintype Z] [Fintype Q]
  [DecidableEq Z]

/-- The seed-averaged quantum block at an output of the hash. -/
def extractorWeightedOp (H : HashFamily S C Z) (ρ : CQState C Q) (z : Z) : Op Q :=
  (1 / Fintype.card S : ℝ) •
    ∑ s : S, ∑ c : C, if H.hash s c = z then (ρ.stateMap c).toOp else 0

/-- Hashing preserves the sum of quantum blocks. -/
theorem sum_extractorWeightedOp (H : HashFamily S C Z) (ρ : CQState C Q) :
    ∑ z, extractorWeightedOp H ρ z = ρ.quantumMarginal.toOp := by
  let : Nonempty S := H.seedNonempty
  unfold extractorWeightedOp
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hi (s : S) :
      (∑ z : Z, ∑ c : C, if H.hash s c = z then (ρ.stateMap c).toOp else 0) =
        ∑ c, (ρ.stateMap c).toOp := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [hi]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    one_div, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]
  rfl

/-- The CQ output after averaging over and discarding a uniform seed. -/
def extractorOutputState (H : HashFamily S C Z) (ρ : CQState C Q) : CQState Z Q :=
  CQState.ofBlocks (extractorWeightedOp H ρ)
    (fun z => by
      apply Matrix.PosSemidef.smul
      · exact Matrix.posSemidef_sum _ fun s _ => Matrix.posSemidef_sum _ fun c _ => by
          split_ifs
          · exact (ρ.stateMap c).posSemidef
          · exact Matrix.PosSemidef.zero
      · positivity)
    (by
      rw [← Complex.re_sum, ← Matrix.trace_sum, sum_extractorWeightedOp]
      exact ρ.quantumMarginal.trace_le_one)

namespace SeedKey

/-- The quantum block at a retained public seed and hash output. -/
def weightedOp (H : HashFamily S C Z) (ρ : CQState C Q) (s : S) (z : Z) : Op Q :=
  (1 / Fintype.card S : ℝ) •
    ∑ c : C, if H.hash s c = z then (ρ.stateMap c).toOp else 0

/-- Summing the public seed–key blocks returns the quantum marginal. -/
theorem sum_weightedOp (H : HashFamily S C Z) (ρ : CQState C Q) :
    ∑ sz : S × Z, weightedOp H ρ sz.1 sz.2 = ρ.quantumMarginal.toOp := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  change (∑ z, ∑ s, (1 / Fintype.card S : ℝ) •
    ∑ c, if H.hash s c = z then (ρ.stateMap c).toOp else 0) = _
  simp_rw [← Finset.smul_sum]
  simpa only [extractorWeightedOp, ← Finset.smul_sum] using sum_extractorWeightedOp H ρ

/-- Hashing with the uniformly sampled seed retained in the classical output. -/
def output (H : HashFamily S C Z) (ρ : CQState C Q) : CQState (S × Z) Q :=
  CQState.ofBlocks (fun sz => weightedOp H ρ sz.1 sz.2)
    (fun sz => by
      apply Matrix.PosSemidef.smul
      · exact Matrix.posSemidef_sum _ fun c _ => by
          split_ifs
          · exact (ρ.stateMap c).posSemidef
          · exact Matrix.PosSemidef.zero
      · positivity)
    (by
      rw [← Complex.re_sum, ← Matrix.trace_sum, sum_weightedOp]
      exact ρ.quantumMarginal.trace_le_one)

end SeedKey

end InfoTheory.QuantumLHL
