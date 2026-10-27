import QCryptLean.InfoTheory.SmoothMinEntropy.Bipartite
import QCryptLean.InfoTheory.SmoothMinEntropy.BipartiteRegularity
import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementChannel
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementEntropy
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Measurement Bounds -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Matrix
open scoped Kronecker

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable {n m : ℕ}

namespace RankOneProjectiveBasis

end RankOneProjectiveBasis

/-- Rank-one smooth uncertainty follows by native transport of every ball member and
feasible reference, at the same radius. -/
theorem smoothBipartiteMinEntropyOptReal_zDilatedState_le_sub [Nonempty A] [Nonempty B]
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (ρ : SubDensityOp (A × B))
    (hρ : ρ.trace = 1) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    smoothBipartiteMinEntropyOptReal ε (zDilatedState Q ρ) ≤
      smoothBipartiteMinEntropyOptReal ε (xMeasuredMarginal P ρ) -
        RankOneProjectiveBasis.preparationQuality P Q := by
  have hXnorm : (xMeasuredMarginal P ρ).trace = 1 := by rw [xMeasuredMarginal_trace, hρ]
  have hZnorm : (zDilatedState Q ρ).trace = 1 := by rw [zDilatedState_trace, hρ]
  have hbdd := smoothBipartiteMinSet_bddAbove_of_normalized (xMeasuredMarginal P ρ)
    hXnorm hε hε1
  apply csSup_le (smoothBipartiteMinSet_nonempty hε (zDilatedState Q ρ))
  rintro h ⟨τ, hd, rfl⟩
  have hmetric : Quantum.Metrics.purifiedDistance (xMeasuredMarginal P ρ)
      (measDilateTransport P Q τ) ≤ ε := by
    rw [← measDilateTransport_zDilatedState_eq_xMeasuredMarginal P Q ρ]
    exact (measDilateTransport_purifiedDistance_le P Q (zDilatedState Q ρ) τ).trans hd
  have hτ := ne_zero_of_purifiedDistance_of_normalized (zDilatedState Q ρ) τ hZnorm hε hε1 hd
  have hΞτ := ne_zero_of_purifiedDistance_of_normalized (xMeasuredMarginal P ρ)
    (measDilateTransport P Q τ) hXnorm hε hε1 hmetric
  have hval := bipartiteMinEntropyOptReal_measDilateTransport_ge P Q τ hτ hΞτ
  have hball := le_smoothBipartiteMinEntropyOptReal_of_mem_ball ε
    (xMeasuredMarginal P ρ) (measDilateTransport P Q τ) hbdd hmetric
  linarith

/-- The native unsmoothed uncertainty inequality retains its nonzero-state hypothesis. -/
theorem bipartiteMinEntropyOptReal_zDilatedState_le_sub [Nonempty A] [Nonempty B]
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (ρ : SubDensityOp (A × B))
    (hρ : ρ.toOp ≠ 0) :
    bipartiteMinEntropyOptReal (zDilatedState Q ρ) ≤
      bipartiteMinEntropyOptReal (xMeasuredMarginal P ρ) -
        RankOneProjectiveBasis.preparationQuality P Q := by
  have htr := subDensity_trace_re_pos ρ hρ
  have hrec := measDilateTransport_zDilatedState_eq_xMeasuredMarginal P Q ρ
  have hZ : (zDilatedState Q ρ).toOp ≠ 0 := by
    intro hz
    have hh : 0 < (zDilatedState Q ρ).trace := by rw [zDilatedState_trace]; exact htr
    simp only [SubDensityOp.trace, hz, Matrix.trace_zero, Complex.zero_re, lt_self_iff_false] at hh
  have hX : (measDilateTransport P Q (zDilatedState Q ρ)).toOp ≠ 0 := by
    rw [hrec]
    intro hz
    have hh : 0 < (xMeasuredMarginal P ρ).trace := by rw [xMeasuredMarginal_trace]; exact htr
    simp only [SubDensityOp.trace, hz, Matrix.trace_zero, Complex.zero_re, lt_self_iff_false] at hh
  have hh := bipartiteMinEntropyOptReal_measDilateTransport_ge P Q (zDilatedState Q ρ) hZ hX
  rwa [hrec] at hh

end InfoTheory.SmoothMinEntropy
