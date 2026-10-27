import QCryptLean.InfoTheory.Renyi.ConditionalVariance.Defs
import QCryptLean.InfoTheory.Renyi.PetzConditional
import QCryptLean.InfoTheory.Renyi.Basic
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.SpectralTheory.ReindexCFC

/-! # Reindex -/


noncomputable section

namespace InfoTheory.Renyi

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The shared Petz trace is invariant under finite register relabelling. -/
theorem petzTrace_reindex (e : A ≃ B) (α : ℝ) (ρ σ : Matrix A A ℂ)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    petzTrace α (reindex e e ρ) (reindex e e σ) = petzTrace α ρ σ := by
  unfold petzTrace
  rw [← reindex_cfcRpow e ρ hρ, ← reindex_cfcRpow e σ hσ]
  have hm := (map_mul (reindexAlgEquiv ℂ ℂ e) (ρ ^ α) (σ ^ (1 - α))).symm
  change reindex e e (ρ ^ α) * reindex e e (σ ^ (1 - α)) = _ at hm
  rw [hm]
  exact congrArg Complex.re (reindex_trace e _)

/-- The shared bit-valued relative entropy is invariant under register relabelling. -/
theorem relativeEntropyBits_reindex (e : A ≃ B) (ρ σ : Matrix A A ℂ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relativeEntropyBits (reindex e e ρ) (reindex e e σ) = relativeEntropyBits ρ σ := by
  unfold relativeEntropyBits CFC.log
  rw [← reindex_cfc e ρ hρ, ← reindex_cfc e σ hσ]
  change ((reindex e e ρ) * reindex e e (cfc Real.log ρ - cfc Real.log σ)).trace.re /
    ((reindex e e ρ).trace.re * Real.log 2) = _
  have hm := (map_mul (reindexAlgEquiv ℂ ℂ e) ρ
    (cfc Real.log ρ - cfc Real.log σ)).symm
  change reindex e e ρ * reindex e e (cfc Real.log ρ - cfc Real.log σ) =
    reindex e e (ρ * (cfc Real.log ρ - cfc Real.log σ)) at hm
  rw [hm, reindex_trace, reindex_trace]

/-- The shared divergence variance retains both the trace and base-two normalizations. -/
theorem petzDivergenceVariance_reindex (e : A ≃ B) (ρ σ : Matrix A A ℂ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    petzDivergenceVariance (reindex e e ρ) (reindex e e σ) = petzDivergenceVariance ρ σ := by
  unfold petzDivergenceVariance
  rw [relativeEntropyBits_reindex e ρ σ hρ hσ]
  unfold CFC.log
  rw [← reindex_cfc e ρ hρ, ← reindex_cfc e σ hσ]
  have hp : (reindex e e (cfc Real.log ρ - cfc Real.log σ)) ^ 2 =
      reindex e e ((cfc Real.log ρ - cfc Real.log σ) ^ 2) := by
    exact (map_pow (reindexAlgEquiv ℂ ℂ e) _ 2).symm
  change (reindex e e ρ * (reindex e e (cfc Real.log ρ - cfc Real.log σ)) ^ 2).trace.re /
    ((reindex e e ρ).trace.re * Real.log 2 ^ 2) - _ = _
  rw [hp]
  have hm := (map_mul (reindexAlgEquiv ℂ ℂ e) ρ
    ((cfc Real.log ρ - cfc Real.log σ) ^ 2)).symm
  change reindex e e ρ * reindex e e ((cfc Real.log ρ - cfc Real.log σ) ^ 2) =
    reindex e e (ρ * (cfc Real.log ρ - cfc Real.log σ) ^ 2) at hm
  rw [hm, reindex_trace, reindex_trace]

end InfoTheory.Renyi
