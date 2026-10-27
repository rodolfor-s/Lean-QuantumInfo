import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.AncillaBounds
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.DiamondBounds
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Inequality
import QCryptLean.Quantum.Metrics.TraceNorm

/-! # Diamond Inequality -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Metrics

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- The diamond norm is subadditive. -/
theorem diamondNorm_add_le (Φ Ψ : Operation X Y) :
    diamondNorm (Φ + Ψ) ≤ diamondNorm Φ + diamondNorm Ψ := by
  apply diamondNorm_le_of_forall
  intro A hA
  change traceNorm (mapTensorId Φ X A + mapTensorId Ψ X A) ≤ _
  exact (traceNorm_add_le _ _).trans (add_le_add
    (traceNorm_mapTensorId_le_diamondNorm Φ A hA)
    (traceNorm_mapTensorId_le_diamondNorm Ψ A hA))

/-- Diamond submultiplicativity when the outer operation preserves adjoints. -/
theorem diamondNorm_comp_le
    (Φ : Operation Y Z) (Λ : Operation X Y) (h : ∀ A, Φ Aᴴ = (Φ A)ᴴ) :
    diamondNorm (Φ.comp Λ) ≤ diamondNorm Φ * diamondNorm Λ := by
  apply diamondNorm_le_of_forall
  intro A hA
  rw [mapTensorId_comp, LinearMap.comp_apply]
  exact (traceNorm_mapTensorId_le_mul_of_map_conjTranspose Φ (diamondNorm Φ) h
    (fun P hP ht => traceNorm_mapTensorId_le_diamondNorm Φ P
      (by rwa [traceNorm_of_posSemidef P hP])) _).trans
        (mul_le_mul_of_nonneg_left (traceNorm_mapTensorId_le_diamondNorm Λ A hA)
          (diamondNorm_nonneg Φ))

/-- A common postprocessing channel contracts distinguishing distance for arbitrary operations. -/
theorem diamondDist_comp_le
    (A : Operation Y Z) (hA : IsChannel A) (Φ Ψ : Operation X Y) :
    diamondDist (A.comp Φ) (A.comp Ψ) ≤ diamondDist Φ Ψ := by
  unfold diamondDist
  rw [← LinearMap.comp_sub]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply diamondNorm_le_of_forall
  intro W hW
  rw [mapTensorId_comp, LinearMap.comp_apply]
  exact (traceNorm_apply_le _ hA.mapTensorId _).trans
    (traceNorm_mapTensorId_le_diamondNorm _ W hW)

end Quantum.Channels
