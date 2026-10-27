import QCryptLean.Quantum.Channels.Ancilla
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.DiamondBounds
import QCryptLean.Quantum.Channels.Indistinguishable
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Inequality
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic

/-! # Consumer Bounds -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Metrics

variable {I X Y Z R : Type*} [Fintype I] [Fintype X] [Fintype Y] [Fintype Z] [Fintype R]

/-- The diamond norm of the difference of two channels is at most two. -/
theorem diamondNorm_sub_le_two
    {Φ Ψ : Operation X Y} (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) :
    diamondNorm (Φ - Ψ) ≤ 2 := by
  apply diamondNorm_le_of_forall
  intro A hA
  rw [mapTensorId_sub, LinearMap.sub_apply]
  exact (traceNorm_sub_le _ _).trans ((add_le_add
    ((traceNorm_mapTensorId_le Φ hΦ A).trans hA)
    ((traceNorm_mapTensorId_le Ψ hΨ A).trans hA)).trans_eq (by norm_num))

/-- Pre- and postprocessing by channels contract the diamond norm of an
adjoint-preserving operation. -/
theorem diamondNorm_comp_comp_le_of_isChannel
    [Nonempty I]
    (A : Operation Y Z) (hA : IsChannel A)
    (Δ : Operation X Y) (hΔ : ∀ M, Δ Mᴴ = (Δ M)ᴴ)
    (B : Operation I X) (hB : IsChannel B) :
    diamondNorm (A.comp (Δ.comp B)) ≤ diamondNorm Δ := by
  apply diamondNorm_le_of_forall
  intro W hW
  exact traceNorm_mapTensorId_sandwich_le_diamondNorm Δ hΔ A hA B hB W hW

variable {n : ℕ}

/-- CKR reference trace norms contract under output postprocessing. -/
theorem ckrTraceNorm_comp_le_of_isChannel
    (K : Operation Y Z) (hK : IsChannel K) (Δ : Operation (Fin n → X) Y)
    (τ : DensityOp ((Fin n → X) × R)) :
    ckrTraceNorm (K.comp Δ) τ ≤ ckrTraceNorm Δ τ := by
  unfold ckrTraceNorm
  rw [mapTensorId_comp, LinearMap.comp_apply]
  exact traceNorm_mapTensorId_le K hK _

/-- A CKR output obtained by channel postprocessing is bounded by twice the
generalized trace distance, with no positivity assumption on the compared operators. -/
theorem ckrTraceNorm_le_two_traceDistanceGen_of_isChannel_comp_eq
    (Δ : Operation (Fin n → X) Y) (τ : DensityOp ((Fin n → X) × R))
    (Φ : Operation I (Y × R)) (hΦ : IsChannel Φ) (ρ σ : Op I)
    (hout : mapTensorId Δ R τ.toOp = Φ (ρ - σ)) :
    ckrTraceNorm Δ τ ≤ 2 * traceDistanceGen ρ σ := by
  unfold ckrTraceNorm
  rw [hout]
  have h := traceNorm_apply_le Φ hΦ (ρ - σ)
  unfold traceDistanceGen traceDistance
  linarith [abs_nonneg ((ρ.trace - σ.trace).re)]

end Quantum.Channels
