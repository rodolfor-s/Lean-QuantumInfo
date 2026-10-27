import QCryptLean.Math.LinearAlgebra.Matrix.PositiveEntries
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.SubchannelCompletion
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Inequality
import QCryptLean.Quantum.Metrics.PurifiedBasic
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.Extension
import QCryptLean.Quantum.Operators.ExtensionMetrics
import QCryptLean.Quantum.Operators.PrincipalSubmatrix

/-! # Sub Density Monotonicity -/


noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators Quantum.Channels
open scoped ComplexOrder

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- Generalized fidelity increases under every CP trace-nonincreasing linear map.
The proof uses native prerequisites. -/
theorem fidelityGen_le_of_isCompletelyPositive_of_trace_le (Φ : Operation X Y)
    (hcp : IsCompletelyPositive Φ)
    (htni : ∀ A : Op X, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re)
    (ρ σ : SubDensityOp X) (ρ' σ' : SubDensityOp Y)
    (hρ : ρ'.toOp = Φ ρ.toOp) (hσ : σ'.toOp = Φ σ.toOp) :
    fidelityGen ρ σ ≤ fidelityGen ρ' σ' := by
  obtain ⟨Ψ, hΨ, he⟩ := hcp.exists_channel_extend htni
  have h := fidelity_le_apply Ψ hΨ ρ.toDensityOpExtend.toPosSemidefOp
    σ.toDensityOpExtend.toPosSemidefOp ρ'.toDensityOpExtend.toPosSemidefOp
    σ'.toDensityOpExtend.toPosSemidefOp (he ρ ρ' hρ).symm (he σ σ' hσ).symm
  simpa only [SubDensityOp.toDensityOpExtend_fidelity] using h

/-- Purified distance contracts under CP trace-nonincreasing linear maps. -/
theorem purifiedDistance_le_of_isCompletelyPositive_of_trace_le (Φ : Operation X Y)
    (hcp : IsCompletelyPositive Φ)
    (htni : ∀ A : Op X, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re)
    (ρ σ : SubDensityOp X) (ρ' σ' : SubDensityOp Y)
    (hρ : ρ'.toOp = Φ ρ.toOp) (hσ : σ'.toOp = Φ σ.toOp) :
    purifiedDistance ρ' σ' ≤ purifiedDistance ρ σ :=
  purifiedDistance_le_of_le_fidelityGen ρ' σ' ρ σ
    (fidelityGen_le_of_isCompletelyPositive_of_trace_le Φ hcp htni ρ σ ρ' σ' hρ hσ)

/-- A channel increases generalized fidelity between its sub-density outputs. -/
theorem fidelityGen_le_apply (Φ : Operation X Y) (hΦ : IsChannel Φ)
    (ρ σ : SubDensityOp X) :
    fidelityGen ρ σ ≤ fidelityGen (hΦ.applySubDensity ρ) (hΦ.applySubDensity σ) :=
  fidelityGen_le_of_isCompletelyPositive_of_trace_le Φ hΦ.1
    (fun A _ => le_of_eq (congrArg Complex.re (hΦ.2 A))) ρ σ _ _ rfl rfl

/-- A channel contracts purified distance between sub-density states. -/
theorem purifiedDistance_apply_le (Φ : Operation X Y) (hΦ : IsChannel Φ)
    (ρ σ : SubDensityOp X) :
    purifiedDistance (hΦ.applySubDensity ρ) (hΦ.applySubDensity σ) ≤ purifiedDistance ρ σ :=
  purifiedDistance_le_of_le_fidelityGen _ _ _ _ (fidelityGen_le_apply Φ hΦ ρ σ)

/-- Restriction to distinct principal coordinates contracts purified distance. -/
theorem purifiedDistance_submatrix_le (ρ σ : SubDensityOp X) (f : Y → X)
    (hf : Function.Injective f) :
    purifiedDistance (ρ.submatrix f hf) (σ.submatrix f hf) ≤ purifiedDistance ρ σ := by
  let Φ : Operation X Y := ⟨⟨fun A => A.submatrix f f, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have hcp : IsCompletelyPositive Φ := by
    apply isCompletelyPositive_of_mapTensorId_posSemidef
    intro A hA
    exact hA.submatrix (fun p : Y × X => (f p.1, p.2))
  exact purifiedDistance_le_of_isCompletelyPositive_of_trace_le Φ hcp
    (fun A hA => hA.re_trace_submatrix_le f hf) ρ σ _ _ rfl rfl
end Quantum.Metrics
