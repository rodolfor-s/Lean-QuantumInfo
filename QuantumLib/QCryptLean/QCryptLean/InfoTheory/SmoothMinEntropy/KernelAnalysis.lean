import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.Quantum.Operators.Basic

/-!
# Analytic laws for fixed announcement kernels

Matrix norm instances are local Frobenius instances. Entrywise integral laws retain
their full domains and require no integrability assumption where none is needed.
-/

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators MeasureTheory
open scoped Kronecker

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

private local instance {Q : Type*} [Fintype Q] : ContinuousENorm (Op Q) :=
  SeminormedAddGroup.toContinuousENorm

variable {C Q R α : Type*} [Fintype C] [Fintype Q] [Fintype R]

/-- Attaching a fixed kernel preserves blockwise Bochner integrability. -/
theorem tensorLeftKernel_blocks_integrable [MeasurableSpace α] {μ : Measure α}
    (f : α → CQState C Q) (K : C → SubDensityOp R) (c : C)
    (hf : Integrable (fun a => ((f a).stateMap c).toOp) μ) :
    Integrable (fun a => (((f a).tensorLeftKernel K).stateMap c).toOp) μ :=
  (Matrix.kroneckerBilinear (R := ℂ) (K c).toOp :
    Op Q →ₗ[ℂ] Op (R × Q)).toContinuousLinearMap.integrable_comp hf

/-- A fixed kernel commutes entrywise with the mixture integral. -/
theorem tensorLeftKernel_blocks_integral_eq [MeasurableSpace α] {μ : Measure α}
    (ρ : CQState C Q) (f : α → CQState C Q) (K : C → SubDensityOp R)
    (hlin : ∀ c i j, (ρ.stateMap c).toOp i j = ∫ a, ((f a).stateMap c).toOp i j ∂μ)
    (c : C) (i j : R × Q) :
    ((ρ.tensorLeftKernel K).stateMap c).toOp i j =
      ∫ a, (((f a).tensorLeftKernel K).stateMap c).toOp i j ∂μ := by
  change (K c).toOp i.1 j.1 * (ρ.stateMap c).toOp i.2 j.2 =
    ∫ a, (K c).toOp i.1 j.1 * ((f a).stateMap c).toOp i.2 j.2 ∂μ
  rw [hlin, integral_const_mul]

/-- Attaching a fixed kernel preserves blockwise continuity. -/
theorem tensorLeftKernel_blocks_continuous [TopologicalSpace α]
    (f : α → CQState C Q) (K : C → SubDensityOp R) (c : C)
    (hf : Continuous (fun a => ((f a).stateMap c).toOp)) :
    Continuous (fun a => (((f a).tensorLeftKernel K).stateMap c).toOp) :=
  (Matrix.kroneckerBilinear (R := ℂ) (K c).toOp).toContinuousLinearMap.continuous.comp hf

/-- Normalized kernels preserve the trace of every entrywise restricted mixture. -/
theorem trace_setIntegral_tensorLeftKernel_blocks_eq [MeasurableSpace α] {μ : Measure α}
    (f : α → CQState C Q) (K : C → SubDensityOp R)
    (hK : ∀ c, (K c).toOp.trace = 1) (s : Set α) (c : C) :
    (Matrix.of fun i j : R × Q =>
      ∫ a in s, (((f a).tensorLeftKernel K).stateMap c).toOp i j ∂μ).trace =
    (Matrix.of fun i j : Q => ∫ a in s, ((f a).stateMap c).toOp i j ∂μ).trace := by
  have he : (Matrix.of fun i j : R × Q =>
      ∫ a in s, (((f a).tensorLeftKernel K).stateMap c).toOp i j ∂μ) =
      (K c).toOp ⊗ₖ (Matrix.of fun i j : Q =>
        ∫ a in s, ((f a).stateMap c).toOp i j ∂μ) := by
    ext i j
    exact integral_const_mul _ _
  rw [he, Matrix.trace_kronecker, hK, one_mul]

end InfoTheory.SmoothMinEntropy
