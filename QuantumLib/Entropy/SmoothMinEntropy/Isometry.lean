import QuantumLib.Entropy.SmoothMinEntropy.CQState
import QuantumLib.Entropy.SmoothMinEntropy.Channel
import QuantumLib.Entropy.SmoothMinEntropy.KernelOperations
import QuantumLib.Entropy.SmoothMinEntropy.Smooth
import QuantumLib.ForMathlib.LinearAlgebra.Matrix.PiTensorProduct
import QuantumLib.ForPhyslib.QuantumInfo.Channels.Kraus
import QuantumLib.ForPhyslib.QuantumInfo.Channels.KrausAlgebra
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Tensor

/-! # Full-domain entropy transport under rectangular quantum isometries -/

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Quantum.Channels Matrix

variable {C Q R : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
  [Fintype Q] [DecidableEq Q] [Nonempty Q] [Fintype R] [Nonempty R]

/-- A rectangular isometry of both state and reference preserves every feasible
floor in the full joint-CQ smoothing ball. -/
theorem smoothMinEntropy_isometryConjugate_le (V : Matrix R Q ℂ) (hV : Vᴴ * V = 1)
    (ε : ℝ) (ρ : CQState C Q) (σ : SubDensityOp Q) (τ : CQState C R)
    (hτ : ∀ c, (τ.stateMap c).toOp = V * (ρ.stateMap c).toOp * Vᴴ)
    (ω : SubDensityOp R) (hω : ω.toOp = V * σ.toOp * Vᴴ) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy ε τ ω := by
  cases Subsingleton.elim (inferInstance : DecidableEq Q) (Classical.decEq Q)
  classical
  have hΦ := (isChannel_conjLinearMap_iff V).mpr hV
  have he : ρ.applyChannel hΦ = τ := by
    ext c i j
    exact congrFun (congrFun (hτ c).symm i) j
  have hf : hΦ.applySubDensity σ = ω := SubDensityOp.ext hω.symm
  simpa only [he, hf] using smoothMinEntropy_applyChannel_le ε ρ σ hΦ

/-- Sitewise isometries transport tensor-power entropy, also at zero copies.
The input and output single-site registers may have different cardinalities. -/
theorem smoothMinEntropy_tensorPower_conj_le (n : ℕ)
    (V : Matrix R Q ℂ) (hV : Vᴴ * V = 1)
    (ρ : CQState C Q) (τ : CQState C R) (σ : SubDensityOp Q) (ω : SubDensityOp R)
    (hτ : ∀ c, (τ.stateMap c).toOp = V * (ρ.stateMap c).toOp * Vᴴ)
    (hω : ω.toOp = V * σ.toOp * Vᴴ) (ε : ℝ) :
    smoothMinEntropy ε (ρ.tensorPower n) (SubDensityOp.tensorFamily (fun _ : Fin n => σ)) ≤
      smoothMinEntropy ε (τ.tensorPower n) (SubDensityOp.tensorFamily (fun _ : Fin n => ω)) := by
  classical
  apply smoothMinEntropy_isometryConjugate_le (piTensorProduct (fun _ : Fin n => V))
    (by rw [conjTranspose_piTensorProduct, piTensorProduct_mul]; simp [hV])
  · intro cs
    simp only [CQState.tensorPower_stateMap_toOp, hτ, conjTranspose_piTensorProduct,
      piTensorProduct_mul]
  · change piTensorProduct (fun _ : Fin n => ω.toOp) = _
    simp only [hω, SubDensityOp.tensorFamily, conjTranspose_piTensorProduct,
      piTensorProduct_mul]

end InfoTheory.SmoothMinEntropy
