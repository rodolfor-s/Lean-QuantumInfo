import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Classical relabelling preserves the complete CQ entropy domains -/

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Quantum.Metrics

variable {C D Q : Type*} [Fintype C] [Fintype D] [Fintype Q]

/-- Classical relabelling is an equivalence of complete CQ state spaces. -/
def CQState.relabelEquiv (e : C ≃ D) : CQState C Q ≃ CQState D Q where
  toFun := CQState.relabel e
  invFun := CQState.relabel e.symm
  left_inv ρ := by ext c; simp [CQState.relabel]
  right_inv ρ := by ext d; simp [CQState.relabel]

/-- Classical relabelling changes only the joint state's index names. -/
theorem CQState.toJointDensity_relabel [DecidableEq C] [DecidableEq D]
    (e : C ≃ D) (ρ : CQState C Q) :
    (ρ.relabel e).toJointDensity = ρ.toJointDensity.reindex ((Equiv.refl Q).prodCongr e) := by
  apply SubDensityOp.ext
  exact (Matrix.reindex_blockDiagonal (Equiv.refl Q) (Equiv.refl Q) e
    (fun c => (ρ.stateMap c).toOp)).symm

/-- Joint purified distance is invariant under classical relabelling. -/
theorem CQState.purifiedDistance_relabel [DecidableEq C] [DecidableEq D]
    (e : C ≃ D) (ρ τ : CQState C Q) :
    (ρ.relabel e).purifiedDistance (τ.relabel e) = ρ.purifiedDistance τ := by
  unfold CQState.purifiedDistance
  rw [CQState.toJointDensity_relabel, CQState.toJointDensity_relabel]
  unfold Quantum.Metrics.purifiedDistance fidelityGen
  have hf := fidelity_reindex ((Equiv.refl Q).prodCongr e)
    ρ.toJointDensity.toPosSemidefOp τ.toJointDensity.toPosSemidefOp
  change fidelity
    (ρ.toJointDensity.reindex ((Equiv.refl Q).prodCongr e)).toPosSemidefOp
    (τ.toJointDensity.reindex ((Equiv.refl Q).prodCongr e)).toPosSemidefOp = _ at hf
  rw [hf]
  simp only [SubDensityOp.trace, SubDensityOp.reindex, Matrix.reindex_trace]

/-- All feasible scales are unchanged by a bijection of classical outcomes. -/
theorem isFeasible_relabel_iff (e : C ≃ D) (ρ : CQState C Q) (σ : SubDensityOp Q) (t : ℝ) :
    IsFeasible (ρ.relabel e) σ t ↔ IsFeasible ρ σ t := by
  constructor
  · rintro ⟨ht, h⟩
    exact ⟨ht, fun c => by simpa [CQState.relabel] using h (e c)⟩
  · rintro ⟨ht, h⟩
    exact ⟨ht, fun d => h (e.symm d)⟩

/-- The real optimum is independent of classical outcome names. -/
theorem minScale_relabel (e : C ≃ D) (ρ : CQState C Q) (σ : SubDensityOp Q) :
    minScale (ρ.relabel e) σ = minScale ρ σ := by
  unfold minScale
  congr 1
  ext t
  exact isFeasible_relabel_iff e ρ σ t

/-- Signed entropy is independent of classical outcome names. -/
theorem minEntropyReal_relabel (e : C ≃ D) (ρ : CQState C Q) (σ : SubDensityOp Q) :
    minEntropyReal (ρ.relabel e) σ = minEntropyReal ρ σ := by
  simp only [minEntropyReal, minScale_relabel]

/-- Extended entropy preserves all its feasibility branches under relabelling. -/
theorem minEntropy_relabel (e : C ≃ D) (ρ : CQState C Q) (σ : SubDensityOp Q) :
    minEntropy (ρ.relabel e) σ = minEntropy ρ σ := by
  have hs : HasScale (ρ.relabel e) σ ↔ HasScale ρ σ :=
    exists_congr (fun t => isFeasible_relabel_iff e ρ σ t)
  rw [minEntropy, minEntropy, minScale_relabel, minEntropyReal_relabel, hs]

variable [DecidableEq C] [DecidableEq D]

/-- Relabelling preserves the complete real smoothing domain. -/
theorem isInSmoothedSetReal_relabel_iff (e : C ≃ D) (ε : ℝ)
    (ρ : CQState C Q) (σ : SubDensityOp Q) (h : ℝ) :
    IsInSmoothedSetReal ε (ρ.relabel e) σ h ↔ IsInSmoothedSetReal ε ρ σ h := by
  constructor
  · rintro ⟨τ, hh, hτ⟩
    obtain ⟨τ, rfl⟩ := (CQState.relabelEquiv (Q := Q) e).surjective τ
    exact ⟨τ, by simpa only [CQState.relabelEquiv, Equiv.coe_fn_mk,
      minEntropyReal_relabel] using hh,
      by simpa only [CQState.relabelEquiv, Equiv.coe_fn_mk,
        CQState.purifiedDistance_relabel] using hτ⟩
  · rintro ⟨τ, hh, hτ⟩
    exact ⟨τ.relabel e, by simpa only [minEntropyReal_relabel] using hh,
      by simpa only [CQState.purifiedDistance_relabel] using hτ⟩

/-- Real smoothing remains unchanged even when its real supremum is totalized. -/
theorem smoothMinEntropyReal_relabel (e : C ≃ D) (ε : ℝ)
    (ρ : CQState C Q) (σ : SubDensityOp Q) :
    smoothMinEntropyReal ε (ρ.relabel e) σ = smoothMinEntropyReal ε ρ σ := by
  unfold smoothMinEntropyReal
  congr 1
  ext h
  exact isInSmoothedSetReal_relabel_iff e ε ρ σ h

/-- Extended smoothing preserves the whole CQ ball under classical relabelling. -/
theorem smoothMinEntropy_relabel (e : C ≃ D) (ε : ℝ)
    (ρ : CQState C Q) (σ : SubDensityOp Q) :
    smoothMinEntropy ε (ρ.relabel e) σ = smoothMinEntropy ε ρ σ := by
  unfold smoothMinEntropy
  symm
  apply (CQState.relabelEquiv (Q := Q) e).iSup_congr
  intro τ
  simp only [CQState.relabelEquiv, Equiv.coe_fn_mk, CQState.purifiedDistance_relabel,
    minEntropy_relabel]

end InfoTheory.SmoothMinEntropy
