import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Quantum relabelling preserves complete CQ entropy domains -/

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Quantum.Metrics

variable {C Q R : Type*} [Fintype C] [Fintype Q] [Fintype R]

/-- Quantum relabelling is an equivalence on the entire CQ state space. -/
def CQState.reindexEquiv (e : Q ≃ R) : CQState C Q ≃ CQState C R where
  toFun := CQState.reindex e
  invFun := CQState.reindex e.symm
  left_inv ρ := by
    apply CQState.ext
    funext c
    apply SubDensityOp.ext
    ext i j
    simp [CQState.reindex, SubDensityOp.reindex]
  right_inv ρ := by
    apply CQState.ext
    funext c
    apply SubDensityOp.ext
    ext i j
    simp [CQState.reindex, SubDensityOp.reindex]

/-- Quantum relabelling acts on the quantum component of the joint register. -/
theorem CQState.toJointDensity_reindex [DecidableEq C] (e : Q ≃ R) (ρ : CQState C Q) :
    (ρ.reindex e).toJointDensity = ρ.toJointDensity.reindex (e.prodCongr (Equiv.refl C)) := by
  apply SubDensityOp.ext
  exact (Matrix.reindex_blockDiagonal e e (Equiv.refl C)
    (fun c => (ρ.stateMap c).toOp)).symm

/-- Joint purified distance is invariant under quantum register relabelling. -/
theorem CQState.purifiedDistance_reindex [DecidableEq C] (e : Q ≃ R) (ρ τ : CQState C Q) :
    (ρ.reindex e).purifiedDistance (τ.reindex e) = ρ.purifiedDistance τ := by
  unfold CQState.purifiedDistance
  rw [CQState.toJointDensity_reindex, CQState.toJointDensity_reindex]
  unfold Quantum.Metrics.purifiedDistance fidelityGen
  have hf := fidelity_reindex (e.prodCongr (Equiv.refl C))
    ρ.toJointDensity.toPosSemidefOp τ.toJointDensity.toPosSemidefOp
  change fidelity (ρ.toJointDensity.reindex (e.prodCongr (Equiv.refl C))).toPosSemidefOp
    (τ.toJointDensity.reindex (e.prodCongr (Equiv.refl C))).toPosSemidefOp = _ at hf
  rw [hf]
  simp only [SubDensityOp.trace, SubDensityOp.reindex, Matrix.reindex_trace]

/-- Relabelling preserves real-quadratic feasibility on every block. -/
theorem isFeasible_reindex_iff (e : Q ≃ R) (ρ : CQState C Q) (σ : SubDensityOp Q) (t : ℝ) :
    IsFeasible (ρ.reindex e) (σ.reindex e) t ↔ IsFeasible ρ σ t := by
  change (0 ≤ t ∧ ∀ c, OpLe (Matrix.reindex e e (ρ.stateMap c).toOp)
    ((t : ℂ) • Matrix.reindex e e σ.toOp)) ↔ _
  exact and_congr Iff.rfl (forall_congr' fun c =>
    opLe_reindex_iff e (ρ.stateMap c).toOp ((t : ℂ) • σ.toOp))

/-- Quantum relabelling preserves the real infimum, including empty feasible sets. -/
theorem minScale_reindex (e : Q ≃ R) (ρ : CQState C Q) (σ : SubDensityOp Q) :
    minScale (ρ.reindex e) (σ.reindex e) = minScale ρ σ := by
  unfold minScale
  congr 1
  ext t
  exact isFeasible_reindex_iff e ρ σ t

/-- Signed min-entropy is invariant under quantum register relabelling. -/
theorem minEntropyReal_reindex (e : Q ≃ R) (ρ : CQState C Q) (σ : SubDensityOp Q) :
    minEntropyReal (ρ.reindex e) (σ.reindex e) = minEntropyReal ρ σ := by
  simp only [minEntropyReal, minScale_reindex]

/-- Extended min-entropy retains every feasibility and zero branch under relabelling. -/
theorem minEntropy_reindex (e : Q ≃ R) (ρ : CQState C Q) (σ : SubDensityOp Q) :
    minEntropy (ρ.reindex e) (σ.reindex e) = minEntropy ρ σ := by
  have hs : HasScale (ρ.reindex e) (σ.reindex e) ↔ HasScale ρ σ :=
    exists_congr (fun t => isFeasible_reindex_iff e ρ σ t)
  rw [minEntropy, minEntropy, minScale_reindex, minEntropyReal_reindex, hs]

/-- Quantum relabelling preserves the full joint-CQ smoothing ball at every radius. -/
theorem smoothMinEntropy_reindex [DecidableEq C] (e : Q ≃ R) (ε : ℝ)
    (ρ : CQState C Q) (σ : SubDensityOp Q) :
    smoothMinEntropy ε (ρ.reindex e) (σ.reindex e) = smoothMinEntropy ε ρ σ := by
  unfold smoothMinEntropy
  symm
  apply (CQState.reindexEquiv (C := C) e).iSup_congr
  intro τ
  simp only [CQState.reindexEquiv, Equiv.coe_fn_mk, CQState.purifiedDistance_reindex,
    minEntropy_reindex]

end InfoTheory.SmoothMinEntropy
