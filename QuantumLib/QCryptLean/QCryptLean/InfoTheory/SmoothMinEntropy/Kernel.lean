import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.SmoothTransport
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Metrics.SubDensityMonotonicity
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Kernel -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Quantum.Metrics Quantum.Channels Matrix
open scoped ComplexOrder

variable {C Q R : Type*} [Fintype C] [Fintype Q] [Fintype R] {n m : ℕ}

variable [DecidableEq C] [Nonempty C] [Nonempty Q]

/-- A common keep-filter contracts complete CQ purified distance.
The classical filter is a completely positive, trace-nonincreasing conjugation. -/
theorem CQState.purifiedDistance_filterKeep_le (ρ τ : CQState C Q) (keep : C → Bool) :
    (ρ.filterKeep keep).purifiedDistance (τ.filterKeep keep) ≤ ρ.purifiedDistance τ := by
  classical
  let P : Op (Q × C) := diagonal fun p => if keep p.2 then 1 else 0
  have ht (A : Op (Q × C)) (hA : A.PosSemidef) :
      (conjLinearMap P A).trace.re ≤ A.trace.re := by
    have he : (conjLinearMap P A).trace.re =
        ∑ i, if keep i.2 then (A i i).re else 0 := by
      simp only [conjLinearMap_apply, P, diagonal_conjTranspose, Matrix.trace, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      cases hk : keep i.2 <;> simp [hk]
    rw [he, Matrix.trace, Complex.re_sum]
    apply Finset.sum_le_sum
    intro i _
    cases keep i.2 <;> simp [(Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1]
  have he (ω : CQState C Q) : (ω.filterKeep keep).toJointDensity.toOp =
      conjLinearMap P ω.toJointDensity.toOp := by
    ext p q
    simp only [conjLinearMap_apply, P, diagonal_conjTranspose, diagonal_mul,
      mul_diagonal, Pi.star_apply, CQState.toJointDensity, CQState.toJointOp,
      blockDiagonal_apply, CQState.filterKeep]
    by_cases h : p.2 = q.2
    · simp only [h, ↓reduceIte]
      cases keep q.2 <;> simp [SubDensityOp.zero]
    · simp [h]
  exact purifiedDistance_le_of_isCompletelyPositive_of_trace_le (conjLinearMap P)
    (isCompletelyPositive_conjLinearMap P) ht ρ.toJointDensity τ.toJointDensity
    (ρ.filterKeep keep).toJointDensity (τ.filterKeep keep).toJointDensity (he ρ) (he τ)

/-- Filtering never decreases extended smooth entropy, at every real radius.
Each smoothing witness is filtered, preserving every feasible scale. -/
theorem smoothMinEntropy_filterKeep_ge (ε : ℝ) (ρ : CQState C Q)
    (σ : SubDensityOp Q) (keep : C → Bool) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy ε (ρ.filterKeep keep) σ := by
  have h := smoothMinEntropy_le_add_of_feasible_transport ρ σ (ρ.filterKeep keep) σ
    ε ε 0 le_rfl
  simp only [ENNReal.ofReal_zero, add_zero] at h
  apply h
  intro τ hd
  refine ⟨τ.filterKeep keep, (CQState.purifiedDistance_filterKeep_le ρ τ keep).trans hd, ?_⟩
  intro t ht
  simp only [Real.rpow_zero, one_mul]
  refine ⟨ht.1, fun c => ?_⟩
  cases hk : keep c
  · simp only [CQState.filterKeep, hk, Bool.false_eq_true, ↓reduceIte, SubDensityOp.zero]
    exact opLe_of_posSemidef_sub (by
      simpa only [sub_zero] using σ.posSemidef.smul (Complex.zero_le_real.mpr ht.1))
  · simpa [CQState.filterKeep, hk] using ht.2 c
end InfoTheory.SmoothMinEntropy
