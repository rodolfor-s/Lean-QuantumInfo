import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor

/-! # Kernel Operations -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators
open scoped Kronecker

variable {C D Q R : Type*} [Fintype C] [Fintype D] [Fintype Q] [Fintype R]

/-- Keep the selected classical blocks and replace all other blocks by zero. -/
def CQState.filterKeep (keep : C → Bool) (ρ : CQState C Q) : CQState C Q where
  stateMap c := if keep c then ρ.stateMap c else SubDensityOp.zero
  weight_le_one := by
    refine (Finset.sum_le_sum fun c _ => ?_).trans ρ.weight_le_one
    split_ifs
    · exact le_rfl
    · simpa [SubDensityOp.trace, SubDensityOp.zero] using (ρ.stateMap c).trace_nonneg

/-- Filtering acts blockwise without renormalization. -/
@[simp] theorem CQState.filterKeep_stateMap (keep : C → Bool) (ρ : CQState C Q) (c : C) :
    (ρ.filterKeep keep).stateMap c = if keep c then ρ.stateMap c else SubDensityOp.zero := rfl

/-- Successive classical filters retain the intersection of their outcomes. -/
theorem CQState.filterKeep_filterKeep (keep₁ keep₂ : C → Bool) (ρ : CQState C Q) :
    (ρ.filterKeep keep₁).filterKeep keep₂ = ρ.filterKeep (fun c => keep₁ c && keep₂ c) := by
  ext c
  cases h₁ : keep₁ c <;> cases h₂ : keep₂ c <;> simp [filterKeep, h₁, h₂]

/-- Trace mass of a tensor product of subnormalized states. -/
theorem subDensityOp_kronecker_trace (ρ : SubDensityOp Q) (σ : SubDensityOp R) :
    (ρ.kronecker σ).trace = ρ.trace * σ.trace := by
  simp [SubDensityOp.trace, SubDensityOp.kronecker, Matrix.trace_kronecker,
    Complex.mul_re, ρ.trace_im]

/-- Append a classical-label-dependent quantum block on the left. -/
def CQState.tensorLeftKernel (ρ : CQState C Q) (K : C → SubDensityOp R) : CQState C (R × Q) where
  stateMap c := (K c).kronecker (ρ.stateMap c)
  weight_le_one := by
    refine (Finset.sum_le_sum fun c _ => ?_).trans ρ.weight_le_one
    rw [subDensityOp_kronecker_trace]
    exact mul_le_of_le_one_left (ρ.stateMap c).trace_nonneg (K c).trace_le_one

/-- Append a classical-label-dependent quantum block on the right. -/
def CQState.tensorRightKernel (ρ : CQState C Q) (K : C → SubDensityOp R) : CQState C (Q × R) where
  stateMap c := (ρ.stateMap c).kronecker (K c)
  weight_le_one := by
    refine (Finset.sum_le_sum fun c _ => ?_).trans ρ.weight_le_one
    rw [subDensityOp_kronecker_trace]
    exact mul_le_of_le_one_right (ρ.stateMap c).trace_nonneg (K c).trace_le_one

/-- The block of a left announcement is its ordinary tensor product. -/
@[simp] theorem CQState.tensorLeftKernel_stateMap (ρ : CQState C Q)
    (K : C → SubDensityOp R) (c : C) :
    (ρ.tensorLeftKernel K).stateMap c = (K c).kronecker (ρ.stateMap c) := rfl

/-- The block of a right announcement is its ordinary tensor product. -/
@[simp] theorem CQState.tensorRightKernel_stateMap (ρ : CQState C Q)
    (K : C → SubDensityOp R) (c : C) :
    (ρ.tensorRightKernel K).stateMap c = (ρ.stateMap c).kronecker (K c) := rfl

/-- Normalized announcement kernels preserve total weight. -/
theorem CQState.tensorLeftKernel_weight (ρ : CQState C Q) (K : C → SubDensityOp R)
    (hK : ∀ c, (K c).trace = 1) :
    ∑ c, ((ρ.tensorLeftKernel K).stateMap c).trace = ∑ c, (ρ.stateMap c).trace := by
  simp only [tensorLeftKernel_stateMap, subDensityOp_kronecker_trace, hK, one_mul]

/-- Normalized right announcement kernels preserve total weight. -/
theorem CQState.tensorRightKernel_weight (ρ : CQState C Q) (K : C → SubDensityOp R)
    (hK : ∀ c, (K c).trace = 1) :
    ∑ c, ((ρ.tensorRightKernel K).stateMap c).trace = ∑ c, (ρ.stateMap c).trace := by
  simp only [tensorRightKernel_stateMap, subDensityOp_kronecker_trace, hK, mul_one]

/-- Filtering commutes with a left announcement, including dropped zero blocks. -/
theorem CQState.tensorLeftKernel_filterKeep (ρ : CQState C Q) (K : C → SubDensityOp R)
    (keep : C → Bool) :
    (ρ.filterKeep keep).tensorLeftKernel K = (ρ.tensorLeftKernel K).filterKeep keep := by
  apply CQState.ext
  funext c
  apply SubDensityOp.ext
  cases h : keep c <;> simp [filterKeep, tensorLeftKernel, SubDensityOp.kronecker, h,
    SubDensityOp.zero]

/-- Each tensor-power block is indexed by the actual function register. -/
theorem CQState.tensorPower_stateMap_toOp (ρ : CQState C Q) (n : ℕ) (c : Fin n → C) :
    ((ρ.tensorPower n).stateMap c).toOp =
      Matrix.piTensorProduct (fun i => (ρ.stateMap (c i)).toOp) := rfl

/-- Classical coarsening commutes with quantum register relabelling. -/
theorem CQState.coarsen_reindex [DecidableEq D] (ρ : CQState C Q) (f : C → D) (e : Q ≃ R) :
    (ρ.reindex e).coarsen f = (ρ.coarsen f).reindex e := by
  apply CQState.ext
  funext d
  apply SubDensityOp.ext
  change (∑ c, if f c = d then Matrix.reindex e e (ρ.stateMap c).toOp else 0) =
    Matrix.reindex e e (∑ c, if f c = d then (ρ.stateMap c).toOp else 0)
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> rfl

/-- A kernel constant on every coarsening fibre can be attached after coarsening. -/
theorem CQState.coarsen_tensorLeftKernel_factor [DecidableEq D] (ρ : CQState C Q)
    (f : C → D) (K : D → SubDensityOp R) :
    (ρ.tensorLeftKernel (K ∘ f)).coarsen f = (ρ.coarsen f).tensorLeftKernel K := by
  apply CQState.ext
  funext d
  apply SubDensityOp.ext
  change (∑ c, if f c = d then (K (f c)).toOp ⊗ₖ (ρ.stateMap c).toOp else 0) =
    (K d).toOp ⊗ₖ (∑ c, if f c = d then (ρ.stateMap c).toOp else 0)
  ext i j
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with h <;> simp [h]

/-- Applying a classical function at every site commutes with CQ tensor powers. -/
theorem CQState.coarsen_tensorPower [DecidableEq D] (ρ : CQState C Q) (f : C → D) (n : ℕ) :
    (ρ.coarsen f).tensorPower n = (ρ.tensorPower n).coarsen (fun c i => f (c i)) := by
  apply CQState.ext
  funext d
  apply SubDensityOp.ext
  ext i j
  simp only [CQState.tensorPower, CQState.coarsen, CQState.ofBlocks, SubDensityOp.tensorFamily,
    Matrix.piTensorProduct_apply, Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : (fun k => f (c k)) = d
  · simp only [h, ite_true]
    apply Finset.prod_congr rfl
    intro k _
    rw [ite_eq_left (congrFun h k)]
  · rw [ite_eq_right h]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)

end InfoTheory.SmoothMinEntropy
