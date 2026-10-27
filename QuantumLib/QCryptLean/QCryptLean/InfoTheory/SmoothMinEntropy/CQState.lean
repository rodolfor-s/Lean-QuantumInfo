import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.PurifiedBasic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor

/-!
# Classical–quantum states on finite registers

Blocks are subnormalized states; their total weight is at most one. The joint
register is quantum first, `Q × C`, matching the existing CQ convention. All
matrices use explicit PSD witnesses and explicit metric functions. No matrix
order or norm instance is installed. Empty classical and quantum registers are
allowed. Tensor powers use function registers, including the empty power.
-/

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators
open scoped ComplexOrder

/-- A finite family of positive quantum blocks with total weight at most one. -/
structure CQState (C Q : Type*) [Fintype C] [Fintype Q] where
  /-- The subnormalized quantum block for each classical outcome. -/
  stateMap : C → SubDensityOp Q
  /-- The sum of the classical outcome weights is at most one. -/
  weight_le_one : ∑ c, (stateMap c).trace ≤ 1

variable {C D Q R : Type*} [Fintype C] [Fintype D] [Fintype Q] [Fintype R]

/-- CQ states are determined by their blocks. -/
@[ext] theorem CQState.ext {ρ σ : CQState C Q} (h : ρ.stateMap = σ.stateMap) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- The all-zero CQ state, also valid on empty registers. -/
def CQState.zero : CQState C Q where
  stateMap _ := SubDensityOp.zero
  weight_le_one := by simp [SubDensityOp.trace, SubDensityOp.zero]

/-- The classical weight of each outcome. -/
def CQState.classicalMarginal (ρ : CQState C Q) : C → ℝ := fun c => (ρ.stateMap c).trace

/-- Classical outcome weights are nonnegative. -/
theorem CQState.classicalMarginal_nonneg (ρ : CQState C Q) (c : C) :
    0 ≤ ρ.classicalMarginal c := (ρ.stateMap c).trace_nonneg

/-- Each classical outcome has weight at most one. -/
theorem CQState.classicalMarginal_le_one (ρ : CQState C Q) (c : C) :
    ρ.classicalMarginal c ≤ 1 := (ρ.stateMap c).trace_le_one

/-- Sum the classical blocks to obtain the quantum marginal. -/
def CQState.quantumMarginal (ρ : CQState C Q) : SubDensityOp Q where
  toOp := ∑ c, (ρ.stateMap c).toOp
  posSemidef := Matrix.posSemidef_sum _ (fun c _ => (ρ.stateMap c).posSemidef)
  trace_le_one := by
    rw [Matrix.trace_sum, Complex.re_sum]
    exact ρ.weight_le_one

/-- The marginal trace is the total CQ weight. -/
theorem CQState.quantumMarginal_trace (ρ : CQState C Q) :
    ρ.quantumMarginal.trace = ∑ c, (ρ.stateMap c).trace := by
  simp [quantumMarginal, SubDensityOp.trace, Matrix.trace_sum]

/-- The joint operator is block diagonal on the quantum-first register. -/
def CQState.toJointOp [DecidableEq C] (ρ : CQState C Q) : Op (Q × C) :=
  Matrix.blockDiagonal (fun c => (ρ.stateMap c).toOp)

/-- The block-diagonal joint state retains its possible trace deficit. -/
def CQState.toJointDensity [DecidableEq C] (ρ : CQState C Q) : SubDensityOp (Q × C) where
  toOp := ρ.toJointOp
  posSemidef := Matrix.posSemidef_blockDiagonal (fun c => (ρ.stateMap c).posSemidef)
  trace_le_one := by
    rw [toJointOp, Matrix.trace_blockDiagonal, Complex.re_sum]
    exact ρ.weight_le_one

/-- The joint trace equals the total classical weight. -/
theorem CQState.toJointDensity_trace [DecidableEq C] (ρ : CQState C Q) :
    ρ.toJointDensity.trace = ∑ c, (ρ.stateMap c).trace := by
  simp [toJointDensity, toJointOp, SubDensityOp.trace, Matrix.trace_blockDiagonal]

/-- CQ purified distance compares the complete joint states. -/
def CQState.purifiedDistance [DecidableEq C] (ρ σ : CQState C Q) : ℝ :=
  Quantum.Metrics.purifiedDistance ρ.toJointDensity σ.toJointDensity

/-- A CQ state is at zero purified distance from itself. -/
@[simp] theorem CQState.purifiedDistance_self [DecidableEq C] (ρ : CQState C Q) :
    ρ.purifiedDistance ρ = 0 :=
  Quantum.Metrics.purifiedDistance_self _

/-- Relabel the quantum register in every classical block. -/
def CQState.reindex (e : Q ≃ R) (ρ : CQState C Q) : CQState C R where
  stateMap c := (ρ.stateMap c).reindex e
  weight_le_one := by
    simpa only [SubDensityOp.trace, SubDensityOp.reindex, Matrix.reindex_trace]
      using ρ.weight_le_one

/-- Relabel classical outcomes bijectively, without changing quantum blocks. -/
def CQState.relabel (e : C ≃ D) (ρ : CQState C Q) : CQState D Q where
  stateMap d := ρ.stateMap (e.symm d)
  weight_le_one := (Equiv.sum_comp e.symm _).trans_le ρ.weight_le_one

/-- Transpose every quantum block. -/
def CQState.partialTransposeQ (ρ : CQState C Q) : CQState C Q where
  stateMap c := (ρ.stateMap c).transpose
  weight_le_one := ρ.weight_le_one

/-- Discard the right quantum register in each classical block. -/
def CQState.partialTraceRight (ρ : CQState C (Q × R)) : CQState C Q where
  stateMap c := (ρ.stateMap c).partialTraceRight
  weight_le_one := by
    simpa only [SubDensityOp.trace, SubDensityOp.partialTraceRight_toOp,
      Matrix.trace_partialTraceRight] using ρ.weight_le_one

/-- Tensor two CQ states on product classical and quantum registers. -/
def CQState.tensor (ρ : CQState C Q) (σ : CQState D R) : CQState (C × D) (Q × R) where
  stateMap cd := (ρ.stateMap cd.1).kronecker (σ.stateMap cd.2)
  weight_le_one := by
    have ht (c : C) (d : D) : ((ρ.stateMap c).kronecker (σ.stateMap d)).trace =
        (ρ.stateMap c).trace * (σ.stateMap d).trace := by
      simp [SubDensityOp.trace, SubDensityOp.kronecker, Matrix.trace_kronecker,
        Complex.mul_re, (ρ.stateMap c).trace_im]
    simp_rw [Fintype.sum_prod_type, ht, ← Finset.mul_sum, ← Finset.sum_mul]
    exact (mul_le_of_le_one_left
      (Finset.sum_nonneg fun d _ => (σ.stateMap d).trace_nonneg) ρ.weight_le_one).trans
        σ.weight_le_one

/-- Independent CQ states multiply their total classical weights. -/
theorem CQState.tensor_sum_trace (ρ : CQState C Q) (σ : CQState D R) :
    ∑ cd, ((ρ.tensor σ).stateMap cd).trace =
      (∑ c, (ρ.stateMap c).trace) * ∑ d, (σ.stateMap d).trace := by
  simp only [tensor, SubDensityOp.trace, SubDensityOp.kronecker, Matrix.trace_kronecker,
    Complex.mul_re, SubDensityOp.trace_im, mul_zero, sub_zero, Fintype.sum_prod_type,
    ← Finset.mul_sum, ← Finset.sum_mul]

/-- Tensor powers use functions for both classical outcomes and quantum coordinates. -/
def CQState.tensorPower (ρ : CQState C Q) (k : ℕ) : CQState (Fin k → C) (Fin k → Q) where
  stateMap cs := SubDensityOp.tensorFamily (fun i => ρ.stateMap (cs i))
  weight_le_one := by
    simp only [SubDensityOp.trace_tensorFamily]
    rw [← Fintype.prod_sum (fun (_ : Fin k) c => (ρ.stateMap c).trace)]
    exact Finset.prod_le_one₀ (fun _ _ => Finset.sum_nonneg fun c _ =>
      (ρ.stateMap c).trace_nonneg) (fun _ _ => ρ.weight_le_one)

/-- Tensor powers raise the total CQ weight to the number of copies. -/
theorem CQState.tensorPower_trace (ρ : CQState C Q) (k : ℕ) :
    ∑ cs, ((ρ.tensorPower k).stateMap cs).trace = (∑ c, (ρ.stateMap c).trace) ^ k := by
  simp only [tensorPower, SubDensityOp.trace_tensorFamily]
  rw [← Fintype.prod_sum (fun (_ : Fin k) c => (ρ.stateMap c).trace)]
  simp

/-- Normalization of every CQ tensor power. -/
theorem CQState.tensorPower_sum_trace (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) (k : ℕ) :
    ∑ cs, ((ρ.tensorPower k).stateMap cs).trace = 1 := by
  rw [tensorPower_trace, hρ, one_pow]

end InfoTheory.SmoothMinEntropy
