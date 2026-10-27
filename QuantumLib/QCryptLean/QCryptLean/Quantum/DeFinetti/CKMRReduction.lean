import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.RankOne
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKMRCoherent
import QCryptLean.Quantum.DeFinetti.CKMRMeasure
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology

/-! # CKMRReduction -/


noncomputable section
namespace Quantum.DeFinetti
open Matrix Quantum.Operators Quantum.Symmetry MeasureTheory
open scoped Kronecker ComplexOrder
variable {X : Type*} [Fintype X] [DecidableEq X] {n k : ℕ}

/-- Unnormalized retained state after a coherent outcome on the discarded sites. -/
def coherentReduction (x : X) (ρ : DensityOp (Fin n → X)) (hk : k ≤ n)
    (U : unitaryGroup X ℂ) : Op (Fin k → X) :=
  partialTraceRight ((1 ⊗ₖ ((pureStateMap x U).tensorPow (n-k)).toOp) *
    (ρ.reindex (splitLast hk)).toOp)

/-- Conditional coherent contractions are positive. -/
theorem coherentReduction_posSemidef (x : X) (ρ : DensityOp (Fin n → X)) (hk : k ≤ n)
    (U : unitaryGroup X ℂ) : (coherentReduction x ρ hk U).PosSemidef :=
  (ρ.reindex (splitLast hk)).posSemidef.partialTraceRight_one_kronecker_mul
    ((pureStateMap x U).tensorPow (n-k)).posSemidef

/-- Conditional contractions depend continuously on the Haar outcome. -/
theorem continuous_coherentReduction (x : X) (ρ : DensityOp (Fin n → X)) (hk : k ≤ n) :
    Continuous (coherentReduction x ρ hk) := by
  have hc : Continuous (fun U : unitaryGroup X ℂ =>
      (1 : Op (Fin k → X)) ⊗ₖ ((pureStateMap x U).tensorPow (n-k)).toOp) :=
    continuous_pi fun i => continuous_pi fun j => continuous_const.mul
      ((DensityOp.continuous_tensorPow_entry (n-k) i.2 j.2).comp (continuous_pureStateMap x))
  have hm := hc.mul (continuous_const (y := (ρ.reindex (splitLast hk)).toOp))
  exact continuous_pi fun i => continuous_pi fun j => continuous_finsetSum _ fun b _ =>
    (continuous_apply (j,b)).comp ((continuous_apply (i,b)).comp hm)

/-- Projecting the retained block contracts the globally coherent projector. -/
theorem pureStateMap_mul_coherentReduction (x : X) (ρ : DensityOp (Fin n → X)) (hk : k ≤ n)
    (U : unitaryGroup X ℂ) :
    ((pureStateMap x U).tensorPow k).toOp * coherentReduction x ρ hk U =
      partialTraceRight (reindex (splitLast hk) (splitLast hk)
        (((pureStateMap x U).tensorPow n).toOp * ρ.toOp)) := by
  change _ * partialTraceRight _ = _
  rw [← partialTraceRight_kronecker_one_mul, ← Matrix.mul_assoc, ← mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]
  change partialTraceRight ((Op.tensorPow (pureStateMap x U).toOp k ⊗ₖ
    Op.tensorPow (pureStateMap x U).toOp (n-k)) *
    reindex (splitLast hk) (splitLast hk) ρ.toOp) = _
  rw [← tensorPow_reindex_splitLast (pureStateMap x U).toOp hk]
  congr 1
  exact (reindexAlgEquiv ℂ ℂ (splitLast hk)).map_mul _ _ |>.symm

/-- The retained coherent sandwich has scalar weight equal to the full coherent outcome. -/
theorem pureStateMap_sandwich_coherentReduction (x : X) (ρ : DensityOp (Fin n → X))
    (hk : k ≤ n) (U : unitaryGroup X ℂ) :
    ((pureStateMap x U).tensorPow k).toOp * coherentReduction x ρ hk U *
        ((pureStateMap x U).tensorPow k).toOp =
      (((pureStateMap x U).tensorPow n).toOp * ρ.toOp).trace •
        ((pureStateMap x U).tensorPow k).toOp := by
  let v := Ket.tensorFamily (fun _ : Fin k => (unitaryColumn x U).toKet)
  have hp : ((pureStateMap x U).tensorPow k).toOp = vecMulVec v.vec (star v.vec) :=
    (Ket.projector_tensorFamily _).symm
  have ht : (((pureStateMap x U).tensorPow k).toOp * coherentReduction x ρ hk U).trace =
      (((pureStateMap x U).tensorPow n).toOp * ρ.toOp).trace := by
    rw [pureStateMap_mul_coherentReduction, trace_partialTraceRight, reindex_trace]
  rw [← ht, hp, vecMulVec_sandwich_eq_trace_smul]

end Quantum.DeFinetti
