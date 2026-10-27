import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.FidelityOrder
import QCryptLean.Quantum.Metrics.Flagged
import QCryptLean.Quantum.Metrics.FlaggedBounds
import QCryptLean.Quantum.Metrics.PositiveSandwich
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.Projector

/-! # Fidelity of finite mixtures of projected positive operators -/
namespace Quantum.Metrics
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder
variable {X I : Type*} [Fintype X] [Fintype I] [Nonempty X] [Nonempty I]

omit [Nonempty I] in
/-- Projecting each term in a positive decomposition retains at least its output trace
as fidelity, even when the decomposition is dominated by the input. -/
theorem sum_trace_projectorSandwich_le_fidelity (A : I → PosSemidefOp X)
    (P : I → Op X) (hP : ∀ i, IsOrthogonalProjector (P i)) (B : PosSemidefOp X)
    (hle : (∑ i, (A i).val) ≤ B.val) :
    (∑ i, (P i * (A i).val * P i).trace.re) ≤
      fidelity B (sumPosSemidefOp Finset.univ (fun i => ⟨P i * (A i).val * P i, by
        simpa only [(hP i).isHermitian.eq] using
          (A i).property.conjTranspose_mul_mul_same (P i)⟩)) := by
  classical
  let C : I → PosSemidefOp X := fun i => ⟨P i * (A i).val * P i, by
    simpa only [(hP i).isHermitian.eq] using
      (A i).property.conjTranspose_mul_mul_same (P i)⟩
  have he (i : I) : fidelity (A i) (C i) = (P i * (A i).val * P i).trace.re :=
    fidelity_projectorSandwich (A i) (hP i)
  calc
    _ = ∑ i, fidelity (A i) (C i) := Finset.sum_congr rfl (fun i _ => (he i).symm)
    _ ≤ fidelity (sumPosSemidefOp Finset.univ A) (sumPosSemidefOp Finset.univ C) :=
      sum_fidelity_le_fidelity_sum A C
    _ ≤ fidelity B (sumPosSemidefOp Finset.univ C) := by
      rw [fidelity_comm, fidelity_comm B]
      exact fidelity_mono_right _ _ _ (by simpa [sumPosSemidefOp] using hle)

end Quantum.Metrics
