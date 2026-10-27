import QCryptLean.InfoTheory.BellDiagonal.AliceZ
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQCore
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Alice-Z coarsening of a measured signal pair

Alice's bit is the first component of the classical signal outcome. Its conditional
state is the partial trace of the common Alice-Z projector sandwich.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators InfoTheory.SmoothMinEntropy
open InfoTheory.BellDiagonal Measurement Matrix
open scoped Kronecker

variable (E : Type*) [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
/-- Alice's Z-bit CQ state, with the arbitrary retained quantum register unchanged. -/
def aliceZCQState (Ψ : DensityOp (Signal × E)) : CQState Bit E :=
  (singleRoundCQState E Ψ).coarsen Prod.fst

omit [DecidableEq E] in
/-- Coarsening the complete signal measurement preserves total probability one. -/
lemma aliceZCQState_weight_eq_one (Ψ : DensityOp (Signal × E)) :
    ∑ z : Bit, ((aliceZCQState E Ψ).stateMap z).trace = 1 := by
  rw [← CQState.quantumMarginal_trace, aliceZCQState,
    CQState.quantumMarginal_coarsen, CQState.quantumMarginal_trace]
  exact singleRoundConditioned_weight_sum E Ψ

/-- Coarsening the pair measurement is Alice's projector sandwich followed by a partial trace. -/
theorem aliceZCQState_origin (Ψ : DensityOp (Signal × E)) (z : Bit) :
    ((aliceZCQState E Ψ).stateMap z).toOp =
      partialTraceLeft ((aliceZProj z ⊗ₖ (1 : Op E)) * Ψ.toOp *
        (aliceZProj z ⊗ₖ (1 : Op E))) := by
  have hP : aliceZProj z ⊗ₖ (1 : Op E) =
      diagonal (fun p : Signal × E => if p.1.1 = z then (1 : ℂ) else 0) := by
    rw [aliceZProj, ← diagonal_one, diagonal_kronecker_diagonal]
    simp
  rw [hP]
  ext a b
  change (∑ x : Signal, if x.1 = z then
    ((singleRoundCQState E Ψ).stateMap x).toOp else 0) a b = _
  simp only [Matrix.sum_apply, partialTraceLeft, diagonal_mul, mul_diagonal, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x.1 = z <;> simp [hx, singleRoundCQState_stateMap_toOp_apply]

end QKD.BB84.FiniteKey
