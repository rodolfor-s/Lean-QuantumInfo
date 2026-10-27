import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology

/-! # Basic -/


noncomputable section

namespace Quantum.DeFinetti

open Quantum.Operators MeasureTheory

variable {X : Type*} [Fintype X]

/-- A probability distribution over density operators. -/
structure DensityMeasure (X : Type*) [Fintype X] where
  /-- The measure on the Borel state space. -/
  measure : Measure (DensityOp X)
  /-- Total mass is one. -/
  isProbability : IsProbabilityMeasure measure

/-- The entrywise integral of tensor powers of a single-site density operator. -/
def integralTensorPower (k : ℕ) (μ : DensityMeasure X) : Op (Fin k → X) :=
  Matrix.of fun x y => ∫ ρ, (ρ.tensorPow k).toOp x y ∂μ.measure

/-- Split a function into its final `k` sites and its initial `n - k` sites. -/
def splitLast {n k : ℕ} (hk : k ≤ n) :
    (Fin n → X) ≃ (Fin k → X) × (Fin (n - k) → X) where
  toFun v := (fun i => v ⟨n - k + i, by omega⟩, fun i => v ⟨i, by omega⟩)
  invFun v i := if hi : (i : ℕ) < n - k then v.2 ⟨i, hi⟩
    else v.1 ⟨i - (n - k), by omega⟩
  left_inv v := by
    funext i
    dsimp
    split_ifs with hi
    · rfl
    · congr 1
      apply Fin.ext
      change n - k + (↑i - (n - k)) = ↑i
      omega
  right_inv v := by
    apply Prod.ext <;> funext i
    · dsimp
      rw [dite_eq_right (by omega)]
      apply congrArg v.1
      apply Fin.ext
      change n - k + ↑i - (n - k) = ↑i
      omega
    · dsimp
      rw [dite_eq_left (by omega)]

/-- Keep the final `k` sites of a density operator. -/
def partialTraceLast {n k : ℕ} (hk : k ≤ n) (ρ : DensityOp (Fin n → X)) :
    DensityOp (Fin k → X) := (ρ.reindex (splitLast hk)).partialTraceRight

end Quantum.DeFinetti
