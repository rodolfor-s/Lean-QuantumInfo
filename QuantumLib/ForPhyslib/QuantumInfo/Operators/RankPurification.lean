import QuantumLib.ForMathlib.LinearAlgebra.Matrix.IdempotentTrace
import QuantumLib.ForMathlib.LinearAlgebra.Matrix.RankFactor
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Operators.BraKet
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Purification
import QuantumLib.ForPhyslib.QuantumInfo.Operators.StateOperations

/-! # Pure vectors and rank-bounded environments on finite registers -/

noncomputable section
namespace Quantum.Operators
open Matrix
variable {X R : Type*} [Fintype X] [Fintype R]

/-- Every pure density operator is the projector of a normalized vector. -/
theorem DensityOp.IsPure.exists_normKet (ρ : DensityOp X) (hρ : ρ.IsPure) :
    ∃ v : NormKet X, v.toDensityOp = ρ := by
  classical
  have ht : ρ.toOp.trace = (ρ.toOp.rank : ℂ) :=
    Matrix.trace_eq_rank_of_mul_self_eq _ hρ
  have hr : ρ.toOp.rank = 1 := by
    rw [ρ.trace_one] at ht
    exact_mod_cast ht.symm
  obtain ⟨V, hV⟩ := ρ.posSemidef.exists_factor_of_rank_le (R := Unit) (by simp [hr])
  let v : Ket X := ⟨fun i => V i ()⟩
  have hp : v.projector = ρ.toOp := by
    rw [← hV]
    ext i j
    change V i () * star (V j ()) = (V * Vᴴ) i j
    simp [Matrix.mul_apply, conjTranspose_apply]
  have hn : v.IsNormalized := by rw [Ket.IsNormalized, ← Ket.trace_projector, hp, ρ.trace_one]
  exact ⟨⟨v, hn⟩, DensityOp.ext hp⟩

end Quantum.Operators
