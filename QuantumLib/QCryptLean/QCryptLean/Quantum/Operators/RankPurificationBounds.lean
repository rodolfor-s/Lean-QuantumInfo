import QCryptLean.Math.LinearAlgebra.Matrix.RankFactor
import QCryptLean.Math.LinearAlgebra.Matrix.UnitaryGram
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.RankPurification
import QCryptLean.Quantum.Operators.StateOperations

/-! # Rank Purification Bounds -/


noncomputable section

namespace Quantum.Operators

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

variable {X R : Type*} [Fintype X] [Fintype R]

/-- Any reference large enough for the state's rank admits a pure extension. -/
theorem DensityOp.exists_isPure_partialTraceRight_eq_of_rank_le
    (ρ : DensityOp X) (h : ρ.toOp.rank ≤ Fintype.card R) :
    ∃ ψ : DensityOp (X × R), ψ.IsPure ∧ ψ.partialTraceRight = ρ := by
  classical
  obtain ⟨V, hV⟩ := ρ.posSemidef.exists_factor_of_rank_le h
  let v := Ket.vectorize V
  have hm : Matrix.partialTraceRight v.projector = ρ.toOp :=
    (Ket.partialTraceRight_vectorize V).trans hV
  have hn : v.IsNormalized := by
    rw [Ket.IsNormalized, ← Ket.trace_projector, ← Matrix.trace_partialTraceRight, hm, ρ.trace_one]
  let w : NormKet (X × R) := ⟨v, hn⟩
  exact ⟨w.toDensityOp, w.isPure_toDensityOp, DensityOp.ext hm⟩

end Quantum.Operators
