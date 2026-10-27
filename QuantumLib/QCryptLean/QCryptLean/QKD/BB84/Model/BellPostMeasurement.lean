import QCryptLean.QKD.BB84.Model.BellMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.BellMixture

/-! # Bell Post Measurement -/


noncomputable section

namespace QKD.BB84.Model

open Quantum.Operators Quantum.Symmetry Measurement Matrix

/-- Bell measurement with the output pair recording `(phase, bit)`. -/
def bellBasisRotation : Op Signal :=
  reindex (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm
    (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)
    bellSinglePairRotation

/-- The Bell change of basis preserves every inner product. -/
theorem conjTranspose_mul_bellBasisRotation : bellBasisRotationᴴ * bellBasisRotation = 1 := by
  simp only [bellBasisRotation, reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  exact (congrArg (fun A : Op (Bool × Bool) =>
    A.submatrix (finTwoEquiv.prodCongr finTwoEquiv) (finTwoEquiv.prodCongr finTwoEquiv))
      bellSinglePairRotation_conjTranspose_mul).trans (submatrix_one_equiv _)

end QKD.BB84.Model
