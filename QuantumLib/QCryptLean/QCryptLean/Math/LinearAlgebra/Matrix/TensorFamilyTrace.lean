import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic

/-! # Partial traces of tensor families without enumerating the sites -/
namespace Matrix

/-- Regrouping a tensor family and discarding its second registers acts at each site. -/
theorem partialTraceRight_reindex_piTensorProduct
    {I X Y R : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [CommSemiring R]
    (A : I → Matrix (X × Y) (X × Y) R) :
    partialTraceRight (reindex (Equiv.arrowProdEquivProdArrow I (fun _ => X) (fun _ => Y))
      (Equiv.arrowProdEquivProdArrow I (fun _ => X) (fun _ => Y)) (piTensorProduct A)) =
        piTensorProduct (fun i => partialTraceRight (A i)) := by
  classical
  ext x y
  exact (Fintype.prod_sum (fun i r => A i (x i, r) (y i, r))).symm

end Matrix
