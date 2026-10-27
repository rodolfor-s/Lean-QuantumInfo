import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.SpectralTheory.MatrixCFC

/-!
# Functional calculus under finite matrix reindexing

The real continuous functional calculus of Hermitian complex matrices commutes
with arbitrary register equivalences. Matrix star order is opened locally only
for positive real powers. No matrix norm instance is installed or exported.
-/

noncomputable section

namespace Matrix

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Real functional calculus commutes with a finite register equivalence. -/
theorem reindex_cfc (e : X ≃ Y) (A : Matrix X X ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    reindex e e (cfc f A) = cfc f (reindex e e A) := by
  let φ : Matrix X X ℂ →⋆ₐ[ℂ] Matrix Y Y ℂ :=
    { (reindexAlgEquiv ℂ ℂ e).toAlgHom with
      map_star' := fun M => (conjTranspose_reindex e e M).symm }
  exact StarAlgHomClass.map_cfc φ f A
    (hf := A.finite_real_spectrum.continuousOn f)
    (hφ := by
      apply continuous_matrix
      intro i j
      change Continuous (fun a : Matrix X X ℂ => a (e.symm i) (e.symm j))
      exact (continuous_apply _).comp (continuous_apply _))
    (ha := hA) (hφa := hA.reindex e)

open scoped ComplexOrder MatrixOrder in
/-- Positive real powers, including support pseudo-inverses, commute with reindexing. -/
theorem reindex_cfcRpow (e : X ≃ Y) (A : Matrix X X ℂ) (hA : A.PosSemidef) (r : ℝ) :
    reindex e e (A ^ r) = (reindex e e A) ^ r := by
  rw [CFC.rpow_eq_cfc_real hA.nonneg,
    CFC.rpow_eq_cfc_real ((posSemidef_reindex_iff e A).mpr hA).nonneg]
  exact reindex_cfc e A hA.isHermitian (fun t => t ^ r)

end Matrix
