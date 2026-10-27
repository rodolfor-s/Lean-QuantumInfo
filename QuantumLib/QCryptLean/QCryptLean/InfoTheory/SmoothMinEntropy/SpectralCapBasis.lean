import Mathlib.Data.Fin.Tuple.Sort
import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.Math.SpectralTheory.MatrixCFC
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Projector

/-! # Sorted reference projectors on the original quantum register

Only the spectral labels use a finite ordered enumeration. The operators and
basis vectors retain their original register type throughout.
-/
noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder

namespace RankOneProjectiveBasis
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Two basis projectors multiply to the first projector exactly when the labels agree. -/
theorem proj_mul (P : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (i j : Q) :
    proj P i * proj P j = if i = j then proj P i else 0 := by
  have hi := inner_vec P i j
  change star (vec P i).vec ⬝ᵥ (vec P j).vec = _ at hi
  change vecMulVec (vec P i).vec (star (vec P i).vec) *
    vecMulVec (vec P j).vec (star (vec P j).vec) = _
  rw [vecMulVec_mul_vecMulVec, hi]
  split_ifs with h
  · subst j
    simp only [one_smul]
    rfl
  · simp

end RankOneProjectiveBasis

namespace SpectralCap
open _root_.InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Ordered eigenvalue labels, with values in the original register's basis index type. -/
def labels (σ : PosSemidefOp Q) : Fin (Fintype.card Q) ≃ Q :=
  (Tuple.sort (fun i => σ.property.isHermitian.eigenvalues ((Fintype.equivFin Q).symm i))).trans
    (Fintype.equivFin Q).symm

/-- The reference eigenvalues in nondecreasing order. -/
def eigenvalue (σ : PosSemidefOp Q) (z : Fin (Fintype.card Q)) : ℝ :=
  σ.property.isHermitian.eigenvalues (labels σ z)

/-- The corresponding rank-one projector, acting on `Q`. -/
def eigenprojector (σ : PosSemidefOp Q) (z : Fin (Fintype.card Q)) : Op Q :=
  proj σ.property.isHermitian.eigenvectorBasis (labels σ z)

/-- The sorted reference eigenvalues are nonnegative. -/
theorem eigenvalue_nonneg (σ : PosSemidefOp Q) (z : Fin (Fintype.card Q)) :
    0 ≤ eigenvalue σ z := σ.property.eigenvalues_nonneg _

/-- The reference label ordering is monotone in the eigenvalue. -/
theorem eigenvalue_monotone (σ : PosSemidefOp Q) : Monotone (eigenvalue σ) := by
  intro i j hij
  exact Tuple.monotone_sort (fun i => σ.property.isHermitian.eigenvalues
    ((Fintype.equivFin Q).symm i)) hij

/-- The sorted eigenprojectors still resolve the identity on `Q`. -/
theorem sum_eigenprojector (σ : PosSemidefOp Q) : ∑ z, eigenprojector σ z = 1 := by
  rw [show (∑ z, eigenprojector σ z) = ∑ q, proj σ.property.isHermitian.eigenvectorBasis q
    from (labels σ).sum_comp _]
  exact sum_proj _

/-- Reference spectral expansion on the original quantum register. -/
theorem sum_eigenvalue_smul_eigenprojector (σ : PosSemidefOp Q) :
    (∑ z, (eigenvalue σ z : ℂ) • eigenprojector σ z) = σ.val := by
  have he := Math.SpectralTheory.conjStarAlgAut_eigenvectorUnitary_diagonal
    σ.property.isHermitian (fun q => (σ.property.isHermitian.eigenvalues q : ℂ))
  have hs := σ.property.isHermitian.spectral_theorem
  simp only [Function.comp_def, RCLike.ofReal_eq_complex_ofReal] at hs
  rw [he] at hs
  calc
    _ = ∑ q, (σ.property.isHermitian.eigenvalues q : ℂ) •
        proj σ.property.isHermitian.eigenvectorBasis q := (labels σ).sum_comp _
    _ = σ.val := hs.symm

/-- The cumulative spectral projector retaining all eigenvalues from a label onwards. -/
def cumulativeProjector (σ : PosSemidefOp Q) (z : Fin (Fintype.card Q)) : Op Q :=
  ∑ j ∈ Finset.univ.filter (fun j => z ≤ j), eigenprojector σ j

/-- Each cumulative reference projector is an orthogonal projection. -/
theorem cumulativeProjector_isOrthogonalProjector
    (σ : PosSemidefOp Q) (z : Fin (Fintype.card Q)) :
    IsOrthogonalProjector (cumulativeProjector σ z) := by
  refine ⟨?_, ?_⟩
  · unfold cumulativeProjector
    rw [IsHermitian, conjTranspose_sum]
    exact Finset.sum_congr rfl fun j _ => (Ket.posSemidef_projector _).isHermitian.eq
  · unfold cumulativeProjector
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Matrix.mul_sum]
    have hh (b : Fin (Fintype.card Q)) : eigenprojector σ a * eigenprojector σ b =
        if a = b then eigenprojector σ a else 0 := by
      simpa only [eigenprojector, EmbeddingLike.apply_eq_iff_eq] using
        proj_mul σ.property.isHermitian.eigenvectorBasis (labels σ a) (labels σ b)
    simp_rw [hh]
    simp only [Finset.sum_ite_eq, ha, ite_true]

end SpectralCap
end InfoTheory.SmoothMinEntropy
