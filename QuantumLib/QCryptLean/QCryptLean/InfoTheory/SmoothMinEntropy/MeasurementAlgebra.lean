import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.Math.LinearAlgebra.Matrix.ProjectionOrder
import QCryptLean.Quantum.Operators.BraKet

/-! # Measurement Algebra -/


noncomputable section
namespace InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Kronecker
variable {A : Type*} [Fintype A]

/-- Each squared overlap is bounded by the largest squared overlap. -/
theorem normSq_overlap_le_overlapConst [Nonempty A]
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (x z : A) :
    Complex.normSq ((vec P x).dag * vec Q z : ℂ) ≤ overlapConst P Q := by
  classical
  exact Finset.le_sup' (fun p : A × A => Complex.normSq ((vec P p.1).dag * vec Q p.2 : ℂ))
    (Finset.mem_univ (x, z))

/-- The overlap bound is nonnegative. -/
theorem overlapConst_nonneg [Nonempty A]
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) : 0 ≤ overlapConst P Q := by
  let x := Classical.choice ‹Nonempty A›
  exact (Complex.normSq_nonneg _).trans (normSq_overlap_le_overlapConst P Q x x)

/-- Two complete orthonormal bases on a nonempty register have a positive overlap. -/
theorem overlapConst_pos [Nonempty A]
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) : 0 < overlapConst P Q := by
  classical
  let z := Classical.choice ‹Nonempty A›
  by_contra hn
  have hn : overlapConst P Q ≤ 0 := le_of_not_gt hn
  have hz : ∀ x, (vec P x).dag * vec Q z = (0 : ℂ) := by
    intro x
    exact Complex.normSq_eq_zero.mp (le_antisymm
      ((normSq_overlap_le_overlapConst P Q x z).trans hn) (Complex.normSq_nonneg _))
  have hzero : P.repr (Q z) = 0 := by
    ext x
    rw [P.repr_apply_apply]
    have hh := hz x
    change (∑ i, star ((P x) i) * (Q z) i) = 0 at hh
    simpa only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, mul_comm,
      PiLp.zero_apply] using hh
  have hq : Q z = 0 := P.repr.injective (by simpa using hzero)
  have hh := Q.orthonormal.norm_eq_one z
  rw [hq, norm_zero] at hh
  exact zero_ne_one hh

variable [DecidableEq A]

omit [DecidableEq A] in
/-- The measurement range is a star projection. -/
theorem isStarProjection_dilationRange
    (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) :
    IsStarProjection (dilationIso P * (dilationIso P)ᴴ) := by
  classical
  constructor
  · change (_ * _) * (_ * _) = _
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dilationIso P)ᴴ,
      dilationIso_isometry, Matrix.one_mul]
  · exact isHermitian_mul_conjTranspose_self _

/-- The complement of the coherent measurement range is positive. -/
theorem dilationCoprojector_posSemidef
    (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) :
    (1 - dilationIso P * (dilationIso P)ᴴ).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (isStarProjection_dilationRange P).one_sub.nonneg

omit [DecidableEq A] in
/-- Pulling back one dilation and applying the other recovers the other dilation. -/
theorem partialIsometryW_mul_dilationIso
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) :
    partialIsometryW P Q * dilationIso Q = dilationIso P := by
  classical
  rw [partialIsometryW, Matrix.mul_assoc, dilationIso_isometry, Matrix.mul_one]

omit [DecidableEq A] in
/-- The partial isometry's initial projection is the input measurement range. -/
theorem partialIsometryW_dagger_mul_self_eq
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) :
    (partialIsometryW P Q)ᴴ * partialIsometryW P Q =
      dilationIso Q * (dilationIso Q)ᴴ := by
  classical
  rw [partialIsometryW, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc (dilationIso P)ᴴ, dilationIso_isometry,
    Matrix.one_mul]

end InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis
