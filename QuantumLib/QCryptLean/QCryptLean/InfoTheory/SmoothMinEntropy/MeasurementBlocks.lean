import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementAlgebra
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.VectorBlock
import QCryptLean.Math.LinearAlgebra.PartialTrace.Weighted
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet

/-! # The vector blocks of a coherent measurement reference -/
noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators
open scoped Kronecker ComplexOrder MatrixOrder
variable {A B : Type*} [Fintype A]
open _root_.InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis

/-- The diagonal paired-basis blocks sum below the full marginal. -/
theorem sum_vectorBlock_pair_le [Finite B] (Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (σ : Op ((A × A) × B)) (hσ : σ.PosSemidef) :
    ∑ z, vectorBlock σ ((vec Q z).kronecker (vec Q z)).vec
      ((vec Q z).kronecker (vec Q z)).vec ≤ partialTraceLeft σ := by
  classical
  let := Fintype.ofFinite B
  let V : Matrix (A × A) A ℂ := fun p z => (Q z) p.1 * (Q z) p.2
  have hV : Vᴴ * V = 1 := by
    ext x z
    change (∑ p : A × A, star ((Q x) p.1 * (Q x) p.2) *
      ((Q z) p.1 * (Q z) p.2)) = if x = z then 1 else 0
    have hi := inner_vec Q x z
    change (∑ i, star ((Q x) i) * (Q z) i) = _ at hi
    calc
      _ = (∑ i, star ((Q x) i) * (Q z) i) ^ 2 := by
        simp only [Fintype.sum_prod_type, star_mul', pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hi]; split_ifs <;> norm_num
  have hp : IsStarProjection (V * Vᴴ) := by
    refine ⟨?_, isHermitian_mul_conjTranspose_self _⟩
    change (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]
  have he : ∑ z, vectorBlock σ ((vec Q z).kronecker (vec Q z)).vec
      ((vec Q z).kronecker (vec Q z)).vec =
      partialTraceLeft (σ * ((V * Vᴴ) ⊗ₖ (1 : Op B))) := by
    simp_rw [vectorBlock_eq_partialTraceLeft]
    rw [← partialTraceLeft_sum, ← Matrix.mul_sum]
    congr 2
    have hVV : V * Vᴴ = ∑ z, vecMulVec
        ((vec Q z).kronecker (vec Q z)).vec (star ((vec Q z).kronecker (vec Q z)).vec) := by
      ext p q
      rw [Matrix.sum_apply]
      rfl
    rw [hVV]
    exact (LinearMap.map_sum₂ (kroneckerBilinear (R := ℂ) (α := ℂ)) _ _ _).symm
  rw [he, Matrix.le_iff]
  have hh := hσ.partialTraceLeft_mul_kronecker
    (Matrix.nonneg_iff_posSemidef.mp hp.one_sub.nonneg)
  have hd : (1 - V * Vᴴ) ⊗ₖ (1 : Op B) = 1 - (V * Vᴴ) ⊗ₖ (1 : Op B) := by
    conv_rhs => lhs; rw [← one_kronecker_one (α := ℂ)]
    ext p q
    exact sub_mul _ _ _
  rwa [hd, Matrix.mul_sub, Matrix.mul_one, partialTraceLeft_sub] at hh

/-- Expand the partial isometry between the coherent measurement ranges in rank-one terms. -/
theorem partialIsometryW_eq_sum_vecMulVec
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) :
    partialIsometryW P Q = ∑ x, ∑ z, ((vec P x).dag * vec Q z : ℂ) •
      vecMulVec (dilationKet P x).vec (star (dilationKet Q z).vec) := by
  ext i j
  simp only [partialIsometryW, Matrix.mul_apply, dilationIso, Matrix.conjTranspose_apply,
    star_sum, star_mul', star_star, Finset.sum_mul_sum, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  change (∑ k, _ * _ * (_ * _)) =
    (∑ k, star ((vec P x).vec k) * (vec Q z).vec k) * _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Discarding the two repeated basis copies eliminates off-diagonal outcomes. -/
theorem partialTraceRight_reindex_dilationKet [DecidableEq A]
    (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (x y : A) (M : Op B) :
    partialTraceRight (reindex measTraceEquiv measTraceEquiv
      (vecMulVec (dilationKet P x).vec (star (dilationKet P y).vec) ⊗ₖ M)) =
      (if x = y then (1 : ℂ) else 0) •
        (vecMulVec (vec P x).vec (star (vec P y).vec) ⊗ₖ M) := by
  have hi := inner_vec P y x
  change (∑ i, star ((P y) i) * (P x) i) = _ at hi
  ext p q
  change (∑ r : A × A, (((P x) p.1 * (P x) r.1) * (P x) r.2) *
    star (((P y) q.1 * (P y) r.1) * (P y) r.2) * M p.2 q.2) = _
  have he : (∑ r : A × A, (((P x) p.1 * (P x) r.1) * (P x) r.2) *
      star (((P y) q.1 * (P y) r.1) * (P y) r.2) * M p.2 q.2) =
      (∑ i, star ((P y) i) * (P x) i) ^ 2 * ((P x) p.1 * star ((P y) q.1) * M p.2 q.2) := by
    simp only [Fintype.sum_prod_type, star_mul', pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, hi]
  change (if y = x then (1 : ℂ) else 0) ^ 2 * _ = (if x = y then (1 : ℂ) else 0) * _
  by_cases h : x = y
  · subst y
    simp [RankOneProjectiveBasis.vec, vecMulVec_apply]
  · simp [h, Ne.symm h]

end InfoTheory.SmoothMinEntropy
