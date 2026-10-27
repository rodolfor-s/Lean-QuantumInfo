import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementAlgebra
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementBlocks
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementChannel
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementReference
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.VectorBlock
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet

/-! # The overlap bound for a transported conditional-entropy reference -/
noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators Quantum.Channels
open scoped Kronecker ComplexOrder MatrixOrder
open _root_.InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Transport of an identity-times-reference is the overlap-weighted sum of paired blocks. -/
theorem measTransportMap_one_kronecker_eq
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (σ : Op ((A × A) × B)) :
    measTransportMap P Q ((1 : Op A) ⊗ₖ σ) =
      ∑ x, ∑ z, (Complex.normSq ((vec P x).dag * vec Q z : ℂ) : ℂ) •
        (proj P x ⊗ₖ vectorBlock σ ((vec Q z).kronecker (vec Q z)).vec
          ((vec Q z).kronecker (vec Q z)).vec) := by
  let T : Op (((A × A) × A) × B) →ₗ[ℂ] Op (A × B) :=
    partialTraceRightLinearMap.comp
      (reindexLinearEquiv ℂ ℂ measTraceEquiv measTraceEquiv).toLinearMap
  let N := reindex measEntropyEquiv.symm measEntropyEquiv.symm ((1 : Op A) ⊗ₖ σ)
  let W := partialIsometryW P Q ⊗ₖ (1 : Op B)
  have hmap : measTransportMap P Q ((1 : Op A) ⊗ₖ σ) = T (W * N * Wᴴ) := by
    rw [measTransportMap_apply]
    change partialTraceRight _ = partialTraceRight
      (reindex measTraceEquiv measTraceEquiv (W * N * Wᴴ))
    congr 1
    have hN : reindex measEntropyEquiv measEntropyEquiv N = ((1 : Op A) ⊗ₖ σ) := by
      ext i j
      simp [N, reindex_apply]
    rw [← hN]
    change reindex measTraceEquiv measEntropyEquiv W *
      reindex measEntropyEquiv measEntropyEquiv N *
      (reindex measTraceEquiv measEntropyEquiv W)ᴴ = _
    simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  let K (x z : A) := vecMulVec (dilationKet P x).vec (star (dilationKet Q z).vec) ⊗ₖ
    (1 : Op B)
  have hW : W = ∑ x, ∑ z, ((vec P x).dag * vec Q z : ℂ) • K x z := by
    dsimp [W]
    rw [partialIsometryW_eq_sum_vecMulVec]
    ext p q
    simp only [Matrix.sum_apply, kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_mul, K]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    ring
  have hWd : Wᴴ = ∑ x, ∑ z, star ((vec P x).dag * vec Q z : ℂ) • (K x z)ᴴ := by
    rw [hW, conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [conjTranspose_sum, conjTranspose_smul]
  have hterm (x z y w : A) : T (K x z * N * (K y w)ᴴ) =
      (if x = y then (1 : ℂ) else 0) • (if z = w then (1 : ℂ) else 0) •
        (vecMulVec (vec P x).vec (star (vec P y).vec) ⊗ₖ
          vectorBlock σ ((vec Q z).kronecker (vec Q z)).vec
            ((vec Q w).kronecker (vec Q w)).vec) := by
    dsimp only [K]
    rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_vecMulVec, star_star,
      vecMulVec_kronecker_sandwich]
    change partialTraceRight (reindex measTraceEquiv measTraceEquiv _) = _
    rw [partialTraceRight_reindex_dilationKet]
    dsimp only [N]
    rw [vectorBlock_entropyReference, kronecker_smul]
  rw [hmap, hWd, hW]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul]
  have hcc (c : ℂ) : star c * c = (Complex.normSq c : ℂ) := by
    rw [mul_comm]
    exact Complex.mul_conj c
  simp only [hterm, ite_smul, one_smul, zero_smul, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_smul, hcc]
  rfl

/-- Every transported reference is bounded by the overlap constant times its marginal. -/
theorem measTransportMap_one_kronecker_le [Nonempty A]
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (σ : Op ((A × A) × B)) (hσ : σ.PosSemidef) :
    measTransportMap P Q ((1 : Op A) ⊗ₖ σ) ≤
      (overlapConst P Q : ℂ) • ((1 : Op A) ⊗ₖ partialTraceLeft σ) := by
  let C (z : A) := vectorBlock σ ((vec Q z).kronecker (vec Q z)).vec
    ((vec Q z).kronecker (vec Q z)).vec
  have hc : (0 : ℂ) ≤ (overlapConst P Q : ℂ) :=
    Complex.zero_le_real.mpr (overlapConst_nonneg P Q)
  have hd (x : A) : ∑ z, (Complex.normSq ((vec P x).dag * vec Q z : ℂ) : ℂ) • C z ≤
      (overlapConst P Q : ℂ) • partialTraceLeft σ := by
    calc
      _ ≤ ∑ z, (overlapConst P Q : ℂ) • C z := by
        apply Finset.sum_le_sum
        intro z _
        apply smul_le_smul_of_nonneg_right
          (show (Complex.normSq ((vec P x).dag * vec Q z : ℂ) : ℂ) ≤
              (overlapConst P Q : ℂ) from by
            exact_mod_cast normSq_overlap_le_overlapConst P Q x z)
        exact (hσ.vectorBlock _).nonneg
      _ ≤ _ := by
        rw [← Finset.smul_sum]
        exact smul_le_smul_of_nonneg_left (sum_vectorBlock_pair_le Q σ hσ) hc
  rw [measTransportMap_one_kronecker_eq]
  have he : (overlapConst P Q : ℂ) • ((1 : Op A) ⊗ₖ partialTraceLeft σ) =
      ∑ x, proj P x ⊗ₖ ((overlapConst P Q : ℂ) • partialTraceLeft σ) := by
    rw [← kronecker_smul, ← sum_proj P]
    exact LinearMap.map_sum₂ (kroneckerBilinear (R := ℂ) (α := ℂ)) _ _ _
  rw [he]
  apply Finset.sum_le_sum
  intro x _
  have hl : (∑ z, (Complex.normSq ((vec P x).dag * vec Q z : ℂ) : ℂ) •
      (proj P x ⊗ₖ C z)) = proj P x ⊗ₖ
        (∑ z, (Complex.normSq ((vec P x).dag * vec Q z : ℂ) : ℂ) • C z) := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.smul_apply, kroneckerMap_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [hl, Matrix.le_iff]
  have h := ((vec P x).posSemidef_projector).kronecker (Matrix.le_iff.mp (hd x))
  convert h using 1
  ext p q
  exact (mul_sub _ _ _).symm

end InfoTheory.SmoothMinEntropy
