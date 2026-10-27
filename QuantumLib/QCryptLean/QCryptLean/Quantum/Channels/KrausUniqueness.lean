import QCryptLean.Math.LinearAlgebra.Matrix.UnitaryGram
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus

/-! # Kraus Uniqueness -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators

variable {X Y E F I J : Type*} [Fintype X] [Fintype Y] [Fintype E] [Fintype F]
  [Fintype I] [Fintype J]

/-- Stack the Choi vectors of all environment slices of a Kraus family. -/
def stackedKrausChoiVec (K : I → Matrix (Y × E) X ℂ) : Matrix (X × Y) (E × I) ℂ :=
  fun p q => K q.2 (p.2, q.1) p.1

omit [Fintype Y] in
/-- The row Gram is exactly the Choi matrix of the retained output marginal. -/
theorem stackedKrausChoiVec_gram_eq_choi_marginal (K : I → Matrix (Y × E) X ℂ) :
    stackedKrausChoiVec K * (stackedKrausChoiVec K)ᴴ =
      choiMatrix ((partialTraceRightLinearMap (S := ℂ)).comp (krausMap K)) := by
  classical
  ext p q
  simp only [mul_apply, conjTranspose_apply, stackedKrausChoiVec, Fintype.sum_prod_type,
    choiMatrix, LinearMap.comp_apply, partialTraceRightLinearMap_apply,
    partialTraceRight_apply, krausMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  simp [single_apply, ite_and]

omit [Fintype Y] in
/-- Marginal equality gives equality of stacked row Grams. -/
theorem gram_stackedKrausChoiVec_eq_of_partialTrace_eq
    (K : I → Matrix (Y × E) X ℂ) (L : J → Matrix (Y × F) X ℂ)
    (h : ∀ A, partialTraceRight (krausMap K A) = partialTraceRight (krausMap L A)) :
    stackedKrausChoiVec K * (stackedKrausChoiVec K)ᴴ =
      stackedKrausChoiVec L * (stackedKrausChoiVec L)ᴴ := by
  rw [stackedKrausChoiVec_gram_eq_choi_marginal, stackedKrausChoiVec_gram_eq_choi_marginal]
  congr 1
  exact LinearMap.ext h

omit [Fintype Y] in
open scoped Classical in
/-- A larger combined register admits an isometric intertwiner for equal marginals. -/
theorem kraus_exists_isometry_of_partialTrace_eq [Finite Y]
    (K : I → Matrix (Y × E) X ℂ) (L : J → Matrix (Y × F) X ℂ)
    (h : ∀ A, partialTraceRight (krausMap K A) = partialTraceRight (krausMap L A))
    (hdim : Fintype.card (F × J) ≤ Fintype.card (E × I)) :
    ∃ V : Matrix (E × I) (F × J) ℂ, Vᴴ * V = 1 ∧
      stackedKrausChoiVec K = stackedKrausChoiVec L * Vᴴ := by
  classical
  obtain ⟨W, hW, he⟩ := exists_coisometry_of_rowGram_eq
    (stackedKrausChoiVec L) (stackedKrausChoiVec K)
    (gram_stackedKrausChoiVec_eq_of_partialTrace_eq K L h).symm hdim
  refine ⟨Wᴴ, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose]
    convert hW using 1
    ext p q
    by_cases h : p = q <;> simp [Matrix.one_apply, h]
  · rw [conjTranspose_conjTranspose]
    exact he

open scoped Classical in
/-- Minimal representations have equal combined dimensions, so the isometric conclusion applies. -/
theorem kraus_unique_partial_isometry_of_partialTraceB_eq
    (K : I → Matrix (Y × E) X ℂ) (L : J → Matrix (Y × F) X ℂ)
    (h : ∀ A, partialTraceRight (krausMap K A) = partialTraceRight (krausMap L A))
    (hK : Fintype.card (E × I) =
      (choiMatrix ((partialTraceRightLinearMap (S := ℂ)).comp (krausMap K))).rank)
    (hL : Fintype.card (F × J) =
      (choiMatrix ((partialTraceRightLinearMap (S := ℂ)).comp (krausMap L))).rank) :
    ∃ V : Matrix (E × I) (F × J) ℂ, Vᴴ * V = 1 ∧
      stackedKrausChoiVec K = stackedKrausChoiVec L * Vᴴ := by
  apply kraus_exists_isometry_of_partialTrace_eq K L h
  have he : (partialTraceRightLinearMap (S := ℂ)).comp (krausMap K) =
      (partialTraceRightLinearMap (S := ℂ)).comp (krausMap L) := LinearMap.ext h
  exact le_of_eq (hL.trans (by rw [hK, he]))

end Quantum.Channels
