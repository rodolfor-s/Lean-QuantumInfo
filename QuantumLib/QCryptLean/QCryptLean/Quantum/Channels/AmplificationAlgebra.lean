import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Marginal and regrouping identities for native amplification -/
namespace Quantum.Channels
open Matrix Quantum.Operators
variable {X Y R S : Type*}

/-- Discarding the full reference commutes with an amplified linear map. -/
theorem partialTraceRight_mapTensorId [Fintype R] (Φ : Operation X Y) (A : Op (X × R)) :
    Matrix.partialTraceRight (mapTensorId Φ R A) = Φ (Matrix.partialTraceRight A) := by
  have he : (∑ r, Matrix.of fun i j => A (i, r) (j, r)) =
      Matrix.partialTraceRight A := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.of_apply, Matrix.partialTraceRight]
  have h := (map_sum Φ (fun r => Matrix.of fun i j => A (i, r) (j, r)) Finset.univ).symm
  have h' := h.trans (congrArg Φ he)
  ext x y
  refine Eq.trans ?_ (congrArg (fun M : Op Y => M x y) h')
  simp only [Matrix.sum_apply]
  rfl

/-- Discarding the last of two reference factors commutes with amplification. -/
theorem partialTraceRight_mapTensorId_assoc [Fintype S] (Φ : Operation X Y)
    (A : Op ((X × R) × S)) :
    Matrix.partialTraceRight (Matrix.reindex (Equiv.prodAssoc Y R S).symm
      (Equiv.prodAssoc Y R S).symm
      (mapTensorId Φ (R × S) (Matrix.reindex (Equiv.prodAssoc X R S)
        (Equiv.prodAssoc X R S) A))) =
      mapTensorId Φ R (Matrix.partialTraceRight A) := by
  ext ⟨x, r⟩ ⟨y, s⟩
  have he : (∑ t, Matrix.of fun i j => A ((i, r), t) ((j, s), t)) =
      Matrix.of (fun i j => Matrix.partialTraceRight A (i, r) (j, s)) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.of_apply, Matrix.partialTraceRight]
  have h := (map_sum Φ (fun t => Matrix.of fun i j => A ((i, r), t) ((j, s), t))
    Finset.univ).symm
  have h' := h.trans (congrArg Φ he)
  refine Eq.trans ?_ (congrArg (fun M : Op Y => M x y) h')
  simp only [Matrix.sum_apply]
  rfl

/-- Amplification applies the operation to each pair of reference coordinates. -/
@[simp] theorem mapTensorId_apply (Φ : Operation X Y) (A : Op (X × R)) (p q : Y × R) :
    mapTensorId Φ R A p q =
      Φ (A.submatrix (fun x => (x, p.2)) (fun x => (x, q.2))) p.1 q.1 := rfl

/-- Every reference block of an amplification is the image of that input block. -/
theorem mapTensorId_submatrix (Φ : Operation X Y) (A : Op (X × R)) (r s : R) :
    (mapTensorId Φ R A).submatrix (fun y => (y, r)) (fun y => (y, s)) =
      Φ (A.submatrix (fun x => (x, r)) (fun x => (x, s))) := rfl

/-- Amplifying the identity operation gives the identity. -/
@[simp] theorem mapTensorId_id :
    mapTensorId (LinearMap.id : Operation X X) R = LinearMap.id := rfl

/-- Successive reference extensions agree after reassociating the reference factors. -/
theorem mapTensorId_assoc (Φ : Operation X Y) (A : Op ((X × R) × S)) :
    mapTensorId (mapTensorId Φ R) S A =
      Matrix.reindex (Equiv.prodAssoc Y R S).symm (Equiv.prodAssoc Y R S).symm
        (mapTensorId Φ (R × S)
          (Matrix.reindex (Equiv.prodAssoc X R S) (Equiv.prodAssoc X R S) A)) := rfl

/-- Amplification preserves adjoint preservation. -/
theorem mapTensorId_conjTranspose (Φ : Operation X Y)
    (hΦ : ∀ A, Φ Aᴴ = (Φ A)ᴴ) (A : Op (X × R)) :
    mapTensorId Φ R Aᴴ = (mapTensorId Φ R A)ᴴ := by
  ext p q
  rw [mapTensorId_apply, Matrix.conjTranspose_apply, mapTensorId_apply,
    ← Matrix.conjTranspose_submatrix, hΦ, Matrix.conjTranspose_apply]

/-- Trace preservation holds separately in each diagonal reference block. -/
theorem mapTensorId_trace_block [Fintype X] [Fintype Y]
    (Φ : Operation X Y) (hΦ : IsTracePreserving Φ) (A : Op (X × R)) (r : R) :
    ∑ y, mapTensorId Φ R A (y, r) (y, r) = ∑ x, A (x, r) (x, r) :=
  hΦ (A.submatrix (fun x => (x, r)) (fun x => (x, r)))

/-- Amplification commutes with simultaneous system and reference relabelling. -/
theorem mapTensorId_reindex {X' Y' R' : Type*}
    (e : X ≃ X') (f : Y ≃ Y') (g : R ≃ R') (Φ : Operation X Y) (A : Op (X × R)) :
    mapTensorId ((Matrix.reindexLinearEquiv ℂ ℂ f f).toLinearMap.comp
      (Φ.comp (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap)) R'
      (Matrix.reindex (e.prodCongr g) (e.prodCongr g) A) =
        Matrix.reindex (f.prodCongr g) (f.prodCongr g) (mapTensorId Φ R A) := by
  ext p q
  change Φ (fun i j => A (e.symm (e i), g.symm p.2) (e.symm (e j), g.symm q.2))
      (f.symm p.1) (f.symm q.1) =
    Φ (fun i j => A (i, g.symm p.2) (j, g.symm q.2)) (f.symm p.1) (f.symm q.1)
  simp only [Equiv.symm_apply_apply]

/-- Amplification commutes with scalar multiplication of operations. -/
theorem mapTensorId_smul (c : ℂ) (Φ : Operation X Y) :
    mapTensorId (c • Φ) R = c • mapTensorId Φ R := rfl

/-- Amplification commutes with finite sums of operations. -/
theorem mapTensorId_sum {I : Type*} (s : Finset I) (Φ : I → Operation X Y) :
    mapTensorId (∑ i ∈ s, Φ i) R = ∑ i ∈ s, mapTensorId (Φ i) R := by
  ext A p q
  simp only [mapTensorId_apply, LinearMap.sum_apply, Matrix.sum_apply]

/-- A trivial reference is precisely structural relabelling by the product equivalence. -/
theorem mapTensorId_prodUnique [Unique R] (Φ : Operation X Y) (A : Op X) :
    mapTensorId Φ R (Matrix.reindex (Equiv.prodUnique X R).symm
      (Equiv.prodUnique X R).symm A) =
    Matrix.reindex (Equiv.prodUnique Y R).symm (Equiv.prodUnique Y R).symm (Φ A) := rfl

open scoped Kronecker in
/-- An amplified operation acts only on the first Kronecker factor. -/
theorem mapTensorId_kronecker (Φ : Operation X Y) (A : Op X) (B : Op R) :
    mapTensorId Φ R (A ⊗ₖ B) = Φ A ⊗ₖ B := by
  ext p q
  have h : (A ⊗ₖ B).submatrix (fun x => (x, p.2)) (fun x => (x, q.2)) =
      B p.2 q.2 • A := by
    ext i j
    simp [Matrix.kroneckerMap_apply, mul_comm]
  rw [mapTensorId_apply, h, map_smul]
  simp [Matrix.kroneckerMap_apply, mul_comm]

end Quantum.Channels
