import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # The native linear real-minus-uniform public-seed hash operation -/
noncomputable section
namespace InfoTheory.QuantumLHL.SeedKey
open Matrix Quantum.Operators Quantum.Channels
open InfoTheory.SmoothMinEntropy
variable {S C Z X Y R : Type*} [Fintype S] [Fintype C] [Fintype Z]
  [DecidableEq S] [DecidableEq Z]

/-- Hash an operator-valued instrument and subtract its seed-key-uniform target. -/
def hashDifferenceOperation (H : HashFamily S C Z) (L : C → Operation X Y) :
    Operation X (Y × (S × Z)) where
  toFun A := Matrix.blockDiagonal fun sz =>
    ((1 / Fintype.card S : ℝ) : ℂ) • (∑ c, if H.hash sz.1 c = sz.2 then L c A else 0) -
      (((Fintype.card (S × Z) : ℝ)⁻¹) : ℂ) • ∑ c, L c A
  map_add' A B := by
    have hi (sz : S × Z) (c : C) :
        (if H.hash sz.1 c = sz.2 then L c (A + B) else 0) =
          (if H.hash sz.1 c = sz.2 then L c A else 0) +
            (if H.hash sz.1 c = sz.2 then L c B else 0) := by
      split_ifs <;> simp only [map_add, add_zero]
    ext ⟨y, sz⟩ ⟨y', sz'⟩
    simp only [Matrix.blockDiagonal_apply, Matrix.add_apply]
    split_ifs
    · simp only [hi]
      simp only [map_add, Finset.sum_add_distrib, smul_add,
        Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
      ring
    · simp
  map_smul' a A := by
    have hi (sz : S × Z) (c : C) :
        (if H.hash sz.1 c = sz.2 then L c (a • A) else 0) =
          a • (if H.hash sz.1 c = sz.2 then L c A else 0) := by
      split_ifs <;> simp only [map_smul, smul_zero]
    ext ⟨y, sz⟩ ⟨y', sz'⟩
    simp only [Matrix.blockDiagonal_apply, Matrix.smul_apply]
    split_ifs
    · simp only [hi]
      simp only [map_smul, ← Finset.smul_sum, smul_smul,
        Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp

/-- The linear hash difference has exactly the CQ real-minus-uniform interpretation. -/
theorem hashDifferenceOperation_apply [Fintype Y] [Nonempty S] [Nonempty Z]
    (H : HashFamily S C Z) (L : C → Operation X Y) (A : Op X) (ρ : CQState C Y)
    (hρ : ∀ c, (ρ.stateMap c).toOp = L c A) :
    hashDifferenceOperation H L A = (output H ρ).toJointDensity.toOp -
      (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp := by
  ext ⟨y, sz⟩ ⟨y', sz'⟩
  simp only [hashDifferenceOperation, LinearMap.coe_mk, AddHom.coe_mk,
    CQState.toJointDensity, CQState.toJointOp, output, weightedOp, uniformCQState,
    CQState.ofBlocks, CQState.quantumMarginal, Matrix.blockDiagonal_apply, Matrix.sub_apply,
    hρ]
  split_ifs <;> simp

/-- Regroup a quantum reference before the seed-key register. -/
def hashReferenceEquiv : ((Y × (S × Z)) × R) ≃ ((Y × R) × (S × Z)) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)

/-- Reference amplification commutes with the linear public-seed hash difference. -/
theorem hashDifferenceOperation_mapTensorId
    (H : HashFamily S C Z) (L : C → Operation X Y) (A : Op (X × R)) :
    hashDifferenceOperation H (fun c => mapTensorId (L c) R) A =
      Matrix.reindex (hashReferenceEquiv (Y := Y) (R := R) (S := S) (Z := Z))
        hashReferenceEquiv (mapTensorId (hashDifferenceOperation H L) R A) := by
  ext ⟨⟨y, r⟩, sz⟩ ⟨⟨y', r'⟩, sz'⟩
  let B : Op X := fun i j => A (i, r) (j, r')
  change (Matrix.blockDiagonal (fun sz =>
    ((1 / Fintype.card S : ℝ) : ℂ) •
      (∑ c, if H.hash sz.1 c = sz.2 then mapTensorId (L c) R A else 0) -
        (((Fintype.card (S × Z) : ℝ)⁻¹) : ℂ) • ∑ c, mapTensorId (L c) R A))
      ((y, r), sz) ((y', r'), sz') =
    (Matrix.blockDiagonal (fun sz =>
      ((1 / Fintype.card S : ℝ) : ℂ) •
        (∑ c, if H.hash sz.1 c = sz.2 then L c B else 0) -
          (((Fintype.card (S × Z) : ℝ)⁻¹) : ℂ) • ∑ c, L c B)) (y, sz) (y', sz')
  simp only [Matrix.blockDiagonal_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply]
  split_ifs
  · congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> rfl
  · rfl


/-- Relabelling the quantum output relabels the complete real-minus-uniform hash operator. -/
theorem hashDifference_reindex [Fintype Y] [Nonempty S] [Nonempty Z]
    {Y' : Type*} [Fintype Y'] (e : Y ≃ Y') (H : HashFamily S C Z) (ρ : CQState C Y) :
    (output H (ρ.reindex e)).toJointDensity.toOp -
      (uniformCQState (C := S × Z) (ρ.reindex e).quantumMarginal).toJointDensity.toOp =
        Matrix.reindex (e.prodCongr (Equiv.refl (S × Z))) (e.prodCongr (Equiv.refl (S × Z)))
          ((output H ρ).toJointDensity.toOp -
            (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp) := by
  ext ⟨y, sz⟩ ⟨y', sz'⟩
  simp only [CQState.toJointDensity, CQState.toJointOp, output, weightedOp, uniformCQState,
    CQState.ofBlocks, CQState.quantumMarginal, CQState.reindex, SubDensityOp.reindex,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_symm, Equiv.refl_apply,
    Matrix.blockDiagonal_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply]
  split_ifs
  · congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> rfl
  · rfl

end InfoTheory.QuantumLHL.SeedKey
