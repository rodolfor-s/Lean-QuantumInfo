import Batteries.Tactic.OpenPrivate
import QCryptLean.Math.LinearAlgebra.Matrix.Reindex
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.RankPurification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.BellDickeCore
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.BellCopy
import QCryptLean.Quantum.Symmetry.BellDicke
import QCryptLean.Quantum.Symmetry.BellDoubling
import QCryptLean.Quantum.Symmetry.BellMixture
import QCryptLean.Quantum.Symmetry.BellSpectrum
import QCryptLean.Quantum.Symmetry.Paired

/-! # Bell Doubling Algebra -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped Kronecker ComplexOrder

/-- The full joint Bell mixture is the coherent doubling of the symmetric reference. -/
theorem bellPairedDeFinettiStateOp_eq_conj_symmetricProjector (k : ℕ) :
    bellPairedDeFinettiStateOp k =
      reindex (pairFunctions (Bool × Bool) (Bool × Bool) k)
        (pairFunctions (Bool × Bool) (Bool × Bool) k)
        (bellDoublingIsometryPow k *
          (((k + 3).choose 3 : ℂ)⁻¹ • symmetricProjector (Bool × Bool) k) *
            (bellDoublingIsometryPow k)ᴴ) := by
  classical
  rw [symmetricProjector_eq_bellDicke_resolution]
  simp only [Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul, reindex_sum,
    Matrix.mul_smul, Matrix.smul_mul, reindex_smul, bellPairedDeFinettiStateOp]
  apply Finset.sum_congr rfl
  intro T _
  rw [bellPairedKraus_eq_smul]
  let a : ℝ := ((k + 3).choose 3 : ℝ)⁻¹ * (bellTypeMult k T : ℝ)⁻¹
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : (Real.sqrt a : ℂ) * star (Real.sqrt a : ℂ) =
      ((k + 3).choose 3 : ℂ)⁻¹ * (bellTypeMult k T : ℂ)⁻¹ := by
    rw [show star (Real.sqrt a : ℂ) = (Real.sqrt a : ℂ) from by simp,
      ← Complex.ofReal_mul, Real.mul_self_sqrt ha]
    simp [a]
  have hp : bellDoublingIsometryPow k * (bellDickeKet k T).projector *
      (bellDoublingIsometryPow k)ᴴ =
      vecMulVec (bellDoublingIsometryPow k *ᵥ (bellDickeKet k T).vec)
        (star (bellDoublingIsometryPow k *ᵥ (bellDickeKet k T).vec)) := by
    change bellDoublingIsometryPow k *
      vecMulVec (bellDickeKet k T).vec (star (bellDickeKet k T).vec) *
        (bellDoublingIsometryPow k)ᴴ = _
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  rw [hp]
  ext ⟨p, q⟩ ⟨r, s⟩
  change (((Real.sqrt a : ℂ) * bellTypeProjector k T p q) *
      star ((Real.sqrt a : ℂ) * bellTypeProjector k T r s)) = _
  simp only [Matrix.smul_apply, smul_eq_mul, reindex_apply, submatrix_apply,
    vecMulVec_apply, Pi.star_apply]
  change _ = ((k + 3).choose 3 : ℂ)⁻¹ * ((bellTypeMult k T : ℂ)⁻¹ *
    ((bellDoublingIsometryPow k *ᵥ (bellDickeKet k T).vec) (fun i => (p i, q i)) *
      star ((bellDoublingIsometryPow k *ᵥ (bellDickeKet k T).vec)
        (fun i => (r i, s i)))))
  rw [bellDoubling_dicke_vectorize, bellDoubling_dicke_vectorize, star_mul]
  calc _ = ((Real.sqrt a : ℂ) * star (Real.sqrt a : ℂ)) *
      (bellTypeProjector k T p q * star (bellTypeProjector k T r s)) := by ring
    _ = _ := by rw [hs]; ring

/-- Pure tensor powers lie below the symmetric projector. -/
theorem tensorPow_opLe_symmetricProjector_of_isPure {X : Type*} [Fintype X]
    [DecidableEq X] (k : ℕ) (φ : DensityOp X) (hφ : φ.IsPure) :
    OpLe (φ.tensorPow k).toOp (symmetricProjector X k) := by
  classical
  obtain ⟨v, hv⟩ := DensityOp.IsPure.exists_normKet φ hφ
  let w := Ket.tensorFamily (fun _ : Fin k => v.toKet)
  have hp : (φ.tensorPow k).toOp = w.projector := by
    rw [← hv]
    exact (Ket.projector_tensorFamily _).symm
  have hw : symmetricProjector X k *ᵥ w.vec = w.vec := by
    apply (symmetricProjector_mulVec_eq_iff _).mpr
    intro σ x
    change (∏ i : Fin k, v.vec (x (σ i))) = ∏ i : Fin k, v.vec (x i)
    exact Equiv.prod_comp σ (fun i => v.vec (x i))
  let P := symmetricProjector X k
  let A := (φ.tensorPow k).toOp
  have hPA : P * A = A := by
    change symmetricProjector X k * (φ.tensorPow k).toOp = (φ.tensorPow k).toOp
    rw [hp]
    change symmetricProjector X k * vecMulVec w.vec (star w.vec) = _
    rw [Matrix.mul_vecMulVec, hw]
    rfl
  have hAP : A * P = A := by
    have h := congrArg Matrix.conjTranspose hPA
    rw [conjTranspose_mul] at h
    change (φ.tensorPow k).toOpᴴ * (symmetricProjector X k)ᴴ =
      (φ.tensorPow k).toOpᴴ at h
    simpa only [symmetricProjector_isHermitian.eq, (φ.tensorPow k).isHermitian.eq] using h
  apply opLe_of_posSemidef_sub
  have h := posSemidef_conjTranspose_mul_self (P - A)
  have he : (P - A)ᴴ * (P - A) = P - A := by
    rw [conjTranspose_sub, symmetricProjector_isHermitian.eq,
      (φ.tensorPow k).isHermitian.eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      symmetricProjector_mul_self, hPA, hAP, show A * A = A from DensityOp.isPure_tensorPow hφ k]
    abel
  rwa [he] at h

/-- Bell-doubled pure tensor powers are dominated by the small joint Bell reference. -/
theorem bellWembed_tensorPow_opLe_smul_bellPairedState
    (k : ℕ) (φ : DensityOp (Bool × Bool)) (hφ : φ.IsPure) :
    OpLe (reindex (pairFunctions (Bool × Bool) (Bool × Bool) k)
      (pairFunctions (Bool × Bool) (Bool × Bool) k) ((bellWembed φ).tensorPow k).toOp)
      (((k + 3).choose 3 : ℂ) • (bellPairedDeFinettiState k).toOp) := by
  have hp := (opLe_iff_posSemidef_sub (φ.tensorPow k).isHermitian
    symmetricProjector_isHermitian).mp (tensorPow_opLe_symmetricProjector_of_isPure k φ hφ)
  have hs := hp.mul_mul_conjTranspose_same (bellDoublingIsometryPow k)
  have hn : ((k + 3).choose 3 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (Nat.choose_pos (by omega)))
  apply opLe_of_posSemidef_sub
  rw [bellWembed_tensorPow_toOp_eq_conj]
  change ((((k + 3).choose 3 : ℂ) • bellPairedDeFinettiStateOp k) - _).PosSemidef
  rw [bellPairedDeFinettiStateOp_eq_conj_symmetricProjector]
  have he : ((k + 3).choose 3 : ℂ) •
      reindex (pairFunctions (Bool × Bool) (Bool × Bool) k)
        (pairFunctions (Bool × Bool) (Bool × Bool) k)
        (bellDoublingIsometryPow k *
          (((k + 3).choose 3 : ℂ)⁻¹ • symmetricProjector (Bool × Bool) k) *
          (bellDoublingIsometryPow k)ᴴ) =
      reindex (pairFunctions (Bool × Bool) (Bool × Bool) k)
        (pairFunctions (Bool × Bool) (Bool × Bool) k)
        (bellDoublingIsometryPow k * symmetricProjector (Bool × Bool) k *
          (bellDoublingIsometryPow k)ᴴ) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, reindex_smul, smul_smul,
      mul_inv_cancel₀ hn, one_smul]
  rw [he]
  simpa only [Matrix.mul_sub, Matrix.sub_mul, reindex_apply,
    Matrix.submatrix_sub, Pi.sub_apply] using
    hs.submatrix
    (pairFunctions (Bool × Bool) (Bool × Bool) k).symm

end Quantum.Symmetry
