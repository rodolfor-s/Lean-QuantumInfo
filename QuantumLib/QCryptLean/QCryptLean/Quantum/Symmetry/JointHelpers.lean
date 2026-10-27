import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.FiniteGroupCommutant
import QCryptLean.Quantum.Symmetry.FiniteGroupTensorCommutant
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Commutant
import QCryptLean.Quantum.Symmetry.JointAction
import QCryptLean.Quantum.Symmetry.TensorPowerSpan

/-! # Joint Helpers -/


noncomputable section
namespace Quantum.Symmetry
open Matrix Quantum.Operators
variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G]

/-- Independent actions form a representation on the function register. -/
def tensorFamilyRep (ρ : G →* Op X) (k : ℕ) : (Fin k → G) →* Op (Fin k → X) where
  toFun v := piTensorProduct (fun i => ρ (v i))
  map_one' := by simp only [Pi.one_apply, map_one, piTensorProduct_one]
  map_mul' v w := by simp only [Pi.mul_apply, map_mul, piTensorProduct_mul]

/-- The joint action is a representation of the existing permutation semidirect product. -/
def tensorWreathRep (ρ : G →* Op X) (k : ℕ) :
    SemidirectProduct (Fin k → G) (Equiv.Perm (Fin k)) (wordPermutationAction G k) →*
      Op (Fin k → X) where
  toFun x := jointAction ρ k (x.left, x.right)
  map_one' := by
    simp only [jointAction, SemidirectProduct.one_left, SemidirectProduct.one_right,
      Pi.one_apply, map_one, piTensorProduct_one, permutationRepresentation,
      tensorPermutation_one, one_mul]
  map_mul' x y := by
    have hc := tensorPermutation_conj_piTensorProduct x.right
      (fun i => ρ (y.left i))
    have hu := (tensorPermutation_unitary (X := X) (R := ℂ) x.right).1
    have he := congrArg (· * tensorPermutation (X := X) (R := ℂ) x.right) hc
    simp only [Matrix.mul_assoc, hu, Matrix.mul_one] at he
    change piTensorProduct (fun i => ρ (x.left i * y.left (x.right.symm i))) *
      tensorPermutation (x.right * y.right) = _
    simp only [map_mul, ← piTensorProduct_mul, ← tensorPermutation_mul,
      jointAction, permutationRepresentation]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (piTensorProduct (fun i => ρ (x.left i)))
      (piTensorProduct (fun i => ρ (y.left (x.right.symm i))))]
    rw [← he]
    simp only [Matrix.mul_assoc]

/-- The bundled representation and pair-indexed action have the same range. -/
theorem range_tensorWreathRep (ρ : G →* Op X) (k : ℕ) :
    Set.range (tensorWreathRep ρ k) = Set.range (jointAction ρ k) := by
  ext A
  constructor
  · rintro ⟨⟨v, σ⟩, rfl⟩; exact ⟨(v, σ), rfl⟩
  · rintro ⟨⟨v, σ⟩, rfl⟩; exact ⟨⟨v, σ⟩, rfl⟩

/-- Joint commutation is independent-action and permutation commutation. -/
theorem mem_jointAction_commutant_iff (ρ : G →* Op X) (k : ℕ) (T : Op (Fin k → X)) :
    T ∈ commutant (Set.range (jointAction ρ k)) ↔
      (∀ v, Commute (tensorFamilyRep ρ k v) T) ∧
        (∀ σ : Equiv.Perm (Fin k), Commute (permutationRepresentation σ) T) := by
  constructor
  · intro h
    constructor
    · intro v
      have hv := h _ ⟨(v, 1), rfl⟩
      change tensorFamilyRep ρ k v * T = T * tensorFamilyRep ρ k v
      simpa only [tensorFamilyRep, MonoidHom.coe_mk, OneHom.coe_mk,
        jointAction, permutationRepresentation, tensorPermutation_one, mul_one]
        using hv
    · intro σ
      have hs := h _ ⟨(1, σ), rfl⟩
      change permutationRepresentation σ * T = T * permutationRepresentation σ
      simpa only [jointAction, Pi.one_apply, map_one, piTensorProduct_one, one_mul] using hs
  · rintro ⟨hG, hP⟩ M ⟨⟨v, σ⟩, rfl⟩
    exact ((hG v).mul_left (hP σ)).eq

/-- Independent finite averages commute with tensor powers. -/
theorem finiteGroupMatrixAverage_tensorPow [Fintype G] (ρ : G →* Op X) (A : Op X) (k : ℕ) :
    finiteGroupMatrixAverage (tensorFamilyRep ρ k) (Op.tensorPow A k) =
      Op.tensorPow (finiteGroupMatrixAverage ρ A) k := by
  ext x y
  simp only [finiteGroupMatrixAverage, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    tensorFamilyRep, MonoidHom.coe_mk, OneHom.coe_mk, Pi.inv_apply, Op.tensorPow,
    piTensorProduct_mul, piTensorProduct_apply, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow]
  change ((Fintype.card G : ℂ) ^ k)⁻¹ *
    (∑ c : Fin k → G, ∏ i, (ρ (c i) * A * ρ ((c i)⁻¹)) (x i) (y i)) = _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow,
    Fintype.prod_sum]

end Quantum.Symmetry
