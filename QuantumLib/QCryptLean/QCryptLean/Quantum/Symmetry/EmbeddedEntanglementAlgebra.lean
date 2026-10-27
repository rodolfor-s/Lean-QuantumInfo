import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.EmbeddedEntanglement
import QCryptLean.Quantum.Symmetry.Paired

/-! # Trace pairings and tensor families of embedded entangled vectors -/
namespace Quantum.Operators
open Matrix
open scoped Kronecker
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

omit [DecidableEq X] in
/-- A product observable on an embedded entangled vector pairs with the transposed restriction. -/
theorem trace_embeddedMaxEntangled_mul_kronecker (e : X ↪ Y) (A : Op X) (B : Op Y) :
    ((embeddedMaxEntangled e).projector * (A ⊗ₖ B)).trace =
      (A * (B.submatrix e e)ᵀ).trace := by
  change (∑ p : X × Y, ∑ q : X × Y,
    ((1 : Op Y) (e p.1) p.2 * star ((1 : Op Y) (e q.1) q.2)) *
      (A q.1 p.1 * B q.2 p.2)) = ∑ a : X, ∑ b : X, A a b * B (e a) (e b)
  have hstar (a b : Y) : star (if a = b then (1 : ℂ) else 0) =
      if a = b then (1 : ℂ) else 0 := by split_ifs <;> simp
  simp only [Fintype.sum_prod_type, Matrix.one_apply, hstar,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Finset.sum_comm

omit [Fintype X] [Fintype Y] [DecidableEq X] in
/-- Tensoring embedded entangled vectors commutes with grouping the two registers. -/
theorem tensorFamily_embeddedMaxEntangled_reindex (e : X ↪ Y) (k : ℕ) :
    (Ket.tensorFamily (fun _ : Fin k => embeddedMaxEntangled e)).reindex
      (Quantum.Symmetry.pairFunctions X Y k) =
      embeddedMaxEntangled (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y)) := by
  ext p
  change (∏ i : Fin k, if e (p.1 i) = p.2 i then (1 : ℂ) else 0) =
    if e ∘ p.1 = p.2 then (1 : ℂ) else 0
  simp only [Fintype.prod_boole, ← funext_iff]
  rfl

end Quantum.Operators

namespace Quantum.Symmetry
open Matrix Quantum.Operators
open scoped Kronecker
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] {k : ℕ}

omit [Fintype X] [Fintype Y] in
/-- Restriction along a pointwise embedding intertwines site permutations. -/
theorem permutationRepresentation_submatrix_arrowCongrRight (e : X ↪ Y)
    (σ : Equiv.Perm (Fin k)) :
    (permutationRepresentation (X := Y) σ).submatrix e.arrowCongrRight e.arrowCongrRight =
      permutationRepresentation (X := X) σ := by
  ext a b
  change (if e ∘ a = (e ∘ b) ∘ σ.symm then (1 : ℂ) else 0) =
    if a = b ∘ σ.symm then (1 : ℂ) else 0
  have he : e ∘ a = (e ∘ b) ∘ σ.symm ↔ a = b ∘ σ.symm := by
    exact e.injective.comp_left.eq_iff
  simp only [he]

/-- A permutation on the second entangled register transfers as its inverse to the first. -/
theorem trace_embeddedMaxEntangled_mul_tensor_permutation (e : X ↪ Y)
    (A : Op (Fin k → X)) (σ : Equiv.Perm (Fin k)) :
    ((embeddedMaxEntangled (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))).projector *
      (A ⊗ₖ permutationRepresentation (X := Y) σ)).trace =
      (A * permutationRepresentation (X := X) σ⁻¹).trace := by
  rw [trace_embeddedMaxEntangled_mul_kronecker, permutationRepresentation_submatrix_arrowCongrRight]
  exact congrArg (fun B => (A * B).trace) (tensorPermutation_transpose σ)

end Quantum.Symmetry
