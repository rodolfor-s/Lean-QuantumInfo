import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementBlocks
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementChannel
import QCryptLean.Math.LinearAlgebra.PartialTrace.VectorBlock
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet

/-! # Domination of the transported measurement reference -/
noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators
open scoped Kronecker ComplexOrder MatrixOrder
open _root_.InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis
variable {A B : Type*} [Fintype A] [DecidableEq A]

/-- The identity on the outcome register removes cross terms between distinct basis vectors. -/
theorem vectorBlock_entropyReference
    (Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (σ : Op ((A × A) × B)) (z w : A) :
    vectorBlock (reindex measEntropyEquiv.symm measEntropyEquiv.symm ((1 : Op A) ⊗ₖ σ))
      (dilationKet Q z).vec (dilationKet Q w).vec =
      (if z = w then (1 : ℂ) else 0) • vectorBlock σ
        ((vec Q z).kronecker (vec Q z)).vec ((vec Q w).kronecker (vec Q w)).vec := by
  have hi := inner_vec Q z w
  change (∑ i, star ((Q z) i) * (Q w) i) = _ at hi
  ext b c
  change (∑ i : (A × A) × A, ∑ j : (A × A) × A,
    star (((Q z) i.1.1 * (Q z) i.1.2) * (Q z) i.2) *
      ((1 : Op A) i.1.1 j.1.1 * σ ((i.1.2, i.2), b) ((j.1.2, j.2), c)) *
        (((Q w) j.1.1 * (Q w) j.1.2) * (Q w) j.2)) = _
  simp only [Fintype.sum_prod_type, one_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have he : (∑ a, ∑ i, ∑ j, ∑ k, ∑ l,
      star (((Q z) a * (Q z) i) * (Q z) j) * σ ((i, j), b) ((k, l), c) *
        (((Q w) a * (Q w) k) * (Q w) l)) =
      (∑ a, star ((Q z) a) * (Q w) a) *
        (vectorBlock σ ((vec Q z).kronecker (vec Q z)).vec
          ((vec Q w).kronecker (vec Q w)).vec) b c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    simp only [vectorBlock, of_apply, Fintype.sum_prod_type, Ket.kronecker,
      RankOneProjectiveBasis.vec, Finset.mul_sum, star_mul']
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, hi]
  rfl

end InfoTheory.SmoothMinEntropy
