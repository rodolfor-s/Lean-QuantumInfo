import QCryptLean.Math.LinearAlgebra.Matrix.PartialTranspose
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra

/-! # Separable operations on natural registers

The family predicate describes finite product-Kraus operations and does not impose
trace preservation. The bipartite channel predicate includes Kraus completeness.
Positivity uses Mathlib's `Matrix.PosSemidef`; no norm or order instance is installed.
-/

noncomputable section
namespace Quantum.Channels
open Matrix Quantum.Operators
open scoped Kronecker ComplexOrder

/-- An operation between register families has a finite family of product Kraus matrices. -/
def IsSeparableOperation {P : Type*} [Fintype P] [DecidableEq P] {X Y : P → Type*}
    [∀ p, Fintype (X p)] (Φ : Operation (∀ p, X p) (∀ p, Y p)) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (K : I → ∀ p, Matrix (Y p) (X p) ℂ),
    Φ = krausMap (fun i => Matrix.piTensorProduct (K i))

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

open scoped Classical in
/-- A bipartite channel with a complete finite product-Kraus presentation. -/
def IsSeparableChannel (Φ : Operation (A × B) (C × D)) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (K : I → Matrix C A ℂ) (L : I → Matrix D B ℂ),
    Φ = krausMap (fun i => K i ⊗ₖ L i) ∧
      ∑ i, (K i ⊗ₖ L i)ᴴ * (K i ⊗ₖ L i) = 1

/-- A complete product-Kraus presentation certifies a channel. -/
theorem IsSeparableChannel.isChannel {Φ : Operation (A × B) (C × D)}
    (h : IsSeparableChannel Φ) : IsChannel Φ := by
  classical
  obtain ⟨I, _, K, L, rfl, hK⟩ := h
  refine ⟨isCompletelyPositive_krausMap _, ?_⟩
  intro ρ
  rw [trace_krausMap, hK, Matrix.one_mul]

omit [Fintype C] [Fintype D] in
/-- Grouping the Choi registers by laboratory exposes a sum of positive product matrices. -/
theorem reindex_choiMatrix_krausMap_kronecker {I : Type*} [Fintype I]
    (K : I → Matrix C A ℂ) (L : I → Matrix D B ℂ) :
    Matrix.reindex (Equiv.prodProdProdComm A B C D) (Equiv.prodProdProdComm A B C D)
      (choiMatrix (krausMap (fun i => K i ⊗ₖ L i))) =
      ∑ i, Matrix.vecMulVec (fun p : A × C => K i p.2 p.1)
        (star (fun p : A × C => K i p.2 p.1)) ⊗ₖ
          Matrix.vecMulVec (fun p : B × D => L i p.2 p.1)
            (star (fun p : B × D => L i p.2 p.1)) := by
  rw [choiMatrix_krausMap]
  ext ⟨⟨a, c⟩, b, d⟩ ⟨⟨a', c'⟩, b', d'⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (K i c a * L i d b) * star (K i c' a' * L i d' b') =
    (K i c a * star (K i c' a')) * (L i d b * star (L i d' b'))
  rw [star_mul]
  ring

/-- The laboratory-grouped Choi matrix of a separable channel has positive partial transpose. -/
theorem IsSeparableChannel.posSemidef_partialTransposeRight_choiMatrix
    {Φ : Operation (A × B) (C × D)} (h : IsSeparableChannel Φ) :
    (Matrix.partialTransposeRight
      (Matrix.reindex (Equiv.prodProdProdComm A B C D) (Equiv.prodProdProdComm A B C D)
        (choiMatrix Φ))).PosSemidef := by
  obtain ⟨I, _, K, L, rfl, _⟩ := h
  rw [reindex_choiMatrix_krausMap_kronecker]
  exact Matrix.posSemidef_partialTransposeRight_sum_kronecker _ _ _
    (fun _ _ => Matrix.posSemidef_vecMulVec_self_star _)
    (fun _ _ => Matrix.posSemidef_vecMulVec_self_star _)

end Quantum.Channels
