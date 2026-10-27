import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.ConsumerBounds
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Channels.PostselectionBound
import QCryptLean.Quantum.Channels.SubstateExtraction
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNormSum
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.RankPurification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.RandomizedBlocking

/-! # CKRConsequences -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Metrics Quantum.Symmetry
open scoped Kronecker ComplexOrder

variable {X Y Z R S : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype R] [Fintype S] {n : ℕ}

/-- CKR trace norms are independent of the finite reference used to purify a fixed marginal.
No channel, adjoint-preservation, nonemptiness or equal-reference-size hypothesis is needed. -/
theorem tensorTraceNorm_eq_of_shared_marginal
    (Δ : Operation (Fin n → X) Y) (σ : DensityOp (Fin n → X))
    (τ₁ : DensityOp ((Fin n → X) × R)) (τ₂ : DensityOp ((Fin n → X) × S))
    (h₁pure : τ₁.IsPure) (h₂pure : τ₂.IsPure)
    (h₁ : τ₁.partialTraceRight = σ) (h₂ : τ₂.partialTraceRight = σ) :
    ckrTraceNorm Δ τ₁ = ckrTraceNorm Δ τ₂ := by
  obtain ⟨v, hv⟩ := DensityOp.IsPure.exists_normKet τ₁ h₁pure
  obtain ⟨w, hw⟩ := DensityOp.IsPure.exists_normKet τ₂ h₂pure
  have hm : partialTraceRight τ₁.toOp = partialTraceRight τ₂.toOp :=
    congrArg DensityOp.toOp (h₁.trans h₂.symm)
  unfold ckrTraceNorm
  apply le_antisymm
  · have h := traceNorm_mapTensorId_le_of_partialTraceRight_le Δ τ₁.toOp τ₁.posSemidef w.toKet
    have he : w.toKet.projector = τ₂.toOp := congrArg DensityOp.toOp hw
    simpa only [he] using h (by rw [he, hm, sub_self]; exact PosSemidef.zero)
  · have h := traceNorm_mapTensorId_le_of_partialTraceRight_le Δ τ₂.toOp τ₂.posSemidef v.toKet
    have he : v.toKet.projector = τ₁.toOp := congrArg DensityOp.toOp hv
    simpa only [he] using h (by rw [he, hm, sub_self]; exact PosSemidef.zero)

/-- Input permutations transfer to the untouched reference of a paired-invariant state. -/
theorem ckrTraceNorm_comp_permConjLin [DecidableEq X]
    (Δ : Operation (Fin n → X) Y)
    (τ : DensityOp ((Fin n → X) × (Fin n → X)))
    (hτ : IsPairedPermInvariant τ) (π : Equiv.Perm (Fin n)) :
    ckrTraceNorm (Δ.comp (permConjLin π)) τ = ckrTraceNorm Δ τ := by
  classical
  let e : (Fin n → X) ≃ (Fin n → X) := {
    toFun x := x ∘ π
    invFun x := x ∘ π.symm
    left_inv x := by ext i; simp
    right_inv x := by ext i; simp }
  have hp (x r y s : Fin n → X) :
      τ.toOp (x ∘ π, r ∘ π) (y ∘ π, s ∘ π) = τ.toOp (x, r) (y, s) := by
    have h := congrArg (fun A : Op ((Fin n → X) × (Fin n → X)) => A (x, r) (y, s)) (hτ π)
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      permutationRepresentation, tensorPermutation, Fintype.sum_prod_type,
      eq_comp_symm_iff, apply_ite] using h
  have he : mapTensorId (Δ.comp (permConjLin π)) (Fin n → X) τ.toOp =
      reindex ((Equiv.refl Y).prodCongr e) ((Equiv.refl Y).prodCongr e)
        (mapTensorId Δ (Fin n → X) τ.toOp) := by
    ext p q
    let M : Op (Fin n → X) := fun x y => τ.toOp (x, p.2) (y, q.2)
    change Δ (permutationRepresentation (X := X) π * M *
        (permutationRepresentation (X := X) π)ᴴ) p.1 q.1 =
        Δ (fun x y => τ.toOp (x, p.2 ∘ π.symm) (y, q.2 ∘ π.symm)) p.1 q.1
    apply congrArg (fun A : Op (Fin n → X) => Δ A p.1 q.1)
    ext x y
    rw [permutationRepresentation, tensorPermutation_conj_apply]
    simpa [Function.comp_def] using hp x (p.2 ∘ π.symm) y (q.2 ∘ π.symm)
  unfold ckrTraceNorm
  rw [he, traceNorm_reindex]

/-- A permutation average of channel-postprocessed base schemes preserves their CKR bound. -/
theorem ckrTraceNorm_symAverage_le_of_baseScheme_bound
    [DecidableEq X]
    (Δ : Operation (Fin n → X) Y) (announce : Equiv.Perm (Fin n) → Operation Y Z)
    (hAnnounce : ∀ π, IsChannel (announce π)) (symDiff : Operation (Fin n → X) Z)
    (τ : DensityOp ((Fin n → X) × (Fin n → X))) (hτ : IsPairedPermInvariant τ)
    {B : ℝ} (hexpand : symDiff = (n.factorial : ℂ)⁻¹ •
      ∑ π : Equiv.Perm (Fin n), (announce π).comp (Δ.comp (permConjLin π)))
    (hBase : ckrTraceNorm Δ τ ≤ B) : ckrTraceNorm symDiff τ ≤ B := by
  classical
  let L : Operation (Fin n → X) Z →ₗ[ℂ] Op (Z × (Fin n → X)) := {
    toFun F := mapTensorId F (Fin n → X) τ.toOp
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hs π : traceNorm (L ((announce π).comp (Δ.comp (permConjLin π)))) ≤ B :=
    (ckrTraceNorm_comp_le_of_isChannel (announce π) (hAnnounce π) _ τ).trans
      ((ckrTraceNorm_comp_permConjLin Δ τ hτ π).le.trans hBase)
  change traceNorm (L symDiff) ≤ B
  rw [hexpand, map_smul, map_sum, traceNorm_smul]
  have hb : traceNorm (∑ π : Equiv.Perm (Fin n),
      L ((announce π).comp (Δ.comp (permConjLin π)))) ≤
        ∑ _ : Equiv.Perm (Fin n), B := by
    apply (Quantum.Metrics.traceNorm_sum_le Finset.univ
      (fun π : Equiv.Perm (Fin n) => L ((announce π).comp
        (Δ.comp (permConjLin π))))).trans
    exact Finset.sum_le_sum fun π _ => hs π
  have hn : ‖(n.factorial : ℂ)⁻¹‖ = (n.factorial : ℝ)⁻¹ := by simp
  calc
    _ ≤ ‖(n.factorial : ℂ)⁻¹‖ * (∑ _ : Equiv.Perm (Fin n), B) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = B := by
      rw [hn]
      simp [Fintype.card_perm, nsmul_eq_mul, Nat.factorial_ne_zero]

end Quantum.Channels
