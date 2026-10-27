import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.CentralizerHaar
import QCryptLean.Quantum.Symmetry.Commutant
import QCryptLean.Quantum.Symmetry.JointAction
import QCryptLean.Quantum.Symmetry.JointActionAlgebra
import QCryptLean.Quantum.Symmetry.LocalCommutantTwirl
import QCryptLean.Quantum.Symmetry.UnitaryCentralizer

/-! # Centralizer Haar Algebra -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators MeasureTheory
open scoped Kronecker

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G] {d k : ℕ}

/-- Unitary centralizer powers have the full constrained tensor-power commutant.
The proof is assembled from the analytic extension and constrained duality results. -/
theorem commutant_unitaryCentralizer_tensorPow_eq [Finite G]
    (ρ : G →* Op X) (hρ : ∀ g, (ρ g)ᴴ = ρ g⁻¹) (k : ℕ) :
    commutant (Set.range fun U : unitaryCentralizer ρ =>
      (unitaryCentralizerTensorPower ρ k U).val) =
        Submodule.span ℂ (Set.range (jointAction ρ k)) := by
  rw [← commutant_centralizer_tensorPow_eq ρ k]
  ext T
  constructor
  · intro hT M hM
    obtain ⟨A, rfl⟩ := hM
    exact (commute_tensorPow_of_unitaryCentralizer (Set.range ρ)
      (by rintro _ ⟨g, rfl⟩; exact ⟨g⁻¹, (hρ g).symm⟩) T
      (fun U hU => hT _ ⟨⟨U, fun g => hU _ ⟨g, rfl⟩⟩, rfl⟩)
      A.val (fun M hM => A.property M hM)).eq
  · intro hT M hM
    obtain ⟨U, rfl⟩ := hM
    exact hT _ ⟨⟨U.val.val, by rintro _ ⟨g, rfl⟩; exact (U.property g).eq⟩, rfl⟩

/-- Joint generators acting locally compress the entire centralizer commutant. -/
theorem hasLocalCommutant_unitaryCentralizer_tensorPow
    {Y : Type*} [Fintype Y] [DecidableEq Y] [Finite G]
    (ρ : G →* Op X) (hρ : ∀ g, (ρ g)ᴴ = ρ g⁻¹)
    (Q : Op ((Fin k → Y) × (Fin k → X)))
    (hgen : ∀ v, ∃ A : Op (Fin k → Y),
      (1 ⊗ₖ jointAction ρ k v) * Q = (A ⊗ₖ (1 : Op (Fin k → X))) * Q) :
    HasLocalCommutant (fun U : unitaryCentralizer ρ =>
      (unitaryCentralizerTensorPower ρ k U).val) Q := by
  let U := fun V : unitaryCentralizer ρ => (unitaryCentralizerTensorPower ρ k V).val
  let R := Set.range U
  apply hasLocalCommutant_of_span U Q
    {T | ∃ (A : Op (Fin k → Y)) (M : Op (Fin k → X)),
      (∀ B ∈ R, Commute B M) ∧ T = A ⊗ₖ M}
  · intro T hT
    let B (a b : Fin k → Y) : Op (Fin k → X) := fun r s => T (a, r) (b, s)
    have he : T = ∑ a, ∑ b, single a b (1 : ℂ) ⊗ₖ B a b := by
      ext ⟨a, r⟩ ⟨b, s⟩
      simp only [Matrix.sum_apply]
      change T (a, r) (b, s) = ∑ a', ∑ b', (single a' b' (1 : ℂ)) a b * B a' b' r s
      simp [Matrix.single_apply, B, ite_and]
    rw [he]
    apply Submodule.sum_mem
    intro a _
    apply Submodule.sum_mem
    intro b _
    apply Submodule.subset_span
    refine ⟨single a b 1, B a b, ?_, rfl⟩
    rintro M ⟨V, rfl⟩
    change U V * B a b = B a b * U V
    ext r s
    change (∑ x, U V r x * T (a, x) (b, s)) =
      ∑ x, T (a, r) (b, x) * U V x s
    have h := congrFun (congrFun (hT V).eq (a, r)) (b, s)
    simpa [Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type] using h
  · rintro T ⟨A, M, hM, rfl⟩
    have hspan : M ∈ Submodule.span ℂ (Set.range (jointAction ρ k)) := by
      rw [← commutant_unitaryCentralizer_tensorPow_eq ρ hρ]
      exact fun B hB => (hM B hB).eq
    clear hM
    induction hspan using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨v, rfl⟩ := hM
      obtain ⟨B, hB⟩ := hgen v
      refine ⟨A * B, ?_⟩
      calc
        (A ⊗ₖ jointAction ρ k v) * Q =
            (A ⊗ₖ (1 : Op (Fin k → X))) * ((1 ⊗ₖ jointAction ρ k v) * Q) := by
          rw [← Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
        _ = _ := by rw [hB, ← Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.mul_one]
    | zero => refine ⟨0, ?_⟩; simp
    | add M N _ _ hM hN =>
      obtain ⟨B, hB⟩ := hM
      obtain ⟨C, hC⟩ := hN
      exact ⟨B + C, by rw [kronecker_add, add_mul, hB, hC, add_kronecker, add_mul]⟩
    | smul c M _ hM =>
      obtain ⟨B, hB⟩ := hM
      exact ⟨c • B, by rw [kronecker_smul, Matrix.smul_mul, hB,
        smul_kronecker, Matrix.smul_mul]⟩

/-- The restricted Haar tensor moment is its support normalized by the inverse marginal.
The proof uses the twirl identity once local commutant compression is supplied. -/
theorem unitaryCentralizerHaar_moment_eq_inverse_marginal
    {Y : Type*} [Fintype Y] [DecidableEq Y] [Finite G]
    (ρ : G →* Op X) (hρ : ∀ g, (ρ g)ᴴ = ρ g⁻¹)
    (T Q : Op ((Fin k → Y) × (Fin k → X))) (hQ : Q.IsHermitian) (hTQ : T * Q = T)
    (hgen : ∀ v, ∃ A : Op (Fin k → Y),
      (1 ⊗ₖ jointAction ρ k v) * Q = (A ⊗ₖ (1 : Op (Fin k → X))) * Q)
    (hcomm : ∀ U : unitaryCentralizer ρ,
      Commute ((1 : Op (Fin k → Y)) ⊗ₖ (unitaryCentralizerTensorPower ρ k U).val) Q)
    (hΩ : IsUnit (partialTraceRight Q)) (hT : partialTraceRight T = 1) :
    referenceTwirl (unitaryCentralizerHaar ρ) (unitaryCentralizerTensorPower ρ k) T =
      ((partialTraceRight Q)⁻¹ ⊗ₖ (1 : Op (Fin k → X))) * Q := by
  exact referenceTwirl_eq_inverse_marginal_mul _ _ T Q
    (integrable_referenceTwirl _ _ (continuous_subtype_val.comp
      (continuous_unitaryCentralizerTensorPower ρ k)) T)
    hQ hTQ hcomm (hasLocalCommutant_unitaryCentralizer_tensorPow ρ hρ Q hgen) hΩ hT

/-- Joint group and permutation support supplies local centralizer compression. -/
theorem hasLocalCommutant_unitaryCentralizer_of_joint_fixed
    {Y : Type*} [Fintype Y] [DecidableEq Y] [Finite G]
    (α : G →* Op Y) (ρ : G →* Op X) (hρ : ∀ g, (ρ g)ᴴ = ρ g⁻¹)
    (Q : Op ((Fin k → Y) × (Fin k → X)))
    (hG : ∀ v : Fin k → G,
      (piTensorProduct (fun i => α (v i)) ⊗ₖ piTensorProduct (fun i => ρ (v i))) * Q = Q)
    (hP : ∀ σ : Equiv.Perm (Fin k),
      (permutationRepresentation σ ⊗ₖ permutationRepresentation σ) * Q = Q) :
    HasLocalCommutant (fun U : unitaryCentralizer ρ =>
      (unitaryCentralizerTensorPower ρ k U).val) Q := by
  apply hasLocalCommutant_unitaryCentralizer_tensorPow ρ hρ Q
  rintro ⟨v, σ⟩
  let A := (permutationRepresentation (X := Y) σ)ᴴ *
    piTensorProduct (fun i => α (v i)⁻¹)
  have hA : A * jointAction α k (v, σ) = 1 := by
    change (_ * _) * (_ * _) = _
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (piTensorProduct _), piTensorProduct_mul]
    simp only [← map_mul, inv_mul_cancel, map_one, piTensorProduct_one, one_mul]
    exact (tensorPermutation_unitary σ).1
  have hfix : (jointAction α k (v, σ) ⊗ₖ jointAction ρ k (v, σ)) * Q = Q := by
    rw [jointAction, jointAction, mul_kronecker_mul, Matrix.mul_assoc, hP, hG]
  refine ⟨A, ?_⟩
  have h := congrArg (fun T => (A ⊗ₖ (1 : Op (Fin k → X))) * T) hfix
  simpa only [← Matrix.mul_assoc, ← mul_kronecker_mul, hA, one_mul] using h

/-- The Haar moment for operators fixed by the joint group and permutation actions. -/
theorem unitaryCentralizerHaar_moment_eq_inverse_marginal_of_joint_fixed
    {Y : Type*} [Fintype Y] [DecidableEq Y] [Finite G]
    (α : G →* Op Y) (ρ : G →* Op X) (hρ : ∀ g, (ρ g)ᴴ = ρ g⁻¹)
    (T Q : Op ((Fin k → Y) × (Fin k → X))) (hQ : Q.IsHermitian) (hTQ : T * Q = T)
    (hG : ∀ v : Fin k → G,
      (piTensorProduct (fun i => α (v i)) ⊗ₖ piTensorProduct (fun i => ρ (v i))) * Q = Q)
    (hP : ∀ σ : Equiv.Perm (Fin k),
      (permutationRepresentation σ ⊗ₖ permutationRepresentation σ) * Q = Q)
    (hcomm : ∀ U : unitaryCentralizer ρ,
      Commute ((1 : Op (Fin k → Y)) ⊗ₖ (unitaryCentralizerTensorPower ρ k U).val) Q)
    (hΩ : IsUnit (partialTraceRight Q)) (hT : partialTraceRight T = 1) :
    referenceTwirl (unitaryCentralizerHaar ρ) (unitaryCentralizerTensorPower ρ k) T =
      ((partialTraceRight Q)⁻¹ ⊗ₖ (1 : Op (Fin k → X))) * Q := by
  exact referenceTwirl_eq_inverse_marginal_mul _ _ T Q
    (integrable_referenceTwirl _ _ (continuous_subtype_val.comp
      (continuous_unitaryCentralizerTensorPower ρ k)) T)
    hQ hTQ hcomm (hasLocalCommutant_unitaryCentralizer_of_joint_fixed α ρ hρ Q hG hP) hΩ hT

end Quantum.Symmetry
