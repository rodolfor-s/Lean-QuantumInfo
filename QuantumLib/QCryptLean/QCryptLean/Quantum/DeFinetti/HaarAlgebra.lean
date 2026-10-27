import Mathlib.MeasureTheory.Group.Integral
import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Math.Probability.HaarMeasure
import QCryptLean.Math.Probability.UnitaryHaar
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.DeFinetti.Integral
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Commutant
import QCryptLean.Quantum.Symmetry.CommutantAlgebra
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.PairedAlgebra
import QCryptLean.Quantum.Symmetry.UnitaryCentralizer

/-! # Haar Algebra -/


noncomputable section

namespace Quantum.DeFinetti

open Matrix Quantum.Operators Quantum.Symmetry MeasureTheory

variable {X : Type*} [Fintype X] [DecidableEq X] {d k : ℕ}

/-- On finite numeric indices the two independently normalized Haar constructions coincide. -/
theorem haarProbUnitary_fin_eq (d : ℕ) :
    UnitaryGroup.haarProbUnitary (Fin d) = Math.HaarMeasure.haarProbUnitary d := rfl

/-- The normalized symmetric projector is the Haar mixture of pure tensor powers. -/
theorem deFinettiState_eq_haar_integral [Nonempty X] (x : X) (k : ℕ) :
    (Quantum.Symmetry.deFinettiState X k).toOp =
      integralTensorPower k (haarDensityMeasure x) := by
  classical
  let μ := UnitaryGroup.haarProbUnitary X
  let A (U : unitaryGroup X ℂ) := ((pureStateMap x U).tensorPow k).toOp
  let M : Op (Fin k → X) := Matrix.of (fun i j => ∫ U, A U i j ∂μ)
  have hint (i j : Fin k → X) : Integrable (fun U => A U i j) μ := by
    exact ((DensityOp.continuous_tensorPow_entry k i j).comp
      (continuous_pureStateMap x)).integrable_of_compactSpace
  have hM : M = integralTensorPower k (haarDensityMeasure x) := by
    ext i j
    symm
    apply integral_map (continuous_pureStateMap x).measurable.aemeasurable
      (DensityOp.continuous_tensorPow_entry k i j).measurable.aestronglyMeasurable
  have hstar (B : Op X) : (Op.tensorPow B k)ᴴ = Op.tensorPow Bᴴ k :=
    conjTranspose_piTensorProduct _
  have hcov (U V : unitaryGroup X ℂ) :
      Op.tensorPow U.val k * A V * (Op.tensorPow U.val k)ᴴ = A (U * V) := by
    have he : U.val * (pureStateMap x V).toOp * U.valᴴ = (pureStateMap x (U * V)).toOp := by
      change U.val * vecMulVec (fun i => V.val i x) (star (fun i => V.val i x)) * U.valᴴ = _
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
      rfl
    change Op.tensorPow U.val k * Op.tensorPow (pureStateMap x V).toOp k *
      (Op.tensorPow U.val k)ᴴ = Op.tensorPow (pureStateMap x (U * V)).toOp k
    rw [hstar, ← Op.tensorPow_mul, ← Op.tensorPow_mul, he]
  have hc (U : unitaryGroup X ℂ) : Commute (Op.tensorPow U.val k) M := by
    have he : Op.tensorPow U.val k * M * (Op.tensorPow U.val k)ᴴ = M := by
      rw [Matrix.sandwich_entryIntegral _ hint]
      ext i j
      simp only [Matrix.of_apply, hcov]
      exact integral_mul_left_eq_self (fun V => A V i j) U
    have hu : (Op.tensorPow U.val k)ᴴ * Op.tensorPow U.val k = 1 := by
      rw [hstar, ← Op.tensorPow_mul, show U.valᴴ * U.val = 1 from Unitary.coe_star_mul_self U]
      exact piTensorProduct_one
    have he' := congrArg (· * Op.tensorPow U.val k) he
    change Op.tensorPow U.val k * M = M * Op.tensorPow U.val k
    simpa only [Matrix.mul_assoc, hu, Matrix.mul_one] using he'
  have hspan : M ∈ permSpan (X := X) k := by
    rw [← commutant_matrixTensorPow_eq_permSpan]
    rintro _ ⟨B, rfl⟩
    exact (commute_tensorPow_of_unitaryCentralizer ∅ (by simp) M
      (fun U _ => hc U) B (by simp)).eq
  have hsupport : symmetricProjector X k * M = M := by
    rw [Matrix.mul_entryIntegral _ hint]
    ext i j
    apply integral_congr_ae
    filter_upwards [] with U
    have hp : A U = (Ket.tensorFamily (fun _ : Fin k => (unitaryColumn x U).toKet)).projector :=
      (Ket.projector_tensorFamily _).symm
    let v := Ket.tensorFamily (fun _ : Fin k => (unitaryColumn x U).toKet)
    have hv : symmetricProjector X k *ᵥ v.vec = v.vec := by
      apply (symmetricProjector_mulVec_eq_iff _).mpr
      intro σ a
      exact Equiv.prod_comp σ (fun t => U.val (a t) x)
    change (symmetricProjector X k * A U) i j = A U i j
    rw [hp]
    change (symmetricProjector X k * vecMulVec v.vec (star v.vec)) i j = _
    rw [Matrix.mul_vecMulVec, hv]
    rfl
  have hex : ∃ c : ℂ, symmetricProjector X k * M = c • symmetricProjector X k := by
    clear hM hc hsupport
    generalize M = N at hspan ⊢
    induction hspan using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨σ, rfl⟩ := hB
      refine ⟨1, ?_⟩
      rw [one_smul]
      have h := congrArg Matrix.conjTranspose
        (permutationRepresentation_mul_symmetricProjector (X := X) σ⁻¹)
      simpa only [conjTranspose_mul, symmetricProjector_isHermitian.eq,
        permutationRepresentation, tensorPermutation_conjTranspose, inv_inv] using h
    | zero => exact ⟨0, by simp⟩
    | add B C _ _ hB hC =>
      obtain ⟨b, hb⟩ := hB
      obtain ⟨c, hc⟩ := hC
      exact ⟨b + c, by rw [Matrix.mul_add, hb, hc, add_smul]⟩
    | smul c B _ hB =>
      obtain ⟨b, hb⟩ := hB
      exact ⟨c * b, by rw [Matrix.mul_smul, hb, smul_smul]⟩
  obtain ⟨c, hc⟩ := hex
  rw [hsupport] at hc
  have ht : c * (symmetricProjector X k).trace = 1 := by
    rw [← smul_eq_mul, ← Matrix.trace_smul, ← hc, hM]
    exact trace_integralTensorPower _ _
  have he : c = (symmetricProjector X k).trace⁻¹ := by
    apply (mul_right_cancel₀ (Quantum.Symmetry.symmetricProjector_trace_ne_zero
      (X := X) (k := k)))
    rw [ht, inv_mul_cancel₀ (Quantum.Symmetry.symmetricProjector_trace_ne_zero
      (X := X) (k := k))]
  rw [← hM, hc, he]
  rfl

end Quantum.DeFinetti
