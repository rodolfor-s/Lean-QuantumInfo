import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Star.Unitary
import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.SqrtKronecker
import QCryptLean.Math.LinearAlgebra.Matrix.SqrtScale
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Cyclic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Local Commutant Twirl -/


noncomputable section

namespace Quantum.Symmetry

open Quantum.Operators Matrix MeasureTheory
open scoped Kronecker

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

private local instance {X : Type*} [Fintype X] : ContinuousENorm (Op X) :=
  SeminormedAddGroup.toContinuousENorm

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The commutant of a reference action acts locally after restriction to `Q`. -/
def HasLocalCommutant {H : Type*} (U : H → Op Y) (Q : Op (X × Y)) : Prop :=
  ∀ T : Op (X × Y), (∀ g, Commute (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g)) T) →
    ∃ X : Op X, T * Q = Matrix.kroneckerMap (· * ·) X (1 : Op Y) * Q

/-- It suffices to check local commutant compression on spanning generators. -/
theorem hasLocalCommutant_of_span {H : Type*} (U : H → Op Y)
    (Q : Op (X × Y)) (s : Set (Op (X × Y)))
    (hspan : ∀ T, (∀ g, Commute (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g)) T) →
      T ∈ Submodule.span ℂ s)
    (hgen : ∀ T ∈ s, ∃ X : Op X, T * Q = Matrix.kroneckerMap (· * ·) X (1 : Op Y) * Q) :
    HasLocalCommutant U Q := by
  intro T hT
  have hmem := hspan T hT
  clear hT
  induction hmem using Submodule.span_induction with
  | mem T hT => exact hgen T hT
  | zero =>
      refine ⟨0, ?_⟩
      rw [show (0 : Op X) = (0 : ℂ) • (0 : Op X) from (zero_smul _ _).symm,
        smul_kronecker, zero_smul, zero_mul]
  | add T₁ T₂ _ _ h₁ h₂ =>
      obtain ⟨X₁, h₁⟩ := h₁
      obtain ⟨X₂, h₂⟩ := h₂
      exact ⟨X₁ + X₂, by rw [add_mul, h₁, h₂, add_kronecker, add_mul]⟩
  | smul c T _ h =>
      obtain ⟨X, hX⟩ := h
      exact ⟨c • X, by rw [smul_mul_assoc, hX, smul_kronecker, smul_mul_assoc]⟩

/-- Local commutant compression makes the marginal determine an invariant supported operator. -/
theorem HasLocalCommutant.eq_of_marginal {H : Type*}
    {U : H → Op Y} {Q T : Op (X × Y)} (hlocal : HasLocalCommutant U Q)
    (hΩ : IsUnit (partialTraceRight Q)) (hTQ : T * Q = T)
    (hT : ∀ g, Commute (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g)) T) :
    T = ((partialTraceRight T * (partialTraceRight Q)⁻¹) ⊗ₖ (1 : Op Y)) * Q := by
  obtain ⟨A, hA⟩ := hlocal T hT
  rw [hTQ] at hA
  have hm : partialTraceRight T = A * partialTraceRight Q := by
    rw [hA]
    exact partialTraceRight_kronecker_one_mul A Q
  rw [hm, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hΩ), Matrix.mul_one]
  exact hA

/-- The reference-side twirl for an arbitrary unitary family and measure. -/
def referenceTwirl {H : Type*} [MeasurableSpace H]
    (μ : Measure H) (U : H → Matrix.unitaryGroup Y ℂ) (T : Op (X × Y)) :
    Op (X × Y) :=
  ∫ g, Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y) * T *
    (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))ᴴ ∂μ

/-- Continuous unitary orbits over a compact parameter space are integrable. -/
theorem integrable_referenceTwirl {H : Type*} [TopologicalSpace H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [IsFiniteMeasure μ]
    (U : H → Matrix.unitaryGroup Y ℂ) (hU : Continuous (fun g => (U g : Op Y))) (T : Op (X × Y)) :
    Integrable (fun g => Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y) * T *
      (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))ᴴ) μ := by
  have hK : Continuous (fun g => Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_const.mul
      ((continuous_apply j.2).comp ((continuous_apply i.2).comp
        hU))
  exact ((hK.matrix_mul continuous_const).matrix_mul
    hK.matrix_conjTranspose).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Partial trace commutes with an integrable reference-side twirl. -/
theorem partialTraceRight_referenceTwirl {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ]
    (U : H → Matrix.unitaryGroup Y ℂ) (T : Op (X × Y))
    (hint : Integrable (fun g => Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y) * T *
      (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))ᴴ) μ) :
    partialTraceRight (referenceTwirl μ U T) = partialTraceRight T := by
  let L : Op (X × Y) →ₗ[ℂ] Op X :=
    { toFun := partialTraceRight
      map_add' := Matrix.partialTraceRight_add
      map_smul' := Matrix.partialTraceRight_smul }
  change L.toContinuousLinearMap (∫ g, _ ∂μ) = _
  refine (L.toContinuousLinearMap.integral_comp_comm hint).symm.trans ?_
  have htrace (g : H) : L (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y) * T *
      (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))ᴴ) = partialTraceRight T := by
    change partialTraceRight _ = _
    rw [conjTranspose_kronecker, conjTranspose_one]
    apply partialTraceRight_one_kronecker_sandwich_of_mul_eq_one
    exact (Matrix.mem_unitaryGroup_iff').mp (U g).2
  calc
    _ = ∫ _ : H, partialTraceRight T ∂μ := integral_congr_ae (Filter.Eventually.of_forall htrace)
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]

/-- A left-invariant average is invariant under conjugation by the reference action. -/
theorem referenceTwirl_conj {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
     (μ : Measure H) [μ.IsMulLeftInvariant]
    (U : H →* Matrix.unitaryGroup Y ℂ) (T : Op (X × Y))
    (hint : Integrable (fun g => Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y) * T *
      (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))ᴴ) μ) (g : H) :
    Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y) * referenceTwirl μ U T *
      (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))ᴴ = referenceTwirl μ U T := by
  let K (g : H) : Op (X × Y) := Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y)
  have hK (g h : H) : K (g * h) = K g * K h := by
    simp only [K, map_mul, Submonoid.coe_mul, ← mul_kronecker_mul, one_mul]
  let L := ((LinearMap.mulRight ℂ (K g)ᴴ).comp
    (LinearMap.mulLeft ℂ (K g))).toContinuousLinearMap
  change L (∫ h, K h * T * (K h)ᴴ ∂μ) = ∫ h, K h * T * (K h)ᴴ ∂μ
  refine (L.integral_comp_comm hint).symm.trans ?_
  calc
    _ = ∫ h, K (g * h) * T * (K (g * h))ᴴ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with h
      change K g * (K h * T * (K h)ᴴ) * (K g)ᴴ = _
      rw [hK, Matrix.conjTranspose_mul]
      simp only [mul_assoc]
    _ = _ := integral_mul_left_eq_self (μ := μ) (fun h => K h * T * (K h)ᴴ) g

/-- A left-invariant reference twirl lies in the commutant of its unitary action. -/
theorem referenceTwirl_commute {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
     (μ : Measure H) [μ.IsMulLeftInvariant]
    (U : H →* Matrix.unitaryGroup Y ℂ) (T : Op (X × Y))
    (hint : Integrable (fun g => Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y) * T *
      (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))ᴴ) μ) (g : H) :
    Commute (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y)) (referenceTwirl μ U T) := by
  have hunit : (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))ᴴ *
      Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y) = 1 := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, one_mul,
      ← Matrix.star_eq_conjTranspose,
      (Matrix.mem_unitaryGroup_iff').mp (U g).2, one_kronecker_one]
  have h := congrArg (fun M => M * Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))
    (referenceTwirl_conj μ U T hint g)
  simpa only [Commute, SemiconjBy, mul_assoc, hunit, mul_one] using h

/-- A reference twirl preserves right support on an invariant projection. -/
theorem referenceTwirl_mul_eq {H : Type*} [MeasurableSpace H]
    (μ : Measure H) (U : H → Matrix.unitaryGroup Y ℂ) (T Q : Op (X × Y))
    (hint : Integrable (fun g => Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y) * T *
      (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))ᴴ) μ)
    (hQ : Q.IsHermitian) (hTQ : T * Q = T)
    (hcomm : ∀ g, Commute (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y)) Q) :
    referenceTwirl μ U T * Q = referenceTwirl μ U T := by
  let L := (LinearMap.mulRight ℂ Q).toContinuousLinearMap
  change L (∫ g, _ ∂μ) = ∫ g, _ ∂μ
  refine (L.integral_comp_comm hint).symm.trans ?_
  apply integral_congr_ae
  filter_upwards [] with g
  change (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y) * T *
    (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))ᴴ) * Q = _
  have hstar := congrArg Matrix.conjTranspose (hcomm g).eq
  simp only [Matrix.conjTranspose_mul, hQ.eq] at hstar
  rw [mul_assoc, ← hstar, ← mul_assoc, mul_assoc _ T Q, hTQ]

/-- A restricted Haar moment with identity marginal is the locally normalized projection. -/
theorem referenceTwirl_eq_inverse_marginal_mul
    {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
     (μ : Measure H) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (U : H →* Matrix.unitaryGroup Y ℂ) (T Q : Op (X × Y))
    (hint : Integrable (fun g => Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y) * T *
      (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))ᴴ) μ)
    (hQ : Q.IsHermitian) (hTQ : T * Q = T)
    (hcomm : ∀ g, Commute (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y)) Q)
    (hlocal : HasLocalCommutant (fun g => (U g : Op Y)) Q)
    (hΩ : IsUnit (partialTraceRight Q)) (hT : partialTraceRight T = 1) :
    referenceTwirl μ U T = Matrix.kroneckerMap (· * ·) (partialTraceRight Q)⁻¹ (1 : Op Y) * Q := by
  rw [hlocal.eq_of_marginal hΩ (referenceTwirl_mul_eq μ U T Q hint hQ hTQ hcomm)
    (referenceTwirl_commute μ U T hint), partialTraceRight_referenceTwirl μ U T hint,
    hT, one_mul]

open scoped ComplexOrder MatrixOrder in
/-- A normalized local commutant twirl has the positive square-root sandwich form. -/
theorem referenceTwirl_eq_sqrt_sandwich
    {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
    (μ : Measure H) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (U : H →* Matrix.unitaryGroup Y ℂ) (T Q : Op (X × Y))
    (hint : Integrable (fun g => Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y) * T *
      (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y))ᴴ) μ)
    (hQ : Q.IsHermitian) (hTQ : T * Q = T)
    (hcomm : ∀ g, Commute (Matrix.kroneckerMap (· * ·) (1 : Op X) (U g : Op Y)) Q)
    (hlocal : HasLocalCommutant (fun g => (U g : Op Y)) Q)
    (K : Op X) (hK : K.PosDef) (hKi : K⁻¹ = partialTraceRight Q)
    (hKc : Commute (K ⊗ₖ (1 : Op Y)) Q) (hT : partialTraceRight T = 1) :
    referenceTwirl μ U T = (CFC.sqrt K ⊗ₖ (1 : Op Y)) * Q *
      (CFC.sqrt K ⊗ₖ (1 : Op Y)) := by
  let := hK.isUnit.invertible
  have hΩ : IsUnit (partialTraceRight Q) := hKi ▸ hK.inv.isUnit
  rw [referenceTwirl_eq_inverse_marginal_mul μ U T Q hint hQ hTQ hcomm hlocal hΩ hT,
    ← hKi, Matrix.inv_inv_of_invertible]
  have hs := Matrix.sqrt_commute hKc
  rw [hK.posSemidef.sqrt_kronecker Matrix.PosSemidef.one, CFC.sqrt_one] at hs
  symm
  rw [Matrix.mul_assoc, ← hs.eq, ← Matrix.mul_assoc, ← mul_kronecker_mul,
    mul_one, CFC.sqrt_mul_sqrt_self K hK.posSemidef.nonneg]

end Quantum.Symmetry
