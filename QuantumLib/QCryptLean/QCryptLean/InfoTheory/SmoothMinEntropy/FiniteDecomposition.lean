import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Math.Analysis.ConvexHull
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Finite Decomposition -/


noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Quantum.Operators MeasureTheory
open scoped ComplexOrder MatrixOrder ENNReal
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

private local instance {Q : Type*} [Fintype Q] : ContinuousENorm (Op Q) :=
  SeminormedAddGroup.toContinuousENorm
private local instance {X Q : Type*} [Fintype X] [Fintype Q] :
    ContinuousENorm (X → Op Q) := SeminormedAddGroup.toContinuousENorm
private local instance {X Q : Type*} [Fintype X] [Fintype Q] :
    ESeminormedAddMonoid (X → Op Q) :=
  (NormedAddGroup.toENormedAddMonoid (F := X → Op Q)).toESeminormedAddMonoid

/-- A restricted continuous CQ integral is a finite subconvex combination of supported points. -/
theorem integralRestrict_eq_finite_subConvexCombination
    {A Q X : Type*} [Fintype A] [Fintype Q] [Fintype X]
    (μ : Quantum.DeFinetti.DensityMeasure A)
    (f : DensityOp A → CQState X Q)
    (goodSet : Set (DensityOp A))
    (hMeas : MeasurableSet goodSet) (hClosed : IsClosed goodSet)
    (hcont : ∀ x : X, Continuous (fun τ : DensityOp A => ((f τ).stateMap x).toOp))
    (P : Set (DensityOp A)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P) :
    ∃ (N : ℕ) (p : Fin N → ℝ) (ψ : Fin N → DensityOp A),
      (∀ z, 0 ≤ p z) ∧ (∑ z, p z ≤ 1) ∧ (∀ z, ψ z ∈ goodSet) ∧ (∀ z, ψ z ∈ P) ∧
      (∀ (x : X) (i j : Q),
        (∫ τ in goodSet, ((f τ).stateMap x).toOp i j ∂μ.measure)
          = ∑ z, (p z : ℂ) • ((f (ψ z)).stateMap x).toOp i j) := by
  classical
  have hprob : IsProbabilityMeasure μ.measure := μ.isProbability
  set F : DensityOp A → (X → Op Q) := fun τ x => ((f τ).stateMap x).toOp with hFdef
  have hFcont : Continuous F := continuous_pi hcont
  have hGoodCompact : IsCompact goodSet :=
    hClosed.isCompact
  have hPgoodCompact : IsCompact (goodSet ∩ P) :=
    (hClosed.inter hP_closed).isCompact
  have hImgCompact : IsCompact (F '' (goodSet ∩ P)) := hPgoodCompact.image hFcont
  have hHullClosed : IsClosed (convexHull ℝ (F '' (goodSet ∩ P))) :=
    (IsCompact.convexHull hImgCompact).isClosed
  have hFint_restrict : Integrable F (μ.measure.restrict goodSet) :=
    ContinuousOn.integrableOn_compact hGoodCompact hFcont.continuousOn
  by_cases hzero : μ.measure goodSet = 0
  · refine ⟨0, fun _ => 0, fun z => z.elim0, fun z => z.elim0, by simp, fun z => z.elim0,
      fun z => z.elim0, ?_⟩
    intro x i j
    rw [MeasureTheory.setIntegral_measure_zero _ hzero]
    simp
  · -- positive-mass branch
    set m : ℝ := (μ.measure goodSet).toReal with hm
    have hmne_top : μ.measure goodSet ≠ ∞ := measure_ne_top _ _
    have hmpos : 0 < m := by rw [hm]; exact ENNReal.toReal_pos hzero hmne_top
    have hmle : m ≤ 1 := by
      rw [hm]
      have hle : μ.measure goodSet ≤ 1 := by
        calc μ.measure goodSet ≤ μ.measure Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      calc (μ.measure goodSet).toReal ≤ (1 : ℝ≥0∞).toReal :=
            ENNReal.toReal_mono (by norm_num) hle
        _ = 1 := by norm_num
    set ν : Measure (DensityOp A) :=
      (μ.measure goodSet)⁻¹ • μ.measure.restrict goodSet with hνdef
    have hνprob : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hzero
    have hcinv_ne_zero : (μ.measure goodSet)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hmne_top
    have hcinv_ne_top : (μ.measure goodSet)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hzero
    have hFint_ν : Integrable F ν := by
      rw [hνdef]
      exact (MeasureTheory.integrable_smul_measure (f := F)
        (μ := μ.measure.restrict goodSet)
        hcinv_ne_zero hcinv_ne_top).mpr hFint_restrict
    set Y : X → Op Q := ∫ τ in goodSet, F τ ∂μ.measure with hYdef
    have hae : ∀ᵐ τ ∂ν, F τ ∈ convexHull ℝ (F '' (goodSet ∩ P)) := by
      rw [hνdef]
      refine MeasureTheory.Measure.ae_smul_measure ?_ _
      filter_upwards [MeasureTheory.ae_restrict_mem hMeas,
        MeasureTheory.ae_restrict_of_ae hP_ae] with τ hτ hτP
      exact subset_convexHull ℝ _ (Set.mem_image_of_mem F ⟨hτ, hτP⟩)
    have hmem : (∫ τ, F τ ∂ν) ∈ convexHull ℝ (F '' (goodSet ∩ P)) :=
      Convex.integral_mem (convex_convexHull ℝ _) hHullClosed hae hFint_ν
    obtain ⟨σ, hσfin, weq, zpt, hw0, hwsum, hzmem, hcomb⟩ :=
      mem_convexHull_iff_exists_fintype.mp hmem
    let : Fintype σ := hσfin
    choose ψ0 hψ0mem hψ0eq using hzmem
    have hintν : (∫ τ, F τ ∂ν) = m⁻¹ • Y := by
      rw [hνdef, MeasureTheory.integral_smul_measure, ENNReal.toReal_inv]
    have hYeq : Y = ∑ s, (m * weq s) • F (ψ0 s) := by
      have hY0 : Y = m • (∫ τ, F τ ∂ν) := by
        rw [hintν, smul_smul, mul_inv_cancel₀ (ne_of_gt hmpos), one_smul]
      rw [hY0, ← hcomb, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [smul_smul, hψ0eq s]
    have hYentry : ∀ (x : X) (i j : Q),
        Y x i j = ∫ τ in goodSet, F τ x i j ∂μ.measure := by
      intro x i j
      set L : (X → Op Q) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
        { toFun := fun g => g x i j, map_add' := fun a b => rfl, map_smul' := fun c a => rfl }
        with hLdef
      have hcomm := ContinuousLinearMap.integral_comp_comm L hFint_restrict
      exact hcomm.symm
    have hentry_σ : ∀ (x : X) (i j : Q),
        Y x i j = ∑ s, (↑(m * weq s) : ℂ) • ((f (ψ0 s)).stateMap x).toOp i j := by
      intro x i j
      rw [hYeq]
      simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, hFdef]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Complex.real_smul, smul_eq_mul]
    set e : Fin (Fintype.card σ) ≃ σ := (Fintype.equivFin σ).symm with hedef
    refine ⟨Fintype.card σ, fun z => m * weq (e z), fun z => ψ0 (e z), ?_, ?_, ?_, ?_, ?_⟩
    · exact fun z => mul_nonneg hmpos.le (hw0 (e z))
    · calc ∑ z, m * weq (e z) = ∑ s, m * weq s := Equiv.sum_comp e (fun s => m * weq s)
        _ = m * ∑ s, weq s := (Finset.mul_sum _ _ _).symm
        _ = m * 1 := by rw [hwsum]
        _ = m := mul_one m
        _ ≤ 1 := hmle
    · exact fun z => (hψ0mem (e z)).1
    · exact fun z => (hψ0mem (e z)).2
    · intro x i j
      rw [show (∫ τ in goodSet, ((f τ).stateMap x).toOp i j ∂μ.measure) = Y x i j from
        (hYentry x i j).symm, hentry_σ x i j]
      exact (Equiv.sum_comp e
        (fun s => (↑(m * weq s) : ℂ) • ((f (ψ0 s)).stateMap x).toOp i j)).symm


end InfoTheory.SmoothMinEntropy
