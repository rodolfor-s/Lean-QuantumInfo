import QCryptLean.InfoTheory.SmoothMinEntropy.Bipartite
import QCryptLean.InfoTheory.SmoothMinEntropy.BipartiteRegularity
import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementAlgebra
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementChannel
import QCryptLean.InfoTheory.SmoothMinEntropy.MeasurementReferenceBound
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Guarded min-entropy transport under coherent measurement

The reference domain keeps its feasibility guard. Positive domination scales are
compared before applying the decreasing negative logarithm in base two.
-/
noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators Quantum.Channels Quantum.Metrics
open scoped Kronecker ComplexOrder MatrixOrder
open _root_.InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]

/-- Measurement transport multiplies each feasible reference scale by the overlap bound. -/
theorem isDmaxFeasible_measDilateTransport_of_feasible
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (τ : SubDensityOp (A × ((A × A) × B))) (σ : Op ((A × A) × B))
    (hσ : σ.PosSemidef) {s : ℝ} (ht : IsDmaxFeasible τ.toOp ((1 : Op A) ⊗ₖ σ) s) :
    IsDmaxFeasible (measDilateTransport P Q τ).toOp
      ((1 : Op A) ⊗ₖ partialTraceLeft σ) (s * overlapConst P Q) := by
  refine ⟨mul_nonneg ht.1 (overlapConst_nonneg P Q), ?_⟩
  have hs : (0 : ℂ) ≤ (s : ℂ) := Complex.zero_le_real.mpr ht.1
  have hp := (opLe_iff_posSemidef_sub τ.isHermitian
    ((PosSemidef.one.kronecker hσ).smul hs).isHermitian).mp ht.2
  have hm := (isCompletelyPositive_measTransportMap P Q).posSemidef hp
  rw [map_sub, map_smul] at hm
  apply opLe_of_posSemidef_sub
  apply Matrix.le_iff.mp
  change measTransportMap P Q τ.toOp ≤ _
  calc
    _ ≤ (s : ℂ) • measTransportMap P Q ((1 : Op A) ⊗ₖ σ) := Matrix.le_iff.mpr hm
    _ ≤ (s : ℂ) • ((overlapConst P Q : ℂ) • ((1 : Op A) ⊗ₖ partialTraceLeft σ)) :=
      smul_le_smul_of_nonneg_left (measTransportMap_one_kronecker_le P Q σ hσ) hs
    _ = _ := by rw [smul_smul, Complex.ofReal_mul]

/-- The infimum of transported scales is at most the overlap times the original infimum. -/
theorem dmaxScale_measDilateTransport_le
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (τ : SubDensityOp (A × ((A × A) × B))) (σ : Op ((A × A) × B))
    (hσ : σ.PosSemidef) (hZ : HasDmaxScale τ.toOp ((1 : Op A) ⊗ₖ σ)) :
    dmaxScale (measDilateTransport P Q τ).toOp ((1 : Op A) ⊗ₖ partialTraceLeft σ) ≤
      overlapConst P Q * dmaxScale τ.toOp ((1 : Op A) ⊗ₖ σ) := by
  have hc := overlapConst_pos P Q
  have hh : dmaxScale (measDilateTransport P Q τ).toOp
      ((1 : Op A) ⊗ₖ partialTraceLeft σ) / overlapConst P Q ≤
      dmaxScale τ.toOp ((1 : Op A) ⊗ₖ σ) := by
    apply le_csInf hZ
    intro s hsf
    rw [div_le_iff₀ hc]
    exact dmaxScale_le_of_isDmaxFeasible _ _
      (isDmaxFeasible_measDilateTransport_of_feasible P Q τ σ hσ hsf)
  rw [div_le_iff₀ hc] at hh
  simpa only [mul_comm] using hh

/-- Guarded optimized entropy transports when the input and its image are nonzero. -/
theorem bipartiteMinEntropyOptReal_measDilateTransport_ge [Nonempty B]
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (τ : SubDensityOp (A × ((A × A) × B)))
    (hτ : τ.toOp ≠ 0) (hΞτ : (measDilateTransport P Q τ).toOp ≠ 0) :
    bipartiteMinEntropyOptReal τ ≤
      bipartiteMinEntropyOptReal (measDilateTransport P Q τ) - preparationQuality P Q := by
  apply csSup_le (nonempty_bipartiteMinEntropySet τ)
  rintro h ⟨σ, hσ, rfl⟩
  have hf : HasDmaxScale (measDilateTransport P Q τ).toOp
      ((1 : Op A) ⊗ₖ σ.partialTraceLeft.toOp) := by
    obtain ⟨s, hs⟩ := hσ
    exact ⟨s * overlapConst P Q,
      isDmaxFeasible_measDilateTransport_of_feasible P Q τ σ.toOp σ.posSemidef hs⟩
  have hposZ := dmaxScale_pos_of_ne_zero τ hτ σ hσ
  have hposX := dmaxScale_pos_of_ne_zero (measDilateTransport P Q τ) hΞτ σ.partialTraceLeft hf
  have hc := overlapConst_pos P Q
  have hkey := dmaxScale_measDilateTransport_le P Q τ σ.toOp σ.posSemidef hσ
  have hlog : Real.log (dmaxScale (measDilateTransport P Q τ).toOp
      ((1 : Op A) ⊗ₖ σ.partialTraceLeft.toOp)) ≤
      Real.log (dmaxScale τ.toOp ((1 : Op A) ⊗ₖ σ.toOp)) + Real.log (overlapConst P Q) := by
    rw [← Real.log_mul (ne_of_gt hposZ) (ne_of_gt hc)]
    apply Real.log_le_log hposX
    simpa only [SubDensityOp.partialTraceLeft_toOp, mul_comm] using hkey
  have hlift : bipartiteMinEntropyReal τ σ + preparationQuality P Q ≤
      bipartiteMinEntropyReal (measDilateTransport P Q τ) σ.partialTraceLeft := by
    unfold bipartiteMinEntropyReal preparationQuality
    rw [← add_div, div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    linarith
  have hopt : bipartiteMinEntropyReal (measDilateTransport P Q τ) σ.partialTraceLeft ≤
      bipartiteMinEntropyOptReal (measDilateTransport P Q τ) :=
    le_csSup (bddAbove_bipartiteMinEntropySet _) ⟨σ.partialTraceLeft, hf, rfl⟩
  linarith

end InfoTheory.SmoothMinEntropy
