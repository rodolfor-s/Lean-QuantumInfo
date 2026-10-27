import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQ
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Integral
import QCryptLean.Math.LinearAlgebra.Matrix.Reindex
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.PrincipalSubmatrix
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Paired

/-! # Sifted accept blocks and their reference marginals

The sift acts on the signal register. Discarding a reference therefore commutes with
both the sifted pre-channel and the outcome block extraction, including after the
fail-closed parameter-estimation filter. All retained registers are arbitrary finite types.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels
open Quantum.DeFinetti Quantum.Symmetry
open InfoTheory.SmoothMinEntropy QKD.BB84.Model QKD.BB84.Measurement Matrix
open scoped Kronecker

variable (E : Type*) [Fintype E] [DecidableEq E]
variable {R S : Type*} [Fintype R] [Fintype S]

omit [Fintype E] [DecidableEq E] [Fintype R] in
/-- Discarding the last reference factor commutes with outcome block extraction. -/
lemma sifted_partialTraceRight_trailing_submatrix_tauEmbedding {n : ℕ}
    (M : Op ((Signals n × E) × (R × S))) (ω : Signals n) :
    partialTraceRight (reindex (Equiv.prodAssoc E R S).symm (Equiv.prodAssoc E R S).symm
      (M.submatrix (tauOutcomeEveRefEmbedding ω) (tauOutcomeEveRefEmbedding ω))) =
      (partialTraceRight (reindex (Equiv.prodAssoc (Signals n × E) R S).symm
        (Equiv.prodAssoc (Signals n × E) R S).symm M)).submatrix
          (tauOutcomeEveRefEmbedding ω) (tauOutcomeEveRefEmbedding ω) := rfl

open scoped Classical in
/-- Apply the pre-channel and sift while retaining an arbitrary reference. -/
def siftedTauPreOutputDensity {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (τ : DensityOp (Signals n × R)) :
    DensityOp ((Signals n × E) × R) :=
  UnitaryOp.evolve (⟨(siftedRotation n peSel xSel ⊗ₖ (1 : Op E)) ⊗ₖ (1 : Op R),
    mem_unitaryGroup_iff'.mpr (by
      rw [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
        conjTranspose_mul_siftedRotation_tensor_one, one_mul, one_kronecker_one])⟩ :
          UnitaryOp ((Signals n × E) × R)) (tauOutputDensity E pre hpre τ)

/-- The Eve/reference block selected by the measured signal string. -/
def siftedTauEveRefConditioned {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (τ : DensityOp (Signals n × R))
    (ω : Signals n) : SubDensityOp (E × R) :=
  (siftedTauPreOutputDensity E pre hpre peSel xSel τ).toSubDensityOp.submatrix
    (tauOutcomeEveRefEmbedding ω) (tauOutcomeEveRefEmbedding_injective ω)

/-- The sifted conditional blocks exhaust the total trace. -/
theorem sum_trace_siftedTauEveRefConditioned {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (τ : DensityOp (Signals n × R)) :
    ∑ ω, (siftedTauEveRefConditioned E pre hpre peSel xSel τ ω).trace = 1 := by
  simpa only [siftedTauEveRefConditioned, SubDensityOp.submatrix, SubDensityOp.trace,
    Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Complex.re_sum, DensityOp.toSubDensityOp]
    using tauOutcomeEveRefEmbedding_diag_sum_eq_one
      (siftedTauPreOutputDensity E pre hpre peSel xSel τ)

/-- Discarding a trailing spectator commutes with the complete sifted conditional experiment. -/
theorem siftedTauEveRefConditioned_partialTraceRight_assoc {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (τ : DensityOp ((Signals n × R) × S)) (ω : Signals n) :
    partialTraceRight (reindex (Equiv.prodAssoc E R S).symm (Equiv.prodAssoc E R S).symm
      (siftedTauEveRefConditioned E pre hpre peSel xSel
        (τ.reindex (Equiv.prodAssoc _ _ _)) ω).toOp) =
      (siftedTauEveRefConditioned E pre hpre peSel xSel τ.partialTraceRight ω).toOp := by
  classical
  let : DecidableEq (Signals n) := Classical.decEq _
  let : DecidableEq (R × S) := Classical.decEq _
  let U := siftedRotation n peSel xSel ⊗ₖ (1 : Op E)
  have hu : reindex (Equiv.prodAssoc (Signals n × E) R S).symm
      (Equiv.prodAssoc (Signals n × E) R S).symm (U ⊗ₖ (1 : Op (R × S))) =
        (U ⊗ₖ (1 : Op R)) ⊗ₖ (1 : Op S) := by
    ext i j
    simp only [reindex_apply, submatrix_apply, kroneckerMap_apply, one_apply]
    split_ifs <;> simp_all
  change partialTraceRight (reindex _ _
    ((siftedTauPreOutputDensity E pre hpre peSel xSel
      (τ.reindex (Equiv.prodAssoc _ _ _))).toOp.submatrix
        (tauOutcomeEveRefEmbedding ω) (tauOutcomeEveRefEmbedding ω))) = _
  rw [sifted_partialTraceRight_trailing_submatrix_tauEmbedding]
  change _ = (siftedTauPreOutputDensity E pre hpre peSel xSel τ.partialTraceRight).toOp.submatrix
    (tauOutcomeEveRefEmbedding ω) (tauOutcomeEveRefEmbedding ω)
  apply congrArg (fun M : Op ((Signals n × E) × R) =>
    M.submatrix (tauOutcomeEveRefEmbedding ω) (tauOutcomeEveRefEmbedding ω))
  change partialTraceRight (reindex _ _
    ((U ⊗ₖ (1 : Op (R × S))) * mapTensorId pre (R × S)
      (reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _) τ.toOp) *
        (U ⊗ₖ (1 : Op (R × S)))ᴴ)) = _
  rw [reindex_mul, reindex_mul, ← conjTranspose_reindex, hu,
    conjTranspose_kronecker, conjTranspose_one, partialTraceRight_kronecker_one_sandwich,
    partialTraceRight_mapTensorId_assoc]
  rfl

/-- The normalized CQ state of the sifted reference experiment. -/
def siftedTauPostMeasurementNormalizedCQState {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (τ : DensityOp (Signals n × R)) :
    NormalizedCQState (Signals n) (E × R) where
  stateMap := siftedTauEveRefConditioned E pre hpre peSel xSel τ
  weight_le_one := (sum_trace_siftedTauEveRefConditioned E pre hpre peSel xSel τ).le
  weight_eq_one := sum_trace_siftedTauEveRefConditioned E pre hpre peSel xSel τ

/-- The sifted reference experiment's parameter-estimation accept weight. -/
def siftedEveVisiblePEPassWeight {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (τ : DensityOp (Signals n × R)) : ℝ :=
  ∑ ω, ((postMeasurementCQSiftedLocalPEPassFilter (E × R) peSel xSel Q δ
    (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel τ)).stateMap ω).trace

/-- The output marginal is the sifted pre-channel applied to the input marginal. -/
theorem siftedTauPreOutputDensity_partialTraceRight_eq {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (τ : DensityOp (Signals n × R)) :
    partialTraceRight (siftedTauPreOutputDensity E pre hpre peSel xSel τ).toOp =
      (siftedRotatedPreOutput E pre hpre peSel xSel τ.partialTraceRight).toOp := by
  classical
  change partialTraceRight (((siftedRotation n peSel xSel ⊗ₖ (1 : Op E)) ⊗ₖ (1 : Op R)) *
    mapTensorId pre R τ.toOp *
      ((siftedRotation n peSel xSel ⊗ₖ (1 : Op E)) ⊗ₖ (1 : Op R))ᴴ) = _
  rw [conjTranspose_kronecker, conjTranspose_one, partialTraceRight_kronecker_one_sandwich,
    partialTraceRight_mapTensorId]
  rfl

/-- The conditioned marginal is the corresponding Eve block of the input marginal. -/
theorem partialTraceRight_conditioned_eq {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (τ : DensityOp (Signals n × R)) (ω : Signals n) :
    partialTraceRight (siftedTauEveRefConditioned E pre hpre peSel xSel τ ω).toOp =
      (siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight ω).toOp := by
  change (partialTraceRight (siftedTauPreOutputDensity E pre hpre peSel xSel τ).toOp).submatrix
    (fun a => (ω, a)) (fun a => (ω, a)) = _
  rw [siftedTauPreOutputDensity_partialTraceRight_eq]
  rfl

/-- At a CKR purification the conditioned marginal is the CKR experiment's Eve block. -/
theorem partialTraceRight_conditioned_ckr_eq {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (τ : DensityOp (Signals n × R))
    (hτ : IsCKRDeFinettiPurification τ) (ω : Signals n) :
    partialTraceRight (siftedTauEveRefConditioned E pre hpre peSel xSel τ ω).toOp =
      (siftedEveConditioned E pre hpre peSel xSel (ckrDeFinettiState Signal n) ω).toOp := by
  rw [partialTraceRight_conditioned_eq, hτ.marginal]

omit [DecidableEq E] in
/-- A common classical filter preserves blockwise marginal identities. -/
theorem partialTraceRight_passFilter_stateMap {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (ρER : CQState (Signals n) (E × R)) (ρE : CQState (Signals n) E)
    (hblocks : ∀ ω, partialTraceRight (ρER.stateMap ω).toOp = (ρE.stateMap ω).toOp)
    (ω : Signals n) :
    partialTraceRight
      ((postMeasurementCQSiftedLocalPEPassFilter (E × R) peSel xSel Q δ ρER).stateMap ω).toOp =
      ((postMeasurementCQSiftedLocalPEPassFilter E peSel xSel Q δ ρE).stateMap ω).toOp := by
  cases h : siftedLocalPETestPassed peSel xSel δ Q ω <;>
    simp [postMeasurementCQSiftedLocalPEPassFilter, CQState.filterKeep, h,
      SubDensityOp.zero, hblocks]

/-- At the CKR mixture, accepted reference blocks trace down to the accepted Eve blocks. -/
theorem partialTraceRight_accepted_stateMap {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (μ : DensityMeasure Signal)
    (hμ : integralTensorPowerDensity n μ = ckrDeFinettiState Signal n) (Q δ : ℝ)
    (τ : DensityOp (Signals n × R)) (hτ : IsCKRDeFinettiPurification τ) (ω : Signals n) :
    partialTraceRight
      ((postMeasurementCQSiftedLocalPEPassFilter (E × R) peSel xSel Q δ
        (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel τ)).stateMap ω).toOp =
      ((siftedLocalPEAcceptedPostMeasurementCQState E pre hpre peSel xSel μ Q δ).stateMap
        ω).toOp := by
  apply partialTraceRight_passFilter_stateMap
  intro ω
  rw [hμ]
  exact partialTraceRight_conditioned_ckr_eq E pre hpre peSel xSel τ hτ ω

/-- Discarding the CKR reference preserves the parameter-estimation acceptance weight. -/
theorem eveVisible_acceptedWeight_eq {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (μ : DensityMeasure Signal)
    (hμ : integralTensorPowerDensity n μ = ckrDeFinettiState Signal n) (Q δ : ℝ)
    (τ : DensityOp (Signals n × R)) (hτ : IsCKRDeFinettiPurification τ) :
    siftedEveVisiblePEPassWeight E pre hpre peSel xSel Q δ τ =
      ∑ ω, ((siftedLocalPEAcceptedPostMeasurementCQState E pre hpre peSel xSel μ Q δ).stateMap
        ω).trace := by
  unfold siftedEveVisiblePEPassWeight
  apply Finset.sum_congr rfl
  intro ω _
  unfold SubDensityOp.trace
  rw [← trace_partialTraceRight, partialTraceRight_accepted_stateMap E pre hpre peSel xSel μ hμ
    Q δ τ hτ ω]

end QKD.BB84.FiniteKey
