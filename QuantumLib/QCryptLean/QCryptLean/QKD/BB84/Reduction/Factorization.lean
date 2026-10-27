import QCryptLean.QKD.BB84.CompleteOutput
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Reduction.Factorization.Real
import QCryptLean.QKD.BB84.Reduction.Factorization.Reconstruction
import QCryptLean.QKD.BB84.Reduction.Factorization.Resource
import QCryptLean.QKD.BB84.Reduction.Preprocessor
import QCryptLean.QKD.BB84.Reduction.QuotaShortage
import QCryptLean.QKD.BB84.Reduction.RetainedExperiment
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.Protocol
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.ConsumerBounds
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Operators.Basic

/-! # Factorization -/


open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Reduction

open LOCC QKD.BB84 QKD.BB84.Reduction
open QKD.BB84.Measurement QKD.BB84.Sampling
open QKD.BB84.FiniteKey


/-- Exact ideal factorization, reduced to the real factorization and resource intertwining. -/
theorem ideal_eq_retainedFactorizedIdeal
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    (QKD.BB84.protocol
      pA pB N nK mZ mX ell ellEV leakEC ec delta Q).ideal =
      retainedFactorizedIdeal
        pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q := by
  let A := QKD.BB84.protocol
    pA pB N nK mZ mX ell ellEV leakEC ec delta Q
  let e := constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q
  let Post := (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap.comp
    (reconstruction N nK mZ mX ell ellEV leakEC pA pB)
  let R := Quantum.Channels.mapTensorId
    (retainedAnalysisResource nK mZ mX ell ellEV leakEC)
    (ComparisonControl N (nK + mZ + mX))
  let L := retainedControlLift N (nK + mZ + mX)
    (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
    (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)
  let Pre := comparisonPre N nK mZ mX pA pB hN
  have hreal : A.real = Post.comp (L.comp Pre) := by
    exact real_eq_retainedFactorizedReal
      pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q
  have hcomm : A.resource.comp Post = Post.comp R := by
    exact reconstruction_resource_intertwines
      pA pB N nK mZ mX ell ellEV leakEC ec delta Q
  have hlift : R.comp L =
      retainedControlLift N (nK + mZ + mX)
        (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
        ((retainedAnalysisResource nK mZ mX ell ellEV leakEC).comp
          (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)) :=
    retainedControlLift_comp _ _ _ _ _ _
  change A.resource.comp A.real = _
  refine (congrArg (fun F => A.resource.comp F) hreal).trans ?_
  refine (LinearMap.comp_assoc (L.comp Pre) Post A.resource).symm.trans ?_
  refine (congrArg (fun F => F.comp (L.comp Pre)) hcomm).trans ?_
  refine (LinearMap.comp_assoc (L.comp Pre) R Post).trans ?_
  refine (congrArg (fun F => Post.comp F) (LinearMap.comp_assoc Pre L R).symm).trans ?_
  simpa only [retainedFactorizedIdeal, retainedAnalysisIdeal] using
    (congrArg (fun F => Post.comp (F.comp Pre)) hlift)

/-- Exact factorization of the physical real-minus-ideal map. -/
theorem difference_eq_retainedFactorizedDifference
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    (QKD.BB84.protocol
      pA pB N nK mZ mX ell ellEV leakEC ec delta Q).difference =
      retainedFactorizedDifference
        pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q := by
  rw [(QKD.BB84.protocol
    pA pB N nK mZ mX ell ellEV leakEC ec delta Q).difference_eq_real_sub_ideal]
  rw [real_eq_retainedFactorizedReal
      pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q,
    ideal_eq_retainedFactorizedIdeal
      pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q]
  simp only [retainedFactorizedReal, retainedFactorizedIdeal,
    retainedFactorizedDifference, retainedAnalysisDifference]
  rw [retainedControlLift_sub]
  conv_rhs =>
    rw [← LinearMap.comp_assoc, LinearMap.comp_sub, LinearMap.sub_comp]
  rfl

/-- For feasible quotas, the physical real-minus-ideal map has at most the diamond norm of the
retained-round difference. -/
theorem difference_diamondNorm_le_retained_of_le
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    Quantum.Channels.diamondNorm
        (QKD.BB84.protocol
          pA pB N nK mZ mX ell ellEV leakEC ec delta Q).difference ≤
      Quantum.Channels.diamondNorm
        (retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q) := by
  set Delta := retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q with hDelta
  have hHerm : ∀ M : Quantum.Operators.Op (Signals (nK + mZ + mX)),
      Delta Mᴴ = (Delta M)ᴴ :=
    retainedAnalysisDifference_preserves_conjTranspose
      nK mZ mX ell ellEV leakEC ec delta Q
  have hLiftHerm := retainedControlLift_preserves_conjTranspose
    N (nK + mZ + mX) (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
    Delta hHerm
  rw [difference_eq_retainedFactorizedDifference
    pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q]
  exact (Quantum.Channels.diamondNorm_comp_comp_le_of_isChannel
      ((Matrix.reindexLinearEquiv ℂ ℂ
        (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q).symm
        (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q).symm).toLinearMap.comp
        (reconstruction N nK mZ mX ell ellEV leakEC pA pB))
      ((Quantum.Channels.isChannel_reindex _).comp
        (isChannel_reconstruction N nK mZ mX ell ellEV leakEC pA pB))
      (retainedControlLift N (nK + mZ + mX)
        (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC) Delta)
      hLiftHerm
      (comparisonPre N nK mZ mX pA pB hN)
      (isChannel_comparisonPre N nK mZ mX pA pB hN)).trans
    (retainedControlLift_diamondNorm_le
      N (nK + mZ + mX) (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
      Delta hHerm)

/-- The coefficient-one physical-to-retained diamond-norm reduction, including the all-shortage
branch when the physical batch is too small for the quotas. -/
theorem difference_diamondNorm_le_retained
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    Quantum.Channels.diamondNorm
        (QKD.BB84.protocol
          pA pB N nK mZ mX ell ellEV leakEC ec delta Q).difference ≤
      Quantum.Channels.diamondNorm
        (retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q) := by
  by_cases hN : nK + mZ + mX ≤ N
  · exact difference_diamondNorm_le_retained_of_le
      pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q
  · have hgt : N < nK + mZ + mX := Nat.lt_of_not_ge hN
    have hzero := difference_eq_zero_of_totalQuota_gt
      pA pB N nK mZ mX ell ellEV leakEC hgt ec delta Q
    rw [hzero]
    rw [Quantum.Channels.diamondNorm_zero]
    exact Quantum.Channels.diamondNorm_nonneg _

end QKD.BB84.Reduction
