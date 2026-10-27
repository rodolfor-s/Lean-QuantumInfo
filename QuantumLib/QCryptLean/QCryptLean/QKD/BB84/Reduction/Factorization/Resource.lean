import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.BoundaryKeyLayout.Hom
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.Instrument.WeightedChoice
import QCryptLean.Math.FiniteEmbedding.SubsetPerm
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.CompleteOutput
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Reduction.Factorization.Reconstruction
import QCryptLean.QKD.BB84.Reduction.Preprocessor
import QCryptLean.QKD.BB84.Reduction.RetainedExperiment
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.Sampling.TotalKernels
import QCryptLean.QKD.BB84.TailTranscript
import QCryptLean.QKD.OutputLayout
import QCryptLean.QKD.Protocol
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Resource -/


open Quantum.Operators (Op)

open Quantum.Channels (
  mapTensorId
  mapTensorId_apply
  mapTensorId_trace_block)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Reduction

open LOCC QKD.BB84 QKD.BB84.Reduction
open QKD.BB84.Measurement QKD.BB84.Sampling
open QKD.BB84.FiniteKey


/-- The retained-analysis resource applied in every block of the complete comparison control. -/
abbrev retainedControlResource (N nK mZ mX ell ellEV leakEC : ℕ) :
    Op (ReconstructionInput N nK mZ mX ell ellEV leakEC) →ₗ[ℂ]
      Op (ReconstructionInput N nK mZ mX ell ellEV leakEC) :=
  mapTensorId (retainedAnalysisResource nK mZ mX ell ellEV leakEC) (ComparisonControl N (nK + mZ +
    mX))

/-- **On one success slice the blockwise retained resource is the retained-tail resource.**

Read at the success input coordinates of a retained subset `S` and an announced permutation `pi`,
the retained resource in every control block is the retained-tail ideal of the same slice. -/
theorem retainedControlResource_successInput
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (rho : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) :
    (retainedControlResource N nK mZ mX ell ellEV leakEC rho).submatrix
        (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi)
        (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi) =
      (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout.ideal
        (rho.submatrix (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi)
          (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi)) := by
  ext u v
  have h := (retainedAnalysisFibreHom nK mZ mX ell ellEV leakEC pi).ideal_apply
    ((rho.submatrix (fun a => (a, Sum.inl S)) (fun a => (a, Sum.inl S))).submatrix
      (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC)
      (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC)) u v
  rw [coe_retainedAnalysisFibreHom] at h
  rw [Matrix.submatrix_apply, mapTensorId_apply]
  exact (retainedAnalysisResource_entry nK mZ mX ell ellEV leakEC _ _ _).trans h

/-- **The complete-output resource commutes with one success branch of the reconstruction.** -/
theorem reconstructionSuccessKraus_resource_intertwines
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S pi)
    (rho : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) :
    (QKD.BB84.outputLayout N nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal
        (Matrix.conjLinearMap
          (reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi omega) rho) =
      Matrix.conjLinearMap
        (reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi omega)
        (retainedControlResource N nK mZ mX ell ellEV leakEC rho) := by
  have hsupport : ∀ (M : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) y z,
      (y ∉ Set.range (successCompleteOutputHom N nK mZ mX ell ellEV leakEC omega.1
          (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega)) ∨
        z ∉ Set.range (successCompleteOutputHom N nK mZ mX ell ellEV leakEC omega.1
          (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega))) →
      Matrix.conjLinearMap
          (reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi omega) M y z =
        0 := by
    rw [coe_successCompleteOutputHom]
    rintro M y z (hy | hz)
    · exact Matrix.conjLinearMap_apply_eq_zero_of_row_left _ M
        (reconstructionSuccessKraus_row_eq_zero N nK mZ mX ell ellEV leakEC pA pB S pi omega
          hy) z
    · exact Matrix.conjLinearMap_apply_eq_zero_of_row_right _ M y
        (reconstructionSuccessKraus_row_eq_zero N nK mZ mX ell ellEV leakEC pA pB S pi omega
          hz)
  have hpull : ∀ M : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC),
      (Matrix.conjLinearMap
          (reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi omega) M).submatrix
          (successCompleteOutputHom N nK mZ mX ell ellEV leakEC omega.1
            (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega))
          (successCompleteOutputHom N nK mZ mX ell ellEV leakEC omega.1
            (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega)) =
        (star (Instrument.weightedChoiceScale (totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi)) omega.1) *
            Instrument.weightedChoiceScale (totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi)) omega.1) •
          M.submatrix (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi)
            (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi) := by
    intro M
    rw [coe_successCompleteOutputHom]
    exact Matrix.conjLinearMap_submatrix_of_row_eq_single _ M _ _ _
      (reconstructionSuccessKraus_row N nK mZ mX ell ellEV leakEC pA pB S pi omega)
  rw [BoundaryKeyLayout.Hom.ideal_eq_iff _ (hsupport rho) (hsupport _), hpull, hpull, map_smul,
    retainedControlResource_successInput]

/-- **The complete-output resource commutes with one shortage branch of the reconstruction.** -/
theorem reconstructionShortageKraus_resource_intertwines
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX)) (omega : FailureControlSupport N nK mZ mX pA pB j)
    (rho : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) :
    (QKD.BB84.outputLayout N nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal
        (∑ r, Matrix.conjLinearMap
          (reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r omega) rho) =
      ∑ r, Matrix.conjLinearMap
        (reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r omega)
        (retainedControlResource N nK mZ mX ell ellEV leakEC rho) := by
  have hsum : ∀ M : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC),
      ∑ r, Matrix.conjLinearMap
          (reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r omega) M =
        Matrix.single
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega.1
            (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega))
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega.1
            (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega))
          (Instrument.weightedChoiceScale (totalFailureControlKernel N nK mZ mX pA pB j) omega.1 *
            (∑ r, M (r, Sum.inr j) (r, Sum.inr j)) *
            star (Instrument.weightedChoiceScale (totalFailureControlKernel N nK mZ mX pA pB j)
              omega.1)) := by
    intro M
    simp_rw [reconstructionShortageKraus_eq_single]
    refine (Finset.sum_congr rfl (fun r _ => Matrix.conjLinearMap_single _ _ _ M)).trans ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    generalize shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega.1
      (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega) = y
    exact (map_sum (Matrix.singleAddMonoidHom (α := ℂ) y y) _ _).symm
  rw [hsum, hsum, BoundaryKeyLayout.ideal_single_of_abort _ rfl
      (shortageCompleteOutput_disposition N nK mZ mX ell ellEV leakEC omega.1
        (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega))]
  have htrace := mapTensorId_trace_block
      (retainedAnalysisResource nK mZ mX ell ellEV leakEC)
      (isChannel_retainedAnalysisResource nK mZ mX ell ellEV leakEC).2
      rho (Sum.inr j : ComparisonControl N (nK + mZ + mX))
  exact congrArg (fun z : ℂ => Matrix.single _ _
    (Instrument.weightedChoiceScale (totalFailureControlKernel N nK mZ mX pA pB j) omega.1 *
      z * star (Instrument.weightedChoiceScale
        (totalFailureControlKernel N nK mZ mX pA pB j) omega.1))) htrace.symm

/-- The complete-output resource commutes with the whole reconstruction channel. -/
theorem reconstructionInstrument_resource_intertwines
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (rho : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) :
    (QKD.BB84.outputLayout N nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal
        ((reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel rho) =
      (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel
        (retainedControlResource N nK mZ mX ell ellEV leakEC rho) := by
  rw [reconstructionInstrument_channel_apply, reconstructionInstrument_channel_apply,
    map_add, map_sum, map_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun a _ => ?_)
    (Finset.sum_congr rfl fun j _ => ?_)
  · exact reconstructionSuccessKraus_resource_intertwines N nK mZ mX ell ellEV leakEC pA pB
      a.1 a.2.1 a.2.2 rho
  · rw [map_sum]
    exact Finset.sum_congr rfl fun omega _ =>
      reconstructionShortageKraus_resource_intertwines N nK mZ mX ell ellEV leakEC pA pB
        j omega rho

/-- Reconstruction intertwines the physical program's key resource with the retained resource.
The inverse structural boundary equivalence restores the actual program output. -/
theorem reconstruction_resource_intertwines
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    let A := QKD.BB84.protocol pA pB N nK mZ mX ell ellEV leakEC ec delta Q
    let e := constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q
    let post := (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap.comp
      (reconstruction N nK mZ mX ell ellEV leakEC pA pB)
    A.resource.comp post = post.comp
      (retainedControlResource N nK mZ mX ell ellEV leakEC) := by
  intro A e post
  apply LinearMap.ext
  intro rho
  apply (Matrix.reindexLinearEquiv ℂ ℂ e e).injective
  have h := constructionSpaceEquiv_resource pA pB N nK mZ mX ell ellEV leakEC ec delta Q
    (post rho)
  change Matrix.reindex e e (A.resource (post rho)) =
    Matrix.reindex e e (post (retainedControlResource N nK mZ mX ell ellEV leakEC rho))
  change _ = Matrix.reindex e e (A.resource (post rho)) at h
  rw [← h]
  have he (M : Op (ReconstructionOutput N nK mZ mX ell ellEV leakEC)) :
      Matrix.reindex e e (Matrix.reindex e.symm e.symm M) = M := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
  change _ = Matrix.reindex e e
    (Matrix.reindex e.symm e.symm (reconstruction N nK mZ mX ell ellEV leakEC pA pB
      (retainedControlResource N nK mZ mX ell ellEV leakEC rho)))
  rw [he]
  change (QKD.BB84.outputLayout N nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal
    (Matrix.reindex e e (Matrix.reindex e.symm e.symm
      (reconstruction N nK mZ mX ell ellEV leakEC pA pB rho))) = _
  rw [he]
  exact reconstructionInstrument_resource_intertwines N nK mZ mX ell ellEV leakEC pA pB rho

end QKD.BB84.Reduction
