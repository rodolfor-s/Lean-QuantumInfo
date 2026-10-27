import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Instrument.Discard
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.Instrument.WeightedChoice
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Classical
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.CompleteOutput
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.Measurement.LatePublicControl
import QCryptLean.QKD.BB84.Measurement.LatePublicControl.BranchValues
import QCryptLean.QKD.BB84.Measurement.OutputLaw
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Measurement.SelectedRecords
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Reduction.Factorization.Reconstruction
import QCryptLean.QKD.BB84.Reduction.Preprocessor
import QCryptLean.QKD.BB84.Reduction.RetainedExperiment
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Disintegration
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.Sampling.TotalKernels
import QCryptLean.QKD.KeyEnd
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-! # Shortage -/


open Quantum.Operators (Op)

open Quantum.Channels
open Quantum.Symmetry (pairFunctions)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Reduction

open LOCC LOCC.TwoParty QKD.BB84 QKD.BB84.Reduction
open QKD.BB84.Measurement QKD.BB84.Sampling
open QKD.BB84.FiniteKey


/-- At a complete shortage output the reconstruction channel keeps only the totalized failure
kernel against the retained diagonal of the failure-control blocks. -/
private theorem reconstruction_shortage
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hshort : ¬ HasQuotas nK mZ mX omega)
    (mid : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) :
    reconstruction N nK mZ mX ell ellEV leakEC pA pB mid
        (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)
        (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) =
      ∑ j : Fin (nK + mZ + mX),
        ((totalFailureControlKernel N nK mZ mX pA pB j omega).toReal : ℂ) *
          ∑ r : RetainedAnalysisOutput nK mZ mX ell ellEV leakEC,
            mid
              (r, Sum.inr j) (r, Sum.inr j) := by
  have hsuccessRow
      (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (pi : Equiv.Perm (Fin (nK + mZ + mX)))
      (eta : SelectedControlSupport N nK mZ mX pA pB S pi)
      (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
      reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB
          (Sum.inl ⟨S, pi, eta⟩)
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) x = 0 := by
    change reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC
        pA pB S pi eta
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) x = 0
    unfold reconstructionSuccessKraus
    dsimp only
    split
    · rename_i hc
      exfalso
      have hrc := congrArg (fun y =>
        QKD.BB84.lateSelectionExitEquiv N nK mZ mX
          ((QKD.BB84.exitEquiv N nK mZ mX ell ellEV leakEC) y.1).1) hc.2.2
      rw [shortageCompleteOutput_rawControl] at hrc
      rw [successCompleteOutputEmbedding_exit] at hrc
      unfold successExitMap at hrc
      rw [Equiv.apply_symm_apply] at hrc
      have hrc' : omega = eta.1 := by
        exact hrc
      apply hshort
      rw [hrc']
      exact selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi eta
    · rfl
  let sigma := mid
  have hrow_of_control_ne
      (j : Fin (nK + mZ + mX))
      (r : RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
      (eta : FailureControlSupport N nK mZ mX pA pB j)
      (heta : eta.1 ≠ omega)
      (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
      reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB
          (Sum.inr ⟨j, r, eta⟩)
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) x = 0 := by
    change reconstructionShortageKraus N nK mZ mX ell ellEV leakEC
        pA pB j r eta
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) x = 0
    unfold reconstructionShortageKraus
    refine (Matrix.smul_apply _ _ _ _).trans ?_
    have hrow : shortageCompleteOutput N nK mZ mX ell ellEV leakEC eta.1
        (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j eta) ≠
        shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort := by
      intro heq
      have hrc := congrArg (fun y =>
        QKD.BB84.lateSelectionExitEquiv N nK mZ mX
          ((QKD.BB84.exitEquiv N nK mZ mX ell ellEV leakEC) y.1).1) heq
      rw [shortageCompleteOutput_rawControl,
        shortageCompleteOutput_rawControl] at hrc
      exact heta hrc
    exact (congrArg (fun z : ℂ => _ • z)
      (Matrix.single_apply_of_row_ne hrow
        ((r, Sum.inr j) : ReconstructionInput N nK mZ mX ell ellEV leakEC)
        x (1 : ℂ))).trans (smul_zero _)
  -- The right-hand side reads `sigma` on the diagonal.
  change _ = ∑ j : Fin (nK + mZ + mX),
    ((totalFailureControlKernel N nK mZ mX pA pB j omega).toReal : ℂ) *
      ∑ r : RetainedAnalysisOutput nK mZ mX ell ellEV leakEC,
        sigma (r, Sum.inr j) (r, Sum.inr j)
  unfold reconstruction
  rw [Instrument.channel_eq_sum, Fintype.sum_unique, Instrument.operation,
    Quantum.Channels.krausMap_eq_sum_conjLinearMap]
  simp only [LinearMap.sum_apply, Matrix.sum_apply, reconstructionInstrument]
  -- Every success row vanishes at a shortage output.
  have hsuccess
      (k : Σ S : Set.powersetCard (Fin N) (nK + mZ + mX),
        Σ pi : Equiv.Perm (Fin (nK + mZ + mX)), SelectedControlSupport N nK mZ mX pA pB S pi) :
      Matrix.conjLinearMap (reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB (Sum.inl k)) sigma
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) = 0 :=
    Matrix.conjLinearMap_apply_eq_zero_of_row_left _ _ (funext (hsuccessRow k.1 k.2.1 k.2.2)) _
  change (∑ r : ReconstructionKrausIndex N nK mZ mX ell ellEV leakEC pA pB,
    Matrix.conjLinearMap (reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB r) sigma
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)) = _
  rw [Fintype.sum_sum_type]
  simp only [hsuccess, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  let K := totalFailureControlKernel N nK mZ mX pA pB j
  let x0 : ReconstructionInput N nK mZ mX ell ellEV leakEC := (r, Sum.inr j)
  by_cases hpos : 0 < K omega
  · -- Only the shortage row of the actual control `omega` survives; it reads `sigma x0 x0`.
    let eta0 : FailureControlSupport N nK mZ mX pA pB j := ⟨omega, hpos⟩
    have hrow_self :
        reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB (Sum.inr ⟨j, r, eta0⟩)
            (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) =
          Pi.single x0 (Instrument.weightedChoiceScale K omega) := by
      funext x
      change reconstructionShortageKraus N nK mZ mX ell ellEV leakEC
          pA pB j r eta0
            (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) x = _
      unfold reconstructionShortageKraus
      refine (Matrix.smul_apply _ _ _ _).trans ?_
      rw [Pi.single_apply]
      by_cases hx : x = x0
      · subst x
        rw [ite_eq_left rfl]
        refine (congrArg (fun z : ℂ => (_ : ℂ) • z)
          (Matrix.single_apply_same _ _ (1 : ℂ))).trans ?_
        exact mul_one _
      · rw [ite_eq_right hx]
        exact (congrArg (fun z : ℂ => (_ : ℂ) • z)
          (Matrix.single_apply_of_col_ne _ _ (Ne.symm hx) (1 : ℂ))).trans (smul_zero _)
    rw [Fintype.sum_eq_single eta0 fun eta heta =>
        Matrix.conjLinearMap_apply_eq_zero_of_row_left _ _
          (funext (hrow_of_control_ne j r eta fun h => heta (Subtype.ext h))) _,
      Matrix.conjLinearMap_apply_of_row_eq_single _ _ hrow_self hrow_self, mul_right_comm,
      mul_comm (Instrument.weightedChoiceScale K omega), Instrument.weightedChoiceScale_star_mul]
  · -- A control of zero weight carries no shortage row at all.
    rw [show K omega = 0 from bot_unique (le_of_not_gt hpos), ENNReal.toReal_zero,
      Complex.ofReal_zero, zero_mul]
    exact Finset.sum_eq_zero fun eta _ =>
      Matrix.conjLinearMap_apply_eq_zero_of_row_left _ _
        (funext (hrow_of_control_ne j r eta fun h => hpos (h ▸ eta.2))) _

/-- The quota-shortage branch discards both records and aborts. -/
private theorem quota_denote_shortage
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hshort : ¬ HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total) :
    (Matrix.reindexLinearEquiv ℂ ℂ (quotaSpaceEquiv N nK mZ mX ell ellEV leakEC ec delta Q omega)
      (quotaSpaceEquiv N nK mZ mX ell ellEV leakEC ec delta Q omega)).toLinearMap
      ((if h : HasQuotas nK mZ mX omega then
        (retainAlice (selectedEmbedding omega h)).then <|
          (retainBob (selectedEmbedding omega h)).then <|
            (forgetAliceBases N (nK + mZ + mX)).then <|
              (forgetBobBases N (nK + mZ + mX)).then <|
                classicalTail (nK + mZ + mX) (mZ + mX) ell ellEV
                  packedPESel packedXSel leakEC ec delta Q
      else (discardAlice (A := CompletedLocalRecord N) (B := CompletedLocalRecord N)).then
        (discardBob.then (.done KeyEnd.abort))).denote rho)
      (Equiv.cast (congrArg Boundary.space
        (completeContinuationBoundary_shortage N nK mZ mX ell ellEV leakEC omega hshort).symm)
          ⟨(), (pairEquiv Unit Unit).symm ((), ())⟩)
      (Equiv.cast (congrArg Boundary.space
        (completeContinuationBoundary_shortage N nK mZ mX ell ellEV leakEC omega hshort).symm)
          ⟨(), (pairEquiv Unit Unit).symm ((), ())⟩) =
      (discardBob (A := Unit) (B := CompletedLocalRecord N)).successorOperation ()
        ((discardAlice (A := CompletedLocalRecord N)
          (B := CompletedLocalRecord N)).successorOperation () rho)
          ((pairEquiv Unit Unit).symm ((), ())) ((pairEquiv Unit Unit).symm ((), ())) := by
  have hE := show quotaSpaceEquiv N nK mZ mX ell ellEV leakEC ec delta Q omega = _ from
    dite_eq_right hshort
  simp only [hE]
  let success (h : HasQuotas nK mZ mX omega) :
      Program (system (CompletedLocalRecord N) (CompletedLocalRecord N))
        (KeyEnd TwoParty.Party.alice TwoParty.Party.bob) :=
    (retainAlice (selectedEmbedding omega h)).then <|
      (retainBob (selectedEmbedding omega h)).then <|
        (forgetAliceBases N (nK + mZ + mX)).then <|
          (forgetBobBases N (nK + mZ + mX)).then <|
            classicalTail (nK + mZ + mX) (mZ + mX) ell ellEV
              packedPESel packedXSel leakEC ec delta Q
  let failure : Program (system (CompletedLocalRecord N) (CompletedLocalRecord N))
      (KeyEnd TwoParty.Party.alice TwoParty.Party.bob) :=
    (discardAlice (A := CompletedLocalRecord N) (B := CompletedLocalRecord N)).then <|
      (discardBob (A := Unit) (B := CompletedLocalRecord N)).then (.done KeyEnd.abort)
  have hp : (if h : HasQuotas nK mZ mX omega then success h else failure) = failure :=
    dite_eq_right hshort
  have hD := Program.denote_congr hp rho
  have hDa := congrFun (congrFun hD ⟨(), (pairEquiv Unit Unit).symm ((), ())⟩)
    ⟨(), (pairEquiv Unit Unit).symm ((), ())⟩
  simp only [LinearEquiv.coe_coe, Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, ← Equiv.cast_symm, Equiv.cast_apply, cast_cast] at hDa ⊢
  refine hDa.trans ?_
  exact private_pair_denote_apply (Instrument.discardToUnit (CompletedLocalRecord N))
    (Instrument.discardToUnit (CompletedLocalRecord N)) (.done KeyEnd.abort) rho _ _

/-- The complete shortage output records the two private discards after public control. -/
private theorem program_denote_shortage_eq_abort
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hshort : ¬ HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : Op (Measurement.weightedStreamSystem Unit N).total) :
    (Matrix.reindexLinearEquiv ℂ ℂ (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec
      delta Q) (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q)).toLinearMap
      ((construction pA pB N nK mZ mX ell ellEV leakEC ec delta Q).denote rho)
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) =
    (discardBob (A := Unit) (B := CompletedLocalRecord N)).successorOperation ()
      ((discardAlice (A := CompletedLocalRecord N)
        (B := CompletedLocalRecord N)).successorOperation ()
        ((announceShuffle omega.a omega.b).successorOperation omega.order
          ((announceBobBases N).successorOperation omega.b
            ((announceAliceBases N).successorOperation omega.a
              (measurementState pA pB Unit N rho)))))
      ((pairEquiv Unit Unit).symm ((), ())) ((pairEquiv Unit Unit).symm ((), ())) := by
  let q : (completeContinuationBoundary N nK mZ mX ell ellEV leakEC
      (lateSelectionExit N nK mZ mX omega)).space :=
    (Equiv.cast (congrArg Boundary.space
        (completeContinuationBoundary_shortage N nK mZ mX ell ellEV leakEC omega hshort).symm)
          ⟨(), (pairEquiv Unit Unit).symm ((), ())⟩)
  let channel := (Matrix.reindexLinearEquiv ℂ ℂ (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV
    leakEC ec delta Q) (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta
    Q)).toLinearMap
    ((construction pA pB N nK mZ mX ell ellEV leakEC ec delta Q).denote rho)
  refine (congrArg (fun z => channel z z)
    (graftSpaceEquiv_symm_shortage_fibre N nK mZ mX ell ellEV leakEC omega hshort q).symm).trans ?_
  apply Eq.trans
  · apply construction_denote_control
  · apply quota_denote_shortage
    exact hshort

/-- Closed form of the program's diagonal entry at a complete shortage output. -/
private theorem program_denote_shortage_output_formula
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hshort : ¬ HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : Op (Measurement.weightedStreamSystem Unit N).total) :
    (Matrix.reindexLinearEquiv ℂ ℂ (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec
      delta Q) (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q)).toLinearMap
      ((construction pA pB N nK mZ mX ell ellEV leakEC ec delta Q).denote rho)
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) =
      ((rawControlLaw N pA pB omega).toReal : ℂ) *
        ∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
          Matrix.conjLinearMap
            (fixedBasisPairKraus
              (completeStoredRecords omega.a xA)
              (completeStoredRecords omega.b xB))
            ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
              (weightedScheduleUnitInputEquiv N)).toLinearMap rho) () () := by
  rw [program_denote_shortage_eq_abort]
  rw [weightedLatePublicSelectionProgram_abort_apply]
  rw [rawControlLaw_toReal_eq]

/-- Retained-real trace of a failure control block of the lifted preprocessor output. -/
private theorem retainedMid_failure_trace
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : Op (ComparisonPreInput N))
    (j : Fin (nK + mZ + mX)) :
    let pre := comparisonPre N nK mZ mX pA pB hN
      (Matrix.reindex (comparisonPreInputEquiv N)
        (comparisonPreInputEquiv N) rho)
    let mid := retainedControlLift N (nK + mZ + mX)
      (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
      (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q) pre
    (∑ r : RetainedAnalysisOutput nK mZ mX ell ellEV leakEC,
      mid (r, Sum.inr j) (r, Sum.inr j)) =
      if j.val = 0 then
        comparisonPreFailureCoefficient N nK mZ mX pA pB *
          ∑ a : ComparisonPreInput N, rho a a
      else 0 := by
  dsimp only
  let regrouped := Matrix.reindex
    (comparisonPreToRetainedControlEquiv N (nK + mZ + mX))
    (comparisonPreToRetainedControlEquiv N (nK + mZ + mX))
    (comparisonPre N nK mZ mX pA pB hN
      (Matrix.reindex (comparisonPreInputEquiv N) (comparisonPreInputEquiv N) rho))
  let block : Op (Signals (nK + mZ + mX)) :=
    fun i k => regrouped (i, Sum.inr j) (k, Sum.inr j)
  have hregroup (i k : Signals (nK + mZ + mX)) :
      regrouped (i, Sum.inr j) (k, Sum.inr j) =
        comparisonPreEntry N nK mZ mX pA pB rho
          (pairFunctions Bit Bit (nK + mZ + mX) i, Sum.inr j)
          (pairFunctions Bit Bit (nK + mZ + mX) k, Sum.inr j) := by
    have hin : Matrix.reindex (weightedScheduleUnitInputEquiv N)
        (weightedScheduleUnitInputEquiv N)
        (Matrix.reindex (comparisonPreInputEquiv N) (comparisonPreInputEquiv N) rho) = rho := by
      ext a b
      simp [comparisonPreInputEquiv, Matrix.reindex_apply]
    change (comparisonPreInstrument N nK mZ mX pA pB hN).channel
      (Matrix.reindex (weightedScheduleUnitInputEquiv N) (weightedScheduleUnitInputEquiv N)
        (Matrix.reindex (comparisonPreInputEquiv N) (comparisonPreInputEquiv N) rho))
      (pairFunctions Bit Bit (nK + mZ + mX) i, Sum.inr j)
      (pairFunctions Bit Bit (nK + mZ + mX) k, Sum.inr j) = _
    rw [hin, comparisonPreInstrument_channel_apply]
  have htrace : (∑ i : Signals (nK + mZ + mX), block i i) =
      if j.val = 0 then
        comparisonPreFailureCoefficient N nK mZ mX pA pB *
          ∑ a : ComparisonPreInput N, rho a a
      else 0 := by
    let i0 := (pairFunctions Bit Bit (nK + mZ + mX)).symm
      (comparisonZeroNativeInput (nK + mZ + mX))
    rw [Finset.sum_eq_single i0]
    · rw [show block i0 i0 =
          if j.val = 0 then
            comparisonPreFailureCoefficient N nK mZ mX pA pB *
              ∑ a : ComparisonPreInput N, rho a a
          else 0 by
        rw [show block i0 i0 = comparisonPreEntry N nK mZ mX pA pB rho
            (comparisonZeroNativeInput (nK + mZ + mX), Sum.inr j)
            (comparisonZeroNativeInput (nK + mZ + mX), Sum.inr j) by
          dsimp only [block, Matrix.of_apply]
          rw [hregroup]
          simp [i0]]
        simp [comparisonPreEntry]]
    · intro i _ hi
      rw [show block i i = comparisonPreEntry N nK mZ mX pA pB rho
          (((pairFunctions Bit Bit (nK + mZ + mX)).symm).symm i, Sum.inr j)
          (((pairFunctions Bit Bit (nK + mZ + mX)).symm).symm i, Sum.inr j) by
        exact hregroup i i]
      simp only [comparisonPreEntry]
      rw [ite_eq_right]
      intro hc
      apply hi
      calc
        i = (pairFunctions Bit Bit (nK + mZ + mX)).symm
              (((pairFunctions Bit Bit (nK + mZ + mX)).symm).symm i) :=
            (((pairFunctions Bit Bit (nK + mZ + mX)).symm).apply_symm_apply i).symm
        _ = i0 := by rw [hc.2.2.1]
    · intro hi
      exact (hi (Finset.mem_univ i0)).elim
  change (∑ x, mapTensorId
    (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)
    (ComparisonControl N (nK + mZ + mX)) regrouped (x, Sum.inr j) (x, Sum.inr j)) = _
  rw [mapTensorId_trace_block _
    (isChannel_retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q).2]
  exact htrace

/-- The totalized status law reproduces the raw-control law on a shortage exit. -/
private theorem totalized_failure_mass_formula
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) (omega : RawControl N)
    (hshort : ¬ HasQuotas nK mZ mX omega) :
    let hn : nK + mZ + mX ≠ 0 := by
      intro hzero
      have hnK : nK = 0 := by omega
      have hmZ : mZ = 0 := by omega
      have hmX : mX = 0 := by omega
      subst nK
      subst mZ
      subst mX
      exact hshort (by simp [HasQuotas])
    let j0 : Fin (nK + mZ + mX) := ⟨0, Nat.pos_of_ne_zero hn⟩
    selectionFailureMass N nK mZ mX pA pB *
        totalFailureControlKernel N nK mZ mX pA pB j0 omega =
      rawControlLaw N pA pB omega := by
  dsimp only
  have hn : nK + mZ + mX ≠ 0 := by
    intro hzero
    have hnK : nK = 0 := by omega
    have hmZ : mZ = 0 := by omega
    have hmX : mX = 0 := by omega
    subst nK
    subst mZ
    subst mX
    exact hshort (by simp [HasQuotas])
  have hpoint := congrArg
    (fun P : PMF (Bool × RawControl N) => P (false, omega))
    (totalizedReconstructedStatusRawLaw_eq N nK mZ mX pA pB hN)
  change totalizedReconstructedStatusRawLaw N nK mZ mX pA pB hN
      (false, omega) =
    taggedRawControlLaw N nK mZ mX pA pB (false, omega) at hpoint
  have htagged :
      taggedRawControlLaw N nK mZ mX pA pB (false, omega) =
        rawControlLaw N pA pB omega := by
    rw [taggedRawControlLaw, PMF.map_apply]
    simp only [tsum_fintype]
    rw [Finset.sum_eq_single omega]
    · simp [hshort]
    · intro x _ hne
      simp [show omega ≠ x by exact Ne.symm hne]
    · simp
  rw [htagged] at hpoint
  rw [totalizedReconstructedStatusRawLaw, dite_eq_right hn] at hpoint
  simp only [PMF.bind_apply, PMF.pure_apply, tsum_fintype,
    Fintype.sum_bool, selectionStatusLaw, PMF.ofFintype_apply,
    selectionStatusWeight, Bool.false_eq_true, ite_false, ite_true,
    Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero] at hpoint
  simp only [false_and, ite_false,
    Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at hpoint
  simp only [Finset.sum_const_zero, mul_zero, zero_add] at hpoint
  simpa only [mul_assoc] using hpoint

/-- Complex form of the totalized shortage mass identity. -/
private theorem totalized_failure_complex_mass_formula
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) (omega : RawControl N)
    (hshort : ¬ HasQuotas nK mZ mX omega) :
    let hn : nK + mZ + mX ≠ 0 := by
      intro hzero
      have hnK : nK = 0 := by omega
      have hmZ : mZ = 0 := by omega
      have hmX : mX = 0 := by omega
      subst nK
      subst mZ
      subst mX
      exact hshort (by simp [HasQuotas])
    let j0 : Fin (nK + mZ + mX) := ⟨0, Nat.pos_of_ne_zero hn⟩
    comparisonPreFailureCoefficient N nK mZ mX pA pB *
        ((totalFailureControlKernel N nK mZ mX pA pB j0 omega).toReal : ℂ) =
      ((rawControlLaw N pA pB omega).toReal : ℂ) := by
  dsimp only
  have hmass := totalized_failure_mass_formula
    N nK mZ mX pA pB hN omega hshort
  dsimp only at hmass
  unfold comparisonPreFailureCoefficient
  have hreal := congrArg ENNReal.toReal hmass
  rw [ENNReal.toReal_mul] at hreal
  exact_mod_cast hreal

/-- On a quota-shortage exit, the BB84 program and the factorized real map have the same diagonal
entry at the metadata-bearing abort output, for every complex input operator. -/
theorem retainedFactorization_shortage_sector
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (omega : RawControl N) (hshort : ¬ HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : Op (Measurement.weightedStreamSystem Unit N).total) :
    let rhoBits := (Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
      (weightedScheduleUnitInputEquiv N)).toLinearMap rho
    let pre := comparisonPre N nK mZ mX pA pB hN
      (Matrix.reindex (comparisonPreInputEquiv N)
        (comparisonPreInputEquiv N) rhoBits)
    let mid := retainedControlLift N (nK + mZ + mX)
      (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
      (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q) pre
    (Matrix.reindexLinearEquiv ℂ ℂ (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec
      delta Q) (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q)).toLinearMap
      ((construction pA pB N nK mZ mX ell ellEV leakEC ec delta Q).denote rho)
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) =
    reconstruction N nK mZ mX ell ellEV leakEC pA pB mid
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) := by
  dsimp only
  rw [program_denote_shortage_output_formula]
  rw [sum_matrixConjLinear_fixedBasisPairKraus]
  rw [reconstruction_shortage]
  simp_rw [retainedMid_failure_trace]
  have hn : nK + mZ + mX ≠ 0 := by
    intro hzero
    have hnK : nK = 0 := by omega
    have hmZ : mZ = 0 := by omega
    have hmX : mX = 0 := by omega
    subst nK
    subst mZ
    subst mX
    exact hshort (by simp [HasQuotas])
  let j0 : Fin (nK + mZ + mX) := ⟨0, Nat.pos_of_ne_zero hn⟩
  rw [Finset.sum_eq_single j0]
  · rw [ite_eq_left (by rfl)]
    have hmass := totalized_failure_complex_mass_formula
      N nK mZ mX pA pB hN omega hshort
    dsimp only at hmass
    rw [← hmass]
    dsimp only [j0]
    change comparisonPreFailureCoefficient N nK mZ mX pA pB *
        ((totalFailureControlKernel N nK mZ mX pA pB
          ⟨0, Nat.pos_of_ne_zero hn⟩ omega).toReal : ℂ) *
          (∑ a, ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
            (weightedScheduleUnitInputEquiv N)).toLinearMap rho) a a) = _
    ring
  · intro j _ hne
    have hj : j.val ≠ 0 := by
      intro hj0
      apply hne
      apply Fin.ext
      exact hj0
    rw [ite_eq_right hj]
    ring
  · intro hmem
    exact (hmem (Finset.mem_univ j0)).elim

end QKD.BB84.Reduction
