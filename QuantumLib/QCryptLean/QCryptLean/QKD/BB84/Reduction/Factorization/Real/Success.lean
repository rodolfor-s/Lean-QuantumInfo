import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.Instrument.WeightedChoice
import QCryptLean.LOCC.LocalAction.ComputationalMeasurement
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Classical
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.FiniteEmbedding.SubsetPerm
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.Acceptance
import QCryptLean.QKD.BB84.CompleteOutput
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Measurement.LatePublicControl
import QCryptLean.QKD.BB84.Measurement.LatePublicControl.BranchValues
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Measurement.SelectedBornRule
import QCryptLean.QKD.BB84.Measurement.SelectedMarginal
import QCryptLean.QKD.BB84.Measurement.SelectedRecords
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Reduction.BasisErasure
import QCryptLean.QKD.BB84.Reduction.ClassicalTail
import QCryptLean.QKD.BB84.Reduction.Factorization.Reconstruction
import QCryptLean.QKD.BB84.Reduction.Preprocessor
import QCryptLean.QKD.BB84.Reduction.RetainedBlocks
import QCryptLean.QKD.BB84.Reduction.RetainedExperiment
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Disintegration
import QCryptLean.QKD.BB84.Sampling.FiberMass
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.Sampling.TotalKernels
import QCryptLean.QKD.BB84.SiftOperation
import QCryptLean.QKD.BB84.TailOutput
import QCryptLean.QKD.BB84.TailTranscript
import QCryptLean.QKD.KeyEnd
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-!
# The success sector of the retained-round factorization

Assume `nK + mZ + mX ≤ N` and let `omega` be a raw control that meets every quota
(`Sampling.HasQuotas`).  For every complex input operator and all classical-tail outputs `qa`,
`qb`, `retainedFactorization_success_sector` identifies the output entry of the BB84 program between
the successful complete outputs `successCompleteOutputEmbedding … omega hquota qa` and
`… qb` with the corresponding entry of
`reconstruction ∘ retainedControlLift (retainedAnalysisReal …) ∘ comparisonPre`.

The program side is evaluated through the success branch value of the sifting stage
(`Measurement.weightedLatePublicSelectionProgram_success_apply`), basis erasure
(`forgetAliceBases_forgetBobBases_denote_diag`) and the classical tail. The factorized side
is evaluated through the success rows of the reconstruction Kraus family, the success coefficient of
`comparisonPre` and the reference-block formula of the retained experiment
(`retainedAnalysisReal_referenceBlock_eq_program`).  The two agree because the totalized
selection law disintegrates the raw-control law over retained subsets and inner permutations
(`Sampling.totalizedReconstructedStatusRawLaw_eq`).
-/

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


/-- Entry of a conjugation `A · B · Aᴴ`, as the iterated coordinate sum. -/
private theorem mul_mul_conjTranspose_apply {m n : Type} [Fintype n] (A : Matrix m n ℂ)
    (B : Matrix n n ℂ) (i j : m) :
    (A * B * Aᴴ) i j = ∑ x, (∑ y, A i y * B y x) * star (A j x) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem successfulCompleteContinuation_output_apply
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (sigma : Op
      (Measurement.weightedSelectedRecordSystem N (nK + mZ + mX)).total)
    (qa qb : (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX)
      ell ellEV (@Sampling.packedPESel nK mZ mX) leakEC).space) :
    (Matrix.reindexLinearEquiv ℂ ℂ (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
      packedPESel packedXSel leakEC ec delta Q) (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ +
        mX) ell ellEV
      packedPESel packedXSel leakEC ec delta Q)).toLinearMap
      ((classicalTail (nK + mZ + mX) (mZ + mX) ell ellEV
        packedPESel packedXSel leakEC ec delta Q).denote
        ((forgetBobBases N (nK + mZ + mX)).successorOperation ()
          ((forgetAliceBases N (nK + mZ + mX)).successorOperation () sigma))) qa qb =
      if qa = qb then
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            if rawClassicalTailOutputPoint (nK + mZ + mX) (mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) leakEC ec
                delta Q x st = qa then
              (Fintype.card (KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                (∑ qB : Measurement.SelectedLocalRecord N (nK + mZ + mX),
                  ∑ qA : Measurement.SelectedLocalRecord N (nK + mZ + mX),
                    if x .alice = qA.2 ∧
                        x .bob = qB.2 then
                      sigma ((TwoParty.pairEquiv _ _).symm (qA, qB))
                        ((TwoParty.pairEquiv _ _).symm (qA, qB))
                    else 0)
            else 0
      else 0 := by
  refine (rawClassicalTailProgram_output_apply (nK + mZ + mX) (mZ + mX) ell ellEV
    packedPESel packedXSel leakEC ec delta Q _ qa qb).trans ?_
  by_cases hq : qa = qb
  · rw [ite_eq_left hq, ite_eq_left hq]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro st _
    by_cases hout : rawClassicalTailOutputPoint (nK + mZ + mX)
        (mZ + mX) ell ellEV (@Sampling.packedPESel nK mZ mX)
        (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q x st = qa
    · rw [ite_eq_left hout, ite_eq_left hout]
      congr 1
      exact forgetAliceBases_forgetBobBases_denote_diag N (nK + mZ + mX) sigma x
    · rw [ite_eq_right hout, ite_eq_right hout]
  · rw [ite_eq_right hq, ite_eq_right hq]


/-- The quota-success branch retains records and executes the classical tail. -/
private theorem quota_denote_success
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total)
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
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
      (successContinuationSpaceEquiv N nK mZ mX ell ellEV leakEC omega hquota qa)
      (successContinuationSpaceEquiv N nK mZ mX ell ellEV leakEC omega hquota qb) =
      (Matrix.reindexLinearEquiv ℂ ℂ (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
        packedPESel packedXSel leakEC ec delta Q) (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ +
          mX) ell ellEV
        packedPESel packedXSel leakEC ec delta Q)).toLinearMap
        ((classicalTail (nK + mZ + mX) (mZ + mX) ell ellEV
          packedPESel packedXSel leakEC ec delta Q).denote
          ((forgetBobBases N (nK + mZ + mX)).successorOperation ()
            ((forgetAliceBases N (nK + mZ + mX)).successorOperation ()
              ((retainBob (selectedEmbedding omega hquota)).successorOperation ()
                ((retainAlice (selectedEmbedding omega hquota)).successorOperation () rho)))))
          qa qb := by
  have hE := show quotaSpaceEquiv N nK mZ mX ell ellEV leakEC ec delta Q omega = _ from
    dite_eq_left hquota
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
  have hp : (if h : HasQuotas nK mZ mX omega then success h else failure) = success hquota :=
    dite_eq_left hquota
  have hD := Program.denote_congr hp rho
  have hDa := congrFun (congrFun hD
    ((rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
      packedPESel packedXSel leakEC ec delta Q).symm qa))
    ((rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
      packedPESel packedXSel leakEC ec delta Q).symm qb)
  simp only [LinearEquiv.coe_coe, Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_trans_apply, ← Equiv.cast_symm,
    successContinuationSpaceEquiv, Equiv.cast_apply, cast_cast, cast_eq] at hDa ⊢
  refine hDa.trans ?_
  refine (LOCC.TwoParty.private_pair_denote_apply
    (Instrument.functionAndForget (selectedLocalRecord (selectedEmbedding omega hquota)))
    (Instrument.functionAndForget (selectedLocalRecord (selectedEmbedding omega hquota)))
    ((forgetAliceBases N (nK + mZ + mX)).then <|
      (forgetBobBases N (nK + mZ + mX)).then <|
        classicalTail (nK + mZ + mX) (mZ + mX) ell ellEV
          packedPESel packedXSel leakEC ec delta Q) _ _ _).trans ?_
  exact LOCC.TwoParty.private_pair_denote_apply
    (Instrument.functionAndForget (fun q : Measurement.SelectedLocalRecord N (nK + mZ + mX) => q.2))
    (Instrument.functionAndForget (fun q : Measurement.SelectedLocalRecord N (nK + mZ + mX) => q.2))
    (classicalTail (nK + mZ + mX) (mZ + mX) ell ellEV
      packedPESel packedXSel leakEC ec delta Q) _ _ _


private theorem program_denote_success_eq_continuation
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : Op (Measurement.weightedStreamSystem Unit N).total)
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    (Matrix.reindexLinearEquiv ℂ ℂ (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec
      delta Q) (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q)).toLinearMap
      ((construction pA pB N nK mZ mX ell ellEV leakEC ec delta Q).denote rho)
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qa)
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qb) =
      (Matrix.reindexLinearEquiv ℂ ℂ (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
        packedPESel packedXSel leakEC ec delta Q) (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ +
          mX) ell ellEV
        packedPESel packedXSel leakEC ec delta Q)).toLinearMap
        ((classicalTail (nK + mZ + mX) (mZ + mX) ell ellEV
          packedPESel packedXSel leakEC ec delta Q).denote
          ((forgetBobBases N (nK + mZ + mX)).successorOperation ()
            ((forgetAliceBases N (nK + mZ + mX)).successorOperation ()
              (selectedControlState pA pB N nK mZ mX omega hquota rho)))) qa qb := by
  have hcontrol := construction_denote_control pA pB N nK mZ mX ell ellEV leakEC ec delta Q
    rho omega
    (successContinuationSpaceEquiv N nK mZ mX ell ellEV leakEC omega hquota qa)
    (successContinuationSpaceEquiv N nK mZ mX ell ellEV leakEC omega hquota qb)
  simp only [graftSpaceEquiv_symm_success_fibre N nK mZ mX ell ellEV leakEC omega hquota,
    Equiv.symm_apply_apply] at hcontrol
  refine hcontrol.trans ?_
  apply quota_denote_success


private theorem program_denote_success_raw_formula
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : Op (Measurement.weightedStreamSystem Unit N).total)
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    (Matrix.reindexLinearEquiv ℂ ℂ (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec
      delta Q) (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q)).toLinearMap
      ((construction pA pB N nK mZ mX ell ellEV leakEC ec delta Q).denote rho)
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qa)
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qb) =
      if qa = qb then
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            if rawClassicalTailOutputPoint (nK + mZ + mX) (mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q x st = qa then
              (Fintype.card (KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                (∑ qB : Measurement.SelectedLocalRecord N (nK + mZ + mX),
                  ∑ qA : Measurement.SelectedLocalRecord N (nK + mZ + mX),
                    if x .alice = qA.2 ∧
                        x .bob = qB.2 then
                      (selectedControlState pA pB N nK mZ mX omega hquota rho)
                        ((TwoParty.pairEquiv _ _).symm (qA, qB))
                        ((TwoParty.pairEquiv _ _).symm (qA, qB))
                    else 0)
            else 0
      else 0 :=
  (program_denote_success_eq_continuation pA pB N nK mZ mX ell ellEV leakEC
    omega hquota ec delta Q rho qa qb).trans
      (successfulCompleteContinuation_output_apply N nK mZ mX ell ellEV leakEC ec delta Q
        (selectedControlState pA pB N nK mZ mX omega hquota rho) qa qb)

private theorem weightedLatePublicSelection_selectedBits_sum
    (pA pB : PMF Basis) (N nK mZ mX : ℕ)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (rho : Op (Measurement.weightedStreamSystem Unit N).total)
    (x : (FinalStage.rawSystem (nK + mZ + mX)).total) :
    (∑ qB : Measurement.SelectedLocalRecord N (nK + mZ + mX),
      ∑ qA : Measurement.SelectedLocalRecord N (nK + mZ + mX),
        if x .alice = qA.2 ∧
            x .bob = qB.2 then
          selectedControlState pA pB N nK mZ mX omega hquota rho
            ((TwoParty.pairEquiv _ _).symm (qA, qB))
            ((TwoParty.pairEquiv _ _).symm (qA, qB))
        else 0) =
      (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ *
        ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
        ((Sampling.basisStringLaw N pB omega.b).toReal : ℂ) *
        fixedBasisSelectedBornBlock (selectedEmbedding omega hquota)
          omega.a omega.b
          (x .alice)
          (x .bob)
          (Matrix.of fun i j =>
            ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
              (weightedScheduleUnitInputEquiv N)).toLinearMap rho) i.1 j.1) () () := by
  let qA0 : Measurement.SelectedLocalRecord N (nK + mZ + mX) :=
    (omega.a,
      x .alice)
  let qB0 : Measurement.SelectedLocalRecord N (nK + mZ + mX) :=
    (omega.b,
      x .bob)
  have hlaw (qA qB : Measurement.SelectedLocalRecord N (nK + mZ + mX)) :
      selectedMeasurementLaw pA pB (selectedEmbedding omega hquota)
          ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
            (weightedScheduleUnitInputEquiv N)).toLinearMap rho) (qA, qB) (qA, qB) =
        ((Sampling.basisStringLaw N pA qA.1).toReal : ℂ) *
          ((Sampling.basisStringLaw N pB qB.1).toReal : ℂ) *
          fixedBasisSelectedBornBlock (selectedEmbedding omega hquota) qA.1 qB.1 qA.2 qB.2
            (Matrix.of fun i j =>
              ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
                (weightedScheduleUnitInputEquiv N)).toLinearMap rho) i.1 j.1) () () := by
    exact (selectedMeasurementLaw_apply pA pB (selectedEmbedding omega hquota)
      ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
        (weightedScheduleUnitInputEquiv N)).toLinearMap rho)
      qA.1 qA.1 qB.1 qB.1 qA.2 qA.2 qB.2 qB.2).trans (ite_eq_left ⟨rfl, rfl⟩)
  have hentry (qA qB : Measurement.SelectedLocalRecord N (nK + mZ + mX)) :
      selectedControlState pA pB N nK mZ mX omega hquota rho
        ((TwoParty.pairEquiv _ _).symm (qA, qB))
        ((TwoParty.pairEquiv _ _).symm (qA, qB)) =
      if qA.1 = omega.a ∧ qA.1 = omega.a ∧ qB.1 = omega.b ∧ qB.1 = omega.b then
        (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ *
          selectedMeasurementLaw pA pB (selectedEmbedding omega hquota)
            ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
              (weightedScheduleUnitInputEquiv N)).toLinearMap rho) (qA, qB) (qA, qB)
      else 0 :=
    weightedLatePublicSelectionProgram_success_apply pA pB N nK mZ mX
      omega hquota rho (qA, qB) (qA, qB)
  simp_rw [hentry, hlaw]
  rw [Finset.sum_eq_single qB0]
  · rw [Finset.sum_eq_single qA0]
    · have ha : x .alice = qA0.2 :=
        rfl
      have hb : x .bob = qB0.2 :=
        rfl
      refine (ite_eq_left ⟨ha, hb⟩).trans ?_
      rw [ite_eq_left ⟨rfl, rfl, rfl, rfl⟩]
      dsimp only [qA0, qB0]
      ring
    · intro qA _ hne
      by_cases hbits : x .alice = qA.2
      · have hbase : qA.1 ≠ omega.a := by
          intro hb
          apply hne
          apply Prod.ext
          · exact hb
          · exact hbits.symm
        simp [hbits, hbase]
      · simp [hbits]
    · simp
  · intro qB _ hne
    by_cases hbits : x .bob = qB.2
    · have hbase : qB.1 ≠ omega.b := by
        intro hb
        apply hne
        apply Prod.ext
        · exact hb
        · exact hbits.symm
      simp [hbits, hbase]
    · simp [hbits]
  · simp

private theorem totalized_success_mass_formula
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) (omega : RawControl N)
    (hquota : HasQuotas nK mZ mX omega) :
    (∑ S : Set.powersetCard (Fin N) (nK + mZ + mX),
      ∑ pi : Equiv.Perm (Fin (nK + mZ + mX)),
        selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)) =
      rawControlLaw N pA pB omega := by
  have hpoint := congrArg
    (fun P : PMF (Bool × RawControl N) => P (true, omega))
    (totalizedReconstructedStatusRawLaw_eq N nK mZ mX pA pB hN)
  change totalizedReconstructedStatusRawLaw N nK mZ mX pA pB hN
      (true, omega) =
    taggedRawControlLaw N nK mZ mX pA pB (true, omega) at hpoint
  have htagged :
      taggedRawControlLaw N nK mZ mX pA pB (true, omega) =
        rawControlLaw N pA pB omega := by
    rw [taggedRawControlLaw, PMF.map_apply]
    simp only [tsum_fintype]
    rw [Finset.sum_eq_single omega]
    · simp [hquota]
    · intro x _ hne
      simp [show omega ≠ x by exact Ne.symm hne]
    · simp
  rw [htagged] at hpoint
  by_cases hn : nK + mZ + mX = 0
  · have hnK : nK = 0 := by omega
    have hmZ : mZ = 0 := by omega
    have hmX : mX = 0 := by omega
    subst nK
    subst mZ
    subst mX
    rw [totalizedReconstructedStatusRawLaw, dite_eq_left rfl] at hpoint
    simp only [PMF.bind_apply, PMF.pure_apply, tsum_fintype,
      Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero] at hpoint
    simpa [selectionSuccessMass_zero_quotas] using hpoint
  · rw [totalizedReconstructedStatusRawLaw, dite_eq_right hn] at hpoint
    simp only [PMF.bind_apply, PMF.pure_apply, tsum_fintype,
      Fintype.sum_bool, selectionStatusLaw, PMF.ofFintype_apply,
      selectionStatusWeight, Bool.false_eq_true, ite_false, ite_true,
      Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero] at hpoint
    simp_rw [Finset.mul_sum] at hpoint
    simp only [mul_ite, mul_zero, Bool.true_eq_false, false_and,
      ite_false, Finset.sum_const_zero, add_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hpoint
    simpa only [mul_assoc] using hpoint

private theorem totalized_success_complex_mass_formula
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) (omega : RawControl N)
    (hquota : HasQuotas nK mZ mX omega) :
    (∑ S : Set.powersetCard (Fin N) (nK + mZ + mX),
      ∑ pi : Equiv.Perm (Fin (nK + mZ + mX)),
        (((selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)).toReal : ℂ))) =
      ((rawControlLaw N pA pB omega).toReal : ℂ) := by
  have hsuccess : selectionSuccessMass N nK mZ mX pA pB ≠ ⊤ :=
    selectionSuccessMass_ne_top N nK mZ mX pA pB
  have hterm (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (pi : Equiv.Perm (Fin (nK + mZ + mX))) :
      selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hsuccess
        ((uniformRetainedSubset hN).apply_ne_top S))
      (ENNReal.mul_ne_top ((uniformInnerPerm _).apply_ne_top pi)
        ((totalSelectedControlKernel N nK mZ mX pA pB _).apply_ne_top omega))
  have hinner (S : Set.powersetCard (Fin N) (nK + mZ + mX)) :
      (∑ pi : Equiv.Perm (Fin (nK + mZ + mX)),
        selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)) ≠ ⊤ := by
    exact (ENNReal.sum_ne_top).2 (fun pi _ => hterm S pi)
  have hmass := totalized_success_mass_formula N nK mZ mX pA pB
    hN omega hquota
  have hreal := congrArg ENNReal.toReal hmass
  rw [ENNReal.toReal_sum (fun S _ => hinner S)] at hreal
  simp_rw [ENNReal.toReal_sum (fun pi _ => hterm _ pi)] at hreal
  exact_mod_cast hreal

private theorem totalized_success_native_formula
    {R : Type}
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) (omega : RawControl N)
    (hquota : HasQuotas nK mZ mX omega)
    (uA uB : Fin (nK + mZ + mX) → Bit)
    (W : Op (((Fin N → Bit) × (Fin N → Bit)) × R)) (s t : R) :
    (∑ S : Set.powersetCard (Fin N) (nK + mZ + mX),
      ∑ pi : Equiv.Perm (Fin (nK + mZ + mX)),
        ((selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)).toReal : ℂ) *
        nativeSelectedBornBlock S
          (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) pi uA uB W s t) =
      ((rawControlLaw N pA pB omega).toReal : ℂ) *
        fixedBasisSelectedBornBlock (selectedEmbedding omega hquota)
          omega.a omega.b uA uB W s t := by
  have hterm (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (pi : Equiv.Perm (Fin (nK + mZ + mX))) :
      ((selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)).toReal : ℂ) *
        nativeSelectedBornBlock S
          (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) pi uA uB W s t =
        ((selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)).toReal : ℂ) *
        fixedBasisSelectedBornBlock (selectedEmbedding omega hquota)
          omega.a omega.b uA uB W s t := by
    by_cases hkernel : totalSelectedControlKernel N nK mZ mX pA pB
        (Math.FiniteEmbedding.joinSubsetPerm S pi) omega = 0
    · simp [hkernel]
    · have hpositive : 0 < totalSelectedControlKernel N nK mZ mX pA pB
          (Math.FiniteEmbedding.joinSubsetPerm S pi) omega :=
        pos_iff_ne_zero.mpr hkernel
      have hselect := totalSelectedControlKernel_select N nK mZ mX pA pB
        (Math.FiniteEmbedding.joinSubsetPerm S pi) omega hpositive
      have hactual : select nK mZ mX omega =
          some (selectedEmbedding omega hquota) := by
        simp [select, hquota]
      rw [hactual] at hselect
      have hembedding : selectedEmbedding omega hquota =
          Math.FiniteEmbedding.joinSubsetPerm S pi :=
        Option.some.inj hselect
      rw [selectedMeasurement_joinSubsetPerm_eq_native omega hquota S pi
        hembedding uA uB W s t]
  simp_rw [hterm]
  simp_rw [← Finset.sum_mul]
  rw [totalized_success_complex_mass_formula N nK mZ mX pA pB
    hN omega hquota]

private theorem program_denote_success_output_formula
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : Op (Measurement.weightedStreamSystem Unit N).total)
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    (Matrix.reindexLinearEquiv ℂ ℂ (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec
      delta Q) (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q)).toLinearMap
      ((construction pA pB N nK mZ mX ell ellEV leakEC ec delta Q).denote rho)
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qa)
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qb) =
      if qa = qb then
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            if rawClassicalTailOutputPoint (nK + mZ + mX) (mZ + mX)
                ell ellEV (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q x st = qa then
              (Fintype.card (KeyHashSeedPairEV
                (nK + mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                (((rawControlLaw N pA pB omega).toReal : ℂ) *
                  fixedBasisSelectedBornBlock (selectedEmbedding omega hquota)
                    omega.a omega.b
                    (x .alice)
                    (x .bob)
                    (Matrix.of fun i j =>
                      ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
                        (weightedScheduleUnitInputEquiv N)).toLinearMap rho)
                        i.1 j.1) () ())
            else 0
      else 0 := by
  rw [program_denote_success_raw_formula]
  simp_rw [weightedLatePublicSelection_selectedBits_sum]
  rw [rawControlLaw_toReal_eq]

private theorem reconstruction_success
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (mid : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) :
    reconstruction N nK mZ mX ell ellEV leakEC pA pB mid
        (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega hquota qa)
        (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega hquota qb) =
      ∑ S, ∑ pi,
        (((totalSelectedControlKernel N nK mZ mX pA pB
          (Math.FiniteEmbedding.joinSubsetPerm S pi) omega).toReal : ℂ) *
        mid
          (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
              ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
                (pi, qa)), Sum.inl S)
          (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
              ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
                (pi, qb)), Sum.inl S)) := by
  have hfailureRow
      (j : Fin (nK + mZ + mX))
      (r : RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
      (eta : FailureControlSupport N nK mZ mX pA pB j)
      (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC)
      (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
      reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB
          (Sum.inr ⟨j, r, eta⟩)
          (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
            omega hquota q) x = 0 := by
    change reconstructionShortageKraus N nK mZ mX ell ellEV leakEC
        pA pB j r eta
          (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
            omega hquota q) x = 0
    unfold reconstructionShortageKraus
    refine (Matrix.smul_apply _ _ _ _).trans ?_
    have hrow : shortageCompleteOutput N nK mZ mX ell ellEV leakEC eta.1
        (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j eta) ≠
        successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega hquota q := by
      intro heq
      have hrc := congrArg (fun y =>
        QKD.BB84.lateSelectionExitEquiv N nK mZ mX
          ((QKD.BB84.exitEquiv N nK mZ mX ell ellEV leakEC) y.1).1) heq
      rw [shortageCompleteOutput_rawControl] at hrc
      rw [successCompleteOutputEmbedding_exit] at hrc
      unfold successExitMap at hrc
      rw [Equiv.apply_symm_apply] at hrc
      change eta.1 = QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionExit N nK mZ mX omega) at hrc
      have hrc' : eta.1 = omega := hrc.trans
        ((QKD.BB84.lateSelectionExitEquiv N nK mZ mX).right_inv omega)
      exact (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j eta)
        (hrc' ▸ hquota)
    exact (congrArg (fun z : ℂ => _ • z)
      (Matrix.single_apply_of_row_ne hrow
        ((r, Sum.inr j) : ReconstructionInput N nK mZ mX ell ellEV leakEC)
        x (1 : ℂ))).trans (smul_zero _)
  let sigma := mid
  unfold reconstruction
  rw [Instrument.channel_eq_sum, Fintype.sum_unique, Instrument.operation,
    Quantum.Channels.krausMap_eq_sum_conjLinearMap]
  -- entry of the Kraus sum `∑ₒ Kₒ σ Kₒᴴ`, one conjugation at a time
  simp only [LinearMap.sum_apply, Matrix.sum_apply,
    Matrix.conjLinearMap_apply_apply,
    ← Finset.sum_mul]
  simp only [reconstructionInstrument]
  conv_lhs => tactic => exact Fintype.sum_sum_type _
  simp only [Fintype.sum_sigma]
  simp_rw [hfailureRow]
  simp only [zero_mul, Finset.sum_const_zero, star_zero, mul_zero, add_zero]
  change _ = ∑ S, ∑ pi,
    (((totalSelectedControlKernel N nK mZ mX pA pB
      (Math.FiniteEmbedding.joinSubsetPerm S pi) omega).toReal : ℂ) *
      sigma
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
            ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
              (pi, qa)), Sum.inl S)
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
            ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
              (pi, qb)), Sum.inl S))
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro pi _
  let E := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
  let D := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
  let xA : ReconstructionInput N nK mZ mX ell ellEV leakEC :=
    (E (D.symm (pi, qa)), Sum.inl S)
  let xB : ReconstructionInput N nK mZ mX ell ellEV leakEC :=
    (E (D.symm (pi, qb)), Sum.inl S)
  let K := totalSelectedControlKernel N nK mZ mX pA pB
    (Math.FiniteEmbedding.joinSubsetPerm S pi)
  change _ = ((K omega).toReal : ℂ) * sigma xA xB
  have hsuccessRaw
      (xi : RawControl N) (hxi : HasQuotas nK mZ mX xi)
      (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC) :
      QKD.BB84.lateSelectionExitEquiv N nK mZ mX
          ((QKD.BB84.exitEquiv N nK mZ mX ell ellEV leakEC)
            (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
              xi hxi q).1).1 = xi := by
    rw [successCompleteOutputEmbedding_exit]
    unfold successExitMap
    rw [Equiv.apply_symm_apply]
    exact (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).right_inv xi
  have hrow_of_control_ne
      (eta : SelectedControlSupport N nK mZ mX pA pB S pi)
      (heta : eta.1 ≠ omega)
      (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC)
      (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
      reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB
          (Sum.inl ⟨S, pi, eta⟩)
          (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
            omega hquota q) x = 0 := by
    change reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC
        pA pB S pi eta
          (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
            omega hquota q) x = 0
    unfold reconstructionSuccessKraus
    dsimp only
    split
    · rename_i hc
      exfalso
      have hrc := congrArg (fun y =>
        QKD.BB84.lateSelectionExitEquiv N nK mZ mX
          ((QKD.BB84.exitEquiv N nK mZ mX ell ellEV leakEC) y.1).1) hc.2.2
      rw [hsuccessRaw omega hquota q,
        hsuccessRaw eta.1
          (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi eta)
          (D (E.symm x.1)).2] at hrc
      exact heta hrc.symm
    · rfl
  by_cases hpos : 0 < K omega
  · let eta0 : SelectedControlSupport N nK mZ mX pA pB S pi :=
      ⟨omega, hpos⟩
    have hrows
        (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC) :
        reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB (Sum.inl ⟨S, pi, eta0⟩)
            (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega hquota q) =
          Pi.single (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi q)
            (Instrument.weightedChoiceScale K omega) := by
      unfold reconstructionKraus
      apply reconstructionSuccessKraus_row
    rw [Finset.sum_eq_single eta0]
    · refine (Matrix.conjLinearMap_apply_of_row_eq_single _ sigma (hrows qa) (hrows qb)).trans ?_
      calc
        (Instrument.weightedChoiceScale K omega * sigma xA xB) *
            star (Instrument.weightedChoiceScale K omega) =
          (star (Instrument.weightedChoiceScale K omega) *
            Instrument.weightedChoiceScale K omega) * sigma xA xB := by ring
        _ = ((K omega).toReal : ℂ) * sigma xA xB := by
          rw [Instrument.weightedChoiceScale_star_mul]
    · intro eta _ heta
      have hcontrol : eta.1 ≠ omega := by
        intro h
        apply heta
        apply Subtype.ext
        exact h
      simp_rw [hrow_of_control_ne eta hcontrol]
      simp
    · simp
  · have hzero : K omega = 0 := bot_unique (le_of_not_gt hpos)
    have hzreal : ((K omega).toReal : ℂ) = 0 := by
      rw [hzero, ENNReal.toReal_zero, Complex.ofReal_zero]
    rw [hzreal, zero_mul]
    apply Finset.sum_eq_zero
    intro eta _
    have hcontrol : eta.1 ≠ omega := by
      intro h
      apply hpos
      rw [← h]
      exact eta.2
    simp_rw [hrow_of_control_ne eta hcontrol]
    simp only [zero_mul, Finset.sum_const_zero, star_zero, mul_zero]

private theorem retainedMid_success
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : Op (ComparisonPreInput N))
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (q q' : (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space) :
    let pre := comparisonPre N nK mZ mX pA pB hN
      (Matrix.reindex (comparisonPreInputEquiv N)
        (comparisonPreInputEquiv N) rho)
    let mid := retainedControlLift N (nK + mZ + mX)
      (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
      (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q) pre
    let block : Op (Signals (nK + mZ + mX)) :=
      Matrix.of fun i j =>
        (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).channel rho
            (pairFunctions Bit Bit (nK + mZ + mX) i)
            (pairFunctions Bit Bit (nK + mZ + mX) j)
    mid
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q, Sum.inl S)
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q', Sum.inl S) =
      comparisonPreSuccessCoefficient N nK mZ mX pA pB *
        retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q block
          (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q)
          (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q') := by
  dsimp only
  let block : Op (Signals (nK + mZ + mX)) := fun i j =>
    (selectedInputMarginalInstrument (increasingSubsetEmbedding S)).channel rho
      (pairFunctions Bit Bit (nK + mZ + mX) i) (pairFunctions Bit Bit (nK + mZ + mX) j)
  let regrouped := Matrix.reindex
    (comparisonPreToRetainedControlEquiv N (nK + mZ + mX))
    (comparisonPreToRetainedControlEquiv N (nK + mZ + mX))
    (comparisonPre N nK mZ mX pA pB hN
      (Matrix.reindex (comparisonPreInputEquiv N) (comparisonPreInputEquiv N) rho))
  have hin : Matrix.reindex (weightedScheduleUnitInputEquiv N) (weightedScheduleUnitInputEquiv N)
      (Matrix.reindex (comparisonPreInputEquiv N) (comparisonPreInputEquiv N) rho) = rho := by
    ext a b
    simp [comparisonPreInputEquiv, Matrix.reindex_apply]
  have hblock : regrouped.submatrix (fun i => (i, Sum.inl S)) (fun i => (i, Sum.inl S)) =
      comparisonPreSuccessCoefficient N nK mZ mX pA pB • block := by
    ext i j
    change (comparisonPreInstrument N nK mZ mX pA pB hN).channel
      (Matrix.reindex (weightedScheduleUnitInputEquiv N) (weightedScheduleUnitInputEquiv N)
        (Matrix.reindex (comparisonPreInputEquiv N) (comparisonPreInputEquiv N) rho))
      (pairFunctions Bit Bit (nK + mZ + mX) i, Sum.inl S)
      (pairFunctions Bit Bit (nK + mZ + mX) j, Sum.inl S) = _
    rw [hin, comparisonPreInstrument_success_apply]
    rfl
  change mapTensorId (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)
    (ComparisonControl N (nK + mZ + mX)) regrouped
    (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q, Sum.inl S)
    (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q', Sum.inl S) = _
  rw [mapTensorId_apply, hblock, map_smul]
  rfl

private theorem retainedAnalysisSiftedState_selected
    (N nK mZ mX : ℕ) (rho : Op (ComparisonPreInput N))
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (x : (FinalStage.rawSystem (nK + mZ + mX)).total) :
    let n := nK + mZ + mX
    let M := (selectedInputMarginalInstrument (increasingSubsetEmbedding S)).channel rho
    let e := TwoParty.pairEquiv (Bits n) (Bits n)
    let rhoP := Matrix.reindex e.symm e.symm M
    let Wphys : Op (ComparisonPreInput N × Unit) := fun i j => rho i.1 j.1
    retainedAnalysisSiftedState packedPESel packedXSel pi rhoP x x =
      nativeSelectedBornBlock S (@Sampling.packedPESel nK mZ mX)
        (@Sampling.packedXSel nK mZ mX) pi (x .alice) (x .bob) Wphys () () := by
  let n := nK + mZ + mX
  let M := (selectedInputMarginalInstrument (increasingSubsetEmbedding S)).channel rho
  let e := TwoParty.pairEquiv (Bits n) (Bits n)
  let rhoP := Matrix.reindex e.symm e.symm M
  let Wphys : Op (ComparisonPreInput N × Unit) := fun i j => rho i.1 j.1
  dsimp only
  let kappa := Model.siftPermHalf n (@Sampling.packedPESel nK mZ mX)
    (@Sampling.packedXSel nK mZ mX) pi
  let kp := Matrix.kronecker kappa kappa
  have hentry : retainedAnalysisSiftedState packedPESel packedXSel pi rhoP x x =
      (kp * M * kpᴴ) (e x) (e x) := by
    have h := congrFun₂ (reindex_retainedAnalysisSiftedState
      (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) pi M) (e x) (e x)
    change retainedAnalysisSiftedState packedPESel packedXSel pi rhoP
      (e.symm (e x)) (e.symm (e x)) = (kp * M * kpᴴ) (e x) (e x) at h
    rw [e.symm_apply_apply] at h
    exact h
  rw [hentry]
  let knative := nativeSiftPairKraus n (@Sampling.packedPESel nK mZ mX)
    (@Sampling.packedXSel nK mZ mX) pi (x .alice) (x .bob)
  change (kp * M * kpᴴ) (e x) (e x) = (knative * M * knativeᴴ) () ()
  have hrow (y : Bits n × Bits n) : kp (e x) y = knative () y := by
    rcases y with ⟨yA, yB⟩
    simp [kp, kappa, e, knative, TwoParty.pairEquiv, nativeSiftPairKraus,
      nativeSiftMeasurementRow, Instrument.computationalMeasurement,
      Instrument.nondemolitionReadout, Instrument.nondemolitionReadoutKraus, Matrix.kronecker]
  rw [mul_mul_conjTranspose_apply, mul_mul_conjTranspose_apply]
  simp only [hrow]

private theorem retainedAnalysisReal_success
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : Op (ComparisonPreInput N))
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    let block : Op (Signals (nK + mZ + mX)) :=
      Matrix.of fun i j =>
        (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).channel rho
            (pairFunctions Bit Bit (nK + mZ + mX) i)
            (pairFunctions Bit Bit (nK + mZ + mX) j)
    let Wphys : Op (ComparisonPreInput N × Unit) :=
      Matrix.of fun i j => rho i.1 j.1
    retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q block
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
          ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
            (pi, qa)))
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
          ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
            (pi, qb))) =
      if qa = qb then
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV
              (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            if rawClassicalTailOutputPoint
                (nK + mZ + mX) (mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q x st = qa then
              (Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹ *
                ((Fintype.card (KeyHashSeedPairEV
                    (nK + mZ + mX) ell ellEV
                    (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                  nativeSelectedBornBlock S
                    (@Sampling.packedPESel nK mZ mX)
                    (@Sampling.packedXSel nK mZ mX) pi
                    (x .alice)
                    (x .bob) Wphys () ())
            else 0
      else 0 := by
  let n := nK + mZ + mX
  let M : Op (Bits n × Bits n) :=
    (selectedInputMarginalInstrument (increasingSubsetEmbedding S)).channel rho
  let e := TwoParty.pairEquiv (Bits n) (Bits n)
  let rhoP := Matrix.reindex e.symm e.symm M
  let D := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
  let Wphys : Op (ComparisonPreInput N × Unit) := fun i j => rho i.1 j.1
  have hNative (x : (FinalStage.rawSystem n).total) :
      retainedAnalysisSiftedState (@Sampling.packedPESel nK mZ mX)
        (@Sampling.packedXSel nK mZ mX) pi rhoP x x =
      nativeSelectedBornBlock S (@Sampling.packedPESel nK mZ mX)
        (@Sampling.packedXSel nK mZ mX) pi (x .alice) (x .bob) Wphys () () :=
    retainedAnalysisSiftedState_selected N nK mZ mX rho S pi x
  have hprogram := retainedAnalysisProgram_denote_apply nK mZ mX ell ellEV leakEC ec delta Q
    rhoP (D.symm (pi, qa)) (D.symm (pi, qb))
  have hin : Matrix.reindex
      ((pairFunctions Bit Bit n).trans e.symm) ((pairFunctions Bit Bit n).trans e.symm)
      (Matrix.of fun i j => M (pairFunctions Bit Bit n i) (pairFunctions Bit Bit n j)) = rhoP := by
    ext i j
    simp [rhoP, Matrix.reindex_apply]
  dsimp only
  unfold retainedAnalysisReal
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Matrix.coe_reindexLinearEquiv]
  rw [hin]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_trans_apply,
    Equiv.symm_apply_apply]
  simp only [LinearEquiv.coe_toLinearMap, Matrix.coe_reindexLinearEquiv,
    Matrix.reindex_apply, Matrix.submatrix_apply] at hprogram
  rw [hprogram]
  have hD (q : RetainedAnalysisOutput nK mZ mX ell ellEV leakEC) :
      retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC (D.symm q) = q :=
    D.apply_symm_apply q
  simp only [hD, Equiv.apply_eq_iff_eq, Prod.mk.injEq, true_and]
  simp_rw [hNative]
  rfl

/-- On a quota-success exit, the BB84 program and the factorized real map have the same complete
output block for every complex input operator and every pair of classical-tail outputs. -/
theorem retainedFactorization_success_sector
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : Op (Measurement.weightedStreamSystem Unit N).total)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    (Matrix.reindexLinearEquiv ℂ ℂ (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec
      delta Q) (constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q)).toLinearMap
      ((construction pA pB N nK mZ mX ell ellEV leakEC ec delta Q).denote rho)
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qa)
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qb) =
      let mid := retainedControlLift N (nK + mZ + mX)
        (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
        (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)
        (comparisonPre N nK mZ mX pA pB hN
          rho)
      reconstruction N nK mZ mX ell ellEV leakEC pA pB mid
        (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega hquota qa)
        (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega hquota qb) := by
  dsimp only
  rw [reconstruction_success pA pB N nK mZ mX ell ellEV leakEC
    omega hquota qa qb]
  let rhoBits : Op (ComparisonPreInput N) :=
    (Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
      (weightedScheduleUnitInputEquiv N)).toLinearMap rho
  have hinput : Matrix.reindex (comparisonPreInputEquiv N) (comparisonPreInputEquiv N)
      rhoBits = rho := by
    ext i j
    simp [comparisonPreInputEquiv, rhoBits, Matrix.reindex_apply]
  conv_rhs => rw [← hinput]
  simp_rw [retainedMid_success pA pB N nK mZ mX ell ellEV leakEC hN
    ec delta Q rhoBits]
  simp_rw [retainedAnalysisReal_success N nK mZ mX ell ellEV leakEC
    ec delta Q rhoBits]
  rw [program_denote_success_output_formula pA pB N nK mZ mX
    ell ellEV leakEC omega hquota ec delta Q rho qa qb]
  by_cases hq : qa = qb
  · subst qb
    simp only [ite_eq_left]
    have hcoeff
        (S : Set.powersetCard (Fin N) (nK + mZ + mX))
        (pi : Equiv.Perm (Fin (nK + mZ + mX))) :
        ((totalSelectedControlKernel N nK mZ mX pA pB
            (Math.FiniteEmbedding.joinSubsetPerm S pi) omega).toReal : ℂ) *
            (comparisonPreSuccessCoefficient N nK mZ mX pA pB *
              (Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹) =
          ((selectionSuccessMass N nK mZ mX pA pB *
            uniformRetainedSubset hN S *
            (uniformInnerPerm (nK + mZ + mX) pi *
              totalSelectedControlKernel N nK mZ mX pA pB
                (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)).toReal : ℂ) := by
      simp [comparisonPreSuccessCoefficient, uniformRetainedSubset,
        uniformInnerPerm, PMF.uniformOfFintype_apply, ENNReal.toReal_mul]
      ring
    let Wphys : Op (ComparisonPreInput N × Unit) :=
      Matrix.of fun i j => rhoBits i.1 j.1
    have hWphys :
        (Matrix.of fun i j =>
          ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
            (weightedScheduleUnitInputEquiv N)).toLinearMap rho) i.1 j.1) =
          Wphys := by
      rfl
    have hreconstruct
        (x : (FinalStage.rawSystem (nK + mZ + mX)).total) :
        ((rawControlLaw N pA pB omega).toReal : ℂ) *
            fixedBasisSelectedBornBlock (selectedEmbedding omega hquota)
              omega.a omega.b
              (x .alice)
              (x .bob) Wphys () () =
          ∑ S : Set.powersetCard (Fin N) (nK + mZ + mX),
            ∑ pi : Equiv.Perm (Fin (nK + mZ + mX)),
              ((selectionSuccessMass N nK mZ mX pA pB *
                uniformRetainedSubset hN S *
                (uniformInnerPerm (nK + mZ + mX) pi *
                  totalSelectedControlKernel N nK mZ mX pA pB
                    (Math.FiniteEmbedding.joinSubsetPerm S pi)
                    omega)).toReal : ℂ) *
                nativeSelectedBornBlock S
                  (@Sampling.packedPESel nK mZ mX)
                  (@Sampling.packedXSel nK mZ mX) pi
                  (x .alice)
                  (x .bob) Wphys () () := by
      exact (totalized_success_native_formula N nK mZ mX pA pB hN
        omega hquota
        (x .alice)
        (x .bob)
        Wphys () ()).symm
    have hterm
        (S : Set.powersetCard (Fin N) (nK + mZ + mX))
        (pi : Equiv.Perm (Fin (nK + mZ + mX)))
        (x : (FinalStage.rawSystem (nK + mZ + mX)).total) :
        ((totalSelectedControlKernel N nK mZ mX pA pB
          (Math.FiniteEmbedding.joinSubsetPerm S pi) omega).toReal : ℂ) *
          (comparisonPreSuccessCoefficient N nK mZ mX pA pB *
            ((Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹ *
              ((Fintype.card (KeyHashSeedPairEV
                (nK + mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                nativeSelectedBornBlock S
                  (@Sampling.packedPESel nK mZ mX)
                  (@Sampling.packedXSel nK mZ mX) pi
                  (x .alice)
                  (x .bob) Wphys () ()))) =
          (Fintype.card (KeyHashSeedPairEV
            (nK + mZ + mX) ell ellEV
            (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
            ((selectionSuccessMass N nK mZ mX pA pB *
              uniformRetainedSubset hN S *
              (uniformInnerPerm (nK + mZ + mX) pi *
                totalSelectedControlKernel N nK mZ mX pA pB
                  (Math.FiniteEmbedding.joinSubsetPerm S pi)
                  omega)).toReal : ℂ) *
            nativeSelectedBornBlock S
              (@Sampling.packedPESel nK mZ mX)
              (@Sampling.packedXSel nK mZ mX) pi
              (x .alice)
              (x .bob) Wphys () () := by
      calc
        _ = (Fintype.card (KeyHashSeedPairEV
              (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
            ((((totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega).toReal : ℂ) *
                (comparisonPreSuccessCoefficient N nK mZ mX pA pB *
                  (Fintype.card
                    (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹)) *
              nativeSelectedBornBlock S
                (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) pi
                (x .alice)
                (x .bob) Wphys () ()) := by ring
        _ = _ := by
          rw [hcoeff S pi]
          ring
    rw [hWphys]
    simp_rw [hreconstruct]
    simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    simp_rw [hterm]
    have hite {A B : Type} [Fintype A] [Fintype B]
        (p : Prop) [Decidable p] (f : A → B → ℂ) :
        (if p then ∑ a, ∑ b, f a b else 0) =
          ∑ a, ∑ b, if p then f a b else 0 := by
      by_cases hp : p <;> simp [hp]
    simp_rw [hite]
    conv_rhs =>
      enter [2, S]
      rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs =>
      enter [2, x]
      enter [2, S]
      rw [Finset.sum_comm]
    conv_rhs =>
      enter [2, x]
      rw [Finset.sum_comm]
    simp only [mul_assoc]
  · simp only [ite_eq_right hq, mul_zero, Finset.sum_const_zero]

end QKD.BB84.Reduction
