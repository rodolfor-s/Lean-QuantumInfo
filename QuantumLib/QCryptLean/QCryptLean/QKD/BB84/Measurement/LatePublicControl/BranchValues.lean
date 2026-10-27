import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.Instrument.UniformChoice
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program.Classical
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.Program.ExitWeight
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.Combinatorics.DoubleProductSum
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.Measurement
import QCryptLean.QKD.BB84.Measurement.LatePublicControl
import QCryptLean.QKD.BB84.Measurement.OutputLaw
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Measurement.SelectedRecords
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.Quantum.Operators.Basic

/-! # Native public-control operation checks -/

open Quantum.Operators (Op)

open scoped Matrix BigOperators ENNReal
open Matrix
noncomputable section
namespace QKD.BB84.Measurement
open LOCC LOCC.TwoParty QKD.BB84.Sampling

/-- Alice's basis readout selects the diagonal entries with the announced basis string. -/
private theorem completedBasisAliceAnnouncement_liftedOperation_diag (N : ℕ)
    (a : Fin N → Basis)
    (sigma : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total)
    (rA rB : CompletedLocalRecord N) :
    (announceAliceBases N).successorOperation a sigma
        ((pairEquiv _ _).symm (rA, rB)) ((pairEquiv _ _).symm (rA, rB)) =
      if completedBasisString N rA = a then
        sigma ((pairEquiv _ _).symm (rA, rB)) ((pairEquiv _ _).symm (rA, rB))
      else 0 := by
  refine (AnnouncedAction.successorOperation_alice_apply
    (Instrument.nondemolitionReadout (completedBasisString N)) id a sigma rA rA rB rB).trans ?_
  simp only [Instrument.nondemolitionReadout_operation_apply, Matrix.submatrix_apply, and_self]

/-- The two basis readouts select the diagonal entries with both announced basis strings. -/
private theorem completedBasisAnnouncements_liftedOperation_diag (N : ℕ)
    (a b : Fin N → Basis)
    (sigma : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total)
    (rA rB : CompletedLocalRecord N) :
    (announceBobBases N).successorOperation b
        ((announceAliceBases N).successorOperation a sigma)
        ((pairEquiv _ _).symm (rA, rB)) ((pairEquiv _ _).symm (rA, rB)) =
      if completedBasisString N rA = a ∧ completedBasisString N rB = b then
        sigma ((pairEquiv _ _).symm (rA, rB)) ((pairEquiv _ _).symm (rA, rB))
      else 0 := by
  refine (AnnouncedAction.successorOperation_bob_apply
    (Instrument.nondemolitionReadout (completedBasisString N)) id b _ rA rA rB rB).trans ?_
  simp only [Instrument.nondemolitionReadout_operation_apply, and_self]
  refine (if_congr Iff.rfl
    (completedBasisAliceAnnouncement_liftedOperation_diag N a sigma rA rB) rfl).trans ?_
  by_cases hA : completedBasisString N rA = a <;>
    by_cases hB : completedBasisString N rB = b <;> simp [hA, hB]

/-- The announced shuffle preserves the registers and contributes its uniform probability. -/
theorem shuffleAnnouncement_liftedOperation_apply (N : ℕ) (a b : Fin N → Basis)
    (order : Shuffle a b)
    (upsilon : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total) :
    (announceShuffle a b).successorOperation order upsilon =
      (Fintype.card (Shuffle a b) : ℂ)⁻¹ • upsilon := by
  ext q q'
  obtain ⟨⟨rA, rB⟩, rfl⟩ := (pairEquiv _ _).symm.surjective q
  obtain ⟨⟨rA', rB'⟩, rfl⟩ := (pairEquiv _ _).symm.surjective q'
  refine (AnnouncedAction.successorOperation_alice_apply
    (Instrument.uniformSample (CompletedLocalRecord N) (Shuffle a b))
      id order upsilon rA rA' rB rB').trans ?_
  rw [Instrument.uniformSample_operation]
  rfl

/-- Retaining records after public control gives the selected measurement law with its weight. -/
theorem weightedLatePublicSelectionProgram_success_apply
    (pA pB : PMF Basis) (N nK mZ mX : ℕ)
    (omega : RawControl N) (h : HasQuotas nK mZ mX omega)
    (rho : Op (weightedStreamSystem Unit N).total)
    (q q' : SelectedLocalRecord N (nK + mZ + mX) ×
      SelectedLocalRecord N (nK + mZ + mX)) :
    let sigma : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total :=
      measurementState pA pB Unit N rho
    let upsilon : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total :=
      (announceBobBases N).successorOperation omega.b
      ((announceAliceBases N).successorOperation omega.a sigma)
    (retainBob (A := SelectedLocalRecord N (nK + mZ + mX))
          (selectedEmbedding omega h)).successorOperation ()
      ((retainAlice (B := CompletedLocalRecord N)
          (selectedEmbedding omega h)).successorOperation ()
        ((announceShuffle omega.a omega.b).successorOperation omega.order upsilon))
      ((pairEquiv _ _).symm q) ((pairEquiv _ _).symm q') =
      if q.1.1 = omega.a ∧ q'.1.1 = omega.a ∧
          q.2.1 = omega.b ∧ q'.2.1 = omega.b then
        (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ *
          selectedMeasurementLaw pA pB (selectedEmbedding omega h)
            ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
              (weightedScheduleUnitInputEquiv N)).toLinearMap rho) q q'
      else 0 := by
  intro sigma upsilon
  refine (congrArg (fun tau : Op (system (CompletedLocalRecord N)
      (CompletedLocalRecord N)).total =>
    (retainBob (A := SelectedLocalRecord N (nK + mZ + mX))
      (selectedEmbedding omega h)).successorOperation ()
      ((retainAlice (B := CompletedLocalRecord N) (selectedEmbedding omega h)).successorOperation
        () tau) ((pairEquiv _ _).symm q) ((pairEquiv _ _).symm q'))
      (shuffleAnnouncement_liftedOperation_apply N omega.a omega.b omega.order upsilon)).trans ?_
  refine (congrFun (congrFun (map_smul
    (((retainBob (A := SelectedLocalRecord N (nK + mZ + mX))
      (selectedEmbedding omega h)).successorOperation ()).comp
      ((retainAlice (B := CompletedLocalRecord N)
        (selectedEmbedding omega h)).successorOperation ()))
    (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ upsilon) _) _).trans ?_
  change (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ * _ = _
  have hselectedSigma :
      (retainBob (A := SelectedLocalRecord N (nK + mZ + mX))
          (selectedEmbedding omega h)).successorOperation ()
        ((retainAlice (B := CompletedLocalRecord N)
          (selectedEmbedding omega h)).successorOperation () sigma)
          ((pairEquiv _ _).symm q) ((pairEquiv _ _).symm q') =
        selectedMeasurementLaw pA pB (selectedEmbedding omega h)
          ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
            (weightedScheduleUnitInputEquiv N)).toLinearMap rho) q q' :=
    congrFun (congrFun (LinearMap.congr_fun
      (measurementState_retain_eq pA pB N (selectedEmbedding omega h)) rho) q) q'
  have hupsilonDiag (rA rB : CompletedLocalRecord N) :
      upsilon ((pairEquiv _ _).symm (rA, rB)) ((pairEquiv _ _).symm (rA, rB)) =
        if completedBasisString N rA = omega.a ∧ completedBasisString N rB = omega.b then
          sigma ((pairEquiv _ _).symm (rA, rB)) ((pairEquiv _ _).symm (rA, rB))
        else 0 :=
    completedBasisAnnouncements_liftedOperation_diag N omega.a omega.b sigma rA rB
  have hselectedBasis
      (r : CompletedLocalRecord N) :
      (selectedLocalRecord (selectedEmbedding omega h) r).1 =
        completedBasisString N r := by
    rfl
  have hselectedUpsilon :
      (retainBob (A := SelectedLocalRecord N (nK + mZ + mX))
          (selectedEmbedding omega h)).successorOperation ()
        ((retainAlice (B := CompletedLocalRecord N)
          (selectedEmbedding omega h)).successorOperation () upsilon)
          ((pairEquiv _ _).symm q) ((pairEquiv _ _).symm q') =
        if q.1.1 = omega.a ∧ q'.1.1 = omega.a ∧
            q.2.1 = omega.b ∧ q'.2.1 = omega.b then
          (retainBob (A := SelectedLocalRecord N (nK + mZ + mX))
          (selectedEmbedding omega h)).successorOperation ()
        ((retainAlice (B := CompletedLocalRecord N)
          (selectedEmbedding omega h)).successorOperation () sigma)
          ((pairEquiv _ _).symm q) ((pairEquiv _ _).symm q')
        else 0 := by
    refine (functionAndForget_pair_operation_apply
      (selectedLocalRecord (selectedEmbedding omega h))
      (selectedLocalRecord (selectedEmbedding omega h)) upsilon q.1 q'.1 q.2 q'.2).trans ?_
    refine Eq.trans ?_ (congrArg (fun z : ℂ =>
      if q.1.1 = omega.a ∧ q'.1.1 = omega.a ∧ q.2.1 = omega.b ∧ q'.2.1 = omega.b
      then z else 0)
      (functionAndForget_pair_operation_apply
        (selectedLocalRecord (selectedEmbedding omega h))
        (selectedLocalRecord (selectedEmbedding omega h)) sigma q.1 q'.1 q.2 q'.2).symm)
    by_cases hg : q.1.1 = omega.a ∧ q'.1.1 = omega.a ∧
        q.2.1 = omega.b ∧ q'.2.1 = omega.b
    · rw [ite_eq_left hg]
      apply Finset.sum_congr rfl
      intro rB _
      by_cases hb : q.2 =
          selectedLocalRecord (selectedEmbedding omega h) rB ∧
        q'.2 = selectedLocalRecord (selectedEmbedding omega h) rB
      · rw [ite_eq_left hb, ite_eq_left hb]
        apply Finset.sum_congr rfl
        intro rA _
        by_cases ha : q.1 =
            selectedLocalRecord (selectedEmbedding omega h) rA ∧
          q'.1 = selectedLocalRecord (selectedEmbedding omega h) rA
        · rw [ite_eq_left ha, ite_eq_left ha, hupsilonDiag]
          have hAr : completedBasisString N rA = omega.a := by
            rw [← hselectedBasis, ← ha.1]
            exact hg.1
          have hBr : completedBasisString N rB = omega.b := by
            rw [← hselectedBasis, ← hb.1]
            exact hg.2.2.1
          rw [ite_eq_left ⟨hAr, hBr⟩]
        · rw [ite_eq_right ha, ite_eq_right ha]
      · rw [ite_eq_right hb, ite_eq_right hb]
    · rw [ite_eq_right hg]
      apply Finset.sum_eq_zero
      intro rB _
      by_cases hb : q.2 =
          selectedLocalRecord (selectedEmbedding omega h) rB ∧
        q'.2 = selectedLocalRecord (selectedEmbedding omega h) rB
      · rw [ite_eq_left hb]
        apply Finset.sum_eq_zero
        intro rA _
        by_cases ha : q.1 =
            selectedLocalRecord (selectedEmbedding omega h) rA ∧
          q'.1 = selectedLocalRecord (selectedEmbedding omega h) rA
        · rw [ite_eq_left ha, hupsilonDiag]
          have hnot : ¬ (completedBasisString N rA = omega.a ∧
              completedBasisString N rB = omega.b) := by
            rintro ⟨hAr, hBr⟩
            apply hg
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [ha.1, hselectedBasis]
              exact hAr
            · rw [ha.2, hselectedBasis]
              exact hAr
            · rw [hb.1, hselectedBasis]
              exact hBr
            · rw [hb.2, hselectedBasis]
              exact hBr
          rw [ite_eq_right hnot]
        · rw [ite_eq_right ha]
      · rw [ite_eq_right hb]
  refine (congrArg (fun z : ℂ => (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ * z)
    (hselectedUpsilon.trans (congrArg (fun z : ℂ =>
      if q.1.1 = omega.a ∧ q'.1.1 = omega.a ∧ q.2.1 = omega.b ∧ q'.2.1 = omega.b
      then z else 0) hselectedSigma))).trans ?_
  by_cases hg : q.1.1 = omega.a ∧ q'.1.1 = omega.a ∧
      q.2.1 = omega.b ∧ q'.2.1 = omega.b <;> simp [hg]

/-- The discard branch sums the Born weights of the announced basis strings. -/
theorem weightedLatePublicSelectionProgram_abort_apply
    (pA pB : PMF Basis) (N : ℕ)
    (omega : RawControl N)
    (rho : Op (weightedStreamSystem Unit N).total) :
    let sigma : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total :=
      measurementState pA pB Unit N rho
    let upsilon : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total :=
      (announceBobBases (A := CompletedLocalRecord N) N).successorOperation omega.b
      ((announceAliceBases (B := CompletedLocalRecord N) N).successorOperation omega.a sigma)
    (discardBob (A := Unit) (B := CompletedLocalRecord N)).successorOperation ()
      ((discardAlice (A := CompletedLocalRecord N)
        (B := CompletedLocalRecord N)).successorOperation ()
        ((announceShuffle (B := CompletedLocalRecord N) omega.a omega.b).successorOperation
          omega.order upsilon))
      ((pairEquiv Unit Unit).symm ((), ())) ((pairEquiv Unit Unit).symm ((), ())) =
      (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ *
      ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
      ((Sampling.basisStringLaw N pB omega.b).toReal : ℂ) *
      ∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
        (Matrix.conjLinearMap
          (fixedBasisPairKraus
            (completeStoredRecords omega.a xA)
            (completeStoredRecords omega.b xB))
          ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
            (weightedScheduleUnitInputEquiv N)).toLinearMap rho)) () () := by
  intro sigma upsilon
  refine (congrArg (fun tau : Op (system (CompletedLocalRecord N)
    (CompletedLocalRecord N)).total =>
      (discardBob (A := Unit) (B := CompletedLocalRecord N)).successorOperation ()
        ((discardAlice (A := CompletedLocalRecord N)
          (B := CompletedLocalRecord N)).successorOperation () tau)
          ((pairEquiv Unit Unit).symm ((), ())) ((pairEquiv Unit Unit).symm ((), ())))
    (shuffleAnnouncement_liftedOperation_apply N omega.a omega.b omega.order upsilon)).trans ?_
  refine (discard_pair_operation_apply
    ((Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ • upsilon)).trans ?_
  simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  have hupsilonDiag (rA rB : CompletedLocalRecord N) :
      upsilon ((pairEquiv _ _).symm (rA, rB)) ((pairEquiv _ _).symm (rA, rB)) =
        if completedBasisString N rA = omega.a ∧ completedBasisString N rB = omega.b then
          sigma ((pairEquiv _ _).symm (rA, rB)) ((pairEquiv _ _).symm (rA, rB))
        else 0 :=
    completedBasisAnnouncements_liftedOperation_diag N omega.a omega.b sigma rA rB
  let recordStreamEquiv : CompletedLocalRecord N ≃
      (Fin N → StoredRecord) :=
    (finishedStreamEquiv Unit N).trans (unitProdEquiv _)
  have hsumRecords (g : CompletedLocalRecord N → ℂ) :
      (∑ q, g q) = ∑ r : Fin N → StoredRecord,
        g (recordStreamEquiv.symm r) := by
    exact (Equiv.sum_comp recordStreamEquiv.symm g).symm
  have hcompletedBasis (r : Fin N → StoredRecord) :
      completedBasisString N (recordStreamEquiv.symm r) =
        storedBasisString r := by
    simp [completedBasisString, recordStreamEquiv, finishedStreamEquiv,
      unitProdEquiv]
  let recordDataEquiv : (Fin N → StoredRecord) ≃
      (Fin N → Basis) × (Fin N → Bit) :=
    { toFun := fun r =>
        (storedBasisString r, fun i => (r i).2.2)
      invFun := fun q i => ((), (q.1 i, q.2 i))
      left_inv := by
        intro r
        funext i
        rcases hri : r i with ⟨u, theta, x⟩
        rcases u with ⟨⟩
        simp only [storedBasisString, hri]
      right_inv := by
        rintro ⟨theta, x⟩
        rfl }
  have hrecordDataSymm
      (q : (Fin N → Basis) × (Fin N → Bit)) :
      recordDataEquiv.symm q =
        fun i => ((), (q.1 i, q.2 i)) := by
    rfl
  have hstoredData (theta : Fin N → Basis) (x : Fin N → Bit) :
      storedBasisString (fun i => ((), (theta i, x i))) = theta := by
    rfl
  have hsumRecordData (g : (Fin N → StoredRecord) → ℂ) :
      (∑ r, g r) =
        ∑ q : (Fin N → Basis) × (Fin N → Bit),
          g (recordDataEquiv.symm q) := by
    exact (Equiv.sum_comp recordDataEquiv.symm g).symm
  have hsigmaRecords (rA rB : Fin N → StoredRecord) :
      sigma
          ((TwoParty.pairEquiv _ _).symm
            (recordStreamEquiv.symm rA, recordStreamEquiv.symm rB))
          ((TwoParty.pairEquiv _ _).symm
            (recordStreamEquiv.symm rA, recordStreamEquiv.symm rB)) =
        ((Sampling.basisStringLaw N pA
          (storedBasisString rA)).toReal : ℂ) *
        ((Sampling.basisStringLaw N pB
          (storedBasisString rB)).toReal : ℂ) *
        (Matrix.conjLinearMap (fixedBasisPairKraus rA rB)
          ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
            (weightedScheduleUnitInputEquiv N)).toLinearMap rho)) () () := by
    have hs := weightedMeasurementSchedule_output_apply pA pB N rho
      rA rA rB rB
    simp only [and_self, ite_true] at hs
    exact hs
  rw [Finset.sum_comm]
  rw [hsumRecords]
  simp_rw [hsumRecords, hupsilonDiag, hcompletedBasis, hsigmaRecords]
  rw [hsumRecordData]
  simp_rw [hsumRecordData, hrecordDataSymm, hstoredData]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single omega.a]
  · simp only [true_and]
    have hsumB (xA : Fin N → Bit) :
        (∑ thetaB : Fin N → Basis, ∑ xB : Fin N → Bit,
          if thetaB = omega.b then
            ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
              ((Sampling.basisStringLaw N pB thetaB).toReal : ℂ) *
              (Matrix.conjLinearMap
                (fixedBasisPairKraus
                  (completeStoredRecords omega.a xA)
                  (completeStoredRecords thetaB xB))
                ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
                  (weightedScheduleUnitInputEquiv N)).toLinearMap rho)) () ()
          else 0) =
        ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
          ((Sampling.basisStringLaw N pB omega.b).toReal : ℂ) *
          ∑ xB : Fin N → Bit,
            (Matrix.conjLinearMap
              (fixedBasisPairKraus
                (completeStoredRecords omega.a xA)
                (completeStoredRecords omega.b xB))
              ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
                (weightedScheduleUnitInputEquiv N)).toLinearMap rho)) () () := by
      rw [Finset.sum_eq_single omega.b]
      · simp only [ite_eq_left]
        rw [← Finset.mul_sum]
      · intro thetaB _ hthetaB
        apply Finset.sum_eq_zero
        intro xB _
        rw [ite_eq_right hthetaB]
      · simp
    let c : ℂ :=
      ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
        ((Sampling.basisStringLaw N pB omega.b).toReal : ℂ)
    have hselectedSums :
        (∑ xA : Fin N → Bit, ∑ thetaB : Fin N → Basis,
          ∑ xB : Fin N → Bit,
            if thetaB = omega.b then
              ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
                ((Sampling.basisStringLaw N pB thetaB).toReal : ℂ) *
                (Matrix.conjLinearMap
                  (fixedBasisPairKraus
                    (completeStoredRecords omega.a xA)
                    (completeStoredRecords thetaB xB))
                  ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
                    (weightedScheduleUnitInputEquiv N)).toLinearMap rho)) () ()
            else 0) =
          c * ∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
            (Matrix.conjLinearMap
              (fixedBasisPairKraus
                (completeStoredRecords omega.a xA)
                (completeStoredRecords omega.b xB))
              ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
                (weightedScheduleUnitInputEquiv N)).toLinearMap rho)) () () := by
      calc
        _ = ∑ xA : Fin N → Bit, c *
              ∑ xB : Fin N → Bit,
                (Matrix.conjLinearMap
                  (fixedBasisPairKraus
                    (completeStoredRecords omega.a xA)
                    (completeStoredRecords omega.b xB))
                  ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
                    (weightedScheduleUnitInputEquiv N)).toLinearMap rho)) () () := by
          apply Finset.sum_congr rfl
          intro xA _
          exact hsumB xA
        _ = _ := by
          rw [Finset.mul_sum]
    change (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ *
        (∑ xA : Fin N → Bit, ∑ thetaB : Fin N → Basis,
          ∑ xB : Fin N → Bit,
            if thetaB = omega.b then
              ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
                ((Sampling.basisStringLaw N pB thetaB).toReal : ℂ) *
                (Matrix.conjLinearMap
                  (fixedBasisPairKraus
                    (completeStoredRecords omega.a xA)
                    (completeStoredRecords thetaB xB))
                  ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
                    (weightedScheduleUnitInputEquiv N)).toLinearMap rho)) () ()
            else 0) = _
    rw [hselectedSums]
    unfold c
    simp only [Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
    simp_rw [Fintype.sum_prod_type]
    ring
  · intro thetaA _ hthetaA
    apply Finset.sum_eq_zero
    intro xA _
    apply Finset.sum_eq_zero
    intro thetaB _
    apply Finset.sum_eq_zero
    intro xB _
    rw [ite_eq_right]
    exact fun hab => hthetaA hab.1
  · simp

/-- The fixed-basis measurement rows of any two basis strings resolve the identity: their Born
weights over all outcome strings add up to the trace.

This is the completeness of the pair of destructive single-round measurements behind the
shortage-branch value; it holds for every operator, with no state, positivity or normalization
hypothesis. -/
theorem sum_matrixConjLinear_fixedBasisPairKraus (N : ℕ) (a b : Fin N → Basis)
    (ρ : Op ((Fin N → Bit) × (Fin N → Bit))) :
    (∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
      Matrix.conjLinearMap (fixedBasisPairKraus (completeStoredRecords a xA)
        (completeStoredRecords b xB)) ρ () ()) = ρ.trace := by
  have hcol (θ : Basis) (j j' : Bit) :
      (∑ s : Bit, star (basisUnitary θ s j) * basisUnitary θ s j') = if j = j' then 1 else 0 := by
    have h := congrFun₂ (fixedBasisKraus_complete θ) j j'
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Matrix.sum_apply, fixedBasisKraus] using h
  have hcomplete :
      (∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
        (fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB))ᴴ *
          fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB)) = 1 := by
    ext v v'
    have hterm (xA xB : Fin N → Bit) :
        ((fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB))ᴴ *
            fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB)) v v' =
          ∏ i, (star (basisUnitary (a i) (xA i) (v.1 i)) * basisUnitary (a i) (xA i) (v'.1 i)) *
            (star (basisUnitary (b i) (xB i) (v.2 i)) * basisUnitary (b i) (xB i) (v'.2 i)) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_unique,
        fixedBasisPairKraus, completeStoredRecords, star_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [star_mul']
      ring
    simp only [Matrix.sum_apply, hterm]
    rw [Fintype.sum_sum_prod (fun i s t =>
      (star (basisUnitary (a i) s (v.1 i)) * basisUnitary (a i) s (v'.1 i)) *
        (star (basisUnitary (b i) t (v.2 i)) * basisUnitary (b i) t (v'.2 i)))]
    simp only [← Finset.sum_mul_sum, hcol, Finset.prod_mul_distrib, Finset.prod_boole,
      Finset.mem_univ, forall_const, Matrix.one_apply]
    by_cases hv : v = v'
    · subst hv
      simp
    · rw [ite_eq_right hv]
      by_cases h1 : ∀ i, v.1 i = v'.1 i
      · have h2 : ¬ ∀ i, v.2 i = v'.2 i := fun h2 => hv (Prod.ext (funext h1) (funext h2))
        rw [ite_eq_left h1, ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, zero_mul]
  calc
    _ = ∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
          Matrix.trace ((fixedBasisPairKraus (completeStoredRecords a xA)
              (completeStoredRecords b xB))ᴴ *
            fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB) * ρ) := by
      refine Finset.sum_congr rfl fun xA _ => Finset.sum_congr rfl fun xB _ => ?_
      rw [← Matrix.trace_mul_cycle]
      simp [Matrix.conjLinearMap, Matrix.trace]
    _ = Matrix.trace ((∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
          (fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB))ᴴ *
            fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB)) *
          ρ) := by
      rw [Finset.sum_mul, Matrix.trace_sum]
      simp_rw [Finset.sum_mul, Matrix.trace_sum]
    _ = ρ.trace := by rw [hcomplete, Matrix.one_mul]

/-- Discarding the measured records after public control gives its mass times the input trace. -/
theorem weightedLatePublicSelectionProgram_shortage_apply
    (pA pB : PMF Basis) (N : ℕ) (omega : RawControl N)
    (rho : Op (weightedStreamSystem Unit N).total) :
    let sigma : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total :=
      measurementState pA pB Unit N rho
    let upsilon : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total :=
      (announceBobBases (A := CompletedLocalRecord N) N).successorOperation omega.b
      ((announceAliceBases (B := CompletedLocalRecord N) N).successorOperation omega.a sigma)
    (discardBob (A := Unit) (B := CompletedLocalRecord N)).successorOperation ()
      ((discardAlice (A := CompletedLocalRecord N)
        (B := CompletedLocalRecord N)).successorOperation ()
        ((announceShuffle (B := CompletedLocalRecord N) omega.a omega.b).successorOperation
          omega.order upsilon))
      ((pairEquiv Unit Unit).symm ((), ())) ((pairEquiv Unit Unit).symm ((), ())) =
      ((rawControlLaw N pA pB omega).toReal : ℂ) * rho.trace := by
  refine (weightedLatePublicSelectionProgram_abort_apply pA pB N omega rho).trans ?_
  rw [sum_matrixConjLinear_fixedBasisPairKraus, rawControlLaw_toReal_eq, trace_reindexOp]

end QKD.BB84.Measurement
