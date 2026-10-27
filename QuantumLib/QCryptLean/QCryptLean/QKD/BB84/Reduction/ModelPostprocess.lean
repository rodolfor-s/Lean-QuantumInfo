import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.Graft
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.BoundaryKeyLayout.Hom
import QCryptLean.LOCC.BoundaryKeyLayout.MatrixUnits
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.LinearAlgebra.MatrixUnits
import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.ClassicalSemantics
import QCryptLean.QKD.BB84.Model.DePaddedQuantumStack
import QCryptLean.QKD.BB84.Model.IdealChannelKeyReplace
import QCryptLean.QKD.BB84.Model.PermAnnounceRegister
import QCryptLean.QKD.BB84.Model.RealChannelEntrywise
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Reduction.ClassicalTail
import QCryptLean.QKD.BB84.Reduction.PackedSelector
import QCryptLean.QKD.BB84.Reduction.RetainedBlocks
import QCryptLean.QKD.BB84.Reduction.RetainedExperiment
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.BB84.TailTranscript
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.QKD.KeyedOutputRegister.KeyReplacement
import QCryptLean.QKD.KeyedOutputRegister.KeyReplacementAlgebra
import QCryptLean.QKD.OutputLayout
import QCryptLean.QKD.OutputLayout.Graft
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.DiamondAlgebra
import QCryptLean.Math.LinearAlgebra.Matrix.Reindex
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.RandomizedBlocking

/-!
# Classical postprocessing from the analytical model to the retained experiment

The model retains the full padded key/key/flag space, its actual public tuple and
an explicit trivial reference. The classical channel reads that tuple and writes
the retained experiment's heterogeneous complete output. Its real and ideal
identities give the coefficient-one retained-to-model distance bound.
-/

open Quantum.Operators Quantum.Channels Quantum.Symmetry
open scoped Matrix BigOperators Kronecker
open Matrix

noncomputable section

namespace QKD.BB84.Reduction

open LOCC LOCC.TwoParty QKD.BB84.Measurement QKD.BB84.FiniteKey QKD.BB84.Model

/-- The complete model output of a measured signal string and announced permutation. -/
def modelOutputIndex (n m ell ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ) (pi : Equiv.Perm (Fin n))
    (st : KeyHashSeedPairEV n ell ellEV peSel) (ω : Signals n) :
    KeyedOutput ell (SymPEAnnouncePublic n m ell ellEV peSel leakEC) × Unit :=
  (KeyedOutput.prodEquiv ell _ _ (outIndex n m ell ellEV peSel xSel leakEC ec delta Q st ω, pi), ())

open scoped Classical in
/-- Measurement followed by the classical kernel depends only on the input diagonal. -/
theorem realProtocolMapBare_eq_sum (n m ell ellEV : ℕ) (peSel xSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (delta Q : ℝ) (A : Op (Signals n)) :
    realProtocolMapBare n m ell ellEV peSel xSel leakEC ec delta Q A =
      ∑ c : Signals n, ∑ st : KeyHashSeedPairEV n ell ellEV peSel,
        (A c c * (Fintype.card (KeyHashSeedPairEV n ell ellEV peSel) : ℂ)⁻¹) •
          Matrix.single (outIndex n m ell ellEV peSel xSel leakEC ec delta Q st c)
            (outIndex n m ell ellEV peSel xSel leakEC ec delta Q st c) (1 : ℂ) := by
  rw [realProtocolMapBare, LinearMap.comp_apply, classicalPostBare_apply]
  have hdiag (c : Signals n) : classicalMap id A c c = A c c := by
    simp [classicalMap_apply, Matrix.sum_apply, Matrix.single_apply]
  simp only [hdiag, Finset.smul_sum, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

open scoped Classical in
/-- The model is the uniform permutation and seed mixture of its measured output points. -/
theorem symReal_eq_sum (n m ell ellEV : ℕ)
    (Q delta : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (rho : Op (Signals n)) :
    symReal n m ell ellEV Q delta peSel xSel leakEC ec rho =
      ∑ pi : Equiv.Perm (Fin n), ∑ c : Signals n,
        ∑ st : KeyHashSeedPairEV n ell ellEV peSel,
          ((n.factorial : ℂ)⁻¹ *
              ((siftedRotation n peSel xSel * permConjLin pi rho *
                  (siftedRotation n peSel xSel)ᴴ) c c *
                (Fintype.card (KeyHashSeedPairEV n ell ellEV peSel) : ℂ)⁻¹)) •
            Matrix.single (modelOutputIndex n m ell ellEV peSel xSel leakEC ec delta Q pi st c)
              (modelOutputIndex n m ell ellEV peSel xSel leakEC ec delta Q pi st c) (1 : ℂ) := by
  rw [symReal_apply_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun pi _ => ?_
  rw [realProtocolMapBare_eq_sum, map_sum]
  simp only [map_sum, map_smul, Matrix.reindex_sum, Matrix.reindex_smul, Finset.smul_sum,
    smul_smul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun st _ => ?_
  congr 1
  simp only [siftedPEAnnounceLinear, LinearMap.coe_mk, AddHom.coe_mk,
    permAnnounceProjector, Matrix.single_kronecker_single, mul_one,
    Matrix.reindex_apply, Matrix.submatrix_single_equiv]
  rfl

/-- The retained classical tail's final point is the final-stage point of its semantic decision flag
and its two key slots. -/
theorem rawClassicalTailFinalPoint_eq_finalStagePoint
    (n m ell ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ)
    (d : QKD.BB84.ClassicalTailData n m ell ellEV peSel leakEC)
    (x : (FinalStage.rawSystem n).total) :
    rawClassicalTailFinalPoint n m ell ellEV peSel xSel leakEC ec delta Q d x =
      finalStagePoint ell
        ((Equiv.boolNot.trans finTwoEquiv.symm)
          (QKD.BB84.acceptFlag n m ellEV peSel xSel leakEC ec delta Q
            d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob)))
        (QKD.BB84.aliceKey n ell peSel d.seedPair.1 (x .alice))
        (QKD.BB84.bobKey n ell peSel leakEC ec d.seedPair.1 d.syndrome (x .bob)) :=
  rfl

/-- The analytical output register, including its explicit trivial reference. -/
abbrev ModelOutput (nK mZ mX ell ellEV leakEC : ℕ) :=
  KeyedOutput ell (SymPEAnnouncePublic (nK + mZ + mX) (mZ + mX) ell ellEV
    (@Sampling.packedPESel nK mZ mX) leakEC) × Unit

variable (nK mZ mX ell ellEV leakEC : ℕ)

/-- Read the model's public tuple as the classical tail's actual announcements. -/
def modelTailData
    (t : PEAnnouncePublic (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    ClassicalTailData (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC :=
  { alicePE := fun i => (t.2 i).1
    bobPE := fun i => (t.2 i).2
    seedPair := t.1.1.1
    evTag := t.1.1.2
    syndrome := t.1.2 }

/-- The retained output point named by a padded model output, discarding abort keys. -/
def modelOutputPoint (j : ModelOutput nK mZ mX ell ellEV leakEC) :
    (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space :=
  (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
    (j.1.2.2.2, (Boundary.graftSpaceEquiv
        (classicalPreDecisionBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC)
        (fun _ => FinalStage.boundary ell)).symm
      ⟨(classicalTailExitEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC).symm
          (modelTailData nK mZ mX ell ellEV leakEC j.1.2.2.1),
        finalStagePoint ell ((Equiv.boolNot.trans finTwoEquiv.symm) j.1.2.1)
          j.1.1.1 j.1.1.2⟩)

open scoped Classical in
/-- Measure the full padded model output and prepare its retained output point. -/
def modelPostprocess : Operation (ModelOutput nK mZ mX ell ellEV leakEC)
    (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC) :=
  classicalMap (fun j => retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
    (modelOutputPoint nK mZ mX ell ellEV leakEC j))

/-- The model-to-retained postprocessor is trace preserving and completely positive. -/
theorem isChannel_modelPostprocess :
    IsChannel (modelPostprocess nK mZ mX ell ellEV leakEC) := by
  classical
  exact isChannel_classicalMap _

open scoped Classical in
/-- The classical postprocessor sends a diagonal matrix unit to its named output point. -/
theorem modelPostprocess_single (j : ModelOutput nK mZ mX ell ellEV leakEC) (c : ℂ) :
    modelPostprocess nK mZ mX ell ellEV leakEC (Matrix.single j j c) =
      Matrix.single
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
          (modelOutputPoint nK mZ mX ell ellEV leakEC j))
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
          (modelOutputPoint nK mZ mX ell ellEV leakEC j)) c := by
  classical
  simp [modelPostprocess, classicalMap_apply, Matrix.single_apply, apply_ite]

/-- `rawClassicalTailDataOf` with its fused announcement decoded: the parameter-estimation bits of
both parties, the seed pair, and Alice's verification tag and syndrome. -/
theorem rawClassicalTailDataOf_eq (n m ell ellEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (x : (FinalStage.rawSystem n).total)
    (st : KeyHashSeedPairEV n ell ellEV peSel) :
    rawClassicalTailDataOf n m ell ellEV peSel leakEC ec x st =
      { alicePE := fun j =>
          x .alice (peRoundIdx (m := m) peSel j)
        bobPE := fun j =>
          x .bob (peRoundIdx (m := m) peSel j)
        seedPair := st
        evTag := verificationTag n ellEV peSel st.2 (QKD.BB84.aliceRawKey n peSel (x .alice))
        syndrome := ec.syndrome (QKD.BB84.aliceRawKey n peSel (x .alice)) } := rfl

/-- The model's public tuple records exactly the classical tail's announcements. -/
theorem modelTailData_eq_rawClassicalTailDataOf
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (x : (FinalStage.rawSystem (nK + mZ + mX)).total)
    (st : KeyHashSeedPairEV (nK + mZ + mX) ell ellEV (@Sampling.packedPESel nK mZ mX)) :
    modelTailData nK mZ mX ell ellEV leakEC
        (((st, verificationTag (nK + mZ + mX) ellEV (@Sampling.packedPESel nK mZ mX)
            st.2 (aliceKeyString (@Sampling.packedPESel nK mZ mX)
              (jointOutcome (nK + mZ + mX) (x .alice) (x .bob)))),
          ec.syndrome (aliceKeyString (@Sampling.packedPESel nK mZ mX)
            (jointOutcome (nK + mZ + mX) (x .alice) (x .bob)))),
          (partEquiv (m := mZ + mX) (@Sampling.packedPESel nK mZ mX)
            (jointOutcome (nK + mZ + mX) (x .alice) (x .bob))).2) =
      rawClassicalTailDataOf (nK + mZ + mX) (mZ + mX) ell ellEV (@Sampling.packedPESel nK mZ mX)
        leakEC ec x st := rfl

/-- A model output of a raw outcome names the retained output of the same outcome. -/
theorem modelOutputPoint_modelOutputIndex
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (st : KeyHashSeedPairEV (nK + mZ + mX) ell ellEV (@Sampling.packedPESel nK mZ mX))
    (x : (FinalStage.rawSystem (nK + mZ + mX)).total) :
    modelOutputPoint nK mZ mX ell ellEV leakEC
        (modelOutputIndex (nK + mZ + mX) (mZ + mX) ell ellEV (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q pi st
          (jointOutcome (nK + mZ + mX) (x .alice) (x .bob))) =
      (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
        (pi, rawClassicalTailOutputPoint (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q
          x st) := by
  have hflag := Model.acceptFlag_eq (nK + mZ + mX) (mZ + mX) ellEV
    (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q
    (packedPESel_keyCount nK mZ mX) st.2 (x .alice) (x .bob)
  have hdata := modelTailData_eq_rawClassicalTailDataOf nK mZ mX ell ellEV leakEC ec x st
  simp only [rawClassicalTailOutputPoint, rawClassicalTailFinalPoint_eq_finalStagePoint,
    rawClassicalTailDataOf_eq]
  rw [hflag]
  unfold modelOutputPoint modelOutputIndex outIndex
  split_ifs with hg
  all_goals
    simp only [Announced.passOutputIndex, Announced.failOutputIndex,
      Announced.pePassOutIndex, Announced.peFailOutIndex, KeyedOutput.prodEquiv,
      Equiv.trans_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_apply,
      Prod.map_apply, Equiv.refl_apply]
    rw [hdata, rawClassicalTailDataOf_eq]
    rfl

/-- **The retained real map is the classical post-processing of the model's real map.**

For every complex input operator on the `4 ^ (nK + mZ + mX)`-dimensional round-grouped register,
the retained experiment's real map equals `modelPostprocess` after the analytical model's real
map `symReal` at sifted block `nK + mZ + mX`, test-set size `mZ + mX` and the
packed selectors.  The two maps read the same input register: the round-grouped-to-Alice/Bob
regrouping by `pairFunctions` is part of `retainedAnalysisReal` itself, so no input
relabelling occurs.  The permutation average, the sift conjugation and the joint measurement of
the model are the announced inner permutation, the two local sift operators and the two private
measurements of the retained experiment (`QKD.BB84.Model.siftPermHalf_pair_conj_reindex`,
`reindex_retainedAnalysisSiftedState`), and the model's announcement index names the retained
output point (`modelOutputPoint_modelOutputIndex`). -/
theorem retainedAnalysisReal_eq_modelPostprocess_comp
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q =
      (modelPostprocess nK mZ mX ell ellEV leakEC).comp
        (symReal (nK + mZ + mX) (mZ + mX) ell ellEV Q delta
          (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec) := by
  classical
  refine LinearMap.ext fun rho => ?_
  have hL : retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q rho =
      Matrix.reindex (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC)
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC)
        ((((Matrix.reindexLinearEquiv ℂ ℂ (retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec
          delta Q) (retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec delta
          Q)).toLinearMap).comp
          (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote)
          (Matrix.reindex (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).symm
            (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).symm
            (Matrix.reindex (pairFunctions Bit Bit (nK + mZ + mX))
              (pairFunctions Bit Bit (nK + mZ + mX)) rho))) := by
    rfl
  rw [hL, retainedAnalysisProgram_denote_eq_sum, LinearMap.comp_apply,
    symReal_eq_sum]
  simp only [map_sum, map_smul, modelPostprocess_single]
  simp only [Matrix.reindex_sum, Matrix.reindex_smul]
  simp only [Matrix.reindex_apply, Matrix.submatrix_single_equiv, Equiv.symm_symm]
  refine Finset.sum_congr rfl fun pi _ => ?_
  rw [← Equiv.sum_comp ((TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).trans
    (pairFunctions Bit Bit (nK + mZ + mX)).symm)]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun st _ => ?_
  have hc (x : (FinalStage.rawSystem (nK + mZ + mX)).total) :
      ((TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).trans
        (pairFunctions Bit Bit (nK + mZ + mX)).symm) x =
      jointOutcome (nK + mZ + mX) (x .alice) (x .bob) := rfl
  have hstate :
      (siftedRotation (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) * permConjLin pi rho *
        (siftedRotation (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX))ᴴ)
          (((TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).trans
            (pairFunctions Bit Bit (nK + mZ + mX)).symm) x)
          (((TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).trans
            (pairFunctions Bit Bit (nK + mZ + mX)).symm) x) =
        retainedAnalysisSiftedState (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) pi
          (Matrix.reindex (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).symm
            (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).symm
            (Matrix.reindex (pairFunctions Bit Bit (nK + mZ + mX))
              (pairFunctions Bit Bit (nK + mZ + mX)) rho)) x x := by
    calc _ = Matrix.reindex (pairFunctions Bit Bit (nK + mZ + mX))
            (pairFunctions Bit Bit (nK + mZ + mX))
            (siftedRotation (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) * permConjLin pi rho *
              (siftedRotation (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX))ᴴ)
            (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX)) x)
            (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX)) x) := rfl
      _ = Matrix.reindex (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX)))
            (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX)))
            (retainedAnalysisSiftedState (@Sampling.packedPESel nK mZ mX)
              (@Sampling.packedXSel nK mZ mX) pi
              (Matrix.reindex (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).symm
                (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).symm
                (Matrix.reindex (pairFunctions Bit Bit (nK + mZ + mX))
                  (pairFunctions Bit Bit (nK + mZ + mX)) rho)))
            (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX)) x)
            (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX)) x) := by
        rw [← QKD.BB84.Model.siftPermHalf_pair_conj_reindex, reindex_retainedAnalysisSiftedState]
        rfl
      _ = _ := by
        rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [hc, modelOutputPoint_modelOutputIndex, ← hc, hstate,
    Fintype.card_perm, Fintype.card_fin]
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  congr 1
  ring


/-- The final-stage ideal fixes the key-free abort leaf. -/
theorem finalStage_ideal_single_abort (ell : ℕ) (a b : Measurement.Bits ell) :
    (FinalStage.outputLayout ell).toBoundaryKeyLayout.ideal
        (Matrix.single (finalStagePoint ell 1 a b) (finalStagePoint ell 1 a b) (1 : ℂ)) =
      Matrix.single (finalStagePoint ell 1 a b) (finalStagePoint ell 1 a b) (1 : ℂ) :=
  BoundaryKeyLayout.ideal_single_of_abort _ rfl rfl 1

/-- **The final-stage ideal on the accepting leaf**: the two keys are replaced by one uniform shared
key. -/
theorem finalStage_ideal_single_accept (ell : ℕ) (a b : Measurement.Bits ell) :
    (FinalStage.outputLayout ell).toBoundaryKeyLayout.ideal
        (Matrix.single (finalStagePoint ell 0 a b) (finalStagePoint ell 0 a b) (1 : ℂ)) =
      ((2 : ℂ) ^ ell)⁻¹ • ∑ k : Measurement.Bits ell,
        Matrix.single (finalStagePoint ell 0 k k) (finalStagePoint ell 0 k k) (1 : ℂ) := by
  let L := (FinalStage.outputLayout ell).toBoundaryKeyLayout
  let e0 : (FinalStage.boundary ell).Exit := ⟨0, ()⟩
  have : Subsingleton (L.Residual e0) := by
    refine ⟨fun x y => Prod.ext (Prod.ext rfl rfl) (funext fun i => ?_)⟩
    rcases i with ⟨⟨p, hp⟩, hpb⟩
    cases p with
    | alice => exact (hp rfl).elim
    | bob => exact (hpb (Subtype.ext rfl)).elim
  let u := (L.coordinates e0 (finalStagePoint ell 0 a b).2).2.2
  have hpt : ∀ a' b' : Measurement.Bits ell,
      finalStagePoint ell 0 a' b' = ⟨e0, (L.coordinates e0).symm (a', b', u)⟩ := by
    intro a' b'
    refine Sigma.ext rfl (heq_of_eq ?_)
    refine ((L.coordinates e0).eq_symm_apply).mpr ?_
    exact Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _))
  have hcard : Fintype.card ((L.disposition e0).Key) = 2 ^ ell := by
    change Fintype.card (Measurement.Bits ell) = 2 ^ ell
    simp only [Fintype.card_fun, Fintype.card_fin]
  rw [hpt a b, L.ideal_single_coordinates e0 a b u, hcard]
  simp_rw [hpt]
  push_cast
  rfl

/-- The inclusion of one final-stage continuation into the retained output, at the announced
permutation `pi` and the pre-decision public exit `e`, as a morphism of key layouts. -/
noncomputable def retainedFinalStageHom (nK mZ mX ell ellEV leakEC : ℕ)
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (e : (QKD.BB84.classicalPreDecisionBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).Exit) :
    BoundaryKeyLayout.Hom (FinalStage.outputLayout ell).toBoundaryKeyLayout
      (retainedAnalysisOutputLayout nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout :=
  (retainedAnalysisFibreHom nK mZ mX ell ellEV leakEC pi).comp
    (QKD.OutputLayout.graftInclHom _ (fun _ => FinalStage.boundary ell)
      (fun _ => FinalStage.outputLayout ell) .alice .bob (by decide) (fun _ => rfl)
      (fun _ => rfl) e)

/-- `retainedFinalStageHom` places a final-stage point at the announced permutation and the
pre-decision exit. -/
theorem retainedFinalStageHom_apply (nK mZ mX ell ellEV leakEC : ℕ)
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (e : (QKD.BB84.classicalPreDecisionBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).Exit)
    (r : (FinalStage.boundary ell).space) :
    retainedFinalStageHom nK mZ mX ell ellEV leakEC pi e r =
      (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
        (pi, (Boundary.graftSpaceEquiv _ (fun _ => FinalStage.boundary ell)).symm ⟨e, r⟩) :=
  rfl

/-- `retainedFinalStageHom` is injective: the retained output decomposition is a bijection and the
graft decomposition of the raw-tail output is a bijection. -/
theorem retainedFinalStageHom_injective (nK mZ mX ell ellEV leakEC : ℕ)
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (e : (QKD.BB84.classicalPreDecisionBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).Exit) :
    Function.Injective (retainedFinalStageHom nK mZ mX ell ellEV leakEC pi e) := by
  intro r r' h
  rw [retainedFinalStageHom_apply, retainedFinalStageHom_apply] at h
  have h1 := congrArg Prod.snd
    ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm.injective h)
  exact eq_of_heq (Sigma.mk.inj_iff.mp
    ((Boundary.graftSpaceEquiv _ (fun _ => FinalStage.boundary ell)).symm.injective h1)).2

open scoped Classical in
/-- Structural transport of the retained key resource on a diagonal matrix unit. -/
theorem retainedAnalysisResource_single
    (u : (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space) :
    retainedAnalysisResource nK mZ mX ell ellEV leakEC
        (Matrix.single (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC u)
          (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC u) (1 : ℂ)) =
      Matrix.reindex (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC)
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC)
        ((retainedAnalysisOutputLayout nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal
          (Matrix.single u u (1 : ℂ))) := by
  simp only [retainedAnalysisResource, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply, Matrix.submatrix_single_equiv,
    Equiv.symm_apply_apply, Equiv.symm_symm]

/-- A model output point is its final-stage point included at the actual public exit. -/
theorem modelOutputPoint_eq (j : ModelOutput nK mZ mX ell ellEV leakEC) :
    modelOutputPoint nK mZ mX ell ellEV leakEC j =
      retainedFinalStageHom nK mZ mX ell ellEV leakEC j.1.2.2.2
        ((classicalTailExitEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC).symm
          (modelTailData nK mZ mX ell ellEV leakEC j.1.2.2.1))
        (finalStagePoint ell ((Equiv.boolNot.trans finTwoEquiv.symm) j.1.2.1)
          j.1.1.1 j.1.1.2) := rfl

open scoped Classical in
/-- The two key resources commute with postprocessing on every model diagonal matrix unit. -/
theorem retainedAnalysisResource_modelPostprocess_single
    (j : ModelOutput nK mZ mX ell ellEV leakEC) :
    retainedAnalysisResource nK mZ mX ell ellEV leakEC
        (modelPostprocess nK mZ mX ell ellEV leakEC (Matrix.single j j (1 : ℂ))) =
      modelPostprocess nK mZ mX ell ellEV leakEC
        (mapTensorId (keyReplace ell (SymPEAnnouncePublic (nK + mZ + mX) (mZ + mX)
          ell ellEV (@Sampling.packedPESel nK mZ mX) leakEC)) Unit
          (Matrix.single j j (1 : ℂ))) := by
  rcases j with ⟨⟨⟨kA, kB⟩, f, t, pi⟩, u⟩
  cases u
  let D := SymPEAnnouncePublic (nK + mZ + mX) (mZ + mX) ell ellEV
    (@Sampling.packedPESel nK mZ mX) leakEC
  let e := Equiv.prodUnique (KeyedOutput ell D) Unit
  have hs : Matrix.single (((kA, kB), (f, (t, pi))), ())
      (((kA, kB), (f, (t, pi))), ()) (1 : ℂ) =
      Matrix.reindex e.symm e.symm
        (Matrix.single ((kA, kB), (f, (t, pi))) ((kA, kB), (f, (t, pi))) (1 : ℂ)) := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_single_equiv, Equiv.symm_symm]
    rfl
  rw [modelPostprocess_single, modelOutputPoint_eq, retainedAnalysisResource_single]
  rw [hs, mapTensorId_prodUnique, keyReplace_single]
  have hinj := retainedFinalStageHom_injective nK mZ mX ell ellEV leakEC pi
    ((classicalTailExitEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).symm (modelTailData nK mZ mX ell ellEV leakEC t))
  have hftrue : (Equiv.boolNot.trans finTwoEquiv.symm) true = (0 : Fin 2) := rfl
  have hffalse : (Equiv.boolNot.trans finTwoEquiv.symm) false = (1 : Fin 2) := rfl
  cases f with
  | true =>
    rw [hftrue]
    simp only [and_self, ite_true, Bool.true_eq_false, ite_false, add_zero]
    rw [BoundaryKeyLayout.Hom.ideal_single_of_injective _ hinj _ _ _
      (finalStage_ideal_single_accept ell kA kB)]
    simp only [Matrix.reindex_smul, Matrix.reindex_sum]
    simp only [Matrix.reindex_apply, Matrix.submatrix_single_equiv, Equiv.symm_symm]
    simp only [map_smul, map_sum, modelPostprocess_single, modelOutputPoint_eq]
    rfl
  | false =>
    rw [hffalse]
    simp only [Bool.false_eq_true, false_and, ite_false, and_self, ite_true, zero_add]
    have habort := BoundaryKeyLayout.Hom.ideal_single_of_injective _ hinj
      (finalStagePoint ell 1 kA kB) 1 (fun _ : Unit => finalStagePoint ell 1 kA kB)
      (by rw [finalStage_ideal_single_abort, Fintype.sum_unique, one_smul])
    rw [Fintype.sum_unique, one_smul] at habort
    rw [habort]
    simp only [Matrix.reindex_apply, Matrix.submatrix_single_equiv, Equiv.symm_symm,
      modelPostprocess_single, modelOutputPoint_eq]
    rfl

/-- The retained ideal map is the same classical postprocessing of the model's ideal map. -/
theorem retainedAnalysisIdeal_eq_modelPostprocess_comp
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    retainedAnalysisIdeal nK mZ mX ell ellEV leakEC ec delta Q =
      (modelPostprocess nK mZ mX ell ellEV leakEC).comp
        (symIdeal (nK + mZ + mX) (mZ + mX) ell ellEV Q delta
          (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec) := by
  refine LinearMap.ext fun rho => ?_
  rw [retainedAnalysisIdeal, LinearMap.comp_apply, retainedAnalysisReal_eq_modelPostprocess_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, symIdeal_eq_keyReplace_real, symReal_eq_sum]
  simp only [map_sum, map_smul, retainedAnalysisResource_modelPostprocess_single]

/-- **The retained real-minus-ideal map is the post-processed model real-minus-ideal map.** -/
theorem retainedAnalysisDifference_eq_modelPostprocess_comp
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q =
      (modelPostprocess nK mZ mX ell ellEV leakEC).comp
        (symReal (nK + mZ + mX) (mZ + mX) ell ellEV Q delta
            (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec -
          symIdeal (nK + mZ + mX) (mZ + mX) ell ellEV Q delta
            (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec) := by
  rw [retainedAnalysisDifference, retainedAnalysisReal_eq_modelPostprocess_comp,
    retainedAnalysisIdeal_eq_modelPostprocess_comp, LinearMap.comp_sub]

/-- **The retained experiment's real/ideal distance is at most the analytical model's.**

The diamond norm of the retained real-minus-ideal map is at most that of
`symReal - symIdeal` at sifted block `nK + mZ + mX`, test-set
size `mZ + mX` and the packed selectors: the retained difference is the model difference followed
by the channel `modelPostprocess`, and post-composing a channel does not increase the diamond norm
(`IsChannel.diamondNorm_comp_le`). No budget, key-rate condition, state
assumption or condition on the error-correction scheme occurs. -/
theorem retainedAnalysisDifference_diamondNorm_le_model
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Quantum.Channels.diamondNorm
        (retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q) ≤
      Quantum.Channels.diamondNorm
        (symReal (nK + mZ + mX) (mZ + mX) ell ellEV Q delta
            (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec -
          symIdeal (nK + mZ + mX) (mZ + mX) ell ellEV Q delta
            (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec) := by
  rw [retainedAnalysisDifference_eq_modelPostprocess_comp]
  exact (isChannel_modelPostprocess nK mZ mX ell ellEV leakEC).diamondNorm_comp_le _


end QKD.BB84.Reduction
