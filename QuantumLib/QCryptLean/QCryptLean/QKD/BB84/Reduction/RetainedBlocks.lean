import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.TwoParty
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.CompleteOutput
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Reduction.ClassicalTail
import QCryptLean.QKD.BB84.Reduction.RetainedExperiment
import QCryptLean.QKD.BB84.Reduction.SymmetrizationPrefix
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.SiftOperation
import QCryptLean.QKD.BB84.TailOutput
import QCryptLean.QKD.BB84.TailTranscript
import QCryptLean.QKD.KeyEnd
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-! # Retained Blocks -/


open Quantum.Channels
open Quantum.Symmetry (pairFunctions)

namespace QKD.BB84.Reduction
open LOCC

open scoped BigOperators Matrix Kronecker
open Quantum.Operators
open LOCC QKD
open LOCC.TwoParty
open QKD.BB84.FiniteKey
open Measurement Sampling

noncomputable section


/-- One external-reference block, reindexed into the actual retained input multipartite system. -/
def retainedAnalysisProgramInputReferenceBlock {n : ℕ} {E : Type*}
    (W : Op ((Bits n × Bits n) × E)) (s t : E) :
    Op (FinalStage.rawSystem n).total :=
  Matrix.reindex (TwoParty.pairEquiv (Bits n) (Bits n)).symm
    (TwoParty.pairEquiv (Bits n) (Bits n)).symm
    (Matrix.of fun i j =>
      W (i, s) (j, t))

/-- The state the two private measurements read after the announced inner permutation.

Alice's and Bob's local sift/permutation operators act in sequence on their computed systems;
the final operator is reindexed into the retained raw-system coordinates. -/
noncomputable def retainedAnalysisSiftedState {n : ℕ}
    (peSel xSel : Fin n → Bool) (pi : Equiv.Perm (Fin n))
    (rho : Op (FinalStage.rawSystem n).total) :
    Op (FinalStage.rawSystem n).total :=
  let R := FinalStage.rawSystem n
  let kappa := QKD.BB84.Model.siftPermHalf n peSel xSel pi
  let ka := (localKrausLift R .alice (Bits n)
    (kappa)).submatrix
    (Equiv.cast (congrArg MultipartiteSystem.total (R.set_self .alice).symm)) id
  let kb := (localKrausLift R .bob (Bits n)
    (kappa)).submatrix
    (Equiv.cast (congrArg MultipartiteSystem.total (R.set_self .bob).symm)) id
  Matrix.conjLinearMap kb (Matrix.conjLinearMap ka rho)

/-- Reference block after the local sift/permutation operators and both private computational
measurements, at the retained raw outcome `x`. -/
noncomputable def retainedAnalysisMeasuredReferenceBlock {n : ℕ} {E : Type*}
    (peSel xSel : Fin n → Bool) (pi : Equiv.Perm (Fin n))
    (W : Op ((Bits n × Bits n) × E))
    (x : (FinalStage.rawSystem n).total) : Op E :=
  Matrix.of fun s t =>
    retainedAnalysisSiftedState peSel xSel pi
      (retainedAnalysisProgramInputReferenceBlock W s t) x x


/-- The two announced retained measurements feed the sifted state to any continuation. -/
private theorem retainedAnalysisPrefix_denote {n : ℕ}
    (peSel xSel : Fin n → Bool)
    (tail : Program (FinalStage.rawSystem n) (KeyEnd Party.alice Party.bob))
    (rho : Op (FinalStage.rawSystem n).total) (pi : Equiv.Perm (Fin n))
    (a b : tail.boundary.space) :
    ((alicePermutationAnnouncement n peSel xSel).then fun pj =>
      (bobSiftUnitAnnouncement n peSel xSel pj).then fun _ => tail).denote rho
        ⟨⟨pi, (), a.1⟩, a.2⟩ ⟨⟨pi, (), b.1⟩, b.2⟩ =
      (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ *
        tail.denote (retainedAnalysisSiftedState peSel xSel pi rho) a b := by
  let R := FinalStage.rawSystem n
  let weight : ℂ := (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹
  let KA (pi : Equiv.Perm (Fin n)) :=
    (localKrausLift R .alice (Bits n)
      (Model.siftPermHalf n peSel xSel pi)).submatrix
      (Equiv.cast (congrArg MultipartiteSystem.total (R.set_self .alice).symm)) id
  let KB (pi : Equiv.Perm (Fin n)) :=
    (localKrausLift R .bob (Bits n)
      (Model.siftPermHalf n peSel xSel pi)).submatrix
      (Equiv.cast (congrArg MultipartiteSystem.total (R.set_self .bob).symm)) id
  have hAlice (pi : Equiv.Perm (Fin n)) (sigma : Op R.total) :
      (alicePermutationAnnouncement n peSel xSel).successorOperation (pi, ()) sigma =
        weight • Matrix.conjLinearMap (KA pi) sigma := by
    ext u v
    change R.total at u v
    change (alicePermutationAnnouncement n peSel xSel).liftedOperation (pi, ()) sigma
      (cast (congrArg MultipartiteSystem.total (R.set_self .alice).symm) u)
      (cast (congrArg MultipartiteSystem.total (R.set_self .alice).symm) v) = _
    refine (alicePermutationAnnouncement_liftedOperation_apply n peSel xSel pi sigma _ _).trans ?_
    refine (congrArg (fun z : ℂ => weight * z)
      (Matrix.conjLinearMap_apply_apply _ sigma _ _)).trans ?_
    simp only [KA, R, weight, Matrix.conjLinearMap_apply_apply,
      Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
      Equiv.cast_apply, id_eq]
    rfl
  have hBob (pi : Equiv.Perm (Fin n)) (sigma : Op R.total) :
      (bobSiftUnitAnnouncement n peSel xSel pi).successorOperation () sigma =
        Matrix.conjLinearMap (KB pi) sigma := by
    ext u v
    change R.total at u v
    change (bobSiftUnitAnnouncement n peSel xSel pi).liftedOperation () sigma
      (cast (congrArg MultipartiteSystem.total (R.set_self .bob).symm) u)
      (cast (congrArg MultipartiteSystem.total (R.set_self .bob).symm) v) = _
    refine (bobSiftUnitAnnouncement_liftedOperation_apply n peSel xSel pi sigma _ _).trans ?_
    refine (Matrix.conjLinearMap_apply_apply _ sigma _ _).trans ?_
    simp only [KB, R, Matrix.conjLinearMap_apply_apply, Matrix.submatrix_apply,
      Equiv.cast_apply, id_eq]
    rfl
  refine (Program.denote_then_publicSpaceEquiv_symm_apply
    (alicePermutationAnnouncement n peSel xSel) (Equiv.prodUnique _ _) (fun _ => rfl)
    (fun pj => (bobSiftUnitAnnouncement n peSel xSel pj).then fun _ => tail)
    rho (pi, ()) ⟨⟨(), a.1⟩, a.2⟩ ⟨⟨(), b.1⟩, b.2⟩).trans ?_
  refine (Program.denote_then_publicSpaceEquiv_symm_apply
    (bobSiftUnitAnnouncement n peSel xSel pi) (Equiv.refl Unit) (fun _ => rfl)
    (fun _ => tail) _ () a b).trans ?_
  change tail.denote ((bobSiftUnitAnnouncement n peSel xSel pi).successorOperation ()
    ((alicePermutationAnnouncement n peSel xSel).successorOperation (pi, ()) rho)) a b = _
  refine (congrArg (fun sigma : Op R.total => tail.denote sigma a b)
    ((hBob pi _).trans (congrArg (Matrix.conjLinearMap (KB pi)) (hAlice pi rho)))).trans ?_
  rw [map_smul, map_smul]
  rfl

/-- A canonical retained output decodes to its permutation and actual tail point. -/
private theorem retainedAnalysisSpaceEquiv_symm_point
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (a : (rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).space) :
    (retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec delta Q).symm
      ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm (pi, a)) =
    let w := (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
      Sampling.packedPESel Sampling.packedXSel leakEC ec delta Q).symm a
    ⟨⟨pi, (), w.1⟩, w.2⟩ := by
  let E := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
  let T := rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
    Sampling.packedPESel Sampling.packedXSel leakEC ec delta Q
  change (let z := E (E.symm (pi, a))
    let w := T.symm z.2
    (⟨⟨z.1, (), w.1⟩, w.2⟩ :
      (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).boundary.space)) = _
  rw [E.apply_symm_apply]

/-- **The channel of the retained-analysis program, entrywise.**

For an arbitrary operator `rho` on the raw input multipartite system, the output is diagonal in the
complete output space.  At a complete output point with announced permutation `pi` and raw-tail
output `w` (`retainedAnalysisOutputDataEquiv`), its weight is the uniform permutation weight times
the uniform seed weight, summed over the raw outcomes `x` and seed pairs `st` whose raw-tail output
point is `w`, of the diagonal entry at `x` of the sifted state `retainedAnalysisSiftedState` of
`pi`. -/
theorem retainedAnalysisProgram_denote_apply
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ)
    (rho : Op (FinalStage.rawSystem (nK + mZ + mX)).total)
    (q q' : (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space) :
    let d := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q
    (Matrix.reindexLinearEquiv ℂ ℂ (retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec delta Q)
      (retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec delta Q)).toLinearMap
      ((retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote rho) q q' =
      if q = q' then
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV
              (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            if rawClassicalTailOutputPoint
                (nK + mZ + mX) (mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q x st = d.2 then
              (Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹ *
                ((Fintype.card (KeyHashSeedPairEV
                    (nK + mZ + mX) ell ellEV
                    (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                  retainedAnalysisSiftedState
                    (@Sampling.packedPESel nK mZ mX)
                    (@Sampling.packedXSel nK mZ mX) d.1 rho x x)
            else 0
      else 0 := by
  classical
  dsimp only
  let n := nK + mZ + mX
  let peSel : Fin n → Bool := @Sampling.packedPESel nK mZ mX
  let xSel : Fin n → Bool := @Sampling.packedXSel nK mZ mX
  let R := FinalStage.rawSystem n
  let tail := classicalTail n (mZ + mX) ell ellEV peSel xSel leakEC ec delta Q
  let E := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
  let F := retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec delta Q
  let T := rawClassicalTailOutputEquiv n (mZ + mX) ell ellEV peSel xSel leakEC ec delta Q
  let weight : ℂ := (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹
  have hDifferent (tail : Program R (KeyEnd Party.alice Party.bob))
      (pi pj : Equiv.Perm (Fin n)) (a b : tail.boundary.space) (h : pi ≠ pj) :
      ((alicePermutationAnnouncement n peSel xSel).then fun pj =>
        (bobSiftUnitAnnouncement n peSel xSel pj).then fun _ => tail).denote rho
          ⟨⟨pi, (), a.1⟩, a.2⟩ ⟨⟨pj, (), b.1⟩, b.2⟩ = 0 := by
    exact Program.denote_isExitBlockDiagonal
      ((alicePermutationAnnouncement n peSel xSel).then fun pj =>
        (bobSiftUnitAnnouncement n peSel xSel pj).then fun _ => tail) rho
      ⟨pi, (), a.1⟩ ⟨pj, (), b.1⟩ a.2 b.2 (fun he => h (congrArg Sigma.fst he))
  obtain ⟨⟨pi, a⟩, rfl⟩ := E.symm.surjective q
  obtain ⟨⟨pj, b⟩, rfl⟩ := E.symm.surjective q'
  change (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote rho
    (F.symm (E.symm (pi, a))) (F.symm (E.symm (pj, b))) = _
  simp only [E, Equiv.apply_symm_apply]
  refine (congrArg₂ ((retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote rho)
    (retainedAnalysisSpaceEquiv_symm_point nK mZ mX ell ellEV leakEC ec delta Q pi a)
    (retainedAnalysisSpaceEquiv_symm_point nK mZ mX ell ellEV leakEC ec delta Q pj b)).trans ?_
  by_cases hpi : pi = pj
  · subst pj
    refine (retainedAnalysisPrefix_denote peSel xSel tail rho pi (T.symm a) (T.symm b)).trans ?_
    refine (congrArg (fun z : ℂ => weight * z)
      (rawClassicalTailProgram_output_apply n (mZ + mX) ell ellEV peSel xSel leakEC ec delta Q
        (retainedAnalysisSiftedState peSel xSel pi rho) a b)).trans ?_
    by_cases hab : a = b
    · subst b
      simp only [ite_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro st _
      split_ifs <;> first | rfl | exact mul_zero _
    · have hne : E.symm (pi, a) ≠ E.symm (pi, b) := fun h =>
        hab (congrArg Prod.snd (E.symm.injective h))
      rw [ite_eq_right hab, mul_zero]
      exact (ite_eq_right hne).symm
  · have hne : E.symm (pi, a) ≠ E.symm (pj, b) := fun h =>
      hpi (congrArg Prod.fst (E.symm.injective h))
    refine (hDifferent tail pi pj (T.symm a) (T.symm b) hpi).trans ?_
    exact (ite_eq_right hne).symm
/-- Complete retained-output blocks with independent reference row and column labels. -/
theorem retainedAnalysisProgram_reference_blocks
    (nK mZ mX ell ellEV leakEC : ℕ) {E : Type*}
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ)
    (W : Op ((Bits (nK + mZ + mX) × Bits (nK + mZ + mX)) × E))
    (q q' : (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space)
    (s t : E) :
    let d := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q
    mapTensorId
      ((Matrix.reindexLinearEquiv ℂ ℂ
          (retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec delta Q)
          (retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec delta Q)).toLinearMap.comp
        ((retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote.comp
          (Matrix.reindexLinearEquiv ℂ ℂ
            (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).symm
            (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).symm).toLinearMap))
      E W (q, s) (q', t) =
      if q = q' then
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV
              (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            if rawClassicalTailOutputPoint
                (nK + mZ + mX) (mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q x st = d.2 then
              (Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹ *
                ((Fintype.card (KeyHashSeedPairEV
                    (nK + mZ + mX) ell ellEV
                    (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                  retainedAnalysisMeasuredReferenceBlock
                    (@Sampling.packedPESel nK mZ mX)
                    (@Sampling.packedXSel nK mZ mX) d.1 W x s t)
            else 0
      else 0 := by
  dsimp only
  rw [mapTensorId_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  let rho := retainedAnalysisProgramInputReferenceBlock W s t
  have hb : (Matrix.reindexLinearEquiv ℂ ℂ
      (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).symm
      (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).symm).toLinearMap
      (W.submatrix (fun x => (x, s)) (fun x => (x, t))) = rho := rfl
  rw [hb, retainedAnalysisProgram_denote_apply]
  rfl

/-- **The channel of the retained-analysis program as a classical mixture.**

The output is the sum, over the announced permutation `pi`, the raw outcome `x` and the seed pair
`st`, of the rank-one projector onto the complete output point `(pi, raw-tail output of x and st)`,
weighted by the uniform permutation and seed weights and the diagonal entry at `x` of the sifted
state of `pi`.  Arbitrary complex input operators. -/
theorem retainedAnalysisProgram_denote_eq_sum
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ)
    (rho : Op (FinalStage.rawSystem (nK + mZ + mX)).total) :
    (((Matrix.reindexLinearEquiv ℂ ℂ (retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec delta
      Q) (retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec delta Q)).toLinearMap).comp
            (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote) rho =
      ∑ pi : Equiv.Perm (Fin (nK + mZ + mX)),
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            ((Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹ *
                ((Fintype.card (KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
                    (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                  retainedAnalysisSiftedState
                    (@Sampling.packedPESel nK mZ mX)
                    (@Sampling.packedXSel nK mZ mX) pi rho x x)) •
              Matrix.single
                ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
                  (pi, rawClassicalTailOutputPoint (nK + mZ + mX) (mZ + mX) ell ellEV
                    (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX)
                    leakEC ec delta Q x st))
                ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
                  (pi, rawClassicalTailOutputPoint (nK + mZ + mX) (mZ + mX) ell ellEV
                    (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX)
                    leakEC ec delta Q x st)) (1 : ℂ) := by
  classical
  ext q q'
  rw [LinearMap.comp_apply, retainedAnalysisProgram_denote_apply]
  obtain ⟨⟨pi, a⟩, rfl⟩ :=
    (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm.surjective q
  rw [Equiv.apply_symm_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hqq : (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm (pi, a) = q'
  · subst hqq
    simp only [ite_true, Equiv.apply_eq_iff_eq, Prod.mk.injEq, and_self]
    rw [Finset.sum_eq_single pi]
    · simp only [true_and]
    · intro pj _ hpj
      exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun st _ => by simp [hpj]
    · intro h
      exact absurd (Finset.mem_univ pi) h
  · rw [ite_eq_right hqq]
    symm
    refine Finset.sum_eq_zero fun pj _ => Finset.sum_eq_zero fun x _ =>
      Finset.sum_eq_zero fun st _ => ?_
    rw [ite_eq_right]
    rintro ⟨⟨rfl, hb⟩, hq'⟩
    exact hqq (by rw [← hq', hb])

/-- **The two local sift-after-permutation operators, in Alice/Bob block coordinates.**

Read through the structural Alice/Bob pair equivalence, the sifted state of `pi` is the
conjugation of the input by the two-party product `siftPermHalf ⊗ siftPermHalf`. -/
theorem reindex_retainedAnalysisSiftedState {n : ℕ}
    (peSel xSel : Fin n → Bool) (pi : Equiv.Perm (Fin n))
    (sigma : Op (Bits n × Bits n)) :
    Matrix.reindex (TwoParty.pairEquiv (Bits n) (Bits n)) (TwoParty.pairEquiv (Bits n) (Bits n))
        (retainedAnalysisSiftedState peSel xSel pi
          (Matrix.reindex (TwoParty.pairEquiv (Bits n) (Bits n)).symm
            (TwoParty.pairEquiv (Bits n) (Bits n)).symm sigma)) =
      Matrix.kronecker (QKD.BB84.Model.siftPermHalf n peSel xSel pi)
          (QKD.BB84.Model.siftPermHalf n peSel xSel pi) * sigma *
        (Matrix.kronecker (QKD.BB84.Model.siftPermHalf n peSel xSel pi)
          (QKD.BB84.Model.siftPermHalf n peSel xSel pi))ᴴ := by
  let R := FinalStage.rawSystem n
  let e := TwoParty.pairEquiv (Bits n) (Bits n)
  let kappa := QKD.BB84.Model.siftPermHalf n peSel xSel pi
  let ka : Matrix R.total R.total ℂ :=
    (localKrausLift R .alice (Bits n)
    (kappa)).submatrix
      (Equiv.cast (congrArg MultipartiteSystem.total (R.set_self .alice).symm)) id
  let kb : Matrix R.total R.total ℂ :=
    (localKrausLift R .bob (Bits n)
    (kappa)).submatrix
      (Equiv.cast (congrArg MultipartiteSystem.total (R.set_self .bob).symm)) id
  have hliftA : Matrix.reindex e e ka =
      Matrix.kronecker kappa (1 : Op (Bits n)) := by
    ext i j
    change localKrausLift R .alice (Bits n)
      (kappa)
      (cast (congrArg MultipartiteSystem.total (R.set_self .alice).symm)
        (R.pairEquiv.symm
          i))
      (R.pairEquiv.symm
        j) = _
    rw [MultipartiteSystem.cast_pairEquiv_symm (R.set_self _).symm]
    refine (localKrausLift_alice_apply R
      (kappa)
      i.1 i.2
      j.2 j.1).trans ?_
    simp [Matrix.kronecker, Matrix.one_apply]
  have hliftB : Matrix.reindex e e kb =
      Matrix.kronecker (1 : Op (Bits n)) kappa := by
    ext i j
    change localKrausLift R .bob (Bits n)
      (kappa)
      (cast (congrArg MultipartiteSystem.total (R.set_self .bob).symm)
        (R.pairEquiv.symm
          i))
      (R.pairEquiv.symm
        j) = _
    rw [MultipartiteSystem.cast_pairEquiv_symm (R.set_self _).symm]
    refine (localKrausLift_bob_apply R
      (kappa)
      i.1 j.1
      i.2 j.2).trans ?_
    simp [Matrix.kronecker, Matrix.one_apply]
  have hprefix : Matrix.reindex e e (kb * ka) =
      Matrix.kronecker kappa kappa := by
    change (kb * ka).submatrix e.symm e.symm = _
    rw [← Matrix.submatrix_mul_equiv kb ka e.symm e.symm e.symm]
    change Matrix.reindex e e kb * Matrix.reindex e e ka = _
    rw [hliftB, hliftA]
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul]
    simp only [one_mul, mul_one]
  change Matrix.reindex e e (Matrix.conjLinearMap kb
    (Matrix.conjLinearMap ka (Matrix.reindex e.symm e.symm sigma))) = _
  rw [← LinearMap.comp_apply, ← Matrix.conjLinearMap_mul]
  simp only [Matrix.conjLinearMap_apply, Matrix.reindex_apply, Equiv.symm_symm]
  rw [← Matrix.submatrix_mul_equiv _ _ e.symm e.symm e.symm,
    ← Matrix.submatrix_mul_equiv _ _ e.symm e.symm e.symm]
  simp only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
  rw [← Matrix.conjTranspose_submatrix]
  change Matrix.reindex e e (kb * ka) * sigma * (Matrix.reindex e e (kb * ka))ᴴ = _
  rw [hprefix]

/-- Group each reference block's signals into the two parties' strings. -/
def retainedAnalysisRoundReferenceToBlock {n : ℕ} {E : Type*}
    (W : Op (Signals n × E)) : Op ((Bits n × Bits n) × E) :=
  Matrix.reindex ((pairFunctions Bit Bit n).prodCongr (Equiv.refl E))
    ((pairFunctions Bit Bit n).prodCongr (Equiv.refl E)) W

/-- The retained map reads exactly the program's reference block after structural round grouping. -/
theorem retainedAnalysisReal_referenceBlock_eq_program
    (nK mZ mX ell ellEV leakEC : ℕ) {E : Type*}
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) (W : Op (Signals (nK + mZ + mX) × E))
    (q q' : (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space) (s t : E) :
    mapTensorId (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q) E W
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q, s)
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q', t) =
      (Matrix.reindexLinearEquiv ℂ ℂ
        (retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec delta Q)
        (retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec delta Q))
        ((retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote
          (retainedAnalysisProgramInputReferenceBlock
            (retainedAnalysisRoundReferenceToBlock W) s t))
        q q' := by
  simp only [mapTensorId_apply, retainedAnalysisReal, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  rfl

end

end QKD.BB84.Reduction
