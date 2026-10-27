import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.Graft
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.BoundaryKeyLayout.Hom
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.CompleteOutput
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Reduction.Preprocessor
import QCryptLean.QKD.BB84.Reduction.SymmetrizationPrefix
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.TailOutput
import QCryptLean.QKD.BB84.TailTranscript
import QCryptLean.QKD.KeyEnd
import QCryptLean.QKD.OutputLayout
import QCryptLean.QKD.OutputLayout.Graft
import QCryptLean.Quantum.Channels.Adjoint
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-! # Retained Experiment -/


open Quantum.Channels
open Quantum.Operators
open Quantum.Symmetry (pairFunctions)

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Reduction
open LOCC

open LOCC.TwoParty
open QKD.BB84.FiniteKey
open Measurement Sampling

/-- Public inner-permutation prefix, including Bob's literal singleton announcement. -/
def retainedAnalysisPrefixBoundary (n : ℕ) : Boundary Party :=
  .announce (Equiv.Perm (Fin n)) fun _ =>
    .announce Unit fun _ => .leaf (FinalStage.rawSystem n)

/-- Prefix public exits are exactly the announced inner permutations; the intervening public
`Unit` and terminal `Unit` are retained by the inverse map. -/
def retainedAnalysisPrefixExitEquiv (n : ℕ) :
    (retainedAnalysisPrefixBoundary n).Exit ≃ Equiv.Perm (Fin n) where
  toFun e := e.1
  invFun pi := ⟨pi, ⟨(), ()⟩⟩
  left_inv e := by
    rcases e with ⟨pi, ⟨u, v⟩⟩
    cases u
    cases v
    rfl
  right_inv _ := rfl

/-- Full retained experiment boundary: public inner permutation followed by every actual
PE/fused/final tail exit. -/
def retainedAnalysisBoundary
    (nK mZ mX ell ellEV leakEC : ℕ) : Boundary Party :=
  (retainedAnalysisPrefixBoundary (nK + mZ + mX)).graft fun _ =>
    QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC

/-- The unweighted retained experiment.

Outer basis-string and selection probabilities are absent: they belong to the later physical
factorization.  Each inner permutation is weighted exactly once, and the literal measure-first
BB84 continuation retains its own hash and error-verification seed randomness.  The construction
is motivated by Renner, arXiv:quant-ph/0512258v2, Section 6.5. -/
noncomputable def retainedAnalysisProgram
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Program (FinalStage.rawSystem (nK + mZ + mX)) (KeyEnd Party.alice Party.bob) :=
  (alicePermutationAnnouncement (nK + mZ + mX) Sampling.packedPESel Sampling.packedXSel).then
    fun pi =>
      (bobSiftUnitAnnouncement (nK + mZ + mX)
        Sampling.packedPESel Sampling.packedXSel pi).then fun _ =>
          classicalTail (nK + mZ + mX) (mZ + mX) ell ellEV
            Sampling.packedPESel Sampling.packedXSel leakEC ec delta Q

/-- Actual ordered local-key layout lifted through the public inner-permutation prefix. -/
noncomputable def retainedAnalysisOutputLayout
    (nK mZ mX ell ellEV leakEC : ℕ) :
    QKD.OutputLayout (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC) :=
  QKD.OutputLayout.graftFixedParties .alice .bob (by decide)
    (fun _ => QKD.BB84.rawClassicalTailOutputLayout
      (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (fun _ => rfl) (fun _ => rfl)

/-- Explicit output decomposition into the public inner permutation and the complete raw-tail
output.  Bob's singleton cell is eliminated only through the explicit bijection
`retainedAnalysisPrefixExitEquiv`. -/
noncomputable def retainedAnalysisOutputDataEquiv
    (nK mZ mX ell ellEV leakEC : ℕ) :
    (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space ≃
      Equiv.Perm (Fin (nK + mZ + mX)) ×
        (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC).space := by
  let G := Boundary.graftSpaceEquiv
    (retainedAnalysisPrefixBoundary (nK + mZ + mX))
    (fun _ => QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
  exact
    { toFun := fun q =>
        let z := G q
        (retainedAnalysisPrefixExitEquiv _ z.1, z.2)
      invFun := fun z =>
        G.symm ⟨(retainedAnalysisPrefixExitEquiv _).symm z.1, z.2⟩
      left_inv := by
        intro q
        dsimp only
        rw [(retainedAnalysisPrefixExitEquiv _).symm_apply_apply]
        exact G.symm_apply_apply q
      right_inv := by
        intro z
        rcases z with ⟨pi, q⟩
        dsimp only
        rw [G.apply_symm_apply, (retainedAnalysisPrefixExitEquiv _).apply_symm_apply] }

/-- Read the comparison experiment in its permutation and complete-tail coordinates. -/
def retainedAnalysisSpaceEquiv
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).boundary.space ≃
      (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space :=
  { toFun := fun q => (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
      (q.1.1, rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
        Sampling.packedPESel Sampling.packedXSel leakEC ec delta Q ⟨q.1.2.2, q.2⟩)
    invFun := fun q =>
      let z := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q
      let w := (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
        Sampling.packedPESel Sampling.packedXSel leakEC ec delta Q).symm z.2
      ⟨⟨z.1, (), w.1⟩, w.2⟩
    left_inv := by
      rintro ⟨⟨pi, u, e⟩, q⟩
      cases u
      dsimp only
      rw [(retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).apply_symm_apply,
        (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
          Sampling.packedPESel Sampling.packedXSel leakEC ec delta Q).symm_apply_apply]
    right_inv := by
      intro q
      dsimp only
      rw [(rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
        Sampling.packedPESel Sampling.packedXSel leakEC ec delta Q).apply_symm_apply]
      exact (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm_apply_apply q }

/-- The complete tail output over one announced inner permutation is a morphism of key layouts
from the retained-tail layout to the retained-analysis layout: the inclusion of that permutation's
continuation into the grafted output. -/
noncomputable def retainedAnalysisFibreHom
    (nK mZ mX ell ellEV leakEC : ℕ) (pi : Equiv.Perm (Fin (nK + mZ + mX))) :
    BoundaryKeyLayout.Hom
      (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout
      (retainedAnalysisOutputLayout nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout :=
  QKD.OutputLayout.graftInclHom (retainedAnalysisPrefixBoundary (nK + mZ + mX))
    (fun _ => QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (fun _ => QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    .alice .bob (by decide) (fun _ => rfl) (fun _ => rfl)
    ((retainedAnalysisPrefixExitEquiv (nK + mZ + mX)).symm pi)

/-- The fibre morphism of an announced permutation reads the explicit output decomposition. -/
@[simp] theorem coe_retainedAnalysisFibreHom
    (nK mZ mX ell ellEV leakEC : ℕ) (pi : Equiv.Perm (Fin (nK + mZ + mX))) :
    ⇑(retainedAnalysisFibreHom nK mZ mX ell ellEV leakEC pi) =
      fun w => (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm (pi, w) :=
  rfl

/-- The public permutation and the complete raw-tail output, with their natural labels. -/
abbrev RetainedAnalysisOutput (nK mZ mX ell ellEV leakEC : ℕ) :=
  Equiv.Perm (Fin (nK + mZ + mX)) ×
    (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).space

/-- Explicit zero-valued semantic transcript used to inhabit the raw-tail output space. -/
def retainedAnalysisDefaultTailData
    (nK mZ mX ell ellEV leakEC : ℕ) :
    QKD.BB84.ClassicalTailData (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC where
  alicePE := fun _ => 0
  bobPE := fun _ => 0
  seedPair := (fun _ _ => 0, fun _ _ => 0)
  evTag := 0
  syndrome := 0

/-- Explicit abort output used only to certify that the raw-tail output type is inhabited. -/
noncomputable def retainedAnalysisDefaultRawTailOutput
    (nK mZ mX ell ellEV leakEC : ℕ) :
    (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).space :=
  let d := retainedAnalysisDefaultTailData nK mZ mX ell ellEV leakEC
  let preExit := (QKD.BB84.classicalTailExitEquiv
    (nK + mZ + mX) (mZ + mX) ell ellEV
    (@Sampling.packedPESel nK mZ mX) leakEC).symm d
  let qAbort : FinalStage.abortSystem.total :=
    (TwoParty.pairEquiv Unit Unit).symm ((), ())
  let finalExit : (FinalStage.boundary ell).Exit := ⟨1, by
    exact (() : (Boundary.leaf FinalStage.abortSystem).Exit)⟩
  let finalSpace : (FinalStage.boundary ell).space := ⟨finalExit, by
    exact qAbort⟩
  (Boundary.graftSpaceEquiv _ _).symm ⟨preExit, finalSpace⟩

/-- The retained real map on signal functions and the natural public output. -/
noncomputable def retainedAnalysisReal
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Operation (Signals (nK + mZ + mX)) (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC) :=
  let e := (retainedAnalysisSpaceEquiv nK mZ mX ell ellEV leakEC ec delta Q).trans
    (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC)
  let f := (pairFunctions Bit Bit (nK + mZ + mX)).trans
    (TwoParty.pairEquiv (Bits (nK + mZ + mX)) (Bits (nK + mZ + mX))).symm
  (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.comp
    ((retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote.comp
      (Matrix.reindexLinearEquiv ℂ ℂ f f).toLinearMap)

/-- Full-exit key replacement, retaining the public permutation and complete tail output. -/
noncomputable def retainedAnalysisResource (nK mZ mX ell ellEV leakEC : ℕ) :
    Operation (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
      (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC) :=
  let e := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
  (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.comp
    ((retainedAnalysisOutputLayout nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal.comp
      (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap)

/-- Read the retained resource through its structural permutation/tail decomposition. -/
theorem retainedAnalysisResource_entry (nK mZ mX ell ellEV leakEC : ℕ)
    (M : Op (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC))
    (x y : (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space) :
    retainedAnalysisResource nK mZ mX ell ellEV leakEC M
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC x)
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC y) =
      (retainedAnalysisOutputLayout nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal
        (M.submatrix (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC)
          (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC)) x y := by
  simp only [retainedAnalysisResource, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply, Equiv.symm_symm,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]

/-- Retained ideal map: the actual full-exit key resource after the retained real map. -/
noncomputable def retainedAnalysisIdeal
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Op (Signals (nK + mZ + mX)) →ₗ[ℂ]
      Op (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC) :=
  (retainedAnalysisResource nK mZ mX ell ellEV leakEC).comp
    (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)

/-- Retained real-minus-ideal map. -/
noncomputable def retainedAnalysisDifference
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Op (Signals (nK + mZ + mX)) →ₗ[ℂ]
      Op (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC) :=
  retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q -
    retainedAnalysisIdeal nK mZ mX ell ellEV leakEC ec delta Q

/-- The retained real map is a channel by denotation and structural reindexing. -/
theorem isChannel_retainedAnalysisReal
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) : IsChannel (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q) :=
  (isChannel_reindex _).comp
    ((retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).isChannel_denote.comp
      (isChannel_reindex _))

/-- The retained full-output key resource is a channel. -/
theorem isChannel_retainedAnalysisResource (nK mZ mX ell ellEV leakEC : ℕ) :
    IsChannel (retainedAnalysisResource nK mZ mX ell ellEV leakEC) :=
  (isChannel_reindex _).comp
    ((retainedAnalysisOutputLayout nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.isChannel_ideal
      |>.comp (isChannel_reindex _))

/-- The retained ideal map is a channel by composition with the full-output resource. -/
theorem isChannel_retainedAnalysisIdeal
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) : IsChannel (retainedAnalysisIdeal nK mZ mX ell ellEV leakEC ec delta Q) :=
  (isChannel_retainedAnalysisResource nK mZ mX ell ellEV leakEC).comp
    (isChannel_retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)

/-- The retained real-minus-ideal map preserves adjoints. -/
theorem retainedAnalysisDifference_preserves_conjTranspose
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) (M : Op (Signals (nK + mZ + mX))) :
    retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q Mᴴ =
      (retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q M)ᴴ :=
  (isChannel_retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q).1.sub_conjTranspose
    (isChannel_retainedAnalysisIdeal nK mZ mX ell ellEV leakEC ec delta Q).1 M

end QKD.BB84.Reduction
