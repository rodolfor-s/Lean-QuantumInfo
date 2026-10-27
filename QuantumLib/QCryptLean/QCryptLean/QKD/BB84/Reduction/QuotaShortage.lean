import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.QKD.BB84.CompleteOutput
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.KeyEnd
import QCryptLean.QKD.OutputLayout
import QCryptLean.QKD.Protocol
import QCryptLean.Quantum.Operators.Basic

/-! # Quota Shortage -/


open Quantum.Operators (Op)

noncomputable section

namespace QKD.BB84.Reduction
open LOCC

open QKD.BB84.FiniteKey

/-- If the total retained quota exceeds the physical round count, every complete exit of the
actual output layout is aborting.

A quota-success branch would supply the explicit
`Sampling.selectedEmbedding : Fin (nK + mZ + mX) ↪ Fin N`, contradicting the cardinal
inequality. The conclusion retains the complete outer basis strings, shuffle, and all
branch-dependent public metadata; it only classifies the leaf disposition. -/
theorem outputLayout_disposition_eq_abort_of_totalQuota_gt
    (pA pB : PMF Measurement.Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (δ Q : ℝ) (hN : N < nK + mZ + mX)
    (e : (protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).boundary.Exit) :
    (protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).layout.disposition e =
      BoundaryKeyLayout.Disposition.abort := by
  have hno (omega : Sampling.RawControl N) :
      ¬ Sampling.HasQuotas nK mZ mX omega := by
    intro hquota
    have hcard : Fintype.card (Fin (nK + mZ + mX)) ≤ Fintype.card (Fin N) :=
      Fintype.card_le_of_injective _ (Sampling.selectedEmbedding omega hquota).injective
    simp only [Fintype.card_fin] at hcard
    omega
  let k :=
    (announceAliceBases N).then fun aliceBases =>
      (announceBobBases N).then fun bobBases =>
        (announceShuffle aliceBases bobBases).then fun order =>
          let control : Sampling.RawControl N := ⟨aliceBases, bobBases, order⟩
          if hasQuotas : Sampling.HasQuotas nK mZ mX control then
            let selected := Sampling.selectedEmbedding control hasQuotas
            (retainAlice selected).then <|
              (retainBob selected).then <|
                (forgetAliceBases N (nK + mZ + mX)).then <|
                  (forgetBobBases N (nK + mZ + mX)).then <|
                    classicalTail (nK + mZ + mX) (mZ + mX) ℓ ℓEV
                      Sampling.packedPESel Sampling.packedXSel leakEC ec δ Q
          else discardAlice.then (discardBob.then (.done KeyEnd.abort))
  change ((measureRounds pA pB Unit N k).terminal e).disposition = .abort
  obtain ⟨e, rfl⟩ := (Equiv.cast
    (congrArg Boundary.Exit (measureRounds_boundary pA pB Unit N k).symm)).surjective e
  refine (measureRounds_terminal pA pB Unit N k
    (fun _ value => value.disposition) e).trans ?_
  rcases e with ⟨a, b, order, e⟩
  revert e
  change ∀ e, ((if hasQuotas : Sampling.HasQuotas nK mZ mX
      (⟨a, b, order⟩ : Sampling.RawControl N) then
    (retainAlice (Sampling.selectedEmbedding ⟨a, b, order⟩ hasQuotas)).then <|
      (retainBob (Sampling.selectedEmbedding ⟨a, b, order⟩ hasQuotas)).then <|
        (forgetAliceBases N (nK + mZ + mX)).then <|
          (forgetBobBases N (nK + mZ + mX)).then <|
            classicalTail (nK + mZ + mX) (mZ + mX) ℓ ℓEV
              Sampling.packedPESel Sampling.packedXSel leakEC ec δ Q
    else (discardAlice (A := Measurement.CompletedLocalRecord N)
      (B := Measurement.CompletedLocalRecord N)).then
        (discardBob.then (.done QKD.KeyEnd.abort))).terminal e).disposition = .abort
  rw [dite_eq_right (hno ⟨a, b, order⟩)]
  intro e
  rfl

/-- If the requested total retained quota exceeds the physical round count, the actual protocol's
derived real-minus-ideal map is zero because every reachable branch is key-free shortage.

The fixed-count shortage is motivated by Pfister et al., arXiv:1506.07502v3, Sections IV--V and
Eq. (35). The exact equality is implementation-specific: the real output is already block
diagonal in its complete public exit, and the boundary ideal preserves every entry inside the
metadata-bearing abort block. -/
theorem difference_eq_zero_of_totalQuota_gt
    (pA pB : PMF Measurement.Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (hN : N < nK + mZ + mX)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    (QKD.BB84.protocol
      pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).difference = 0 := by
  let A := QKD.BB84.protocol
    pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q
  have hresource (rho : Op A.boundary.space)
      (hdiag : Boundary.IsExitBlockDiagonal A.boundary rho) :
      A.resource rho = rho := by
    ext i j
    rcases i with ⟨e, a⟩
    rcases j with ⟨f, b⟩
    change A.layout.toBoundaryKeyLayout.ideal rho ⟨e, a⟩ ⟨f, b⟩ =
      rho ⟨e, a⟩ ⟨f, b⟩
    by_cases hef : e = f
    · subst f
      have hdisposition : A.layout.disposition e =
          BoundaryKeyLayout.Disposition.abort := by
        exact outputLayout_disposition_eq_abort_of_totalQuota_gt
          pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q hN e
      exact A.layout.toBoundaryKeyLayout.ideal_coordinate_abort
        rho e hdisposition a b
    · rw [A.layout.toBoundaryKeyLayout.ideal_crossExit_zero rho hef a b,
        hdiag e f a b hef]
  have hideal : A.ideal = A.real := by
    apply LinearMap.ext
    intro rho
    change A.resource (A.real rho) = A.real rho
    exact hresource (A.real rho) (A.real_isExitBlockDiagonal rho)
  have hdifference : A.difference = 0 := by
    simp [QKD.Protocol.difference, hideal]
  exact hdifference

end QKD.BB84.Reduction
