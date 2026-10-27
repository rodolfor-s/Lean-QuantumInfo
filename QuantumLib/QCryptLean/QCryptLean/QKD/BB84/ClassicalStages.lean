import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.Instrument.ClassicalPreservation
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.TwoPartyClassicalStorage
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.KeyEnd

/-! # Classical Stages -/


noncomputable section

namespace QKD.BB84
open LOCC LOCC.TwoParty Measurement FiniteKey

variable {End : MultipartiteSystem Party → Type 1}

/-- A deterministic local readout preserves honest-register diagonality on every raw branch. -/
theorem announcedReadout_preservesHonestRegistersDiagonal
    {R : MultipartiteSystem Party} (i : Party) {Public Readout : Type}
    [Fintype Public] [DecidableEq Public] [Fintype Readout] [DecidableEq Readout]
    (f : R.reg i → Readout) (announce : Readout → Public) :
    (AnnouncedAction.ofInstrument i
      (Instrument.nondemolitionReadout f) announce).PreservesHonestRegistersDiagonal :=
  AnnouncedAction.ofInstrument_preservesHonestRegistersDiagonal i _ announce
    (Instrument.nondemolitionReadout_preservesDiagonalBranches f)

/-- The recursive test discussion preserves every certified continuation. -/
theorem isHonestClassical_announceTests {n : ℕ} (r : ℕ) (idx : Fin r → Fin n)
    (k : (Fin r → Bit × Bit) → Program (system (Bits n) (Bits n)) End)
    (hk : ∀ tests, (k tests).IsHonestClassical) :
    (announceTests r idx k).IsHonestClassical := by
  induction r with
  | zero => exact hk Fin.elim0
  | succ r ih =>
      refine .announced _ _ (announcedReadout_preservesHonestRegistersDiagonal _ _ _) (fun b => ?_)
      refine .announced _ _ (announcedReadout_preservesHonestRegistersDiagonal _ _ _) (fun a => ?_)
      exact ih (Fin.tail idx) _
        (fun rest => hk (Fin.cons (a, b) rest))

/-- Every action of the classical tail preserves classical honest registers. -/
theorem isHonestClassical_classicalTail
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).IsHonestClassical := by
  unfold classicalTail
  apply isHonestClassical_announceTests
  intro tests
  refine .announced _ _ ?_ (fun cell => ?_)
  · exact AnnouncedAction.ofInstrument_preservesHonestRegistersDiagonal _ _ _
      (Instrument.uniformChoice_preservesDiagonalBranches _ fun _ =>
        Instrument.nondemolitionReadout_preservesDiagonalBranches _)
  · dsimp only
    refine .announced _ _ (announcedReadout_preservesHonestRegistersDiagonal _ _ _)
      (fun flag => ?_)
    dsimp +instances only [announceSeedTagSyndrome, announceAccept, hashAlice, correctAndHashBob,
      discardAlice, discardBob, AnnouncedAction.ofInstrument, PrivateAction.ofInstrument] at *
    split
    · refine .priv _ _ ?_ (.priv _ _ ?_ (.done _))
      all_goals
        exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
          (Instrument.functionAndForget_preservesDiagonalBranches _)
    · refine .priv _ _ ?_ (.priv _ _ ?_ (.done _))
      all_goals
        exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
          (Instrument.discardToUnit_preservesDiagonalBranches (A := Bits n))

/-- BB84's construction is its measurement rounds followed by an honest-classical program. -/
theorem exists_eq_measureRounds_isHonestClassical
    (pA pB : PMF Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ) :
    ∃ k : Program (system (CompletedLocalRecord N) (CompletedLocalRecord N))
        (KeyEnd Party.alice Party.bob),
      construction pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q =
        measureRounds pA pB Unit N k ∧ k.IsHonestClassical := by
  unfold construction
  refine ⟨_, rfl, ?_⟩
  refine .announced _ _ (announcedReadout_preservesHonestRegistersDiagonal _ _ _)
    (fun aliceBases => ?_)
  refine .announced _ _ (announcedReadout_preservesHonestRegistersDiagonal _ _ _)
    (fun bobBases => ?_)
  refine .announced _ _ ?_ (fun order => ?_)
  · exact AnnouncedAction.ofInstrument_preservesHonestRegistersDiagonal _ _ _
      Instrument.uniformSample_preservesDiagonalBranches
  · dsimp only
    unfold announceAliceBases announceBobBases announceShuffle AnnouncedAction.ofInstrument at *
    split
    · refine .priv _ _ ?_ (.priv _ _ ?_ (.priv _ _ ?_ (.priv _ _ ?_ ?_)))
      · exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
          (Instrument.functionAndForget_preservesDiagonalBranches _)
      · exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
          (Instrument.functionAndForget_preservesDiagonalBranches _)
      · exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
          (Instrument.functionAndForget_preservesDiagonalBranches _)
      · exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
          (Instrument.functionAndForget_preservesDiagonalBranches _)
      · exact isHonestClassical_classicalTail _ _ _ _ _ _ _ _ _ _
    · refine .priv _ _ ?_ (.priv _ _ ?_ (.done _))
      all_goals
        exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
          (Instrument.discardToUnit_preservesDiagonalBranches (A := CompletedLocalRecord N))

end QKD.BB84
