import QCryptLean.QKD.BB84.ClassicalStages
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.Measurement.Classicality
import QCryptLean.QKD.BB84.Measurement.Streaming
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Selection

/-!
# Streaming witness for BB84

The construction starts with the recursive private measurement phase. Each round acts only on
its arriving pair and preserves the other stream registers, and the complete phase preserves
zero accumulator blocks. The continuation begins after all quantum stream registers are empty.
-/

noncomputable section
namespace QKD.BB84
open LOCC FiniteKey

/-- BB84's construction begins with all `N` private Alice-then-Bob measurement rounds, and its
public continuation starts only after every qubit is measured. The prefix carries the per-step
online identity and the accumulator block invariant. -/
theorem streamingMeasurementPrefix_construction
    (pA pB : PMF Measurement.Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Measurement.Streaming.StreamingMeasurementPrefix pA pB N
      (QKD.BB84.construction pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q) := by
  obtain ⟨k, hk, _⟩ :=
    exists_eq_measureRounds_isHonestClassical pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q
  refine ⟨k, hk, ?_, ?_⟩
  · intro F _ _ _ n
    exact Measurement.Streaming.weightedStreamRoundProgram_denote_eq_online
      pA pB F n
  · intro F _ _ _ n rho fA fA' fB fB' hzero rA rA' rB rB'
    exact Measurement.scheduleWithMemory_preserves_accumulator_block_zero
      pA pB F n rho fA fA' fB fB' hzero rA rA' rB rB'

end QKD.BB84
