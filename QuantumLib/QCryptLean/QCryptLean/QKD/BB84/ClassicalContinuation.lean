import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Instrument.ClassicalTransition
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.Program.TwoPartyClassicalReplacement
import QCryptLean.LOCC.Program.TwoPartyClassicalStorage
import QCryptLean.QKD.BB84.ClassicalStages
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.Measurement.ClassicalityReference
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.Protocol
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Operators.Basic

/-!
# Classical outputs of the BB84 construction

The private measurement phase produces classical records against arbitrary reference systems.
The certified continuation preserves their classicality through selection, test discussion,
verification and the terminal key or abort declarations.
-/

open Quantum.Operators (Op)

open Quantum.Channels (
  mapTensorId
  mapTensorId_apply
  mapTensorId_comp)

noncomputable section
namespace QKD.BB84
open LOCC LOCC.TwoParty Measurement FiniteKey

/-- The complete protocol produces classical public output and registers against any reference. -/
theorem protocol_real_isClassicalOnFirst
    (pA pB : PMF Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ)
    {E : Type} (rho : Op ((weightedStreamSystem Unit N).total × E)) :
    IsClassicalOnFirst (mapTensorId (protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).real E rho) :=
      by
  change IsClassicalOnFirst (mapTensorId (construction pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).denote
    E rho)
  obtain ⟨k, hk, hc⟩ :=
    exists_eq_measureRounds_isHonestClassical pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q
  rw [hk]
  let e := Equiv.cast (congrArg Boundary.space (measureRounds_boundary pA pB Unit N k))
  have hd := measureRounds_then_denote pA pB Unit N k
  have hcomp := congrArg (fun Φ => mapTensorId Φ E rho) hd
  simp only [mapTensorId_comp, LinearMap.comp_apply] at hcomp
  have hclass := hc.denote_tensorId (mapTensorId (measurementState pA pB Unit N) E rho)
    (weightedMeasurementSchedule_isClassicalOnFirst pA pB N rho)
  intro q q' s t hqq
  have hz := hclass (e q) (e q') s t (e.injective.ne hqq)
  have hentry := congrArg (fun M => M (e q, s) (e q', t)) hcomp
  change (mapTensorId ((Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) E
    (mapTensorId (measureRounds pA pB Unit N k).denote E rho))
      (e q, s) (e q', t) = _ at hentry
  rw [mapTensorId_apply] at hentry
  change (mapTensorId (measureRounds pA pB Unit N k).denote E rho)
    (e.symm (e q), s) (e.symm (e q'), t) = _ at hentry
  simpa only [Equiv.symm_apply_apply] using hentry.trans hz

/-- Every output exit is diagonal in both final honest registers on arbitrary physical inputs. -/
theorem protocol_real_honestRegistersDiagonal
    (pA pB : PMF Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ)
    (rho : Op (weightedStreamSystem Unit N).total) :
    (protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).boundary.HonestRegistersDiagonal
      ((protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).real rho) := by
  intro e q q' hdiff
  have hne : (⟨e, q⟩ :
      (protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).boundary.space) ≠ ⟨e, q'⟩ := by
    intro h
    cases h
    exact hdiff.elim (fun ha => ha rfl) (fun hb => hb rfl)
  exact protocol_real_isClassicalOnFirst pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q
    (E := Unit) (fun x y => rho x.1 y.1) ⟨e, q⟩ ⟨e, q'⟩ () () hne

end QKD.BB84
