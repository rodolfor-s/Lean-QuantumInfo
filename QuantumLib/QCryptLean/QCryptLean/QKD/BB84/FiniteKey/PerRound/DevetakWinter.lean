import QCryptLean.InfoTheory.BellDiagonal.AliceZ
import QCryptLean.InfoTheory.BellDiagonal.AliceZEntropy
import QCryptLean.InfoTheory.BellDiagonal.Entropy
import QCryptLean.InfoTheory.BellDiagonal.Monotonicity
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPRank
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPRates
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.ClassicalEntropy.KLDivergence
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.QKD.BB84.FiniteKey.Budgets.SmoothEntropyBound
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.AEPLevels
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellRotationFactorization
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PhaseErrorUncertainty
import QCryptLean.QKD.BB84.Model.BellMeasurement
import QCryptLean.QKD.BB84.Model.ErrorModel
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.ReferenceTransport
import QCryptLean.Quantum.Operators.ReferenceTransportBounds
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor

/-! # The collective Devetak–Winter rate on natural signal registers

The canonical purifier and the measured reference both use the signal-pair type.
Alice's bit has classical rank at most two, so the IID correction remains
`2 log₂ 5`. Bell pinching and its entropy formula retain the phase/bit label order.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Metrics Matrix
open InfoTheory.SmoothMinEntropy InfoTheory.VonNeumannEntropy
open InfoTheory.BellDiagonal Math.ClassicalEntropy
open QKD.BB84.Model QKD.BB84.Measurement
open scoped Kronecker

/-- Alice's measured bit with the canonical purifying signal-pair reference. -/
def componentAliceZCQState (σ : DensityOp Signal) : CQState Bit Signal :=
  aliceZCQState Signal σ.purification

/-- Unitary freedom of a pure extension identifies every Alice-Z block and marginal. -/
theorem exists_unitary_componentAliceZ_eq_siftedKeyRound_conj
    (ψ : DensityOp (Signal × Signal)) (hψ : ψ.IsPure) :
    ∃ W : UnitaryOp Signal,
      (∀ z : Bit, ((componentAliceZCQState ψ.partialTraceRight).stateMap z).toOp =
        W.valᴴ * ((aliceZCQState Signal ψ).stateMap z).toOp * W.val) ∧
      (componentAliceZCQState ψ.partialTraceRight).quantumMarginal.toOp =
        W.valᴴ * (aliceZCQState Signal ψ).quantumMarginal.toOp * W.val := by
  let σ := ψ.partialTraceRight
  obtain ⟨W, hW⟩ := σ.exists_reference_unitary ψ hψ rfl
  have hUU : W.valᴴ * W.val = 1 :=
    mul_eq_one_comm.mp (Matrix.mem_unitaryGroup_iff.mp W.property)
  have hc (P : Op Signal) (M : Op (Signal × Signal)) :
      partialTraceLeft ((P ⊗ₖ (1 : Op Signal)) * rightTensorUnitaryConj W M *
        (P ⊗ₖ (1 : Op Signal))) =
      W.val * partialTraceLeft ((P ⊗ₖ (1 : Op Signal)) * M *
        (P ⊗ₖ (1 : Op Signal))) * W.valᴴ := by
    have h1 : (P ⊗ₖ (1 : Op Signal)) * ((1 : Op Signal) ⊗ₖ W.val) =
        ((1 : Op Signal) ⊗ₖ W.val) * (P ⊗ₖ (1 : Op Signal)) := by
      simp only [← mul_kronecker_mul, mul_one, one_mul]
    have h2 : ((1 : Op Signal) ⊗ₖ W.valᴴ) * (P ⊗ₖ (1 : Op Signal)) =
        (P ⊗ₖ (1 : Op Signal)) * ((1 : Op Signal) ⊗ₖ W.valᴴ) := by
      simp only [← mul_kronecker_mul, mul_one, one_mul]
    unfold rightTensorUnitaryConj
    rw [conjTranspose_kronecker, conjTranspose_one]
    have he : (P ⊗ₖ (1 : Op Signal)) *
        (((1 : Op Signal) ⊗ₖ W.val) * M * ((1 : Op Signal) ⊗ₖ W.valᴴ)) *
        (P ⊗ₖ (1 : Op Signal)) =
        ((1 : Op Signal) ⊗ₖ W.val) *
          ((P ⊗ₖ (1 : Op Signal)) * M * (P ⊗ₖ (1 : Op Signal))) *
          ((1 : Op Signal) ⊗ₖ W.valᴴ) := by
      simp only [← mul_assoc]
      rw [h1, mul_assoc (((1 : Op Signal) ⊗ₖ W.val) * (P ⊗ₖ 1) * M), h2]
      simp only [← mul_assoc]
    rw [he, partialTraceLeft_one_kronecker_sandwich]
  have hblock (z : Bit) : ((componentAliceZCQState σ).stateMap z).toOp =
      W.valᴴ * ((aliceZCQState Signal ψ).stateMap z).toOp * W.val := by
    change ((aliceZCQState Signal σ.purification).stateMap z).toOp = _
    rw [aliceZCQState_origin, aliceZCQState_origin, hW, hc]
    calc _ = (W.valᴴ * W.val) *
        partialTraceLeft ((aliceZProj z ⊗ₖ (1 : Op Signal)) * σ.purification.toOp *
          (aliceZProj z ⊗ₖ (1 : Op Signal))) * (W.valᴴ * W.val) := by
            rw [hUU, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  refine ⟨W, hblock, ?_⟩
  change (∑ z, ((componentAliceZCQState σ).stateMap z).toOp) =
    W.valᴴ * (∑ z, ((aliceZCQState Signal ψ).stateMap z).toOp) * W.val
  simp only [Finset.mul_sum, Finset.sum_mul, hblock]

/-- The conditional single-round entropy in bits, against the canonical reference. -/
def componentAliceZRate (σ : DensityOp Signal) : ℝ :=
  (vonNeumannEntropy
      ((componentAliceZCQState σ).toJointDensityOp
          (aliceZCQState_weight_eq_one Signal σ.purification)) -
    vonNeumannEntropy
      ((componentAliceZCQState σ).quantumMarginalDensityOp
          (aliceZCQState_weight_eq_one Signal σ.purification))) / Real.log 2

/-- The canonical-purifier rate is Alice's entropy production on the signal pair. -/
theorem componentAliceZRate_eq_dephasingRate (σ : DensityOp Signal) :
    vonNeumannEntropy
        ((componentAliceZCQState σ).toJointDensityOp
          (aliceZCQState_weight_eq_one Signal σ.purification)) -
      vonNeumannEntropy
        ((componentAliceZCQState σ).quantumMarginalDensityOp
          (aliceZCQState_weight_eq_one Signal σ.purification)) =
      vonNeumannEntropy (aliceZDephase σ) - vonNeumannEntropy σ := by
  have hm : partialTraceRight σ.purification.toOp = σ.toOp :=
    congrArg DensityOp.toOp σ.partialTraceRight_purification
  unfold componentAliceZCQState
  rw [aliceZ_measuredJoint_entropy_eq_dephase σ _
          (aliceZCQState_weight_eq_one Signal σ.purification)
      σ.purification σ.isPure_purification hm (aliceZCQState_origin Signal σ.purification),
    aliceZ_quantumMarginal_entropy_eq_self σ _
          (aliceZCQState_weight_eq_one Signal σ.purification)
      σ.purification σ.isPure_purification hm (aliceZCQState_origin Signal σ.purification)]

/-- Bell pinching cannot increase the single-round key rate. -/
theorem componentAliceZRate_bellDephasingDensity_le (σ : DensityOp Signal) :
    componentAliceZRate (bellDephasingDensity σ) ≤ componentAliceZRate σ := by
  unfold componentAliceZRate
  rw [componentAliceZRate_eq_dephasingRate, componentAliceZRate_eq_dephasingRate]
  exact div_le_div_of_nonneg_right
    (vonNeumannEntropy_aliceZDephase_bellDephasingDensity_sub_le σ)
    (Real.log_pos one_lt_two).le

/-- Bell probabilities from fidelity are exactly the physical Bell Born weights. -/
lemma bellProbability_eq_bellBorn (σ : DensityOp Signal) (b : Bit × Bit) :
    bellProbability σ b = bellBorn σ (finProdFinEquiv b) := by
  let v : NormKet Signal :=
    ⟨bellState (finProdFinEquiv b), bellState_dag_mul_self (finProdFinEquiv b)⟩
  exact fidelitySq_pure_right σ.toPosSemidefOp v

/-- Rank-capped IID AEP for Alice's bit, with the unchanged `2 log₂ 5` penalty. -/
theorem le_smoothMinEntropy_tensorPower (σ : DensityOp Signal) (n_copies : ℕ)
    [NeZero n_copies] (ε : ℝ) (hε : 0 < ε) :
    ENNReal.ofReal ((n_copies : ℝ) *
        ((vonNeumannEntropy
            ((componentAliceZCQState σ).toJointDensityOp
          (aliceZCQState_weight_eq_one Signal σ.purification)) -
          vonNeumannEntropy
            ((componentAliceZCQState σ).quantumMarginalDensityOp
          (aliceZCQState_weight_eq_one Signal σ.purification))) / Real.log 2) -
      finiteSizePenalty n_copies ε) ≤
      smoothMinEntropy ε ((componentAliceZCQState σ).tensorPower n_copies)
        (((componentAliceZCQState σ).quantumMarginalDensityOp
          (aliceZCQState_weight_eq_one Signal σ.purification)).toSubDensityOp.tensorPow
            n_copies) := by
  have h := AEP.IID.ofReal_mul_sub_le_smoothMinEntropy_of_classicalRank_le
    (componentAliceZCQState σ)
          (aliceZCQState_weight_eq_one Signal σ.purification) n_copies ε hε 2 (by
      unfold CQState.classicalRank
      exact (Finset.card_filter_le _ _).trans (by simp [Bit]))
  simpa only [Nat.cast_ofNat, show (2 : ℝ) + 3 = 5 by norm_num, mul_sub,
    finiteSizePenalty, AEP.IID.tensorReference] using h

/-- The phase-error entropy floor holds for every signal state, without a rate-window premise. -/
theorem div_le_componentAliceZRate (σ : DensityOp Signal) :
    (Real.log 2 - binaryEntropy (phaseFlipErrorRate σ)) / Real.log 2 ≤
      componentAliceZRate σ := by
  have hΔ := vonNeumannEntropy_aliceZDephase_bellDephasingDensity σ
  simp only [bellProbability_eq_bellBorn] at hΔ
  have hT := vonNeumannEntropy_bellDephasingDensity σ
  simp only [bellProbability_eq_bellBorn] at hT
  have hsub := shannonEntropy_four_le_add_binaryEntropy (bellBorn σ 0) (bellBorn σ 1)
    (bellBorn σ 2) (bellBorn σ 3) (bellBorn_nonneg σ 0) (bellBorn_nonneg σ 1)
    (bellBorn_nonneg σ 2) (bellBorn_nonneg σ 3)
    (by have h := bellBorn_sum σ; rwa [Fin.sum_univ_four] at h)
  rw [bellBorn_phase_rate σ] at hsub
  have hstep : (Real.log 2 - binaryEntropy (phaseFlipErrorRate σ)) / Real.log 2 ≤
      componentAliceZRate (bellDephasingDensity σ) := by
    unfold componentAliceZRate
    rw [componentAliceZRate_eq_dephasingRate, hΔ, hT]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two] at *
    apply (div_le_div_iff_of_pos_right (Real.log_pos one_lt_two)).mpr
    change Real.log 2 - binaryEntropy (phaseFlipErrorRate σ) ≤
      Real.log 2 + binaryEntropy (bellBorn σ 1 + bellBorn σ 3) -
        ((entropyTerm (bellBorn σ 0) + entropyTerm (bellBorn σ 1)) +
          (entropyTerm (bellBorn σ 2) + entropyTerm (bellBorn σ 3)))
    simp [shannonEntropy, Fin.sum_univ_four] at hsub
    linarith
  exact hstep.trans (componentAliceZRate_bellDephasingDensity_le σ)

/-- A phase-rate upper estimate below one half can be substituted into the entropy floor. -/
theorem div_le_componentAliceZRate_of_phaseRate_le (σ : DensityOp Signal) (Q δ dev : ℝ)
    (hbound : Q + δ + dev ≤ 1 / 2) (hphase : phaseFlipErrorRate σ ≤ Q + δ + dev) :
    (Real.log 2 - binaryEntropy (Q + δ + dev)) / Real.log 2 ≤ componentAliceZRate σ := by
  have hmp := binaryEntropy_le_of_le_of_le_half (phaseFlipErrorRate_bounds σ).1 hphase hbound
  exact le_trans ((div_le_div_iff_of_pos_right (Real.log_pos one_lt_two)).mpr (by linarith))
    (div_le_componentAliceZRate σ)

/-- The window version is the free phase-deviation estimate at `dev = δ`. -/
theorem Window.div_le_componentAliceZRate_of_phaseRate_le (σ : DensityOp Signal) (Q δ : ℝ)
    (hbound : Q + 2 * δ ≤ 1 / 2) (hphase : phaseFlipErrorRate σ ≤ Q + 2 * δ) :
    (Real.log 2 - binaryEntropy (Q + 2 * δ)) / Real.log 2 ≤ componentAliceZRate σ := by
  have h := QKD.BB84.FiniteKey.div_le_componentAliceZRate_of_phaseRate_le σ Q δ δ
    (by linarith) (by linarith)
  rwa [show (Q : ℝ) + δ + δ = Q + 2 * δ by ring] at h

end QKD.BB84.FiniteKey
