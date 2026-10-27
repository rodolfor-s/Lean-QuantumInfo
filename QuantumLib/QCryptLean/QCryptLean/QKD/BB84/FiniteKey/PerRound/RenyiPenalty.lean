import QCryptLean.InfoTheory.Renyi.FiniteSizePenalty
import QCryptLean.InfoTheory.Renyi.SecondOrderConstants
import QCryptLean.InfoTheory.Renyi.Basic
import QCryptLean.InfoTheory.Renyi.Continuity
import QCryptLean.InfoTheory.Renyi.QubitVariance
import QCryptLean.InfoTheory.Renyi.SmoothMin
import QCryptLean.InfoTheory.Renyi.Bounds
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PhaseErrorUncertainty
import QCryptLean.QKD.BB84.FiniteKey.PerRound.ConditionalEntropy
import QCryptLean.QKD.BB84.FiniteKey.PerRound.DevetakWinter
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor

/-!
# The `n_copies`-fold AEP lift at the Cor IV.2 binary-variance-bound penalty

The scalar penalty and its elementary properties (`UnclampedRegime`,
`clampedRenyiOffset`, `clampedRenyiOrder`, `clampedRenyiPenalty` and its
closed form) have no quantum content and live in `InfoTheory/Renyi/FiniteSizePenalty.lean`;
this module has the one quantum theorem that pays that penalty: Dupuis–Fawzi's Corollary IV.2
finite-size AEP penalty for the smooth min-entropy of an IID tensor power, charged at the variance
cap `condVariance_le_logb_sq_of_card_eq_two` (`V(X|B) ≤ log₂²(1+√2) ≈ 1.6168` at
`d_A = 2`), the cap recorded as `binaryVarianceBound`.

With `B := log₂(2/ε²)`, `β := clampedRenyiOffset binaryVarianceBound m ε` and `α := 1 + β`,
the chain is

```
Hmin^ε(ρ^{⊗m} ‖ ρ_B^{⊗m})
  ≥ m·H'_α(X|B)_ρ − B/(α−1)
  ≥ m·(H − ((α−1)·log 2/2)·V − (α−1)²·K) − B/β
  ≥ m·H − (binaryVarianceBound/2)·log 2·m·β − K_β·m·β² − B/β
  = m·H − clampedRenyiPenalty binaryVarianceBound m ε.
```

## Main results

- `QKD.BB84.FiniteKey.le_smoothMinEntropy_tensorPower_renyiPenalty`: the `n_copies`-fold
  smooth AEP lift at the Cor IV.2 penalty charged at a free Rényi offset `β ∈ (0, 1)`
  (Dupuis–Fawzi Cor. IV.2 holds at every such `β`).
- `QKD.BB84.FiniteKey.le_smoothMinEntropy_tensorPower_clampedRenyiPenalty`: the same lift at
the
  clamped optimiser `β = clampedRenyiOffset binaryVarianceBound n_copies ε`, as a corollary.

Reference: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`:784`), `K(α)` (`:789`), `\label{eq_eatblock}` (`:1047`), `\label{eq_eathmin_halpha}` (`:1053`),
`\label{eq_alphachoiceext}` (`:1061`); the variance bound replaced by the cap is
`\label{lem:divergence-variance-general-bounds}` (`:394`) with `\label{eq:bound_dalpha}`
(`:398`–`:399`); Tomamichel 2015 (`arXiv:1504.00233`) Prop. 6.5 (`calculus.tex:1025`
`\label{pr:min-renyi}`).
-/

open Quantum.Operators QKD.BB84.Measurement
open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy
open InfoTheory.Renyi InfoTheory.Renyi
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace QKD.BB84.FiniteKey

/-- **The `n_copies`-fold smooth AEP lift at the Rényi Cor IV.2 penalty, at a free Rényi
offset `β`.**

`ofReal (n_K·H(Z_A|E)_σ − renyiPenalty binaryVarianceBound n_K ε β)
≤ Hmin^ε(ρ_σ^{⊗n_K} ‖ ρ_E^{⊗n_K})` for every admissible offset `β ∈ (0, 1)`: the
Dupuis–Fawzi Corollary IV.2 bound holds at every such `β`, not only at the clamped optimiser
`clampedRenyiOffset`.  Via the Rényi argument: the smooth min-entropy of the tensor power is bounded
below through the Petz-down conditional Rényi entropy at order `α = 1 + β`, which Corollary IV.2
relates to the conditional von Neumann entropy using the binary variance bound
`condVariance_le_logb_sq_of_card_eq_two` and the `K(1 + β) ≤ K_β` bound.

Reference: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`:784`), `\label{eq_eatblock}` (`:1047`), `\label{eq_eathmin_halpha}` (`:1053`); Tomamichel 2015
(`arXiv:1504.00233`) Prop. 6.5 (`calculus.tex:1025`). -/
theorem le_smoothMinEntropy_tensorPower_renyiPenalty (σ : DensityOp Signal)
    (n_copies : ℕ) (ε β : ℝ)
    (hε : 0 < ε) (hβpos : 0 < β) (hβ1 : β < 1) :
    ENNReal.ofReal ((n_copies : ℝ) *
          ((vonNeumannEntropy
              ((componentAliceZCQState σ).toJointDensityOp
                (aliceZCQState_weight_eq_one Signal σ.purification))
            - vonNeumannEntropy
              ((componentAliceZCQState σ).quantumMarginalDensityOp
                (aliceZCQState_weight_eq_one Signal σ.purification))) / Real.log 2)
        - renyiPenalty binaryVarianceBound n_copies ε β) ≤
      smoothMinEntropy ε (CQState.tensorPower (componentAliceZCQState σ) n_copies)
        (SubDensityOp.tensorPow
          (DensityOp.toSubDensityOp
            ((componentAliceZCQState σ).quantumMarginalDensityOp
              (aliceZCQState_weight_eq_one Signal σ.purification))) n_copies) := by
  set ρ : CQState (Fin 2) Signal := componentAliceZCQState σ with hρdef
  have hnorm : ∑ z : Fin 2, (ρ.stateMap z).trace = 1 :=
    aliceZCQState_weight_eq_one Signal σ.purification
  -- the Rényi order is `1 + β`, directly (no detour through the clamped optimiser)
  set α : ℝ := 1 + β with hαdef
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hα1 : 1 < α := by rw [hαdef]; linarith
  have hα2' : α < 2 := by rw [hαdef]; linarith
  have hαβ : α - 1 = β := by rw [hαdef]; ring
  have hcard : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  -- Apply the smooth min-entropy bound at `α`.
  have hendpoint :=
    InfoTheory.Renyi.TensorPower.ofReal_mul_condPetzRenyiDown_sub_le_smoothMinEntropy
    α hα1 ε hε ρ hnorm n_copies
  rw [InfoTheory.Renyi.renyiBlockEntropyFloor, hαβ] at hendpoint
  -- Corollary IV.2, per round
  have hcor := sub_sub_le_condPetzRenyiDown α hα1 hα2' ρ hnorm
  -- the two constant caps, the first at the value `log₂²(1+√2)`
  have hV : condVariance ρ ≤ binaryVarianceBound := by
    simpa only [binaryVarianceBound, add_comm] using
      InfoTheory.Renyi.condVariance_le_logb_sq_of_card_eq_two ρ hnorm hcard
  have hK : secondOrderK α ρ ≤ binarySecondOrderRemainderBound β :=
    secondOrderK_le_binarySecondOrderRemainderBound β hβpos hβ1 ρ hnorm hcard
  have hcoef : (0 : ℝ) ≤ (α - 1) * Real.log 2 / 2 := by rw [hαβ]; positivity
  have hVstep : ((α - 1) * Real.log 2 / 2) * condVariance ρ
      ≤ ((α - 1) * Real.log 2 / 2) * binaryVarianceBound := mul_le_mul_of_nonneg_left hV hcoef
  have hKstep : (α - 1) ^ 2 * secondOrderK α ρ ≤ (α - 1) ^ 2 * binarySecondOrderRemainderBound β :=
    mul_le_mul_of_nonneg_left hK (sq_nonneg _)
  -- the per-round floor
  have hround : CQState.condVonNeumannBits ρ - binaryVarianceBound / 2
    * Real.log 2 * β
      - binarySecondOrderRemainderBound β * β ^ 2
      ≤ condPetzRenyiDown α ρ := by
    have h1 : ((α - 1) * Real.log 2 / 2) * binaryVarianceBound
        = binaryVarianceBound / 2 * Real.log 2 * β := by
      rw [hαβ]; ring
    have h2 : (α - 1) ^ 2 * binarySecondOrderRemainderBound β
        = binarySecondOrderRemainderBound β * β ^ 2 := by rw [hαβ]; ring
    linarith only [hcor, hVstep, hKstep, h1, h2]
  -- scale by `n_copies` and subtract the smoothing charge
  have hmnn : (0 : ℝ) ≤ (n_copies : ℝ) := Nat.cast_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hround hmnn
  have hpen : renyiPenalty binaryVarianceBound n_copies ε β
      = binaryVarianceBound / 2 * Real.log 2 * (n_copies : ℝ) * β
        + binarySecondOrderRemainderBound β * (n_copies : ℝ) * β ^ 2
        + Real.logb 2 (2 / ε ^ 2) / β := by
    rw [renyiPenalty,
    InfoTheory.Renyi.renyiVariancePenalty,
    InfoTheory.Renyi.renyiRemainderPenalty,
    InfoTheory.Renyi.renyiSmoothingPenalty,
    InfoTheory.Renyi.smoothingLog]
  -- rewrite `H` into the Devetak–Winter form
  have hbridge : CQState.condVonNeumannBits ρ
      = (vonNeumannEntropy
            ((componentAliceZCQState σ).toJointDensityOp
                (aliceZCQState_weight_eq_one Signal σ.purification))
          - vonNeumannEntropy
            ((componentAliceZCQState σ).quantumMarginalDensityOp
              (aliceZCQState_weight_eq_one Signal σ.purification))) / Real.log 2 := by
    rw [hρdef, condVonNeumannBits_componentAliceZCQState_eq_rate σ, componentAliceZRate]
  rw [← hbridge, hpen]
  refine (ENNReal.ofReal_le_ofReal ?_).trans hendpoint
  calc (n_copies : ℝ) * CQState.condVonNeumannBits ρ
        - (binaryVarianceBound / 2 * Real.log 2 * n_copies * β
          + binarySecondOrderRemainderBound β * n_copies * β ^ 2
          + Real.logb 2 (2 / ε ^ 2) / β)
      = n_copies * (CQState.condVonNeumannBits ρ - binaryVarianceBound
        / 2 * Real.log 2 * β
          - binarySecondOrderRemainderBound β * β ^ 2) - Real.logb 2 (2 / ε ^ 2) / β := by ring
    _ ≤ n_copies * condPetzRenyiDown α ρ - Real.logb 2 (2 / ε ^ 2) / β :=
        sub_le_sub_right hscaled _

/-- **The `n_copies`-fold smooth AEP lift at the Rényi Cor IV.2 penalty** (at the clamped
optimiser `β⋆ = clampedRenyiOffset binaryVarianceBound n_K ε`), as a corollary of the free-β
version, with the completed signed floor cast by `ENNReal.ofReal`. Positivity of `β⋆` uses
`[NeZero n_K]` and `ε < 1`. -/
theorem le_smoothMinEntropy_tensorPower_clampedRenyiPenalty (σ : DensityOp Signal)
    (n_copies : ℕ) [NeZero n_copies] (ε : ℝ)
    (hε : 0 < ε) (hε_lt : ε < 1) :
    ENNReal.ofReal ((n_copies : ℝ) *
          ((vonNeumannEntropy
              ((componentAliceZCQState σ).toJointDensityOp
                (aliceZCQState_weight_eq_one Signal σ.purification))
            - vonNeumannEntropy
              ((componentAliceZCQState σ).quantumMarginalDensityOp
                (aliceZCQState_weight_eq_one Signal σ.purification))) / Real.log 2)
        - clampedRenyiPenalty binaryVarianceBound n_copies ε) ≤
      smoothMinEntropy ε (CQState.tensorPower (componentAliceZCQState σ) n_copies)
        (SubDensityOp.tensorPow
          (DensityOp.toSubDensityOp
            ((componentAliceZCQState σ).quantumMarginalDensityOp
              (aliceZCQState_weight_eq_one Signal σ.purification))) n_copies) := by
  have hβpos : 0 < clampedRenyiOffset binaryVarianceBound n_copies ε :=
    clampedRenyiOffset_pos binaryVarianceBound binaryVarianceBound_pos n_copies ε hε hε_lt
  have h := le_smoothMinEntropy_tensorPower_renyiPenalty σ n_copies ε
    (clampedRenyiOffset binaryVarianceBound n_copies ε) hε hβpos
    ((clampedRenyiOffset_le_one_sixteenth binaryVarianceBound n_copies ε).trans_lt (by norm_num))
  rwa [← clampedRenyiPenalty_eq] at h

end QKD.BB84.FiniteKey

end -- noncomputable section
