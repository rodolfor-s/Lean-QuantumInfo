import QCryptLean.Math.Concentration.BinomialPassSum
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.QKD.BB84.Model.ErrorModel
import QCryptLean.QKD.BB84.Model.TwoBasisMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Symmetry.BellMixture

/-!
# The Bell-basis POVM and its Bell-Born weight

The four-outcome Bell-basis POVM `{|β_k⟩⟨β_k|}` and its per-outcome Born weight, together with
the Bell diagonalization of the phase-flip error projector.  Because `Z⊗Z` (bit) and `X⊗X`
(phase) commute, both the bit-error and the phase-error statistic can in principle be decoded
from a single Bell-basis outcome; this is Renner's single POVM `cM` with a multi-statistic
outcome alphabet (Renner 2005, `arXiv:quant-ph/0512258v2`, §6.5, `pr:PE` / `lem:PEsec`).

## The decisive index ordering

`bellState := ![bellState00, bellState01, bellState10, bellState11]` matches the `states`
vector of `Quantum.Basis.BellStates.bellStates_orthonormal` exactly.  With
`bellPOVM k = |β_k⟩⟨β_k|`, the BB84 phase-flip error projector is a diagonal reordering of
the Bell projectors: `phaseFlipProjector = bellPOVM 2 + bellPOVM 3` (β10, β11).

## Main definitions and results

* `bellState`, `bellPOVM` — the Bell vectors and the four-outcome Bell POVM.
* `bellPOVM_mul_self`, `isHermitian_bellPOVM`, `bellPOVM_complete` — the Bell
  POVM elements are projectors, Hermitian, and sum to the identity.
* `bellPOVM_phase_eq_phaseFlipProjector` — the Bell diagonalization of the phase-flip
  error projector.
* `bellBorn` — the per-outcome Bell-Born weight `⟨β_k|σ|β_k⟩`.
* `bellBorn_nonneg`, `bellBorn_sum` — the Bell-Born weights are nonnegative and sum to
  one.
* `bellBorn_phase_rate` — the phase Bell-Born marginal equals the phase-flip error rate.

## References

Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5 / `pr:PE` + `lem:PEsec`; Nahar, Tupkary, Zhao,
Lütkenhaus, Tan (2024), `arXiv:2403.11851`, Lemma 9 Eq. 44.
-/

open Quantum.Operators Quantum.Symmetry Matrix
open QKD.BB84.Measurement
open scoped ComplexOrder BigOperators

noncomputable section

namespace QKD.BB84.Model

/-- The Bell vectors on Alice's and Bob's bit registers, in phase/bit label order. -/
def bellState (k : Fin 4) : Ket Signal :=
  (bellLabelKet k).reindex (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)

/-- The Bell-basis measurement projectors on the signal pair. -/
def bellPOVM (k : Fin 4) : Op Signal := (bellState k).projector

/-- Each vector in the Bell measurement is normalized. -/
theorem bellState_dag_mul_self (k : Fin 4) : (bellState k).dag * bellState k = 1 := by
  change (∑ x : Signal, star ((bellLabelKet k).vec (finTwoEquiv x.1, finTwoEquiv x.2)) *
    (bellLabelKet k).vec (finTwoEquiv x.1, finTwoEquiv x.2)) = 1
  exact (Equiv.sum_comp (finTwoEquiv.prodCongr finTwoEquiv)
    (fun x => star ((bellLabelKet k).vec x) * (bellLabelKet k).vec x)).trans
      (bellNormKet k).normalized

/-- Each Bell measurement effect is idempotent. -/
theorem bellPOVM_mul_self (k : Fin 4) : bellPOVM k * bellPOVM k = bellPOVM k :=
  (⟨bellState k, bellState_dag_mul_self k⟩ : NormKet Signal).isPure_toDensityOp

/-- Each Bell measurement effect is Hermitian. -/
theorem isHermitian_bellPOVM (k : Fin 4) : (bellPOVM k).IsHermitian :=
  (bellState k).posSemidef_projector.isHermitian

/-- The Bell outcomes exhaust the signal-pair identity. -/
theorem bellPOVM_complete : ∑ k : Fin 4, bellPOVM k = (1 : Op Signal) := by
  change (∑ k, (reindexLinearEquiv ℂ ℂ
    (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)
    (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)) (bellLabelKet k).projector) = _
  rw [← map_sum, bellLabelKet_projectors_sum]
  exact submatrix_one_equiv _

/-- Phase errors are exactly the Bell sectors labelled 2 and 3. -/
theorem bellPOVM_phase_eq_phaseFlipProjector :
    bellPOVM 2 + bellPOVM 3 = phaseFlipProjector := rfl

/-- The Bell measurement probability of a single component. -/
def bellBorn (σ : DensityOp Signal) (k : Fin 4) : ℝ :=
  (bellPOVM k * σ.toOp).trace.re

/-- Bell measurement probabilities are nonnegative. -/
theorem bellBorn_nonneg (σ : DensityOp Signal) (k : Fin 4) : 0 ≤ bellBorn σ k :=
  (Complex.nonneg_iff.mp ((bellState k).posSemidef_projector.trace_mul_nonneg σ.posSemidef)).1

/-- Bell measurement probabilities sum to one. -/
theorem bellBorn_sum (σ : DensityOp Signal) : (∑ k : Fin 4, bellBorn σ k) = 1 := by
  unfold bellBorn
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, bellPOVM_complete,
    Matrix.one_mul, σ.trace_one, Complex.one_re]

/-- The phase Bell marginal equals the single-round phase-error probability. -/
theorem bellBorn_phase_rate (σ : DensityOp Signal) :
    bellBorn σ 2 + bellBorn σ 3 = phaseFlipErrorRate σ := by
  unfold bellBorn phaseFlipErrorRate
  rw [← bellPOVM_phase_eq_phaseFlipProjector, Matrix.add_mul, Matrix.trace_add, Complex.add_re]

end QKD.BB84.Model
