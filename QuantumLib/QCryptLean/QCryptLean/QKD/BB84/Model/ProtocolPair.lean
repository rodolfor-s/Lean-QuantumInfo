import QCryptLean.QKD.BB84.Model.ErrorModel
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic

/-!
# The good-rate set for parameter estimation

The set of de Finetti components whose per-component bit- and phase-flip error rates both lie
within the PE acceptance window.

## Main definitions

* `componentAliceBobMarginal` — the per-component single-round Alice–Bob marginal classifier
  (the identity on the component), used to define `goodRateSet`. Its continuity and measurability
  are proved in `PEConcentration.lean`.
* `goodRateSet` — de Finetti components with acceptable induced bit and phase error rates.

## References

Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024, Lemma 9 Eq. 44.
-/

open Quantum.Operators
open QKD.BB84.Measurement

noncomputable section

namespace QKD.BB84.Model

/-- The per-IID-component single-round Alice–Bob marginal of a de Finetti
component `σ` under the per-round PE POVM (Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024,
arXiv:2403.11851, Lemma 9 Eq.44).

For a single-round BB84 de Finetti component `σ : DensityOp Signal`, the
per-round PE POVM `{Γⱼ}` (the Bell-basis bit-flip and phase-flip projectors) acts
on the single round, so the component's *own* Alice–Bob marginal against which the
per-round Born statistic `Tr(Γⱼ σ)` is measured is `σ` itself.  This is an
attack-independent per-component classifier: a covariant
mixture can carry a bad *average* while every per-component statistic stays good,
so the PE classifier must be keyed to the per-component marginal, not the average.

Explicit definition (the identity on the component), no `Classical.choose`. -/
def componentAliceBobMarginal (σ : DensityOp Signal) : DensityOp Signal :=
  σ

@[simp] theorem componentAliceBobMarginal_eq (σ : DensityOp Signal) :
    componentAliceBobMarginal σ = σ := rfl

/-- The "good σ" set for PE parameters `Q, δ`:
the set of de Finetti components whose **per-component** single-round marginal
`componentAliceBobMarginal σ` (Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024, Lemma 9 Eq.44 — the
component's own Alice–Bob marginal against which the per-round Born statistic `Tr(Γⱼ σ)` is
measured) has bit-flip and phase-flip error rates both ≤ Q + δ.

The classifier is keyed to the **per-component** marginal, not to any attack-averaged
first-round marginal: a covariant mixture (apply `X^{⊗n}` w.p. `f`, identity
otherwise) can carry a bad average while every per-component statistic stays good,
so the average-keyed classifier fails for the clean-majority covariant mixture.
The membership predicate therefore mentions no attack object and no block length. -/
def goodRateSet
    (Q δ : ℝ) :
    Set (DensityOp Signal) :=
  {σ |
    bitFlipErrorRate (componentAliceBobMarginal σ) ≤ Q + δ ∧
    phaseFlipErrorRate (componentAliceBobMarginal σ) ≤ Q + δ}

end QKD.BB84.Model

end -- noncomputable section
