import QCryptLean.Math.Concentration.Serfling
import QCryptLean.QKD.BB84.Model.ProtocolPair
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology

/-!
# The per-component single-round Alice–Bob marginal for BB84 parameter estimation

The parameter-estimation classifier of Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024,
arXiv:2403.11851, Lemma 9 Eq. 44) is keyed to the per-IID-component Born statistic `Tr(Γⱼ σ)`,
where `σ` is a de Finetti component's *own* single-round Alice–Bob state and `Γⱼ` is the per-round
PE POVM element — not an attack-averaged marginal.  A covariant mixture can carry a bad average
while every per-component statistic stays good, so the classifier must be keyed to the
per-component marginal.

In the BB84 instantiation a de Finetti component `σ` is already the single-round Alice–Bob signal
state on `DensityOp Signal`, and the per-round PE POVM elements are the Bell-basis bit-flip and
phase-flip projectors, so the component's own marginal under the PE POVM is `σ` itself.

## Main definitions

- `QKD.BB84.Model.componentAliceBobMarginal`, defined in `QKD.BB84.Model.ProtocolPair`, is the
  per-component single-round Alice–Bob marginal classifier (the identity on the component).
  This module proves its continuity and measurability.
- `QKD.BB84.FiniteKey.componentAliceBobMarginal_continuous`,
  `QKD.BB84.FiniteKey.componentAliceBobMarginal_measurable`: continuity and measurability.
- `QKD.BB84.FiniteKey.tensorPow_preChannel_continuous`: feeding a component's tensor power
  through a fixed linear map is continuous in the component.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851), Lemma 9 Eq. 44;
Renner 2005, §6.4.
-/

open Quantum.Operators Matrix Quantum.Channels
open QKD.BB84.Measurement
open QKD.BB84.Model
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ComplexOrder ENNReal

noncomputable section

namespace QKD.BB84.FiniteKey

/-- Feeding the tensor-power operator of a component through a fixed linear map is continuous
in the component.

Indexed by a bare retained-Eve dimension and an opaque pre-channel rather than by an attack
object; continuity is pure finite-dimensional linearity, so no CPTP hypothesis is needed. -/
lemma tensorPow_preChannel_continuous
    {n : ℕ}
    {E : Type*}
    (pre : Operation (Signals n) (Signals n × E)) :
    Continuous (fun σ : DensityOp Signal => pre (σ.tensorPow n).toOp) :=
  pre.continuous_of_finiteDimensional.comp
    (continuous_pi fun i => continuous_pi fun j => DensityOp.continuous_tensorPow_entry n i j)

-- `componentAliceBobMarginal` is defined in `QKD.BB84.Model.ProtocolPair` (imported above): it is
-- the model math `goodRateSet` is stated on, not FiniteKey-specific analysis. Only the
-- continuity/measurability proofs about it stay here.

/-- The per-component single-round marginal classifier is continuous. -/
lemma componentAliceBobMarginal_continuous :
    Continuous (componentAliceBobMarginal) := by
  exact continuous_id

/-- The per-component single-round marginal classifier is measurable. -/
lemma componentAliceBobMarginal_measurable :
    Measurable (componentAliceBobMarginal) := by
  exact measurable_id

open Math.Probability.SamplingConcentration Math.Concentration.Serfling

end QKD.BB84.FiniteKey

end -- noncomputable section
