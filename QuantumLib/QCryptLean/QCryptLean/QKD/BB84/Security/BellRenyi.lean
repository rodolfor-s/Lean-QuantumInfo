import QCryptLean.InfoTheory.Security.FiniteKey
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.BellRenyi
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellHaarMixture
import QCryptLean.QKD.BB84.FiniteKey.KeyRate.BellRenyi
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhaseTail
import QCryptLean.QKD.BB84.Model
import QCryptLean.QKD.BB84.Parameters
import QCryptLean.QKD.BB84.RealIdeal
import QCryptLean.QKD.BB84.Reduction
import QCryptLean.QKD.BB84.Reduction.PackedSelector
import QCryptLean.QKD.Protocol
import QCryptLean.Quantum.Channels.DiamondAlgebra

/-!
# Bell–Rényi security of the physical memory-free BB84 program

The main result is a normalized diamond bound on the distance between the *configured* physical
experiment's real map and its derived ideal key resource, at the selector-generic Bell
symmetric-subspace,
Corollary IV.2 Rényi, phase-error finite-key budget.  This theorem carries one extra premise on the
error-correction scheme, `ECScheme.IsTranslationEquivariant`, which is exactly what the Bell
`C(n + 3, 3)` postselection lift requires.

## Security reduction

physical program → analytical model → finite-key budget, as in the AEP theorem:

1. `Parameters.realIdealDistance_le_modelDistance` (`QCryptLean.QKD.BB84.Reduction`): the
   physical experiment's real/ideal distance is at most that of its analytical model
   (`QCryptLean.QKD.BB84.Model`).  The reduction is shared with the AEP theorem and uses
   no property of `ec`.
2. `Parameters.modelDistance_le_bellRenyiBudget` (below): the model is within `bellRenyiBudget`.
   This is the finite-key bound
   `half_mul_diamondNorm_sub_le_bellRenyiBudget` at
   the configuration, with `packedPESel_keyCount` as its selector premise.
   The equivariance premise enters here
   only, through the Bell-twirl invariance of the model.

The security conditions are `BellRenyiConditions`: the key-rate condition is
`BellRenyiKeyRate` (free `ε_PA` funded by `privacyAmplificationCost ε_PA = 2·log₂(1/ε_PA) − 2` bits,
  free Rényi
offset
`β ∈ (0, 1)`) and the budget is `bellRenyiBudget epsilonAEP εPA dev`, with
`modelDistance_le_bellRenyiBudget`, `realIdealDistance_le_bellRenyiBudget` and
`isSecure_of_bellRenyiConditions` as its security statements. The exponential choice of
privacy-amplification error is
  obtained at `εPA = exp(−sifted·δ²/2)` and `β = clampedRenyiOffset …`
whenever the window is nonnegative and the clamped offset is admissible. Larger smoothing
budgets use the channel bound; negative windows always reject.

The Bell–Rényi theorem also separates the two roles of `δ`: the **window** of the accept test,
`|observed X-error rate − Q| ≤ δ`, is fixed by the protocol and its completeness requirement, while
the **deviation** `dev` between the window edge `Q + δ` and the phase-error rate the entropy floor
is charged at is fixed by soundness (how small the accept tail must be). In `BellRenyiConditions`
the deviation is a free parameter `dev ≥ 0`: the entropy floor, the accept tail
`exp(−m_X·klBer (Q+δ) (Q+δ+dev))` and the key-rate condition are charged at `Q + δ + dev`, and the
window `δ` stays the protocol's (Nahar et al., arXiv:2403.11851, Lemma 9 Eq. 44 with §V.C).
The entropy edge must be at most `1/2`. No upper bound on the positive smoothing or PA errors
and no lower bound on the key or X-test count is required. Zero deviation or an empty sifted
block gives tail one, so the channel-distance bound applies. `dev = δ` gives
`FiniteKey.windowPhaseTail` .

The finite-key theorem is grounded in Nahar et al., arXiv:2403.11851, Theorem 3, Appendix B and
Section V.C, Dupuis--Fawzi, arXiv:1805.11652, Corollary IV.2, and Christandl--Koenig--Renner,
arXiv:0809.3019, Theorem 1 and Lemma 1.

Neither security theorem implies the other: the two budgets are attached to two different key-rate
conditions, and this one additionally constrains `ec`.
-/

noncomputable section

namespace QKD.BB84
open QKD.BB84.Reduction

open QKD.BB84.FiniteKey
open QKD.BB84.Model

namespace Parameters

variable (p : Parameters)

/-- **Bell–Rényi security conditions with free PA error, offset and deviation.**

The privacy-amplification error and Rényi offset are free parameters: the key-rate
condition is `BellRenyiKeyRate`, which charges the Dupuis--Fawzi, arXiv:1805.11652,
Corollary IV.2 Rényi penalty at an arbitrary admissible offset `β ∈ (0, 1)` instead of the
clamped optimiser `clampedRenyiOffset`, and funds a free privacy-amplification error `ε_PA` with
`privacyAmplificationCost ε_PA = 2·log₂(1/ε_PA) − 2` bits (Nahar et al., arXiv:2403.11851,
  `eq:condLHL`) rather than requiring
`exp(−sifted·δ²/2)`.  The budget contains neither `β` nor the Cor IV.2 penalty, which reach the
security statement only through the key-rate condition together with `beta_pos`/`beta_lt_one`; the
free `ε_PA` also appears in the budget itself as the leftover-hash slot of
`bellRenyiBudget epsilonAEP εPA dev`, with positivity carried by `epsPA_pos`.
The calculation uses the channel-distance bound of one when the actual accept tail `E ≥ 1/8`.
For `E < 1/8`, the entropy proof applies at every positive smoothing radius and every
`ε_PA > 0`. The key-rate condition discharges the single hashing-cap obligation.
An empty sifted block has tail one.

The phase-error **deviation** `dev` is free as well, separating it from the accept-test **window**
`δ = p.tolerance` (Nahar et al., arXiv:2403.11851, Lemma 9 Eq. 44 with §V.C): the window is fixed
by the protocol and its completeness requirement, while the deviation — the gap between the window
edge `Q + δ` and the phase-error rate the entropy floor is charged at — is fixed by soundness, i.e.
by how small the accept tail must be.  The key-rate condition, the entropy floor and the accept
tail are charged at the soundness edge `Q + δ + dev` (`BellRenyiKeyRate`,
`soundnessEdge_le_half` requires this edge to be at most `1/2`, where binary entropy is increasing).
The window `δ` stays the protocol's: it fixes the accept masses and the integrands throughout
the chain. The deviation is nonnegative; at `dev = 0` the tail is one and the budget covers any
channel distance. Positivity of the centre and window is not needed. `dev = δ` gives
`FiniteKey.windowPhaseTail` for nonnegative windows; negative windows always reject. -/
structure BellRenyiConditions (epsilonAEP εPA β dev : ℝ) : Prop where
  /-- The smoothing parameter is positive. -/
  smoothing_pos : 0 < epsilonAEP
  /-- The Bell–Rényi key-rate condition at the free `ε_PA`, free `β` and
  the soundness edge `Q + δ + dev`. -/
  keyRate : BellRenyiKeyRate p.sifted p.tests p.keyLength
    p.tagLength p.leak p.errorRate p.tolerance dev epsilonAEP εPA β
  /-- The error-correction scheme is translation equivariant. -/
  ecTranslationEquivariant : p.ec.IsTranslationEquivariant
  /-- The privacy-amplification error is positive. -/
  epsPA_pos : 0 < εPA
  /-- The Rényi offset is positive. -/
  beta_pos : 0 < β
  /-- The Rényi offset is less than `1`, so Dupuis–Fawzi Corollary IV.2 applies at `1 + β`. -/
  beta_lt_one : β < 1
  /-- The phase-error deviation is nonnegative. -/
  dev_nonneg : 0 ≤ dev
  /-- The soundness edge lies in the increasing domain of binary entropy. -/
  soundnessEdge_le_half : p.errorRate + p.tolerance + dev ≤ 1 / 2

/-- **The Bell postselection budget with a free privacy-amplification error and a free phase-error
deviation.**

The direct verification charge plus the `C(n + 3, 3)` Bell-symmetric lift of secrecy at the
realised X-subsample deviation-scoped KL accept tail
`phaseTail peSel xSel Q δ dev = exp(−m_X·klBer (Q+δ) (Q+δ+dev))`.
Its budget is `2^(−ℓEV) + C(n+3,3)·(ε_PA + 2·ε_AEP + 2·√(2·E))`.
This is a **normalized** diamond-distance budget;
it does not contain `β`, which reaches the security statement only through the key-rate condition
of `BellRenyiConditions`. The window `δ`
stays the protocol's; the tail and the entropy floor are charged at the soundness edge
`Q + δ + dev` (Nahar et al., arXiv:2403.11851, Lemma 9 Eq. 44 with §V.C). -/
def bellRenyiBudget (epsilonAEP εPA dev : ℝ) : ℝ :=
  QKD.BB84.FiniteKey.bellRenyiBudget
    (phaseTail p.peSel p.xSel p.errorRate p.tolerance dev)
    p.sifted p.tagLength epsilonAEP εPA

/-- **The analytical model of the configured experiment is within the Bell postselection budget,
with the freedoms free.**

This is the finite-key bound
`half_mul_diamondNorm_sub_le_bellRenyiBudget` read
at the configuration, with the free privacy-amplification error `ε_PA` (funded by
`privacyAmplificationCost ε_PA = 2·log₂(1/ε_PA) − 2` bits, Nahar et al. `eq:condLHL`), the
  Dupuis--Fawzi, arXiv:1805.11652,
Corollary IV.2 penalty charged at the free offset `β ∈ (0, 1)`, and the free phase-error
deviation `dev`: the window `δ` of the accept test stays the protocol's, while the entropy floor,
the accept tail and the key-rate condition are charged at the soundness edge `Q + δ + dev`
(Nahar et al., Lemma 9 Eq. 44 with §V.C).  The theorem's
selector premise holds by `packedPESel_keyCount`. The key-rate condition funds the single
hashing-cap obligation using `ε_PA > 0`, with no upper bound on `ε_PA`. Every other premise is
a field of `BellRenyiConditions`. -/
theorem modelDistance_le_bellRenyiBudget [NeZero p.sifted] {epsilonAEP εPA β dev : ℝ}
    (h : p.BellRenyiConditions epsilonAEP εPA β dev) :
    p.modelDistance ≤ p.bellRenyiBudget epsilonAEP εPA dev :=
  half_mul_diamondNorm_sub_le_bellRenyiBudget
    p.peSel p.xSel (packedPESel_keyCount p.keyRounds p.zTests p.xTests) p.ec
    h.ecTranslationEquivariant p.errorRate p.tolerance dev epsilonAEP εPA β
    h.dev_nonneg h.soundnessEdge_le_half h.keyRate h.smoothing_pos
    h.epsPA_pos h.beta_pos h.beta_lt_one

/-- An empty sifted block has tail one, so its Bell budget covers any channel distance. -/
private lemma one_le_bellRenyiBudget_of_sifted_eq_zero {epsilonAEP εPA dev : ℝ}
    (hn : p.sifted = 0) (hAEP : 0 ≤ epsilonAEP) (hPA : 0 ≤ εPA) :
    1 ≤ p.bellRenyiBudget epsilonAEP εPA dev := by
  have hx : p.xTests = 0 := by simp only [Parameters.sifted] at hn; omega
  have hs : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  simp only [bellRenyiBudget,
    InfoTheory.Security.verificationError,
    Math.Combinatorics.deFinettiPrefactor_four,
    QKD.BB84.FiniteKey.bellRenyiBudget,
    bellRenyiSecrecyBudget,
    InfoTheory.Security.smoothingError,
    InfoTheory.Security.acceptanceError]
  simp only [phaseTail, Reduction.siftedXTestSampleSize_packed, hx, hn,
    Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero]
  norm_num only [Nat.reduceAdd, Nat.choose_self, Nat.cast_one, one_mul, mul_one]
  have hc : 0 ≤ (2 : ℝ) ^ (-(p.tagLength : ℝ)) := by positivity
  linarith

/-- **The configured measure-first BB84 experiment is within the Bell postselection budget of its
ideal key resource, in normalized diamond distance, with the freedoms free.**

The bound is on the derived real and ideal maps of the actual executable
protocol; the free `ε_PA` (Nahar et al. `eq:condLHL`), free Rényi offset `β` (Dupuis--Fawzi
Corollary IV.2) and free phase-error deviation (window/deviation split, Nahar et al. Lemma 9
Eq. 44 with §V.C) enter only through `BellRenyiConditions`'s key-rate condition and admissibility
fields. -/
theorem realIdealDistance_le_bellRenyiBudget {epsilonAEP εPA β dev : ℝ}
    (h : p.BellRenyiConditions epsilonAEP εPA β dev) :
    p.protocol.realIdealDistance ≤ p.bellRenyiBudget epsilonAEP εPA dev := by
  by_cases hn : p.sifted = 0
  · have hone : p.protocol.realIdealDistance ≤ 1 :=
      p.protocol.isChannel_real.diamondDist_le_one p.protocol.isChannel_ideal
    exact hone.trans (p.one_le_bellRenyiBudget_of_sifted_eq_zero hn
      h.smoothing_pos.le h.epsPA_pos.le)
  · have : NeZero p.sifted := ⟨hn⟩
    exact p.realIdealDistance_le_modelDistance.trans (p.modelDistance_le_bellRenyiBudget h)

/-- The configured experiment is fully interface-secure at the free-`ε_PA`, free-`β`, free-`dev`
Bell postselection budget.

This is the diamond bound above together with the accepted-key classicality of the real output
(`acceptedKeyClassical_protocol`), i.e. the complete full-interface criterion. -/
theorem isSecure_of_bellRenyiConditions {epsilonAEP εPA β dev : ℝ}
    (h : p.BellRenyiConditions epsilonAEP εPA β dev) :
    p.protocol.IsSecure (p.bellRenyiBudget epsilonAEP εPA dev) :=
  p.isSecure_of_realIdealDistance_le (p.realIdealDistance_le_bellRenyiBudget h)

end Parameters

end QKD.BB84
