import QCryptLean.InfoTheory.Security.FiniteKey
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.QKD.BB84.Constants
import QCryptLean.QKD.BB84.FiniteKey.AEP
import QCryptLean.QKD.BB84.FiniteKey.Budgets.BennettPostselectionBudget
import QCryptLean.QKD.BB84.FiniteKey.KeyRate.AEP
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhaseTail
import QCryptLean.QKD.BB84.Model
import QCryptLean.QKD.BB84.Parameters
import QCryptLean.QKD.BB84.RealIdeal
import QCryptLean.QKD.BB84.Reduction
import QCryptLean.QKD.BB84.Reduction.PackedSelector
import QCryptLean.QKD.BB84.Security.AEPRegime
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.Protocol
import QCryptLean.Quantum.Channels.DiamondAlgebra

/-!
# AEP security of the physical memory-free BB84 program

The main result is a normalized diamond bound on the distance between the *configured* physical
experiment's real map and its derived ideal key resource, at the packed-selector AEP
finite-key budget.  The error-correction scheme is arbitrary in this theorem.

## Security reduction

physical program → analytical model → finite-key budget:

1. `Parameters.realIdealDistance_le_modelDistance` (`QCryptLean.QKD.BB84.Reduction`): the
   physical experiment's real/ideal distance is at most that of its analytical model
   `Parameters.modelReal`/`Parameters.modelIdeal` (`QCryptLean.QKD.BB84.Model`), with no
   hypothesis beyond a nonempty sifted block.
2. `Parameters.modelDistance_le_aepBudget` (below): the model is within `aepBudget`.  This is
   the finite-key bound `half_mul_diamondNorm_sub_le_aepBudget` at the configuration,
   whose
   key-count premise follows from `packedPESel_keyCount`. Its KL tail reads the realised X-test
   sample through the configured selectors.

The phase-error analysis follows Nahar et al., arXiv:2403.11851,
Theorem 3, Appendix B and Section V.C, with the reference analysis of Renner,
arXiv:quant-ph/0512258v2, Section 6.5, and the postselection lift of Christandl--Koenig--Renner,
arXiv:0809.3019, Theorem 1 and Lemma 1. The normalized security distance follows
Portmann--Renner and Nahar et al.
-/

noncomputable section

namespace QKD.BB84
open QKD.BB84.Reduction

open QKD.BB84.FiniteKey
open QKD.BB84.Model

namespace Parameters

variable (p : Parameters)

/-- **The conditions of the AEP security theorem.**

The regime `AEPRegime` together with the key-rate condition
`AEPKeyRate`, which prices the final key length, the announced syndrome and
verification tag, the de Finetti prefactor and the smoothing penalty against the key block's
entropy at the tested error rate.

There is **no condition on the error-correction scheme** in this theorem: `ec` is arbitrary.  The
Bell–Rényi theorem's translation-equivariance premise is not required here, and this theorem is not
a
consequence of that one. -/
structure AEPConditions (epsilonAEP : ℝ) : Prop extends AEPRegime p epsilonAEP where
  /-- The AEP key-rate condition at these lengths and this smoothing. -/
  keyRate : AEPKeyRate p.sifted p.tests p.keyLength p.tagLength p.leak
    p.errorRate p.tolerance epsilonAEP

/-- The AEP normalized diamond-distance budget.

Correctness contributes `2^(-tagLength)` directly. Secrecy contributes
`C(sifted+15,15) * (PA + 2 epsilonAEP + 2 √(2E))`, where `E` is the realised-X KL tail
and `PA = ½ exp(-keyRounds/4 * (log 2 - h(errorRate + 2 tolerance)))`.

References: Nahar et al. 2024, arXiv:2403.11851, Appendix B;
Christandl–König–Renner 2009, arXiv:0809.3019, Theorem 1. -/
def aepBudget (epsilonAEP : ℝ) : ℝ :=
  QKD.BB84.FiniteKey.aepBudget
    (windowPhaseTail p.peSel p.xSel p.errorRate p.tolerance)
    p.sifted p.tests p.tagLength p.errorRate p.tolerance epsilonAEP

/-- The configured analytical model satisfies the AEP budget.
The packed selectors give the analysis's key-count identity. Positive smoothing, the soundness
edge at most one half, and the key-rate condition are the fields of `AEPConditions`.
The decoder is arbitrary. -/
theorem modelDistance_le_aepBudget [NeZero p.sifted] {epsilonAEP : ℝ}
    (h : p.AEPConditions epsilonAEP) :
    p.modelDistance ≤ p.aepBudget epsilonAEP :=
  half_mul_diamondNorm_sub_le_aepBudget p.peSel p.xSel
    (packedPESel_keyCount p.keyRounds p.zTests p.xTests) p.ec p.errorRate p.tolerance
    epsilonAEP h.soundnessEdge_le_half h.keyRate h.smoothing_pos

/-- **The configured measure-first BB84 experiment is within the standard finite-key budget of its
ideal key resource, in normalized diamond distance.**

The bound is on the derived real and ideal maps of the actual executable protocol: no phase-bad
estimate, reference state, entropy, trace-norm, diamond-norm or security premise is supplied, the
basis laws and the error-correction scheme are arbitrary, and the statement is total in the
physical batch size — an infeasible quota takes the actual all-shortage branch. -/
theorem realIdealDistance_le_aepBudget {epsilonAEP : ℝ}
    (h : p.AEPConditions epsilonAEP) :
    p.protocol.realIdealDistance ≤ p.aepBudget epsilonAEP := by
  by_cases hn : p.sifted = 0
  · have hone : p.protocol.realIdealDistance ≤ 1 :=
      p.protocol.isChannel_real.diamondDist_le_one p.protocol.isChannel_ideal
    refine hone.trans ?_
    have hx : p.xTests = 0 := by simp only [Parameters.sifted] at hn; omega
    have hs : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    simp only [aepBudget,
    QKD.BB84.FiniteKey.aepBudget,
    aepSecrecyBudget,
    InfoTheory.Security.verificationError,
    Math.Combinatorics.deFinettiPrefactor,
    InfoTheory.Security.acceptanceError,
    InfoTheory.Security.smoothingError,
    QKD.BB84.FiniteKey.aepPrivacyAmplificationError]
    simp only [windowPhaseTail, siftedXTestSampleSize_packed, hx, hn, Nat.cast_zero,
      neg_zero, zero_mul, Real.exp_zero, QKD.BB84.FiniteKey.keyRounds, Nat.zero_sub, zero_div]
    norm_num only [signalDim, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.choose_self,
      Nat.cast_one, one_mul, mul_one]
    have hc : 0 ≤ (2 : ℝ) ^ (-(p.tagLength : ℝ)) := by positivity
    linarith [h.smoothing_pos]
  · have : NeZero p.sifted := ⟨hn⟩
    exact p.realIdealDistance_le_modelDistance.trans (p.modelDistance_le_aepBudget h)

/-- The configured experiment is fully interface-secure at the standard finite-key budget.

This is the diamond bound above together with the accepted-key classicality of the real output
(`acceptedKeyClassical_protocol`), i.e. the complete full-interface criterion. -/
theorem isSecure_of_aepConditions {epsilonAEP : ℝ} (h : p.AEPConditions epsilonAEP) :
    p.protocol.IsSecure (p.aepBudget epsilonAEP) :=
  p.isSecure_of_realIdealDistance_le (p.realIdealDistance_le_aepBudget h)

end Parameters

end QKD.BB84
