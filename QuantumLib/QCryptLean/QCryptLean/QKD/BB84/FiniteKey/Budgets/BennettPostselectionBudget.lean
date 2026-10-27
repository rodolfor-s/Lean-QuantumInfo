import Mathlib.Analysis.Real.Sqrt
import QCryptLean.InfoTheory.Security.FiniteKey
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.QKD.BB84.Constants
import QCryptLean.QKD.BB84.SelectionData

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The Bennett BB84 secrecy budget

The agree-block budget is `PA + 2 ε_AEP + 2 √(2E)`, with
`PA = ½ exp(-(n - m)/4 * (log 2 - h(Q + 2δ)))`. The verification failure probability is charged
separately at the channel level. The verification tag's entropy leakage stays in the key rate.

Reference: Nahar et al. 2024, arXiv:2403.11851, `eq:condLHL`, `eq:condsecrecy`, Appendix B.
-/

open Math.ClassicalEntropy

noncomputable section

namespace QKD.BB84.FiniteKey

/-- Privacy-amplification error funded by the AEP key-rate condition.
Half the asymptotic entropy pays for the key and the other half for this error. -/
noncomputable def aepPrivacyAmplificationError (n m : ℕ) (Q δ : ℝ) : ℝ :=
  (1 / 2) * Real.exp (-(keyRounds n m : ℝ) / 4 *
    (Real.log 2 - binaryEntropy (Q + 2 * δ)))

/-- The collective secrecy budget `PA + 2 ε_AEP + 2 √(2E)` at `n - m` key rounds.
The privacy-amplification term is `½ exp(-(n - m)/4 * (log 2 - h(Q + 2δ)))`. -/
noncomputable def aepSecrecyBudget
    (E : ℝ) (n m : ℕ) (Q δ ε_AEP : ℝ) : ℝ :=
  InfoTheory.Security.acceptanceError E + InfoTheory.Security.smoothingError ε_AEP +
    aepPrivacyAmplificationError n m Q δ

/-- The normalized diamond budget: direct correctness `2^(-ℓEV)` plus
`C(n+15,15)` times `aepSecrecyBudget E n m Q δ ε_AEP`.
The postselection factor uses all `n` rounds; the key-dependent terms use `n - m`. -/
noncomputable def aepBudget (E : ℝ) (n m ℓEV : ℕ) (Q δ ε_AEP : ℝ) : ℝ :=
  InfoTheory.Security.verificationError ℓEV +
    (Math.Combinatorics.deFinettiPrefactor (signalDim ^ 2) n : ℝ) *
      aepSecrecyBudget E n m Q δ ε_AEP

end QKD.BB84.FiniteKey

end
