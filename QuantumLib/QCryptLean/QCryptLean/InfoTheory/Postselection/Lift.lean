import Mathlib.Analysis.SpecialFunctions.Log.Base
import QCryptLean.InfoTheory.Security.FiniteKey

/-! # Lift -/


-- Frobenius normed structure on matrices, needed to integrate operator-valued functions
-- (same local instances as `Quantum.DeFinetti.IntegralPurification`).

noncomputable section

open scoped BigOperators

namespace InfoTheory.Postselection

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]


/-- **Nahar et al. Theorem 3 / Corollary 3.1 secrecy parameter** `ε_PA + 2ε̄ + 2√(2ε_AT)`
    (arXiv:2403.11851, main.tex:487–:490 (unlabeled; the conclusion of `\label{thm:maintheorem}`
    :481–:491) / line 568). -/
def coherentIIDSecrecy (εAT εPA εbar : ℝ) : ℝ :=
  εPA + InfoTheory.Security.smoothingError εbar + InfoTheory.Security.acceptanceError εAT

end InfoTheory.Postselection

end
