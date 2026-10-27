import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.RtFunction

/-! # Error Budget -/


noncomputable section

open scoped BigOperators

namespace InfoTheory.SmoothMinEntropy


/-- Trace-defect budget sufficient for an `ε` purified-distance bound via
`P(ρ, ρ̄) ≤ sqrt (2 · traceDefect)`. -/
def AEP.IID.smoothingTraceBudget (ε : ℝ) : ℝ :=
  ε ^ 2 / 2

end InfoTheory.SmoothMinEntropy

end
