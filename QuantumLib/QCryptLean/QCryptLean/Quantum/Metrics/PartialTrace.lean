import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.PartialTrace
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Inequality
import QCryptLean.Quantum.Operators.Basic

/-! # Partial Trace -/


noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators Quantum.Channels

variable {X R : Type*} [Fintype X] [Fintype R]

/-- Partial trace contracts trace distance on all matrices. -/
theorem traceDistance_partialTraceRight_le (A B : Op (X × R)) :
    traceDistance (partialTraceRight A) (partialTraceRight B) ≤ traceDistance A B :=
  traceDistance_apply_le partialTraceRightLinearMap isChannel_partialTraceRight A B

end Quantum.Metrics
