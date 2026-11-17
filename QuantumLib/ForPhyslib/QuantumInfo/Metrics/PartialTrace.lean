import QuantumLib.ForMathlib.LinearAlgebra.PartialTrace.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Channels.PartialTrace
import QuantumLib.ForPhyslib.QuantumInfo.Metrics.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Metrics.Inequality
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic

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
