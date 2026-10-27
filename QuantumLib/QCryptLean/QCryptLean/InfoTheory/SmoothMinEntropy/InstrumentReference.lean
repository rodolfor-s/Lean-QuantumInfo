import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Instrument
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Native CQ instruments with finite reference registers -/
noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators Quantum.Channels
variable {C X Y R S : Type*} [Fintype C] [Fintype X] [Fintype Y] [Fintype R] [Fintype S]

/-- Apply an accepted instrument while preserving an arbitrary finite reference. -/
def CQState.ofInstrumentWithReference (L : C → Operation X Y)
    (hL : ∀ c, IsCompletelyPositive (L c))
    (hw : ∀ ρ : DensityOp X, ∑ c, (L c ρ.toOp).trace.re ≤ 1)
    (ρ : DensityOp (X × R)) : CQState C (Y × R) :=
  CQState.ofBlocks (fun c => mapTensorId (L c) R ρ.toOp)
    (fun c => ((hL c).mapTensorId (Z := R)).posSemidef ρ.posSemidef)
    (by
      have he (c : C) : (mapTensorId (L c) R ρ.toOp).trace =
          (L c ρ.partialTraceRight.toOp).trace := by
        rw [← trace_partialTraceRight, partialTraceRight_mapTensorId]
        rfl
      simpa only [he] using hw ρ.partialTraceRight)

/-- Tracing out the final reference commutes with the blockwise instrument. -/
theorem CQState.partialTraceRight_ofInstrumentWithReference_assoc
    (L : C → Operation X Y) (hL : ∀ c, IsCompletelyPositive (L c))
    (hw : ∀ ρ : DensityOp X, ∑ c, (L c ρ.toOp).trace.re ≤ 1)
    (ρ : DensityOp ((X × R) × S)) :
    ((CQState.ofInstrumentWithReference L hL hw
      (ρ.reindex (Equiv.prodAssoc X R S))).reindex
        (Equiv.prodAssoc Y R S).symm).partialTraceRight =
      CQState.ofInstrumentWithReference L hL hw ρ.partialTraceRight := by
  apply CQState.ext
  funext c
  apply SubDensityOp.ext
  exact partialTraceRight_mapTensorId_assoc (L c) ρ.toOp

end InfoTheory.SmoothMinEntropy
