import QuantumLib.ForMathlib.LinearAlgebra.PartialTrace.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Channels.Amplification
import QuantumLib.ForPhyslib.QuantumInfo.Channels.AncillaBounds
import QuantumLib.ForPhyslib.QuantumInfo.Channels.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Channels.Diamond
import QuantumLib.ForPhyslib.QuantumInfo.Channels.DiamondBounds
import QuantumLib.ForPhyslib.QuantumInfo.Channels.DiamondInequality
import QuantumLib.ForPhyslib.QuantumInfo.Channels.LeftAmplification
import QuantumLib.ForPhyslib.QuantumInfo.Channels.SubstateExtraction
import QuantumLib.ForPhyslib.QuantumInfo.Metrics.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Metrics.Contractivity
import QuantumLib.ForPhyslib.QuantumInfo.Metrics.Inequality
import QuantumLib.ForPhyslib.QuantumInfo.Metrics.TraceNorm
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Operators.BraKet
import QuantumLib.ForPhyslib.QuantumInfo.Operators.RankPurification
import QuantumLib.ForPhyslib.QuantumInfo.Operators.StateOperations

/-! # Ancilla -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Metrics
open scoped ComplexOrder

variable {X Y R S : Type*} [Fintype X] [Fintype Y] [Fintype R] [Fintype S]

/-- A channel contracts trace norm with any finite reference. -/
theorem traceNorm_mapTensorId_le
    (Φ : Operation X Y) (hΦ : IsChannel Φ) (A : Op (X × R)) :
    traceNorm (mapTensorId Φ R A) ≤ traceNorm A :=
  traceNorm_apply_le _ hΦ.mapTensorId A

/-- Input-sized references suffice for every trace-norm unit-ball input when the map
preserves adjoints. This is the native Kitaev--Watrous stability bound. -/
theorem traceNorm_mapTensorId_le_diamondNorm_of_map_conjTranspose
    (Δ : Operation X Y) (hstar : ∀ A, Δ Aᴴ = (Δ A)ᴴ)
    (A : Op (X × R)) (hA : traceNorm A ≤ 1) :
    traceNorm (mapTensorId Δ R A) ≤ diamondNorm Δ := by
  exact (traceNorm_mapTensorId_le_mul_of_map_conjTranspose Δ (diamondNorm Δ) hstar
    (fun P hP ht => traceNorm_mapTensorId_le_diamondNorm Δ P
      (by rwa [traceNorm_of_posSemidef P hP])) A).trans
        (mul_le_of_le_one_right (diamondNorm_nonneg Δ) hA)

/-- A dominated marginal bounds the output norm by that of any pure dominating extension.
The proof uses native prerequisites. -/
theorem traceNorm_mapTensorId_substate_bound
    (Δ : Operation X Y) (A : Op (X × R)) (hA : A.PosSemidef)
    (ψ : DensityOp (X × S)) (hψ : ψ.IsPure) (a : ℝ) (ha : 0 < a)
    (hdom : ((a : ℂ) • ψ.partialTraceRight.toOp - Matrix.partialTraceRight A).PosSemidef) :
    traceNorm (mapTensorId Δ R A) ≤ a * traceNorm (mapTensorId Δ S ψ.toOp) := by
  obtain ⟨v, hv⟩ := DensityOp.IsPure.exists_normKet ψ hψ
  let w : Ket (X × S) := ⟨fun p => (Real.sqrt a : ℂ) * v.vec p⟩
  have hw : w.projector = (a : ℂ) • ψ.toOp := by
    rw [← hv]
    ext p q
    change (Real.sqrt a : ℂ) * v.vec p * star ((Real.sqrt a : ℂ) * v.vec q) =
      (a : ℂ) * (v.vec p * star (v.vec q))
    have hs : (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = (a : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt ha.le
    have hstar : star (Real.sqrt a : ℂ) = (Real.sqrt a : ℂ) := by simp
    rw [star_mul, hstar]
    calc
      _ = ((Real.sqrt a : ℂ) * (Real.sqrt a : ℂ)) *
          (v.vec p * star (v.vec q)) := by ring
      _ = _ := by rw [hs]
  obtain ⟨Ψ, hΨ, ht, he⟩ := exists_reference_subchannel_of_partialTraceRight_le A hA w (by
    rw [hw, Matrix.partialTraceRight_smul]
    exact hdom)
  rw [he, hw, map_smul, map_smul, mapTensorId_mapIdTensor, traceNorm_smul]
  rw [Complex.norm_real, Real.norm_of_nonneg ha.le]
  exact mul_le_mul_of_nonneg_left
    (traceNorm_apply_le_of_isCompletelyPositive_of_trace_le _ hΨ.mapIdTensor
      (trace_mapIdTensor_le Ψ ht) _) ha.le

end Quantum.Channels
