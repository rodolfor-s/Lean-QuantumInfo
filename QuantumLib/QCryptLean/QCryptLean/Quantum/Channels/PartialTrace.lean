import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus

/-! # Partial Trace -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators

variable {X R : Type*} [Fintype X] [Fintype R]

/-- Right partial trace is a channel, certified by the coordinate-extraction Kraus family. -/
theorem isChannel_partialTraceRight :
    IsChannel (partialTraceRightLinearMap (S := ℂ) : Operation (X × R) X) := by
  classical
  let K : R → Matrix X (X × R) ℂ := fun r x p => if x = p.1 ∧ r = p.2 then 1 else 0
  have he : krausMap K = (partialTraceRightLinearMap (S := ℂ) : Operation (X × R) X) := by
    ext A x y
    simp only [krausMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
    change (∑ r : R, ∑ p : X × R, (∑ q : X × R, K r x q * A q p) *
      star (K r y p)) = ∑ z : R, A (x, z) (y, z)
    simp [K, Fintype.sum_prod_type, ite_and, apply_ite]
  refine ⟨?_, fun A => trace_partialTraceRight A⟩
  rw [← he]
  exact isCompletelyPositive_krausMap K

/-- Left partial trace is a channel with Kraus operators indexed by the left register. -/
theorem isChannel_partialTraceLeft :
    IsChannel (partialTraceLeftLinearMap (S := ℂ) : Operation (R × X) X) := by
  classical
  let K : R → Matrix X (R × X) ℂ := fun r x p => if r = p.1 ∧ x = p.2 then 1 else 0
  have he : krausMap K = (partialTraceLeftLinearMap (S := ℂ) : Operation (R × X) X) := by
    ext A x y
    simp only [krausMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
    change (∑ r : R, ∑ p : R × X, (∑ q : R × X, K r x q * A q p) *
      star (K r y p)) = ∑ z : R, A (z, x) (z, y)
    simp [K, Fintype.sum_prod_type, ite_and, apply_ite]
  refine ⟨?_, fun A => trace_partialTraceLeft A⟩
  rw [← he]
  exact isCompletelyPositive_krausMap K

end Quantum.Channels
