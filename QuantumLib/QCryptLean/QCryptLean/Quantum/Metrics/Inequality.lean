import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Stinespring
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Contractivity
import QCryptLean.Quantum.Metrics.FidelityMonotone
import QCryptLean.Quantum.Metrics.Isometry
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Trace norm and fidelity inequalities -/


noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators Quantum.Channels
open scoped ComplexOrder

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Trace norm contracts on all operators under a channel. -/
theorem traceNorm_apply_le (Φ : Operation X Y) (h : IsChannel Φ) (A : Op X) :
    traceNorm (Φ A) ≤ traceNorm A := by
  exact traceNorm_apply_le_of_isCompletelyPositive_of_trace_le Φ h.1
    (fun B _ => le_of_eq (congrArg Complex.re (h.2 B))) A

/-- Trace-distance data processing, including its factor one half. -/
theorem traceDistance_apply_le (Φ : Operation X Y) (h : IsChannel Φ)
    (A B : Op X) : traceDistance (Φ A) (Φ B) ≤ traceDistance A B := by
  unfold traceDistance
  rw [← map_sub]
  exact mul_le_mul_of_nonneg_left (traceNorm_apply_le Φ h (A - B)) (by norm_num)

/-- Uhlmann fidelity increases under a channel, with explicitly specified positive images. -/
theorem fidelity_le_apply [Nonempty Y] (Φ : Operation X Y) (h : IsChannel Φ)
    (A B : PosSemidefOp X) (C D : PosSemidefOp Y)
    (hC : C.val = Φ A.val) (hD : D.val = Φ B.val) : fidelity A B ≤ fidelity C D := by
  classical
  obtain ⟨V⟩ := h.exists_stinespring
  let A' : PosSemidefOp (Y × (X × Y)) :=
    ⟨V.isometry * A.val * V.isometryᴴ, A.property.mul_mul_conjTranspose_same _⟩
  let B' : PosSemidefOp (Y × (X × Y)) :=
    ⟨V.isometry * B.val * V.isometryᴴ, B.property.mul_mul_conjTranspose_same _⟩
  rw [← fidelity_isometry_conj_of_toOp_eq V.isometry A B A' B' V.isometry_adj_mul rfl rfl]
  have hA' : A'.partialTraceRight = C := Subtype.ext (hC.trans (V.recovers A.val)).symm
  have hB' : B'.partialTraceRight = D := Subtype.ext (hD.trans (V.recovers B.val)).symm
  simpa only [hA', hB'] using fidelity_le_partialTraceRight A' B'

/-- Lower Fuchs--van de Graaf inequality for density operators. -/
theorem one_sub_fidelity_le_traceDistance (ρ σ : DensityOp X) :
    1 - fidelity ρ.toPosSemidefOp σ.toPosSemidefOp ≤ traceDistance ρ.toOp σ.toOp := by
  let : Nonempty X := ρ.nonempty
  have h := one_sub_fidelityGen_le_traceDistanceGen ρ.toSubDensityOp σ.toSubDensityOp
  simpa only [SubDensityOp.toPosSemidefOp, DensityOp.toPosSemidefOp,
    fidelityGen, SubDensityOp.trace, DensityOp.toSubDensityOp,
    DensityOp.trace_one, Complex.one_re, sub_self, zero_mul, Real.sqrt_zero,
    add_zero, traceDistanceGen, Complex.zero_re, abs_zero, mul_zero] using h

/-- Upper Fuchs--van de Graaf inequality for density operators. -/
theorem traceDistance_le_sqrt_one_sub_fidelitySq (ρ σ : DensityOp X) :
    traceDistance ρ.toOp σ.toOp ≤ Real.sqrt (1 - fidelitySq ρ.toPosSemidefOp σ.toPosSemidefOp) := by
  let : Nonempty X := ρ.nonempty
  have h := traceDistanceGen_le_purifiedDistance ρ.toSubDensityOp σ.toSubDensityOp
  simpa only [SubDensityOp.toPosSemidefOp, DensityOp.toPosSemidefOp,
    purifiedDistance, fidelityGen, SubDensityOp.trace, DensityOp.toSubDensityOp,
    DensityOp.trace_one, Complex.one_re, sub_self, zero_mul, Real.sqrt_zero,
    add_zero, traceDistanceGen, Complex.zero_re, abs_zero, mul_zero, fidelitySq] using h

end Quantum.Metrics
