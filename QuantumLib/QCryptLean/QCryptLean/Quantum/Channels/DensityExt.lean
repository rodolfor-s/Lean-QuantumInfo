import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic

/-! # Density states determine complex-linear matrix maps -/
noncomputable section
namespace Quantum.Channels
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder

/-- Agreement on density operators determines a complex-linear operator map. -/
theorem linearMap_eq_of_densityOp {X : Type*} [Fintype X]
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F G : Op X →ₗ[ℂ] E) (h : ∀ ρ : DensityOp X, F ρ.toOp = G ρ.toOp) : F = G := by
  classical
  have hpsd (A : Op X) (hA : A.PosSemidef) : F A = G A := by
    by_cases hz : A.trace = 0
    · rw [hA.trace_eq_zero_iff.mp hz, map_zero, map_zero]
    · have hpos : 0 < A.trace.re := by
        have hn := Complex.nonneg_iff.mp hA.trace_nonneg
        refine lt_of_le_of_ne hn.1 ?_
        intro heq
        apply hz
        exact Complex.ext heq.symm hn.2.symm
      have hscaled : ((((A.trace.re)⁻¹ : ℝ) : ℂ) • A).PosSemidef :=
        hA.smul (by exact_mod_cast inv_nonneg.mpr hpos.le)
      let ρ : DensityOp X :=
        { toOp := (((A.trace.re)⁻¹ : ℝ) : ℂ) • A
          posSemidef := hscaled
          trace_one := by
            have hreal : A.trace = (A.trace.re : ℂ) :=
              Complex.ext rfl (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm
            rw [Matrix.trace_smul, smul_eq_mul, hreal, Complex.ofReal_re, ← Complex.ofReal_mul,
              inv_mul_cancel₀ hpos.ne', Complex.ofReal_one] }
      have hn := h ρ
      change F ((((A.trace.re)⁻¹ : ℝ) : ℂ) • A) =
        G ((((A.trace.re)⁻¹ : ℝ) : ℂ) • A) at hn
      rw [map_smul, map_smul] at hn
      exact (smul_right_injective E (by exact_mod_cast inv_ne_zero hpos.ne')) hn
  apply LinearMap.ext_on (span_selfAdjoint (A := Op X))
  intro A hA
  obtain ⟨P, N, hP, hN, hPN, _⟩ :=
    Quantum.Metrics.exists_posSemidef_sub_traceNorm_eq A hA
  rw [hPN, map_sub, map_sub, hpsd P hP, hpsd N hN]


end Quantum.Channels
