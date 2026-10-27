import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Math.LinearAlgebra.Matrix.ProjectionOrder
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKRMixture
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.DeFinetti.HaarAlgebra
import QCryptLean.Quantum.DeFinetti.Approximation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Dimension
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.PairedAlgebra

/-! # Postselection -/


noncomputable section

namespace Quantum.DeFinetti

open Matrix Quantum.Operators Quantum.Symmetry
open scoped ComplexOrder

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- State postselection with the polynomial upper bound on the CKR factor.
The proof uses native prerequisites. -/
theorem deFinetti_postselection_op_le (n : ℕ) (ρ : DensityOp (Fin n → X))
    (hsupp : symmetricProjector X n * ρ.toOp = ρ.toOp) :
    ∃ μ : DensityMeasure X,
      (((n + 1 : ℝ) ^ (Fintype.card X ^ 2 - 1) : ℂ) •
        integralTensorPower n μ - ρ.toOp).PosSemidef := by
  let x : X := Classical.choice ‹Nonempty X›
  refine ⟨haarDensityMeasure x, ?_⟩
  let P := symmetricProjector X n
  have hP : P.PosSemidef := symmetricProjector_posSemidef
  have hτ : integralTensorPower n (haarDensityMeasure x) = P.trace⁻¹ • P := by
    rw [← deFinettiState_eq_haar_integral x n]
    rfl
  rw [hτ, smul_smul]
  let g : ℝ := (n + 1 : ℝ) ^ (Fintype.card X ^ 2 - 1)
  have ht : P.trace = (P.trace.re : ℂ) := by
    apply Complex.ext <;> simp [(Complex.nonneg_iff.mp hP.trace_nonneg).2.symm]
  have hp : 0 < P.trace.re := by
    have hn := (Complex.nonneg_iff.mp hP.trace_nonneg).1
    refine lt_of_le_of_ne hn ?_
    intro hz
    apply Quantum.Symmetry.symmetricProjector_trace_ne_zero (X := X) (k := n)
    rw [ht, ← hz, Complex.ofReal_zero]
  have hbound : P.trace.re ≤ g := by
    rw [show P = symmetricProjector X n from rfl, symmetricSubspace_dim]
    have hc := Nat.choose_add_le_add_one_pow n (Fintype.card X - 1)
    have hn : n + (Fintype.card X - 1) = n + Fintype.card X - 1 := by
      have := Fintype.card_pos (α := X)
      omega
    rw [hn] at hc
    calc
      (Nat.choose (n + Fintype.card X - 1) (Fintype.card X - 1) : ℝ)
          ≤ (n + 1 : ℝ) ^ (Fintype.card X - 1) := by exact_mod_cast hc
      _ ≤ g := by
        apply pow_le_pow_right₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))
        have := Nat.le_self_pow (by norm_num : 2 ≠ 0) (Fintype.card X)
        omega
  have hfirst : (((g : ℂ) * P.trace⁻¹ - 1) • P).PosSemidef := by
    apply hP.smul
    rw [ht, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.zero_le_real, sub_nonneg]
    simpa only [div_eq_mul_inv] using (le_div_iff₀ hp).mpr (by simpa using hbound)
  have hsecond : (P - ρ.toOp).PosSemidef := Matrix.le_iff.mp
    (ρ.posSemidef.le_projection_of_trace_le_one (by simp [ρ.trace_one])
      hP.isHermitian symmetricProjector_mul_self hsupp)
  have he : ((g : ℂ) * P.trace⁻¹) • P - ρ.toOp =
      (((g : ℂ) * P.trace⁻¹ - 1) • P) + (P - ρ.toOp) := by
    rw [sub_smul, one_smul]
    abel
  rw [← Complex.ofReal_pow]
  change (((g : ℂ) * P.trace⁻¹) • P - ρ.toOp).PosSemidef
  rw [he]
  exact hfirst.add hsecond

omit [DecidableEq X] [Nonempty X] in
/-- Positive tests preserve an operator domination bound under the real trace pairing. -/
theorem deFinetti_postselection_traceMul_le (n : ℕ) (ρ : DensityOp (Fin n → X))
    (μ : DensityMeasure X) (g : ℝ)
    (hbound : ((g : ℂ) • integralTensorPower n μ - ρ.toOp).PosSemidef)
    (M : Op (Fin n → X)) (hM : M.PosSemidef) :
    (M * ρ.toOp).trace.re ≤ g * (M * integralTensorPower n μ).trace.re := by
  have h := (Complex.nonneg_iff.mp (hM.trace_mul_nonneg hbound)).1
  rw [mul_sub, Matrix.mul_smul, trace_sub, trace_smul] at h
  simp only [smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at h
  linarith

/-- The mixed CKR reference is a mixture of tensor powers of local states.
The same probability measure works for every positive number of sites. -/
theorem exists_measure_integralTensorPower_eq_ckrDeFinettiState :
    ∃ μ : DensityMeasure X, ∀ n : ℕ, [NeZero n] →
      integralTensorPower n μ = (ckrDeFinettiState X n).toOp := by
  exact ⟨ckrMixtureMeasure (Classical.choice ‹Nonempty X›),
    fun n _ => integralTensorPower_ckrMixtureMeasure _ n⟩

end Quantum.DeFinetti
