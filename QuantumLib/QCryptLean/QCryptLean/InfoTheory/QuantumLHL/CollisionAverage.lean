import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundSquaredCollisionAlgebra
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.ScalarTwoUniversalL2
import QCryptLean.Math.LinearAlgebra.Matrix.CollisionAlgebra
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace

/-! # Two-universal collision bounds on finite quantum registers

The hash family and its scalar collision inequalities are reused unchanged.
Only the matrix registers in the collision kernel are generalized.
-/
noncomputable section
namespace InfoTheory.QuantumLHL
open Matrix
open scoped ComplexOrder MatrixOrder
open private seed_collision_sum_eq_filter_pair_sum
  from QCryptLean.InfoTheory.QuantumLHL.LambdaBoundSquaredCollisionAlgebra

/-- The average centered second moment of positive hash fibers is bounded by the input
collision sum. -/
theorem average_trace_centered_hash_sq_le
    {S C Z Q : Type*} [Fintype S] [Fintype C] [Fintype Z] [Fintype Q]
    [DecidableEq Z] (H : HashFamily S C Z) (hH : H.IsTwoUniversal)
    (A : C → Matrix Q Q ℂ) (hA : ∀ c, (A c).PosSemidef) :
    (Fintype.card S : ℝ)⁻¹ * ∑ s, ∑ z,
      (((∑ c, if H.hash s c = z then A c else 0) -
        (Fintype.card Z : ℂ)⁻¹ • ∑ c, A c) *
      ((∑ c, if H.hash s c = z then A c else 0) -
        (Fintype.card Z : ℂ)⁻¹ • ∑ c, A c)).trace.re ≤
    ∑ c, (A c * A c).trace.re := by
  classical
  let := H.seedNonempty
  let := H.outputNonempty
  let K (c d : C) := (A c * A d).trace.re
  let tau (c d : C) : ℝ := (Fintype.card S : ℝ)⁻¹ *
    ((Finset.univ.filter (fun s => H.hash s c = H.hash s d)).card : ℝ)
  have hK (c d : C) : 0 ≤ K c d :=
    (Complex.nonneg_iff.mp ((hA c).trace_mul_nonneg (hA d))).1
  have hpoint (c d : C) : tau c d * K c d ≤
      (if c = d then K c d else 0) + (Fintype.card Z : ℝ)⁻¹ * K c d := by
    by_cases hcd : c = d
    · subst d
      have ht : tau c c = 1 := by
        simp [tau]
      rw [ht, one_mul, ite_eq_left rfl]
      exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hK c c))
    · rw [ite_eq_right hcd, zero_add]
      exact mul_le_mul_of_nonneg_right
        (sub_nonpos.mp (by simpa only [one_div] using
          quantumHash_offdiag_coeff_nonpos H hH hcd)) (hK c d)
  have hsum : (∑ c, ∑ d, tau c d * K c d) ≤
      (∑ c, K c c) + (Fintype.card Z : ℝ)⁻¹ * ∑ c, ∑ d, K c d := by
    have h := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) =>
      Finset.sum_le_sum fun d (_ : d ∈ Finset.univ) => hpoint c d
    simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, ← Finset.mul_sum] using h
  have hm : (∑ c, ∑ d, K c d) = ((∑ c, A c) * (∑ c, A c)).trace.re := by
    simp only [K, Finset.sum_mul, Matrix.mul_sum, trace_sum, Complex.re_sum]
  have hf (s : S) : (∑ z, ∑ c, if H.hash s c = z then A c else 0) = ∑ c, A c := by
    rw [Finset.sum_comm]
    simp
  have hc (s : S) := congrArg Complex.re
    (Matrix.sum_trace_centered_sq (fun z => ∑ c, if H.hash s c = z then A c else 0))
  simp only [hf, Complex.re_sum, Complex.sub_re, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hc
  have he (s : S) := congrArg Complex.re (Matrix.sum_trace_hash_fibers_sq A (H.hash s))
  simp only [Complex.re_sum, apply_ite Complex.re, Complex.zero_re] at he
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast] at hc
  simp_rw [hc, he]
  rw [Finset.sum_sub_distrib, mul_sub, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have hp := seed_collision_sum_eq_filter_pair_sum H K
  simp only [one_div] at hp
  change _ ≤ ∑ c, K c c
  rw [hp]
  rw [hm] at hsum
  exact sub_le_iff_le_add.mpr hsum

end InfoTheory.QuantumLHL
