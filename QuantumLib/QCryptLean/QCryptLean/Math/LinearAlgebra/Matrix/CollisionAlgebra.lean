import QCryptLean.Math.SpectralTheory.Matrix

/-! # Finite collision and centering identities for matrix families -/
noncomputable section
namespace Matrix
variable {X C Z : Type*} [Fintype X] [Fintype C] [Fintype Z]

/-- Centering a finite matrix family subtracts the square of its mean from its second moment. -/
theorem sum_trace_centered_sq [Nonempty Z] (A : Z → Matrix X X ℂ) :
    ∑ z, ((A z - ((Fintype.card Z : ℂ)⁻¹) • ∑ w, A w) *
      (A z - ((Fintype.card Z : ℂ)⁻¹) • ∑ w, A w)).trace =
    (∑ z, (A z * A z).trace) - (Fintype.card Z : ℂ)⁻¹ *
      ((∑ z, A z) * (∑ z, A z)).trace := by
  let c : ℂ := (Fintype.card Z : ℂ)⁻¹
  let R := ∑ z, A z
  have he (z : Z) : ((A z - c • R) * (A z - c • R)).trace =
      (A z * A z).trace - c * (A z * R).trace - c * (R * A z).trace +
      c * c * (R * R).trace := by
    simp only [mul_sub, sub_mul, trace_sub, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      trace_smul, smul_eq_mul]
    ring
  change ∑ z, ((A z - c • R) * (A z - c • R)).trace = _
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hL : ∑ z, (A z * R).trace = (R * R).trace := by
    rw [← trace_sum, ← Finset.sum_mul]
  have hR : ∑ z, (R * A z).trace = (R * R).trace := by
    rw [← trace_sum, ← Matrix.mul_sum]
  rw [hL, hR, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hz : (Fintype.card Z : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change _ = (∑ z, (A z * A z).trace) - c * (R * R).trace
  dsimp [c]
  field_simp
  ring

/-- Squaring each hash fiber retains exactly the pairs with equal hash values. -/
theorem sum_trace_hash_fibers_sq [DecidableEq Z]
    (A : C → Matrix X X ℂ) (h : C → Z) :
    ∑ z, ((∑ c, if h c = z then A c else 0) *
      (∑ c, if h c = z then A c else 0)).trace =
    ∑ c, ∑ d, if h c = h d then (A c * A d).trace else 0 := by
  have he (z : Z) : ((∑ c, if h c = z then A c else 0) *
      (∑ c, if h c = z then A c else 0)).trace =
      ∑ c, ∑ d, if h c = z ∧ h d = z then (A c * A d).trace else 0 := by
    simp only [Finset.sum_mul, Matrix.mul_sum, trace_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases hc : h c = z <;> by_cases hd : h d = z <;> simp [hc, hd]
  simp_rw [he]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp_rw [ite_and]
  simp [eq_comm]

end Matrix
