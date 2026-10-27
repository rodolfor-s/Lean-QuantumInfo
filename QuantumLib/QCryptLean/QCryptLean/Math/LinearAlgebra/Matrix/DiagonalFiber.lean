import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace

/-! # Trace bounds for diagonal entries constant on fibers -/
noncomputable section
namespace Matrix
open scoped ComplexOrder

/-- An entry constant on its label fiber is bounded by the inverse fiber size
when the positive matrix has trace at most one. -/
theorem PosSemidef.diag_le_inv_card_fiber {X C : Type*} [Fintype X] [DecidableEq C]
    {M : Matrix X X ℂ} (hM : M.PosSemidef) (ht : M.trace.re ≤ 1)
    (f : X → C) (hf : ∀ i j, f i = f j → M i i = M j j) (i : X) :
    M i i ≤ ((Finset.univ.filter (fun j => f j = f i)).card : ℂ)⁻¹ := by
  let F := Finset.univ.filter (fun j => f j = f i)
  have hi : 0 < F.card := Finset.card_pos.mpr ⟨i, by simp [F]⟩
  have hsum : (F.card : ℝ) * (M i i).re ≤ 1 := by
    calc (F.card : ℝ) * (M i i).re = ∑ j ∈ F, (M j j).re := by
           rw [show (∑ j ∈ F, (M j j).re) = ∑ _j ∈ F, (M i i).re from
             Finset.sum_congr rfl (fun j hj => congrArg Complex.re
               (hf j i (Finset.mem_filter.mp hj).2))]
           simp
         _ ≤ ∑ j, (M j j).re := Finset.sum_le_sum_of_subset_of_nonneg
           (Finset.subset_univ _)
           (fun j _ _ => (Complex.nonneg_iff.mp (hM.diag_nonneg (i := j))).1)
         _ = M.trace.re := (Complex.re_sum _ _).symm
         _ ≤ 1 := ht
  have hb : (M i i).re ≤ (F.card : ℝ)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by exact_mod_cast hi)]
    simpa only [mul_comm] using hsum
  rw [Complex.le_def]
  constructor
  · change (M i i).re ≤ (((F.card : ℝ) : ℂ)⁻¹).re
    rw [← Complex.ofReal_inv, Complex.ofReal_re]
    exact hb
  · have hm := (Complex.nonneg_iff.mp (hM.diag_nonneg (i := i))).2
    simpa only [Complex.inv_im, Complex.natCast_im, neg_zero, zero_div] using hm.symm

end Matrix
