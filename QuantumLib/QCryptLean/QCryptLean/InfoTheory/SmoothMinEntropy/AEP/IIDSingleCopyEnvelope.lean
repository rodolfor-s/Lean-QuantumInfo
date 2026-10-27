import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.RtFunction

/-! # IIDSingle Copy Envelope -/


noncomputable section

open scoped BigOperators

namespace InfoTheory.SmoothMinEntropy


/-- **Per-triple scalar `r_t` bound.** For a live triple with block eigenvalue
`p > 0` and reference eigenvalue `q > 0`, writing `z := q/p > 0` and
`Y := z + z⁻¹ + 2 ∈ [4,∞)`,

  `(p/q)^s ≤ rennerRt(s, Y) − s·ln(q/p) + 1`,

for every tilt `s ≥ 0`. This is the per-letter input to the Jensen aggregation in
`AEP.IID.singleCopyMGF_le_rennerRt_sub_add_one`. -/
theorem div_rpow_le_rennerRt_sub_add_one
    {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : 0 ≤ s) :
    (p / q) ^ s
      ≤ InfoTheory.SmoothMinEntropy.rennerRt s (q / p + p / q + 2) - s * Real.log (q / p) + 1 := by
  have hz : 0 < q / p := div_pos hq hp
  have hzinv : (q / p)⁻¹ = p / q := inv_div q p
  have key : (p / q) ^ s = ((q / p) ^ s)⁻¹ := by
    rw [← hzinv, Real.inv_rpow hz.le]
  have hpq_eq : (p / q) ^ s = InfoTheory.SmoothMinEntropy.rennerRt (-s) (q / p) - s * Real.log (q /
    p) + 1
      := by
    rw [key]; unfold InfoTheory.SmoothMinEntropy.rennerRt; rw [Real.rpow_neg hz.le]; ring
  have hineq1 : InfoTheory.SmoothMinEntropy.rennerRt (-s) (q / p) ≤
    InfoTheory.SmoothMinEntropy.rennerRt |(-s)|
      (q / p + (q / p)⁻¹) :=
    rennerRt_le_rennerRt_abs_add_inv (-s) (q / p) hz
  have habs : |(-s)| = s := by rw [abs_neg, abs_of_nonneg hs]
  rw [habs, hzinv] at hineq1
  -- `z + z⁻¹ ≥ 1` for `z > 0`: one of `z`, `z⁻¹` is at least `1`, the other is positive.
  have hone : (1 : ℝ) ≤ q / p + p / q := by
    rcases le_total 1 (q / p) with h | h
    · exact h.trans (le_add_of_nonneg_right (div_pos hp hq).le)
    · have h' : 1 ≤ p / q := hzinv ▸ (one_le_inv₀ hz).mpr h
      exact h'.trans (le_add_of_nonneg_left hz.le)
  have hmono := monotoneOn_rennerRt_Ici_one s (Set.mem_Ici.mpr hone)
    (Set.mem_Ici.mpr (hone.trans (le_add_of_nonneg_right zero_le_two)))
    (le_add_of_nonneg_right zero_le_two)
  -- `(p/q)^s = rennerRt(-s, z) − s·ln z + 1 ≤ rennerRt(s, z + z⁻¹) − s·ln z + 1 ≤ rennerRt(s, Y) −
  -- s·ln z + 1`.
  linarith only [hpq_eq, hineq1, hmono]


/-- **AM–GM lower bound for the per-triple Jensen argument.** For `p, q > 0`,
`q/p + p/q + 2 ≥ 4`. -/
private lemma four_le_div_add_div_add_two_of_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (4 : ℝ) ≤ q / p + p / q + 2 := by
  have hz : 0 < q / p := div_pos hq hp
  have hmul : (q / p) * (p / q) = 1 := by field_simp
  nlinarith [sq_nonneg (q / p - 1), hmul, hz, div_pos hp hq]

end InfoTheory.SmoothMinEntropy
