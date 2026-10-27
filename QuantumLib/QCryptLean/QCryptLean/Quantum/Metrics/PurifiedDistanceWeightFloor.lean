import QCryptLean.Math.Probability.Bhattacharyya

/-! # Purified Distance Weight Floor -/


noncomputable section

open scoped BigOperators

/-- Explicit total-weight floor forced by an `ε` purified-distance ball whose center
has total weight `weight`.

For traces `weight` and `weight'`, generalized fidelity is bounded above by the
classical two-point fidelity
`√(weight * weight') + √((1 - weight) * (1 - weight'))`.  Solving the resulting
one-dimensional boundary gives this floor when `ε² < weight`. -/
noncomputable def _root_.Quantum.Metrics.purifiedDistanceWeightFloor (ε weight : ℝ) : ℝ :=
  (Real.sqrt weight * Real.sqrt (1 - ε ^ 2) -
      Real.sqrt (1 - weight) * ε) ^ 2

/-- Scalar inversion for the purified-distance total-weight floor.

For two weights `w,w' ∈ [0,1]`, a Bhattacharyya lower bound at radius `ε`
forces `w'` to lie above the explicit floor. -/
theorem _root_.Quantum.Metrics.purifiedDistanceWeightFloor_le_of_bhattacharyya_lower
    {ε w w' : ℝ}
    (hw : w ∈ Set.Icc (0 : ℝ) 1)
    (hw' : w' ∈ Set.Icc (0 : ℝ) 1)
    (hε_nn : 0 ≤ ε)
    (hε_sq_lt_w : ε ^ 2 < w)
    (hB :
      Real.sqrt (1 - ε ^ 2) ≤
        Real.sqrt (w * w') + Real.sqrt ((1 - w) * (1 - w'))) :
    Quantum.Metrics.purifiedDistanceWeightFloor ε w ≤ w' := by
  unfold Quantum.Metrics.purifiedDistanceWeightFloor
  obtain ⟨hw_nonneg, hw_le_one⟩ := hw
  obtain ⟨hw'_nonneg, hw'_le_one⟩ := hw'
  have hone_sub_w_nonneg : 0 ≤ 1 - w := sub_nonneg.mpr hw_le_one
  have hone_sub_w'_nonneg : 0 ≤ 1 - w' := sub_nonneg.mpr hw'_le_one
  have hε_sq_lt_one : ε ^ 2 < 1 := lt_of_lt_of_le hε_sq_lt_w hw_le_one
  have hone_sub_eps_sq_nonneg : 0 ≤ 1 - ε ^ 2 := by
    linarith
  have hB_coord :
      Real.sqrt (1 - ε ^ 2) ≤
        Real.sqrt w * Real.sqrt w' + Real.sqrt (1 - w) * Real.sqrt (1 - w') := by
    calc
      Real.sqrt (1 - ε ^ 2)
          ≤ Real.sqrt (w * w') + Real.sqrt ((1 - w) * (1 - w')) := hB
      _ = Real.sqrt w * Real.sqrt w' + Real.sqrt (1 - w) * Real.sqrt (1 - w') := by
        rw [Real.sqrt_mul hw_nonneg, Real.sqrt_mul hone_sub_w_nonneg]
  have hab :
      (Real.sqrt w) ^ 2 + (Real.sqrt (1 - w)) ^ 2 = 1 := by
    rw [Real.sq_sqrt hw_nonneg, Real.sq_sqrt hone_sub_w_nonneg]
    ring
  have hcs :
      (Real.sqrt (1 - ε ^ 2)) ^ 2 + ε ^ 2 = 1 := by
    rw [Real.sq_sqrt hone_sub_eps_sq_nonneg]
    ring
  have hxy :
      (Real.sqrt w') ^ 2 + (Real.sqrt (1 - w')) ^ 2 = 1 := by
    rw [Real.sq_sqrt hw'_nonneg, Real.sq_sqrt hone_sub_w'_nonneg]
    ring
  have hε_sq_lt_sqrt_w_sq : ε ^ 2 < (Real.sqrt w) ^ 2 := by
    rwa [Real.sq_sqrt hw_nonneg]
  have hcoord :
      (Real.sqrt w * Real.sqrt (1 - ε ^ 2) -
          Real.sqrt (1 - w) * ε) ^ 2 ≤
        (Real.sqrt w') ^ 2 :=
    Real.bhattacharyya_floor_sq_le_sq_of_coord
      (a := Real.sqrt w)
      (b := Real.sqrt (1 - w))
      (c := Real.sqrt (1 - ε ^ 2))
      (s := ε)
      (x := Real.sqrt w')
      (y := Real.sqrt (1 - w'))
      (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
      hε_nn
      (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
      hab
      hcs
      hxy
      hε_sq_lt_sqrt_w_sq
      hB_coord
  rwa [Real.sq_sqrt hw'_nonneg] at hcoord

end
