import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin

/-! # IIDCumulative -/


namespace InfoTheory.SmoothMinEntropy.AEP.IID.Cumulative

variable {d : ℕ}

/-- Real tuple shifted to `Fin (d+1)` by prepending `0`. -/
noncomputable def lamShift (lam : Fin d → ℝ) : Fin (d + 1) → ℝ := Fin.cases 0 lam

@[simp] lemma lamShift_zero (lam : Fin d → ℝ) : lamShift lam 0 = 0 := by
  simp [lamShift]

@[simp] lemma lamShift_succ (lam : Fin d → ℝ) (z : Fin d) :
    lamShift lam z.succ = lam z := by
  simp [lamShift]

/-- Renner's spectral increment `β z = lam z - lam (z-1)`, with the convention
`lam (-1) = 0` so that `β` of the minimal index is `lam` itself. -/
noncomputable def betaIncr (lam : Fin d → ℝ) (z : Fin d) : ℝ :=
  lamShift lam z.succ - lamShift lam z.castSucc

/-- For a nondecreasing nonnegative tuple, the increments are nonnegative. -/
lemma betaIncr_nonneg (lam : Fin d → ℝ) (hmono : Monotone lam)
    (hnonneg : ∀ z, 0 ≤ lam z) (z : Fin d) : 0 ≤ betaIncr lam z := by
  unfold betaIncr
  rw [lamShift_succ]
  have hle : lamShift lam z.castSucc ≤ lam z := by
    rcases Fin.eq_zero_or_eq_succ z.castSucc with h | ⟨w, hw⟩
    · rw [h, lamShift_zero]; exact hnonneg z
    · rw [hw, lamShift_succ]
      apply hmono
      have hval := congrArg Fin.val hw
      simp only [Fin.val_castSucc, Fin.val_succ] at hval
      rw [Fin.le_def]; omega
  linarith

/-- The shifted tuple read as a total `ℕ`-indexed function (extended by `0`). -/
noncomputable def lamNat (lam : Fin d → ℝ) (j : ℕ) : ℝ :=
  if h : j < d + 1 then lamShift lam ⟨j, h⟩ else 0

lemma lamNat_succ (lam : Fin d → ℝ) (z : Fin d) :
    lamNat lam (z.val + 1) = lam z := by
  unfold lamNat
  rw [dite_eq_left (by omega : z.val + 1 < d + 1)]
  have : (⟨z.val + 1, by omega⟩ : Fin (d + 1)) = z.succ := by apply Fin.ext; simp [Fin.val_succ]
  rw [this, lamShift_succ]

lemma lamNat_castSucc (lam : Fin d → ℝ) (z : Fin d) :
    lamNat lam z.val = lamShift lam z.castSucc := by
  unfold lamNat
  rw [dite_eq_left (by omega : z.val < d + 1)]
  have : (⟨z.val, by omega⟩ : Fin (d + 1)) = z.castSucc := by apply Fin.ext; simp [Fin.val_castSucc]
  rw [this]

lemma lamNat_zero (lam : Fin d → ℝ) : lamNat lam 0 = 0 := by
  unfold lamNat
  rw [dite_eq_left (by omega : (0 : ℕ) < d + 1)]
  have : (⟨0, by omega⟩ : Fin (d + 1)) = 0 := by apply Fin.ext; simp
  rw [this, lamShift_zero]

/-- Telescoping: `lam z = ∑_{z' ≤ z} β z'`. -/
lemma sum_betaIncr_filter_le_eq (lam : Fin d → ℝ) (z : Fin d) :
    (Finset.univ.filter (fun z' => z' ≤ z)).sum (fun z' => betaIncr lam z') = lam z := by
  have hset : Finset.univ.filter (fun z' => z' ≤ z) = Finset.Iic z := by
    ext x; simp [Finset.mem_Iic]
  have hbeta : ∀ z' : Fin d, betaIncr lam z' = lamNat lam (z'.val + 1) - lamNat lam z'.val := by
    intro z'
    rw [lamNat_succ, lamNat_castSucc, betaIncr, lamShift_succ]
  rw [hset, Finset.sum_congr rfl (fun z' _ => hbeta z')]
  -- Reindex the `Finset.Iic z` sum (over `Fin d`) to a `Finset.range` sum.
  have reindex : (Finset.Iic z).sum (fun z' => lamNat lam (z'.val + 1) - lamNat lam z'.val)
      = ∑ j ∈ Finset.range (z.val + 1), (lamNat lam (j + 1) - lamNat lam j) := by
    apply Finset.sum_bij (fun (z' : Fin d) _ => z'.val)
    · intro a ha
      rw [Finset.mem_Iic] at ha
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le ha
    · intro a₁ _ a₂ _ h; exact Fin.ext h
    · intro b hb
      rw [Finset.mem_range] at hb
      exact ⟨⟨b, by omega⟩, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hb), rfl⟩
    · intro a _; rfl
  rw [reindex, Finset.sum_range_sub (lamNat lam) (z.val + 1), lamNat_succ, lamNat_zero, sub_zero]

end InfoTheory.SmoothMinEntropy.AEP.IID.Cumulative
