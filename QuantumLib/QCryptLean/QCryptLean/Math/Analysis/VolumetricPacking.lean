import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Volumetric packing and covering bounds in a finite-dimensional real normed space

An `ε`-separated subset of a ball of radius `R` in a `d`-dimensional real normed space has at
most `((2 * R + ε) / ε) ^ d` elements: the open balls of radius `ε / 2` around its points are
pairwise disjoint and all sit inside the ball of radius `R + ε / 2`, so an additive Haar measure
counts them.  Consequently a maximal separated subset is a finite `ε`-cover of the same size.

The argument is the standard volumetric one of Vershynin, *High-Dimensional Probability*
(CUP 2018), §4.2 — the reference `Mathlib/Topology/MetricSpace/CoveringNumbers.lean` itself cites
for its `coveringNumber` / `packingNumber` framework.

## Main statements

- `Math.VolumetricPacking.card_le_of_pairwise_dist_ge`: the finite volumetric count.
- `Math.VolumetricPacking.packingNumber_le_of_subset_closedBall`: the same bound for
  `Metric.packingNumber`.
- `Math.VolumetricPacking.exists_isCover_card_le`: a finite `ε`-cover of a bounded set whose
  cardinality obeys the volumetric bound.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace Math.VolumetricPacking

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- **Volumetric packing count.**  A finite set of points of norm at most `R` whose pairwise
distances are at least `ε > 0` has at most `((2 * R + ε) / ε) ^ (finrank ℝ E)` elements. -/
theorem card_le_of_pairwise_dist_ge (μ : Measure E) [μ.IsAddHaarMeasure]
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) (P : Finset E)
    (hsub : ∀ x ∈ P, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ε ≤ dist x y) :
    (P.card : ℝ) ≤ ((2 * R + ε) / ε) ^ (Module.finrank ℝ E) := by
  set d := Module.finrank ℝ E with hd
  -- the small balls are pairwise disjoint
  have hdisj : (↑P : Set E).PairwiseDisjoint fun x => ball x (ε / 2) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr fun z hzx hzy => ?_
    have h1 : dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
    have h2 : dist x z < ε / 2 := by simpa [dist_comm] using hzx
    have h3 : dist z y < ε / 2 := by simpa [dist_comm] using hzy
    have := hsep x hx y hy hxy
    linarith
  -- the union of the small balls sits inside a big ball
  have hsubset : (⋃ x ∈ P, ball x (ε / 2)) ⊆ ball (0 : E) (R + ε / 2) := by
    intro z hz
    simp only [Set.mem_iUnion, exists_prop] at hz
    obtain ⟨x, hxP, hzx⟩ := hz
    have hxR : ‖x‖ ≤ R := hsub x hxP
    have : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
      simpa using norm_add_le (z - x) x
    have hzx' : ‖z - x‖ < ε / 2 := by simpa [dist_eq_norm] using hzx
    simpa [mem_ball, dist_eq_norm] using lt_of_le_of_lt this (by linarith)
  have hball_pos : 0 < μ (ball (0 : E) 1) := measure_ball_pos μ 0 one_pos
  have hball_lt_top : μ (ball (0 : E) 1) < ⊤ := measure_ball_lt_top
  -- count with the Haar measure
  have hsum : (∑ _x ∈ P, ENNReal.ofReal ((ε / 2) ^ d) * μ (ball (0 : E) 1))
      ≤ ENNReal.ofReal ((R + ε / 2) ^ d) * μ (ball (0 : E) 1) := by
    calc (∑ _x ∈ P, ENNReal.ofReal ((ε / 2) ^ d) * μ (ball (0 : E) 1))
        = ∑ x ∈ P, μ (ball x (ε / 2)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Measure.addHaar_ball μ x (by positivity)]
      _ = μ (⋃ x ∈ P, ball x (ε / 2)) :=
          (measure_biUnion_finset hdisj fun x _ => measurableSet_ball).symm
      _ ≤ μ (ball (0 : E) (R + ε / 2)) := measure_mono hsubset
      _ = ENNReal.ofReal ((R + ε / 2) ^ d) * μ (ball (0 : E) 1) :=
          Measure.addHaar_ball μ 0 (by positivity)
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc] at hsum
  have hcancel : (P.card : ℝ≥0∞) * ENNReal.ofReal ((ε / 2) ^ d)
      ≤ ENNReal.ofReal ((R + ε / 2) ^ d) :=
    (ENNReal.mul_le_mul_iff_left hball_pos.ne' hball_lt_top.ne).mp hsum
  -- move to the reals
  have hreal : (P.card : ℝ) * (ε / 2) ^ d ≤ (R + ε / 2) ^ d := by
    have h1 : ENNReal.ofReal ((P.card : ℝ) * (ε / 2) ^ d)
        ≤ ENNReal.ofReal ((R + ε / 2) ^ d) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      simpa [ENNReal.ofReal_natCast] using hcancel
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have hpos : (0 : ℝ) < (ε / 2) ^ d := by positivity
  have : (P.card : ℝ) ≤ (R + ε / 2) ^ d / (ε / 2) ^ d := (le_div_iff₀ hpos).mpr hreal
  calc (P.card : ℝ) ≤ (R + ε / 2) ^ d / (ε / 2) ^ d := this
    _ = ((R + ε / 2) / (ε / 2)) ^ d := (div_pow _ _ d).symm
    _ = ((2 * R + ε) / ε) ^ d := by
        congr 1
        field_simp

/-- **Volumetric packing bound for `Metric.packingNumber`.** -/
theorem packingNumber_le_of_subset_closedBall (μ : Measure E) [μ.IsAddHaarMeasure]
    {ε : ℝ≥0} (hε : 0 < ε) {R : ℝ} (hR : 0 ≤ R) {S : Set E}
    (hS : S ⊆ closedBall (0 : E) R) {K : ℕ}
    (hK : ((2 * R + (ε : ℝ)) / (ε : ℝ)) ^ (Module.finrank ℝ E) ≤ K) :
    Metric.packingNumber ε S ≤ (K : ℕ∞) := by
  have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  -- every finite separated subset obeys the volumetric count
  have hfin : ∀ F : Finset E, (↑F : Set E) ⊆ S → Metric.IsSeparated ε (↑F : Set E) →
      F.card ≤ K := by
    intro F hFS hFsep
    have hsub : ∀ x ∈ F, ‖x‖ ≤ R := by
      intro x hx
      have := hS (hFS (by exact_mod_cast hx))
      simpa [mem_closedBall, dist_eq_norm] using this
    have hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → (ε : ℝ) ≤ dist x y := by
      intro x hx y hy hxy
      have h : ((ε : ℝ≥0∞)) < edist x y := hFsep (by exact_mod_cast hx) (by exact_mod_cast hy) hxy
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h
      exact h.le
    have := card_le_of_pairwise_dist_ge μ hε' hR F hsub hsep
    exact_mod_cast this.trans hK
  -- hence so does every separated subset
  have hall : ∀ C : Set E, C ⊆ S → Metric.IsSeparated ε C → C.encard ≤ (K : ℕ∞) := by
    intro C hCS hCsep
    by_contra hcon
    push Not at hcon
    have hinf : ∃ F : Finset E, (↑F : Set E) ⊆ C ∧ F.card = K + 1 := by
      rcases C.finite_or_infinite with hCfin | hCinf
      · refine ⟨hCfin.toFinset, by simp, ?_⟩
        have : (hCfin.toFinset.card : ℕ∞) = C.encard := by
          simp [hCfin.encard_eq_coe_toFinset_card]
        exfalso
        exact absurd (this ▸ hcon) (by
          have : (K : ℕ∞) < (hCfin.toFinset.card : ℕ∞) := this ▸ hcon
          have : K < hCfin.toFinset.card := by exact_mod_cast this
          exact fun h => absurd (hfin hCfin.toFinset (by simpa using hCS)
            (hCsep.mono (by simp))) (by omega))
      · exact hCinf.exists_subset_card_eq (K + 1)
    obtain ⟨F, hFC, hFcard⟩ := hinf
    have := hfin F (hFC.trans hCS) (hCsep.mono hFC)
    omega
  simp only [Metric.packingNumber, iSup_le_iff]
  exact fun C hCS hCsep => hall C hCS hCsep

/-- **A bounded set has a finite `ε`-cover obeying the volumetric bound.**  The cover is a
maximal `ε`-separated subset of the set itself. -/
theorem exists_isCover_card_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {ε : ℝ≥0} (hε : 0 < ε) {R : ℝ} (hR : 0 ≤ R) {S : Set E}
    (hS : S ⊆ closedBall (0 : E) R) :
    ∃ N : Finset E, (↑N : Set E) ⊆ S ∧ Metric.IsCover ε S (↑N : Set E) ∧
      (N.card : ℝ) ≤ ((2 * R + (ε : ℝ)) / (ε : ℝ)) ^ (Module.finrank ℝ E) := by
  set K : ℕ := ⌈((2 * R + (ε : ℝ)) / (ε : ℝ)) ^ (Module.finrank ℝ E)⌉₊ with hKdef
  have hK : ((2 * R + (ε : ℝ)) / (ε : ℝ)) ^ (Module.finrank ℝ E) ≤ K := Nat.le_ceil _
  have hpack := packingNumber_le_of_subset_closedBall μ hε hR hS hK
  have hne : Metric.packingNumber ε S ≠ ⊤ := by
    intro h
    rw [h] at hpack
    simp at hpack
  set C := Metric.maximalSeparatedSet ε S with hC
  have hCsub : C ⊆ S := Metric.maximalSeparatedSet_subset
  have hCcover : Metric.IsCover ε S C := Metric.isCover_maximalSeparatedSet hne
  have hCcard : C.encard = Metric.packingNumber ε S := Metric.encard_maximalSeparatedSet hne
  have hCfin : C.Finite := by
    rw [← Set.encard_ne_top_iff, hCcard]
    exact hne
  refine ⟨hCfin.toFinset, by simpa using hCsub, by simpa using hCcover, ?_⟩
  -- the volumetric count applies to the maximal separated set itself
  have hsub : ∀ x ∈ hCfin.toFinset, ‖x‖ ≤ R := by
    intro x hx
    have := hS (hCsub (by simpa using hx))
    simpa [mem_closedBall, dist_eq_norm] using this
  have hsep : ∀ x ∈ hCfin.toFinset, ∀ y ∈ hCfin.toFinset, x ≠ y → (ε : ℝ) ≤ dist x y := by
    intro x hx y hy hxy
    have h : ((ε : ℝ≥0∞)) < edist x y :=
      Metric.isSeparated_maximalSeparatedSet (by simpa using hx) (by simpa using hy) hxy
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h
    exact h.le
  exact card_le_of_pairwise_dist_ge μ (by exact_mod_cast hε) hR hCfin.toFinset hsub hsep

end Math.VolumetricPacking

end
