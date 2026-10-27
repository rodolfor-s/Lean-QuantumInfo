import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import QCryptLean.Math.Analysis.VolumetricPacking
import QCryptLean.Math.LinearAlgebra.UnitaryExtension
import QCryptLean.Math.Probability.HaarMeasure

/-!
# An explicit ball floor for the Haar first-column measure on the unit sphere of `ℂ^D`

Pushing the normalised Haar measure of `U(D)` forward along `U ↦ U e₀` (the first column) gives a
probability measure `haarFirstColumnMeasure D` supported on the unit sphere of
`EuclideanSpace ℂ (Fin D)`.  Two structural facts pin its ball masses from below without any
identification of the measure:

* it is invariant under the `U(D)`-action on `EuclideanSpace ℂ (Fin D)`, because Haar measure is
  left invariant and `firstColumn (V * U) = V • firstColumn U`;
* `U(D)` acts transitively on the unit sphere, because every unit vector is the first column of
  some unitary matrix.

Hence all closed balls of a fixed radius centred on the sphere carry the same mass, and covering
the sphere by `N` such balls forces each to carry at least `1/N`.  Combined with the volumetric
covering count `Math.VolumetricPacking.exists_isCover_card_le`, this yields the explicit floor
`(1 + 2/r)^(-2D) ≤ haarFirstColumnMeasure D (closedBall x r)`.

The covering argument is the one in Vershynin, *High-Dimensional Probability* (CUP 2018), §4.2;
the Haar first-column construction is the one CKR use for the reference state,
arXiv:0809.3019, `main.tex:307-316`.

## Main definitions

- `Math.HaarSphere.firstColumn`: the first column of a unitary matrix as a Euclidean vector.
- `Math.HaarSphere.haarFirstColumnMeasure`: its Haar pushforward.

## Main statements

- `Math.HaarSphere.haarFirstColumnMeasure_closedBall_eq`: all radius-`r` closed balls centred on
  the unit sphere have equal mass.
- `Math.HaarSphere.le_haarFirstColumnMeasure_closedBall`: the explicit floor
  `(1 + 2/r)^(-2D)`.
-/

open MeasureTheory Matrix Metric Math.HaarMeasure
open scoped ENNReal NNReal

noncomputable section

namespace Math.HaarSphere

variable {D : ℕ}

/-- The first column of a unitary matrix, read as a vector of `EuclideanSpace ℂ (Fin D)`. -/
def firstColumn [NeZero D] (U : unitaryGroup (Fin D) ℂ) : EuclideanSpace ℂ (Fin D) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (U : Matrix (Fin D) (Fin D) ℂ) (EuclideanSpace.single 0 1)

/-- The action of a unitary matrix on `EuclideanSpace ℂ (Fin D)`. -/
abbrev act (V : unitaryGroup (Fin D) ℂ) : EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (V : Matrix (Fin D) (Fin D) ℂ)

/-- `act V` is a unitary continuous linear map. -/
theorem act_mem_unitary (V : unitaryGroup (Fin D) ℂ) :
    act V ∈ unitary (EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D)) := by
  have h1 : star (V : Matrix (Fin D) (Fin D) ℂ) * (V : Matrix (Fin D) (Fin D) ℂ) = 1 :=
    UnitaryGroup.star_mul_self V
  have h2 : (V : Matrix (Fin D) (Fin D) ℂ) * star (V : Matrix (Fin D) (Fin D) ℂ) = 1 :=
    mul_eq_one_comm.mp h1
  constructor
  · rw [← map_star, ← map_mul, h1, map_one]
  · rw [← map_star, ← map_mul, h2, map_one]

/-- The unitary action is norm preserving. -/
theorem norm_act (V : unitaryGroup (Fin D) ℂ) (x : EuclideanSpace ℂ (Fin D)) :
    ‖act V x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (act_mem_unitary V) x

/-- The first column of a product is the action of the left factor on the first column. -/
theorem firstColumn_mul [NeZero D] (V U : unitaryGroup (Fin D) ℂ) :
    firstColumn (V * U) = act V (firstColumn U) := by
  have hmul : ((V * U : unitaryGroup (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
      = (V : Matrix (Fin D) (Fin D) ℂ) * (U : Matrix (Fin D) (Fin D) ℂ) := rfl
  simp only [firstColumn, hmul, map_mul]
  rfl

/-- The first column has unit norm. -/
theorem norm_firstColumn [NeZero D] (U : unitaryGroup (Fin D) ℂ) : ‖firstColumn U‖ = 1 := by
  rw [firstColumn, ← show act U = Matrix.toEuclideanCLM (𝕜 := ℂ)
    (U : Matrix (Fin D) (Fin D) ℂ) from rfl, norm_act]
  simp [PiLp.norm_single]

/-- The first column, written as an `ℓ²` vector of matrix entries. -/
theorem firstColumn_eq_toLp [NeZero D] (U : unitaryGroup (Fin D) ℂ) :
    firstColumn U = WithLp.toLp 2 (fun i : Fin D => (U : Matrix (Fin D) (Fin D) ℂ) i 0) := by
  rw [firstColumn, show (EuclideanSpace.single (0 : Fin D) (1 : ℂ))
      = WithLp.toLp 2 (Pi.single (0 : Fin D) (1 : ℂ)) from rfl,
    Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single_one]
  rfl

/-- The first column, entrywise. -/
theorem firstColumn_ofLp [NeZero D] (U : unitaryGroup (Fin D) ℂ) (i : Fin D) :
    WithLp.ofLp (firstColumn U) i = (U : Matrix (Fin D) (Fin D) ℂ) i 0 := by
  rw [firstColumn_eq_toLp]

/-- `U ↦ firstColumn U` is continuous. -/
theorem continuous_firstColumn [NeZero D] : Continuous (firstColumn (D := D)) := by
  have h : (firstColumn (D := D)) = fun U : unitaryGroup (Fin D) ℂ =>
      (WithLp.toLp 2 (fun i : Fin D => (U : Matrix (Fin D) (Fin D) ℂ) i 0)) :=
    funext firstColumn_eq_toLp
  rw [h]
  refine (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => ℂ)).symm.continuous.comp ?_
  exact continuous_pi fun i =>
    (continuous_apply 0).comp ((continuous_apply i).comp continuous_subtype_val)

theorem measurable_firstColumn [NeZero D] : Measurable (firstColumn (D := D)) :=
  continuous_firstColumn.measurable

/-- **The Haar first-column measure**: the pushforward of normalised Haar measure on `U(D)`
along `U ↦ U e₀`.  It is a probability measure carried by the unit sphere of
`EuclideanSpace ℂ (Fin D)`. -/
def haarFirstColumnMeasure (D : ℕ) [NeZero D] : Measure (EuclideanSpace ℂ (Fin D)) :=
  Measure.map firstColumn (haarProbUnitary D)

instance isProbabilityMeasure_haarFirstColumnMeasure (D : ℕ) [NeZero D] :
    IsProbabilityMeasure (haarFirstColumnMeasure D) := by
  have := isProbabilityMeasure_haarProbUnitary D
  constructor
  rw [haarFirstColumnMeasure, Measure.map_apply measurable_firstColumn MeasurableSet.univ]
  simp

/-- Every unit vector of `ℂ^D` is the first column of a unitary matrix. -/
theorem exists_firstColumn_eq [NeZero D] (x : EuclideanSpace ℂ (Fin D)) (hx : ‖x‖ = 1) :
    ∃ U : unitaryGroup (Fin D) ℂ, firstColumn U = x := by
  classical
  set A : Matrix (Fin D) (Fin D) ℂ := Matrix.single 0 0 1 with hA
  set B : Matrix (Fin D) (Fin D) ℂ :=
    Matrix.of fun i j => if j = 0 then WithLp.ofLp x i else 0 with hB
  have hxsum : (∑ i : Fin D, star (WithLp.ofLp x i) * WithLp.ofLp x i) = 1 := by
    have hns : ∑ i : Fin D, ‖WithLp.ofLp x i‖ ^ 2 = 1 := by
      have h2 := congrArg (fun t : ℝ => t ^ 2) hx
      rw [EuclideanSpace.norm_eq] at h2
      simpa [Real.sq_sqrt
        (by positivity : (0:ℝ) ≤ ∑ i : Fin D, ‖WithLp.ofLp x i‖ ^ 2)] using h2
    have hstep : (∑ i : Fin D, star (WithLp.ofLp x i) * WithLp.ofLp x i)
        = ((∑ i : Fin D, ‖WithLp.ofLp x i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hstep, hns]
    norm_num
  have hgram : A.conjTranspose * A = B.conjTranspose * B := by
    ext i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · simpa [hA, hB, Matrix.mul_apply, Matrix.single, hi, hj] using hxsum.symm
    · have h0j : ¬ (0 : Fin D) = j := fun h => hj h.symm
      simp [hA, hB, Matrix.mul_apply, Matrix.single, hi, hj, h0j]
    · have h0i : ¬ (0 : Fin D) = i := fun h => hi h.symm
      simp [hA, hB, Matrix.mul_apply, Matrix.single, hi, hj, h0i]
    · have h0i : ¬ (0 : Fin D) = i := fun h => hi h.symm
      have h0j : ¬ (0 : Fin D) = j := fun h => hj h.symm
      simp [hA, hB, Matrix.mul_apply, Matrix.single, hi, hj, h0i, h0j]
  obtain ⟨U, hU_left, hU_right, hUA⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_unitary_left_mul_of_conjTranspose_mul_self_eq
      A B hgram
  refine ⟨⟨U, hU_left, hU_right⟩, ?_⟩
  apply PiLp.ext
  intro i
  have hentry := congrFun (congrFun hUA i) 0
  rw [firstColumn_ofLp]
  simpa [hA, hB, Matrix.mul_apply, Matrix.single] using hentry

/-- `U(D)` acts transitively on the unit sphere of `ℂ^D`. -/
theorem exists_act_eq [NeZero D] {x y : EuclideanSpace ℂ (Fin D)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ V : unitaryGroup (Fin D) ℂ, act V x = y := by
  obtain ⟨Ux, hUx⟩ := exists_firstColumn_eq x hx
  obtain ⟨Uy, hUy⟩ := exists_firstColumn_eq y hy
  refine ⟨Uy * Ux⁻¹, ?_⟩
  have : act (Uy * Ux⁻¹) (firstColumn Ux) = firstColumn (Uy * Ux⁻¹ * Ux) :=
    (firstColumn_mul (Uy * Ux⁻¹) Ux).symm
  rw [← hUx, this, inv_mul_cancel_right, hUy]

/-- The Haar first-column measure is invariant under the unitary action. -/
theorem haarFirstColumnMeasure_act_preimage [NeZero D] (V : unitaryGroup (Fin D) ℂ)
    {A : Set (EuclideanSpace ℂ (Fin D))} (hA : MeasurableSet A) :
    haarFirstColumnMeasure D (act V ⁻¹' A) = haarFirstColumnMeasure D A := by
  have : (haarProbUnitary D).IsMulLeftInvariant := by
    unfold haarProbUnitary haarOnUnitary
    infer_instance
  have hmeasV : Measurable (act V) := (act V).continuous.measurable
  rw [haarFirstColumnMeasure, Measure.map_apply measurable_firstColumn (hmeasV hA),
    Measure.map_apply measurable_firstColumn hA]
  have hset : (firstColumn (D := D)) ⁻¹' (act V ⁻¹' A)
      = (fun U => V * U) ⁻¹' ((firstColumn (D := D)) ⁻¹' A) := by
    ext U
    simp [Set.mem_preimage, firstColumn_mul]
  rw [hset]
  exact measure_preimage_mul (haarProbUnitary D) V _

/-- Closed balls of a fixed radius centred anywhere on the unit sphere carry the same mass. -/
theorem haarFirstColumnMeasure_closedBall_eq [NeZero D]
    {x y : EuclideanSpace ℂ (Fin D)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (r : ℝ) :
    haarFirstColumnMeasure D (closedBall x r) = haarFirstColumnMeasure D (closedBall y r) := by
  obtain ⟨V, hV⟩ := exists_act_eq hx hy
  have hpre : act V ⁻¹' (closedBall y r) = closedBall x r := by
    ext z
    have : ‖act V z - y‖ = ‖z - x‖ := by
      rw [← hV, ← map_sub, norm_act]
    simp [Set.mem_preimage, mem_closedBall, dist_eq_norm, this]
  rw [← hpre, haarFirstColumnMeasure_act_preimage V measurableSet_closedBall]

/-- The Haar first-column measure lives on the unit sphere. -/
theorem haarFirstColumnMeasure_sphere [NeZero D] :
    haarFirstColumnMeasure D (sphere (0 : EuclideanSpace ℂ (Fin D)) 1) = 1 := by
  have := isProbabilityMeasure_haarProbUnitary D
  rw [haarFirstColumnMeasure,
    Measure.map_apply measurable_firstColumn Metric.isClosed_sphere.measurableSet]
  have : (firstColumn (D := D)) ⁻¹' (sphere (0 : EuclideanSpace ℂ (Fin D)) 1) = Set.univ := by
    ext U
    simp [Set.mem_preimage, mem_sphere_iff_norm, norm_firstColumn U]
  rw [this]
  simp

/-- The real dimension of `ℂ^D`. -/
theorem finrank_real_euclideanSpace_complex (D : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin D)) = 2 * D := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin D)), Complex.finrank_real_complex]
  simp

/-- **Explicit ball floor.**  Every closed ball of radius `r > 0` centred on the unit sphere of
`ℂ^D` carries `haarFirstColumnMeasure`-mass at least `(1 + 2/r)^(-2D)`.

The proof is invariance plus a covering pigeonhole: a maximal `r`-separated subset of the sphere
is an `r`-cover, its cardinality is bounded by the volumetric count of
`Math.VolumetricPacking.exists_isCover_card_le`, and all the covering balls have equal mass. -/
theorem le_haarFirstColumnMeasure_closedBall [NeZero D]
    {x : EuclideanSpace ℂ (Fin D)} (hx : ‖x‖ = 1) {r : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal (((1 : ℝ) + 2 / r) ^ (2 * D)))⁻¹
      ≤ haarFirstColumnMeasure D (closedBall x r) := by
  classical
  set S : Set (EuclideanSpace ℂ (Fin D)) := sphere (0 : EuclideanSpace ℂ (Fin D)) 1 with hS
  have hSsub : S ⊆ closedBall (0 : EuclideanSpace ℂ (Fin D)) 1 := sphere_subset_closedBall
  have hrnn : (0 : ℝ≥0) < r.toNNReal := by
    simpa [Real.toNNReal_pos] using hr
  have hcoe : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr.le
  obtain ⟨N, hNS, hNcover, hNcard⟩ :=
    Math.VolumetricPacking.exists_isCover_card_le
      (Module.finBasis ℝ (EuclideanSpace ℂ (Fin D))).addHaar hrnn zero_le_one hSsub
  have hNcard' : (N.card : ℝ) ≤ ((1 : ℝ) + 2 / r) ^ (2 * D) := by
    have hEq : (2 * (1 : ℝ) + r) / r = 1 + 2 / r := by field_simp; ring
    rw [finrank_real_euclideanSpace_complex, hcoe, hEq] at hNcard
    exact hNcard
  -- the cover controls the total mass
  have hcover : S ⊆ ⋃ p ∈ N, closedBall p r := by
    intro z hz
    obtain ⟨p, hpN, hdist⟩ := hNcover hz
    refine Set.mem_iUnion₂.mpr ⟨p, hpN, ?_⟩
    have : edist z p ≤ (r.toNNReal : ℝ≥0∞) := hdist
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, hcoe,
      ENNReal.ofReal_le_ofReal_iff hr.le] at this
    simpa [mem_closedBall] using this
  have hmass : (1 : ℝ≥0∞) ≤ ∑ p ∈ N, haarFirstColumnMeasure D (closedBall p r) := by
    calc (1 : ℝ≥0∞) = haarFirstColumnMeasure D S := (haarFirstColumnMeasure_sphere).symm
      _ ≤ haarFirstColumnMeasure D (⋃ p ∈ N, closedBall p r) := measure_mono hcover
      _ ≤ ∑ p ∈ N, haarFirstColumnMeasure D (closedBall p r) :=
          measure_biUnion_finset_le N _
  -- all summands equal the mass at `x`
  have hconst : ∀ p ∈ N, haarFirstColumnMeasure D (closedBall p r)
      = haarFirstColumnMeasure D (closedBall x r) := by
    intro p hp
    have hpS : p ∈ S := hNS (by exact_mod_cast hp)
    have hpnorm : ‖p‖ = 1 := by simpa [hS, mem_sphere_iff_norm] using hpS
    exact haarFirstColumnMeasure_closedBall_eq hpnorm hx r
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hmass
  -- turn the pigeonhole into the stated floor
  set m : ℝ≥0∞ := haarFirstColumnMeasure D (closedBall x r) with hm
  have hNpos : 0 < N.card := by
    rcases Nat.eq_zero_or_pos N.card with h0 | h
    · rw [h0] at hmass; simp at hmass
    · exact h
  have hfloor : (N.card : ℝ≥0∞)⁻¹ ≤ m := by
    calc (N.card : ℝ≥0∞)⁻¹ = (N.card : ℝ≥0∞)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (N.card : ℝ≥0∞)⁻¹ * ((N.card : ℝ≥0∞) * m) := by
          exact mul_le_mul_right hmass _
      _ = ((N.card : ℝ≥0∞)⁻¹ * (N.card : ℝ≥0∞)) * m := (mul_assoc _ _ _).symm
      _ = m := by
          rw [ENNReal.inv_mul_cancel (by exact_mod_cast hNpos.ne') (by simp), one_mul]
  refine le_trans ?_ hfloor
  refine ENNReal.inv_le_inv.mpr ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hNcard'

end Math.HaarSphere

end
