import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Star
import Mathlib.Topology.Instances.Matrix

/-!
# Haar Measure on the Unitary Group — compactness, Borel σ-algebra, probability measure

Topological and measure-theoretic infrastructure for the unitary group U(d).

## Main definitions
- `haarOnUnitary`: Unnormalized Haar measure on U(d)
- `haarProbUnitary`: Normalized (probability) Haar measure on U(d)

## Main statements
- `instCompactSpaceUnitaryGroup`: U(d) is compact
- `isProbabilityMeasure_haarProbUnitary`: The normalized measure is a probability measure
-/

open MeasureTheory Matrix
open scoped Matrix

noncomputable section

namespace Math.HaarMeasure

/-- The unitary group U(d) over ℂ is a topological group.
    Multiplication is continuous (from `ContinuousMul` on matrices).
    Inversion is continuous because U⁻¹ = U† and star is continuous on matrices. -/
instance instIsTopologicalGroupUnitaryGroup {d : ℕ} :
    IsTopologicalGroup (unitaryGroup (Fin d) ℂ) where
  continuous_mul := continuous_mul
  continuous_inv := by
    -- inv = star on unitaryGroup (UnitaryGroup.inv_val), star is continuous on matrices
    rw [continuous_induced_rng]
    have h : (Subtype.val ∘ fun (a : unitaryGroup (Fin d) ℂ) => a⁻¹) =
             (Star.star ∘ (Subtype.val : unitaryGroup (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)) := by
      funext a; exact UnitaryGroup.inv_val a
    rw [h]
    exact continuous_star.comp continuous_subtype_val

/-- The unitary group U(d) is compact: closed (preimage of {I} under continuous
    star-multiply maps) and bounded (entries have norm ≤ 1) in M_{d×d}(ℂ). -/
instance instCompactSpaceUnitaryGroup {d : ℕ} :
    CompactSpace (unitaryGroup (Fin d) ℂ) := by
  rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ]
  let row_box : Set (Fin d → ℂ) := {f | ∀ j, f j ∈ Metric.closedBall (0 : ℂ) 1}
  let box : Set (Fin d → Fin d → ℂ) := {M | ∀ i, M i ∈ row_box}
  have hbox : IsCompact box := isCompact_pi_infinite fun _ =>
    isCompact_pi_infinite fun _ => isCompact_closedBall 0 1
  have hsub : Set.range (Subtype.val : unitaryGroup (Fin d) ℂ → _) ⊆ box := by
    rintro M ⟨U, rfl⟩ i j
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact entry_norm_bound_of_unitary U.prop i j
  have hclosed : IsClosed (Set.range (Subtype.val : unitaryGroup (Fin d) ℂ → _)) := by
    rw [Subtype.range_coe_subtype]
    simp only [unitaryGroup]
    exact (isClosed_singleton.preimage (continuous_star.mul continuous_id)).inter
      (isClosed_singleton.preimage (continuous_id.mul continuous_star))
  exact hbox.of_isClosed_subset hclosed hsub

/-- Borel σ-algebra on the unitary group from its subspace topology. -/
instance instMeasurableSpaceUnitaryGroup {d : ℕ} :
    MeasurableSpace (unitaryGroup (Fin d) ℂ) := borel _

instance instBorelSpaceUnitaryGroup {d : ℕ} :
    BorelSpace (unitaryGroup (Fin d) ℂ) := ⟨rfl⟩

/-- Locally compact space instance (follows from compact + T2).
    Chain: CompactSpace → WeaklyLocallyCompactSpace (Mathlib instance),
    then WeaklyLocallyCompactSpace + R1Space → LocallyCompactSpace.
    R1Space holds because U(d) inherits T2 from matrices over ℂ. -/
instance instLocallyCompactSpaceUnitaryGroup {d : ℕ} :
    LocallyCompactSpace (unitaryGroup (Fin d) ℂ) :=
  WeaklyLocallyCompactSpace.locallyCompactSpace

/-- The (unnormalized) Haar measure on U(d). Exists by Mathlib's Haar measure
    construction for locally compact topological groups. -/
noncomputable def haarOnUnitary (d : ℕ) :
    Measure (unitaryGroup (Fin d) ℂ) :=
  Measure.haar

/-- The Haar measure on U(d) has finite mass (since U(d) is compact).
    Uses `IsHaarMeasure` → `IsFiniteMeasureOnCompacts` → compact + univ measurable. -/
lemma haarOnUnitary_finite (d : ℕ) :
    haarOnUnitary d Set.univ < ⊤ := by
  unfold haarOnUnitary
  have : Measure.IsHaarMeasure (Measure.haar : Measure (unitaryGroup (Fin d) ℂ)) := inferInstance
  exact IsCompact.measure_lt_top isCompact_univ

/-- The Haar measure on U(d) has positive mass (nonempty compact group).
    Follows from `IsHaarMeasure` which guarantees the measure is nonzero,
    hence `μ univ > 0`. -/
lemma haarOnUnitary_pos (d : ℕ) :
    0 < haarOnUnitary d Set.univ := by
  unfold haarOnUnitary
  exact pos_iff_ne_zero.mpr (@Measure.IsOpenPosMeasure.open_pos (unitaryGroup (Fin d) ℂ)
    _ _ Measure.haar _ Set.univ isOpen_univ Set.univ_nonempty)

/-- Normalized (probability) Haar measure on U(d). -/
noncomputable def haarProbUnitary (d : ℕ) :
    Measure (unitaryGroup (Fin d) ℂ) :=
  (haarOnUnitary d Set.univ)⁻¹ • haarOnUnitary d

/-- The normalized Haar measure is a probability measure. -/
lemma isProbabilityMeasure_haarProbUnitary (d : ℕ) :
    IsProbabilityMeasure (haarProbUnitary d) := by
  constructor
  simp only [haarProbUnitary, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.inv_mul_cancel]
  · exact ne_of_gt (haarOnUnitary_pos d)
  · exact ne_of_lt (haarOnUnitary_finite d)

/-- **The Haar measure on the compact unitary group `U(d)` is right-invariant.**

Compact groups are unimodular: the left Haar measure is also right-invariant.  On `U(d)`
(compact, Hausdorff, second-countable) the right-translate `μ ∘ (· * g)` is itself a
left-invariant measure finite on compacts, hence a scalar multiple of `μ` by uniqueness of
Haar measure on a compact space; the scalar is forced to `1` because right translation is a
measurable automorphism preserving the total (finite) mass.  This is the analytic input that
makes `U(d)`-Haar averages invariant under the substitution `U ↦ U·W`, the right-translation
companion of the left-invariance already used in this development. -/
instance isMulRightInvariant_haarOnUnitary (d : ℕ) :
    (haarOnUnitary d).IsMulRightInvariant := by
  unfold haarOnUnitary
  set μ : Measure (unitaryGroup (Fin d) ℂ) := Measure.haar with hμdef
  refine ⟨fun g => ?_⟩
  -- `ν := map (· * g) μ` is left-invariant (right and left translation commute).
  set ν : Measure (unitaryGroup (Fin d) ℂ) := Measure.map (fun x => x * g) μ with hνdef
  have hRmeas : Measurable (fun x : unitaryGroup (Fin d) ℂ => x * g) := by fun_prop
  have hμFin : IsFiniteMeasure μ := by
    rw [hμdef]; exact ⟨IsCompact.measure_lt_top isCompact_univ⟩
  have hνLI : ν.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    rw [hνdef, Measure.map_map (by fun_prop) hRmeas]
    have hcomm : (fun x : unitaryGroup (Fin d) ℂ => h * x) ∘ (fun x => x * g)
        = (fun x => x * g) ∘ (fun x => h * x) := by funext x; simp [mul_assoc]
    rw [hcomm, ← Measure.map_map hRmeas (by fun_prop), map_mul_left_eq_self]
  have hνFin : IsFiniteMeasure ν := by
    rw [hνdef]; exact μ.isFiniteMeasure_map (fun x => x * g)
  have hνFinC : IsFiniteMeasureOnCompacts ν := inferInstance
  -- By uniqueness on the compact group, `ν = c • μ`.
  have hsmul : ν = Measure.haarScalarFactor ν μ • μ :=
    Measure.isMulInvariant_eq_smul_of_compactSpace ν μ
  -- The scalar is `1`: right translation preserves the total mass and `μ univ` is finite/nonzero.
  have hmass : ν Set.univ = μ Set.univ := by
    rw [hνdef, Measure.map_apply hRmeas MeasurableSet.univ]; simp
  have hfin : μ Set.univ ≠ ⊤ := ne_of_lt (IsCompact.measure_lt_top isCompact_univ)
  have hpos : μ Set.univ ≠ 0 :=
    ne_of_gt (pos_iff_ne_zero.mpr (@Measure.IsOpenPosMeasure.open_pos _ _ _ μ _ Set.univ
      isOpen_univ Set.univ_nonempty))
  set c := Measure.haarScalarFactor ν μ with hc
  have hc1 : c = 1 := by
    have huniv := congrArg (fun m => m Set.univ) hsmul
    simp only [Measure.smul_apply] at huniv
    rw [hmass] at huniv
    -- `μ univ = c * μ univ` with `μ univ` finite, nonzero ⟹ `c = 1`.
    have heq : (c : ENNReal) * μ Set.univ = 1 * μ Set.univ := by
      rw [one_mul]; exact huniv.symm
    have hcast : (c : ENNReal) = 1 := (ENNReal.mul_left_inj hpos hfin).mp heq
    exact_mod_cast hcast
  rw [hsmul, hc1, one_smul]

end Math.HaarMeasure
